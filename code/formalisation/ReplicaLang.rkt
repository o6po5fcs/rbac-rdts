#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                   ;;;
;;; ReplicaLang                                                       ;;;
;;;                                                                   ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ReplicaLang models the behaviour of a (well-behaved) client which ;;;
;;; interacts with a local replica by evaluating program expressions. ;;;
;;;                                                                   ;;;
;;; More concretely, ReplicaLang specifies:                           ;;;
;;;    - programs,                                                    ;;;
;;;    - values,                                                      ;;;
;;;    - expressions,                                                 ;;;
;;;    - cursors into local replicas, and                             ;;;
;;;    - local replica objects.                                       ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require redex/reduction-semantics
         "CommonLang.rkt"
         "primitive-operations.rkt")

(provide ReplicaLang red-replica red-replica-malicious)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The core ReplicaLang formal language ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-extended-language ReplicaLang CommonLang
  ; Programs (the terms ReplicaLang's core reduction relation operates on)
  (program ::= ((r ...) e))

  ; Values
  (v ::=
     (λ (x ...) e)
     atom
     c)

  ; Expressions
  (e ::= 
     x
     v
     (e e ...)
     (op e ...)
     (if e e e)
     (let ([x e] ...) e)
     (root e)
     (• e k) ; : • c k
     (•! e k e) ; : •! c k v
     (error string))

  ; Operators
  (op ::= + - / * and or not < > =)

  ; Cursors (accumulate a path into a replica object)
  (c ::= (ι_^r p))

  ; Replica objects: name, policy excerpt, actual replicated JSON data,
  ; user environment, and accumulated changes
  (r ::= (ι_^r (priv ...) d env (δ ...)))

  ; Identifiers (replica id)
  (ι ::= string)

  ; Local variables
  (x ::= variable-not-otherwise-mentioned)


  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (let ([x e_x] ...) e_body #:refers-to (shadow x ...)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Extension of ReplicaLang with support for "holes" for the reduction relations ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-extended-language ReplicaLang-inner ReplicaLang
  (E hole
     (E e ...)
     ((λ (x ...) e) v ... E e ...)
     (op v ... E e ...)
     (let ((x v)... (x E) (x e) ...) e)
     (if E e e)
     (root E)
     (• E k)
     (•! E k e)
     (•! c k E)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The core ReplicaLang reduction relation.              ;;
;;                                                       ;;
;; Reduces (a list of replica objects and) an expression ;;
;; to a new (list of replica objects and) expression.    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define red-replica
  (reduction-relation
   ReplicaLang-inner
   #:domain program
   #:codomain program
   (--> ((r ...) (in-hole E (if #f e_1 e_2)))
        ((r ...) (in-hole E e_2))
        "if #f")
   (--> ((r ...) (in-hole E (if v e_1 e_2)))
        ((r ...) (in-hole E e_1))
        "if #t"
        (judgment-holds (distinct v #f)))
   (--> ((r ...) (in-hole E (let ([x v] ...) e)))
        ((r ...) (in-hole E (substitute e [x v] ...)))
        "let")
   (--> ((r ...) (in-hole E ((λ (x ...) e) v ...)))
        ((r ...) (in-hole E (substitute e [x v] ...)))
        "apply")
   (--> ((r ...) (in-hole E (op v ...)))
        ((r ...) (in-hole E (apply-racket-op op v ...)))
        "apply-rkt")
   (--> [(r ...) (in-hole E (root ι_^r))]
        [(r ...) (in-hole E (ι_^r ()))]
        "root-cursor")
   (--> [(r ...) (in-hole E (• (ι_^r (k_1 ...)) k_2))]
        [(r ...) (in-hole E v)]
        (judgment-holds (element-of (ι_^r _ d _ _) (r ...)))
        (where v (json-read ι_^r d (k_1 ... k_2) (k_1 ... k_2)))
        "read")
   (--> [(r ...) (in-hole E (• (ι_^r (k_1 ...)) k_2))]
        [(r ...) (error string)]
        (judgment-holds (element-of (ι_^r _ d _ _) (r ...)))
        (where (error string) (json-read ι_^r d (k_1 ... k_2) (k_1 ... k_2)))
        "¬read")
   (--> [(r ...) (in-hole E (•! (ι_^r (k_1 ...)) k_2 atom))]
        [((ι_^r (priv ...) d_new env (δ ... (! (k_1 ... k_2) atom))) r_other ...) (in-hole E atom)]
        (judgment-holds (element-of r_c (r ...)))
        (where (ι_^r (priv ...) d env (δ ...)) r_c)
        (judgment-holds (is-writable d (k_1 ... k_2) (priv ...) env))
        (where (r_other ...) (list-without (r ...) r_c))
        (where d_new (json-write d (k_1 ... k_2) atom))
        "write")
   (--> [(r ...) (in-hole E (•! (ι_^r (k_1 ...)) k_2 atom))]
        [(r ...) (error "Write forbidden"#;(,(format "Write to ~s of ~s failed: privileges were ~s."
                                                     (term k_2) (term (ι_^r (k_1 ...))) (term (priv ...)))))]
        (judgment-holds (element-of (ι_^r (priv ...) d env _) (r ...)))
        (judgment-holds (¬is-writable d (k_1 ... k_2) (priv ...) env))
        "¬write-¬w")
   (--> [(r ...) (in-hole E (•! (ι_^r (k_1 ...)) k_2 v))]
        [(r ...) (error "Write forbidden")]
        (judgment-holds (¬is-atom v))
        "¬write-¬a")
   ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A malicious extension of the core ReplicaLang reduction relation.           ;;
;;                                                                             ;;
;; This reduction relation is used only in the CLI to model malicious clients, ;;
;; demonstrating the results of a client bypassing Offline Policy Enforcement. ;;
;; Specifically, LeaderLang will still succeed in preventing both Replicated   ;;
;; Data Leaks and Data Contagion.                                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define red-replica-malicious
  (extend-reduction-relation
   red-replica
   ReplicaLang-inner
   (--> [(r ...) (in-hole E (•! (ι_^r (k_1 ...)) k_2 atom))]
        [((ι_^r (priv ...) d_new env (δ ... (! (k_1 ... k_2) atom))) r_other ...) (in-hole E atom)]
        (judgment-holds (element-of r_c (r ...)))
        (where (ι_^r (priv ...) d env (δ ...)) r_c)
        (where (r_other ...) (list-without (r ...) r_c))
        (where d_new (json-write d (k_1 ... k_2) atom))
        "write-malicious")))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Implementation of the primitive operators of ReplicaLang. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction ReplicaLang-inner
  apply-racket-op : op v ... -> v
  [(apply-racket-op op v ...)
   ,(apply (match (term op)
             ['+ +]
             ['- -]
             ['* *]
             ['/ /]
             ['and logical-and]
             ['or logical-or]
             ['not not]
             ['< <]
             ['> >]
             ['= =]
             [_ (error "Unknown primitive operation" (term op))])
           (term (v ...)))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reads a value from a replica object.                     ;;
;;                                                          ;;
;; Returns either the read atom, a cursor into the replica  ;;
;; object, or an error in case the value does not exist.    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction ReplicaLang-inner
  json-read : ι_^r json p_remaining p_complete -> v or (error string)
  ;; Reached destination, found atom -> return atom
  [(json-read ι_^r atom () p_complete)
   atom]
  ;; Reached destination, found empty object -> return empty object
  [(json-read ι_^r () () p_complete)
   ()]
  ;; Reached destination, found json -> return cursor to complete path
  [(json-read ι_^r json () p_complete)
   (ι_^r p_complete)]
  ;; Not at destination, found json -> try with first key/value pair
  [(json-read ι_^r ((k_1 := json_1) kj_2 ...) (k_1 k_3 ...) p_complete)
   (json-read ι_^r json_1 (k_3  ...) p_complete)]
  ;; Not at destination, found json, first key doesn't match -> recurse
  [(json-read ι_^r (kj_1 kj_2 ...) (k ...) p_complete)
   (json-read ι_^r (kj_2 ...) (k ...) p_complete)]
  ;; Any other read is invalid
  [(json-read ι_^r json p_1 p_complete)
   (error "Read failed"#;(,(format "Could not read path ~s into replica ~s: path does not exist."
                                      (term p_1)
                                      (term ι_^r))))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary judgment form: holds if the argument value is not an atom. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-judgment-form
  ReplicaLang
  #:mode     (¬is-atom I)
  #:contract (¬is-atom v)

  [-------------------- "Cursor"
   (¬is-atom c)]

  [-------------------- "Lambda"
   (¬is-atom (λ (x ...) e))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary judgment form: inverts is-writable. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-judgment-form
  ReplicaLang-inner
  #:mode     (¬is-writable I I I I)
  #:contract (¬is-writable d p (priv ...) d)

  [(where #f ,(term (is-writable d p (priv ...) env)))
   -------------------- "Invert result"
   (¬is-writable d p (priv ...) env)])
