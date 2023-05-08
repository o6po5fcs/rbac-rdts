#lang racket
(require redex/reduction-semantics
         redex/pict
         "CommonLang.rkt"
         "primitive-operations.rkt")

(provide ReplicaLang red-replica red-replica-malicious)



(define-extended-language ReplicaLang CommonLang
  (program ::= ((r ...) e))
  (v ::= (λ (x ...) e) atom c)
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
  (op ::= + - / * and or not < > =)
  (c ::= (ιʳ p))
  (r ::= (ιʳ (priv ...) d env (δ ...)))
  (x ιʳ ::= variable-not-otherwise-mentioned)


  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (let ([x e_x] ...) e_body #:refers-to (shadow x ...)))

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
   (--> [(r ...) (in-hole E (root ιʳ))]
        [(r ...) (in-hole E (ιʳ ()))]
        "root-cursor")
   (--> [(r ...) (in-hole E (• (ιʳ (k_1 ...)) k_2))]
        [(r ...) (in-hole E v)]
        (judgment-holds (element-of (ιʳ _ d _ _) (r ...)))
        (where v (json-read ιʳ d (k_1 ... k_2) (k_1 ... k_2)))
        "read")
   (--> [(r ...) (in-hole E (• (ιʳ (k_1 ...)) k_2))]
        [(r ...) (error string)]
        (judgment-holds (element-of (ιʳ _ d _ _) (r ...)))
        (where (error string) (json-read ιʳ d (k_1 ... k_2) (k_1 ... k_2)))
        "¬read")
   (--> [(r ...) (in-hole E (•! (ιʳ (k_1 ...)) k_2 atom))]
        [((ιʳ (priv ...) d_new env (δ ... (! (k_1 ... k_2) atom))) r_other ...) (in-hole E atom)]
        (judgment-holds (element-of r_c (r ...)))
        (where (ιʳ (priv ...) d env (δ ...)) r_c)
        (judgment-holds (is-writable d (k_1 ... k_2) (priv ...) env))
        (where (r_other ...) (list-without (r ...) r_c))
        (where d_new (json-write d (k_1 ... k_2) atom))
        "write")
   (--> [(r ...) (in-hole E (•! (ιʳ (k_1 ...)) k_2 atom))]
        [(r ...) (error "Write forbidden"#;(,(format "Write to ~s of ~s failed: privileges were ~s."
                                                     (term k_2) (term (ιʳ (k_1 ...))) (term (priv ...)))))]
        (judgment-holds (element-of (ιʳ (priv ...) d env _) (r ...)))
        (judgment-holds (¬is-writable d (k_1 ... k_2) (priv ...) env))
        "¬write-¬w")
   (--> [(r ...) (in-hole E (•! (ιʳ (k_1 ...)) k_2 v))]
        [(r ...) (error "Write forbidden")]
        (judgment-holds (¬is-atom v))
        "¬write-¬a")
   ))

(define (render-red-replica . filepath)
  (rule-pict-style 'horizontal)
  (reduction-relation-rule-separation 4)
  (with-compound-rewriter
      'list-without
    (λ (lws)
      (define lhs (list-ref lws 2))
      (define rhs (list-ref lws 3))
      (list "" lhs "\\" rhs ""))
    (with-compound-rewriter
        'element-of
      (λ (lws)
        (define lhs (list-ref lws 2))
        (define rhs (list-ref lws 3))
        (list "" lhs " ∈ " rhs ""))
      (with-compound-rewriter
          'distinct
        (λ (lws)
          (define lhs (list-ref lws 2))
          (define rhs (list-ref lws 3))
          (list "" lhs " ≠ " rhs ""))
        (if (empty? filepath)
            (render-reduction-relation red-replica)
            (render-reduction-relation red-replica (car filepath)))))))
;(render-red-replica)

; a malicious client-side version which excludes the security check for writing values
(define red-replica-malicious
  (extend-reduction-relation
   red-replica
   ReplicaLang-inner
   (--> [(r ...) (in-hole E (•! (ιʳ (k_1 ...)) k_2 atom))]
        [((ιʳ (priv ...) d_new env (δ ... (! (k_1 ... k_2) atom))) r_other ...) (in-hole E atom)]
        (judgment-holds (element-of r_c (r ...)))
        (where (ιʳ (priv ...) d env (δ ...)) r_c)
        (where (r_other ...) (list-without (r ...) r_c))
        (where d_new (json-write d (k_1 ... k_2) atom))
        "write-malicious")))

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

(define-metafunction ReplicaLang-inner
  json-read : ιʳ json p_remaining p_complete -> v or (error string)
  ;; Reached destination, found atom -> return atom
  [(json-read ιʳ atom () p_complete)
   atom]
  ;; Reached destination, found empty object -> return empty object
  [(json-read ιʳ () () p_complete)
   ()]
  ;; Reached destination, found json -> return cursor to complete path
  [(json-read ιʳ json () p_complete)
   (ιʳ p_complete)]
  ;; Not at destination, found json -> try with first key/value pair
  [(json-read ιʳ ((k_1 := json_1) kj_2 ...) (k_1 k_3 ...) p_complete)
   (json-read ιʳ json_1 (k_3  ...) p_complete)]
  ;; Not at destination, found json, first key doesn't match -> recurse
  [(json-read ιʳ (kj_1 kj_2 ...) (k ...) p_complete)
   (json-read ιʳ (kj_2 ...) (k ...) p_complete)]
  ;; Any other read is invalid
  [(json-read ιʳ json p_1 p_complete)
   (error "Read forbidden"#;(,(format "Could not read path ~s into replica ~s: path does not exist."
                                      (term p_1)
                                      (term ιʳ))))])


(define-judgment-form
  ReplicaLang
  #:mode     (¬is-atom I)
  #:contract (¬is-atom v)

  [-------------------- "Cursor"
   (¬is-atom c)]

  [-------------------- "Lambda"
   (¬is-atom (λ (x ...) e))])

(define-judgment-form
  ReplicaLang-inner
  #:mode     (¬is-writable I I I I)
  #:contract (¬is-writable d p (priv ...) d)

  [(where #f ,(term (is-writable d p (priv ...) env)))
   -------------------- "Invert result"
   (¬is-writable d p (priv ...) env)])