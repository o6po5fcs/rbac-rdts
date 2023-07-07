#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; CommonLang                                                                                              ;;;
;;;                                                                                                         ;;;
;;; A common formal language for the parts of the formalism that are shared by the leader and the replicas. ;;;
;;;                                                                                                         ;;;
;;; More concretely, CommonLang specifies:                                                                  ;;;
;;;    - primitive atoms (numbers, booleans, strings, quoted symbols, and the empty object),                ;;;
;;;    - JSON data/objects/keys/...,                                                                        ;;;
;;;    - security roles, and                                                                                ;;;
;;;    - privileges.                                                                                        ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(require redex/reduction-semantics)
(provide CommonLang
         json-write
         json-write-compound
         matches-in-env is-writable is-readable
         data-to-paths data-to-keys
         element-of distinct list-without)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The core CommonLang formal language ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-language CommonLang
  ;; Atomic, primitive values
  (atom ::= number boolean string quoted ())
  (quoted ::= (quote i))
  
  ;; (JSON) data: key/JSON-pairs.
  (d ::= (kj ...))
  (kj ::= (k := json))
  (k ::= number #;string i)
  (json ::= atom d)
  
  ; Paths
  (p ::= (k ...))
  
  ; Changes ("deltas")
  (δ ::= (! p atom))
  
  ; Path selectors
  (ps ::= (p-exp ...))
  (p-exp ::= k * [script-op (~ k ...)] [script-op k] [∪ k ...])
  
  ; Privileges, roles, permissions
  (priv ::= (ALLOW p-role r/w OF ps))
  (p-role ::= role *)
  (r/w ::= READ WRITE)

  ; User environment
  (env ::= d)

  ; Operators usable in a script expression
  (script-op ::= ∈ ∋ < > ≤ ≥ ≠ =)

  ; Identifiers
  (role i ::= variable-not-otherwise-mentioned)
  

  ; Other reserved symbols, used in child languages
  (other-reserved-symbols ::=
                          LOGIN GET-REPLICA PUSH-Δ ACCEPT REJECT INIT ACCEPT-LOGIN
                          if • •! let error root λ
                          + - / * and or not)
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Checks whether path in data is writable according to the privileges and environment. ;;
;;                                                                                      ;;
;; Holds iff WRITE of path selector itself.                                             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-judgment-form
  CommonLang
  #:mode     (is-writable I I I I)
  #:contract (is-writable d p (priv ...) env)

  [(matches-in-env ps p env)
   --------------------
   (is-writable d p (priv_l ... (ALLOW p-role WRITE OF ps) priv_r ...) env)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Checks whether path in data is readable according to the privileges and environment.    ;;
;;                                                                                         ;;
;; Holds iff READ or WRITE of path selector, or a path of which path selector is a prefix. ;;                                             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-judgment-form
  CommonLang
  #:mode     (is-readable I I I I)
  #:contract (is-readable d p (priv ...) env)

  [(where (p_all ...) (data-to-paths d)) (element-of (k_1 ... k_2 ...) (p_all ...)) (matches-in-env ps (k_1 ... k_2 ...) env) (element-of r/w (READ WRITE))
   --------------------
   (is-readable d (k_1 ...) (priv_l ... (ALLOW p-role r/w OF ps) priv_r ...) env)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Writes an atom to a path into a JSON object. ;;
;;                                              ;;
;; Returns the updated JSON object.             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction CommonLang
  json-write : json p atom -> json
  [(json-write atom_old () atom_new)
   atom_new]
  [(json-write d_old () atom_new)
   atom_new]
  [(json-write ((k_1 := json_1) ...
                (k_2 := json_2)
                (k_3 := json_3) ...)
               (k_2 k_4 ...)
               atom_new)
   ((k_1 := json_1) ...
    (k_2 := json_new)
    (k_3 := json_3) ...)
   (where json_new (json-write json_2 (k_4 ...) atom_new))]
  [(json-write ((k_1 := json_1) ...)
               (k_2 k_4 ...)
               atom_new)
   ((k_1 := json_1) ...
    (k_2 := json_new))
   (where json_new (json-write () (k_4 ...) atom_new))])

; Onto `json_1` at `p`: write `json_2`. Receive the updated `json_2`.
(define-metafunction CommonLang
  json-write-compound : json_1 p json_2 -> json_3
  [(json-write-compound json_old () json_new)
   json_new]
  [(json-write-compound (kj_1 ... (k_2 := json_2) kj_3 ...)
                        (k_2 k_4 ...)
                        json_new)
   (kj_1 ... (k_2 := json_2′) kj_3 ...)
   (where json_2′ (json-write-compound json_2 (k_4 ...) json_new))]
  [(json-write-compound (kj_1 ...) (k_2 k_4 ...) json_new)
   (kj_1 ... (k_2 := json_2′))
   (where json_2′ (json-write-compound () (k_4 ...) json_new))]
  [(json-write-compound atom_old (k_2 k_4 ...) json_new)
   ((k_2 := json_2′))
   (where json_2′ (json-write-compound () (k_4 ...) json_new))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Checks whether a script expression holds in a user environment. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-judgment-form
  CommonLang
  #:mode     (env-script-holds I I I I)
  #:contract (env-script-holds script-op k (k ...) env)

  [(where (kj_1 ... (k_2 := atom_2) kj_3 ...) env)
   (atom-script-holds script-op atom_2 k)
   -------------------- "Holds for atom"
   (env-script-holds script-op k (k_2) env)]
  [(where (kj_1 ... (k_2 := d_2) kj_3 ...) env)
   (where (kj_4 ... (k_5 := number) kj_6 ...) d_2)
   -------------------- " Holds if number in"
   (env-script-holds ∈ number (k_2) env)]
  [(where (kj_1 ... (k_2 := d_2) kj_3 ...) env)
   (where (kj_4 ... (k_5 := (quote i)) kj_6 ...) d_2)
   -------------------- " Holds if identifier in"
   (env-script-holds ∈ i (k_2) env)]
  [(where (kj_1 ... (k_2 := d_2) kj_3 ...) env)
   (env-script-holds script-op k (k_4 ...) d_2)
   -------------------- "Recur"
   (env-script-holds script-op k (k_2 k_4 ...) env)]
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Checks whether a script expression holds for 2 constants. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-judgment-form
  CommonLang
  #:mode     (script-holds I I I)
  #:contract (script-holds script-op k k)

  [(atom-script-holds script-op number k)
   -------------------- "Holds for number"
   (script-holds script-op number k)]
  [(atom-script-holds script-op (quote i) k)
   -------------------- "Holds for identifier"
   (script-holds script-op i k)])

(define-judgment-form
  CommonLang
  #:mode     (atom-script-holds I I I)
  #:contract (atom-script-holds script-op atom k)

  [-------------------- "Holds if quoted eq"
   (atom-script-holds = (quote i) i)]
  [-------------------- "Holds if number eq"
   (atom-script-holds = number number)]
  [(side-condition ,(not (equal? (term i_1) (term i_2))))
   -------------------- "Holds if quoted neq"
   (atom-script-holds ≠ (quote i_1) i_2)]
  [(side-condition ,(not (equal? (term number_1) (term number_2))))
   -------------------- "Holds if number neq"
   (atom-script-holds ≠ number_1 number_2)]
  [(side-condition ,(< (term number_1) (term number_2)))
   -------------------- "Holds if number lt"
   (atom-script-holds < number_1 number_2)]
  [(side-condition ,(<= (term number_1) (term number_2)))
   -------------------- "Holds if number le"
   (atom-script-holds ≤ number_1 number_2)]
  [(side-condition ,(> (term number_1) (term number_2)))
   -------------------- "Holds if number gt"
   (atom-script-holds > number_1 number_2)]
  [(side-condition ,(>= (term number_1) (term number_2)))
   -------------------- "Holds if number ge"
   (atom-script-holds ≥ number_1 number_2)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Checks whether a path selector matches a path in a user environment. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-judgment-form
  CommonLang
  #:mode     (matches-in-env I I I)
  #:contract (matches-in-env ps p env)
  
  [--------------------------------- "empty-selector"
   (matches-in-env () () env)]
  [(matches-in-env (p-exp ...) (k_2 ...) env)
   --------------------------------- "literal-key"
   (matches-in-env (k_1 p-exp ...) (k_1 k_2 ...) env)]
  [(matches-in-env (k_1 p-exp ...) (k_2 ...) env)
   --------------------------------- "union-first"
   (matches-in-env ([∪ k_1 k_3 ...] p-exp ...) (k_2 ...) env)]
  [(matches-in-env ([∪ k_3 ...] p-exp ...) (k_2 ...) env)
   --------------------------------- "union-other"
   (matches-in-env ([∪ k_1 k_3 ...] p-exp ...) (k_2 ...) env)]
  [(matches-in-env (p-exp ...) (k_2 ...) env)
   --------------------------------- "wildcard"
   (matches-in-env (* p-exp ...) (k_1 k_2 ...) env)]
  [(script-holds script-op k_3 k_1) (matches-in-env (p-exp ...) (k_2 ...) env)
   --------------------------------- "script"
   (matches-in-env ([script-op k_3] p-exp ...) (k_1 k_2 ...) env)]
  [(env-script-holds script-op k_1 (k ...) env) (matches-in-env (p-exp ...) (k_2 ...) env)
   --------------------------------- "env-script"
   (matches-in-env ([script-op (~ k ...)] p-exp ...) (k_1 k_2 ...) env)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary metafunctions: Determine all paths that exist in a JSON data structure. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction CommonLang
  data-to-paths : d -> (p ...)
  [(data-to-paths d)
   ((k ...) ...)
   (where ((k ...) ...) (data-to-keys d ()))])

; Works, but doesn't typeset nicely with the `append`.
; Appending in the pattern language using `(,@(term _) ,@(term _))` technically works,
; but is typeset the same as `((term _) (term _))`, so the behavior is not clear at all.
#;(define-metafunction CommonLang
    data-to-keys : d (k ...) -> ((k ...) ...)
    [(data-to-keys ((k_1 := json_1) (k_2 := json_2) ...) (k_3 ...))
     ,(append (term (json-to-keys json_1 (k_3 ... k_1)))
              (term (data-to-keys ((k_2 := json_2) ...) (k_3 ...))))]
    [(data-to-keys () (k ...))
     ()])
; Instead, being explicit:
(define-metafunction CommonLang
  data-to-keys : d (k ...) -> ((k ...) ...)
  [(data-to-keys ((k_1 := json_1) (k_2 := json_2) ...) (k_3 ...))
   (p_l ... p_r ...)
   (where (p_l ...) (json-to-keys json_1 (k_3 ... k_1)))
   (where (p_r ...) (data-to-keys ((k_2 := json_2) ...) (k_3 ...)))]
  [(data-to-keys () (k ...))
   ()])

(define-metafunction CommonLang
  json-to-keys : json (k ...) -> ((k ...) ...)
  [(json-to-keys atom (k ...))
   ((k ...))]
  [(json-to-keys d (k ...))
   (data-to-keys d (k ...))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary metafunction: prefixes all paths in the list by a key. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction CommonLang
  prefix-all-by : k (p ...) -> (p ...)
  [(prefix-all-by k ())
   ()]
  [(prefix-all-by k ((k_1 ...) p_2 ...))
   ((k k_1 ...) p_3 ...)
   (where (p_3 ...) (prefix-all-by k (p_2 ...)))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary judgment form: is-prefix-of. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-judgment-form
  CommonLang
  #:mode     (is-prefix-of I I)
  #:contract (is-prefix-of p p)

  [(is-prefix-of (k_2 ...) (k_3 ...))
   --------------------
   (is-prefix-of (k_1 k_2 ...) (k_1 k_3 ...))]

  [--------------------
   (is-prefix-of () p)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary judgment form: selects element from list. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-judgment-form
  CommonLang
  #:mode (element-of O I)
  #:contract (element-of any (any ...))

  [(where (_ ... any_e _ ...) (any_all ...))
   --------------------
   (element-of any_e (any_all ...))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary judgment form: ensure both arguments refer to a different value. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-judgment-form
  CommonLang
  #:mode     (distinct I I)
  #:contract (distinct any any)

  [(distinct any_!_1 any_!_1)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary metafunction: removes element from list. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction
  CommonLang
  list-without : (any ...) any -> (any ...)

  [(list-without (any_l ... any_m any_r ...) any_m)
   (any_l ... any_r ...)]
  [(list-without (any_1 ...) any_2)
   (any_1 ...)])
