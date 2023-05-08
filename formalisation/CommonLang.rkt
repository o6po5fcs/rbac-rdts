#lang racket

(require redex/reduction-semantics
         redex/pict)
(provide CommonLang
         json-write
         json-write-compound
         matches-in-env is-writable is-readable
         data-to-paths data-to-keys
         element-of distinct list-without
         save-as)

;; Common language elements shared between leader and replicas
(define-language CommonLang
  ;; Atomic, primitive values
  (atom ::= number boolean string quoted)
  (quoted ::= (quote i))
  
  ;; (json) data
  (d ::= (kj ...))
  (kj ::= (k := json))
  ;; key
  (k ::= number #;string i)
  (json ::= atom d)
  ; paths
  (p ::= (k ...)) ; TODO: Path starting from root: ($ k ...)
  ;; changes
  (δ ::= (! p atom))
  ; path selectors
  (ps ::= (p-exp ...))
  (p-exp ::= k * [script-op (~ k ...)] [script-op k] [⋃ k ...])
  
  (role ::= i)
  (p-role ::= role *)

  ; privileges
  (priv ::= (ALLOW p-role r/w OF ps))
  ; permissions
  (r/w ::= READ WRITE)

  ; user environment
  (env ::= d)

  (script-op ::= ∈ ∋ < > ≤ ≥ ≠ =)

  (i ::= variable-not-otherwise-mentioned)
  

  ; Other reserved symbols, used in child languages
  (other-reserved-symbols ::=
                          LOGIN GET-REPLICA PUSH-Δ ACCEPT REJECT INIT ACCEPT-LOGIN
                          if • •! let error root λ
                          + - / * and or not)
  
  
  )



; To `json` at `p` write `atom` and receive the updated `json`.
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

; To `json_1` at `p` write `json_2` and receive the updated `json_2`.
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


;; Holds iff WRITE of path selector itself.
(define-judgment-form
  CommonLang
  #:mode     (is-writable I I I I)
  #:contract (is-writable d p (priv ...) env)

  [(matches-in-env ps p env)
   --------------------
   (is-writable d p (priv_l ... (ALLOW p-role WRITE OF ps) priv_r ...) env)])
;(judgment-form->pict is-writable)

;; Holds iff READ or WRITE of path selector (or a path of which path selector is a prefix).
;;
;; FIXME: check if this comment still holds in new solution:
;; Special care has to be taken with path expressions (*/=/∈), as a naive
;; prefix implementation might erroneously grant read-access to some paths.
;; Consider, e.g., a `d` of the form `((0 := ((1 := 2))) ((3 := 4)))`.
;; A path selector `(* 1)` and any user env should not give access to path `(3)`, even
;; though `3` matches `*` and the remainder of the path (`(1)`) can be ignored
;; since prefixes don't care about the rest of the list. Instead, it should be
;; verified that no path `(3 1)` exists, thus `(* 1)` could not have referred to
;; `(3 1)`, thus no access should be granted to `(3)`. We currently enforce this
;; by restricting the choices picked for path expressions to the value
;; of a path that actually exists in the data structure.
(define-judgment-form
  CommonLang
  #:mode     (is-readable I I I I)
  #:contract (is-readable d p (priv ...) env)

  [(where (p_all ...) (data-to-paths d)) (element-of (k_1 ... k_2 ...) (p_all ...))
   (matches-in-env ps (k_1 ... k_2 ...) env) (element-of r/w (READ WRITE))
   --------------------
   (is-readable d (k_1 ...) (priv_l ... (ALLOW p-role r/w OF ps) priv_r ...) env)])

(define (render-is-readable . filepath)
  ;(metafunction-pict-style 'up-down/vertical-side-conditions)
  ;(metafunction-up/down-indent 45)
  ;(metafunction-rule-gap-space 10)
  ;(metafunction-line-gap-space 2)
  (with-compound-rewriter
      'element-of
    (λ (lws)
      (define lhs (list-ref lws 2))
      (define rhs (list-ref lws 3))
      (list "" lhs " ∈ " rhs ""))
    (with-compound-rewriter
        'list-without
      (λ (lws)
        (define lhs (list-ref lws 2))
        (define rhs (list-ref lws 3))
        (list "" lhs "\\" rhs ""))
      (if (empty? filepath)
          (render-judgment-form is-readable)
          (render-judgment-form is-readable (car filepath))))))
;(render-is-readable)

(define-judgment-form
  CommonLang
  #:mode     (is-prefix-of I I)
  #:contract (is-prefix-of p p)

  [(is-prefix-of (k_2 ...) (k_3 ...))
   --------------------
   (is-prefix-of (k_1 k_2 ...) (k_1 k_3 ...))]

  [--------------------
   (is-prefix-of () p)])

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
  [(side-condition ,(not (equal? (term i_1) (term i_2)))) ; FIXME: use i_!_1 ?
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

(define-judgment-form
  CommonLang
  #:mode     (env-script-holds I I I I)
  #:contract (env-script-holds script-op k (k ...) env)

  [(where (kj_1 ... (k_2 := atom_2) kj_3 ...) env)
   (atom-script-holds script-op atom_2 k)
   -------------------- "Holds for atom"
   (env-script-holds script-op k (k_2) env)]
  ; (env-script-holds ∈ k=c1 (k2)=(own-courses) env=((own-courses := ((0 := 'c1) (1 := 'c2)))))
  ; d_2=((0 := 'c1) (1 := 'c2))
  [(where (kj_1 ... (k_2 := d_2) kj_3 ...) env)
   (where (kj_4 ... (k_5 := number) kj_6 ...) d_2)
   -------------------- " Holds if number in"
   (env-script-holds ∈ number (k_2) env)]
  [(where (kj_1 ... (k_2 := d_2) kj_3 ...) env)
   (where (kj_4 ... (k_5 := (quote i)) kj_6 ...) d_2) ;; quote i here
   -------------------- " Holds if identifier in"
   (env-script-holds ∈ i (k_2) env)]
  [(where (kj_1 ... (k_2 := d_2) kj_3 ...) env)
   (env-script-holds script-op k (k_4 ...) d_2)
   -------------------- "Recur"
   (env-script-holds script-op k (k_2 k_4 ...) env)]
  )

(define-metafunction CommonLang
  prefix-all-by : k (p ...) -> (p ...)
  [(prefix-all-by k ())
   ()]
  [(prefix-all-by k ((k_1 ...) p_2 ...))
   ((k k_1 ...) p_3 ...)
   (where (p_3 ...) (prefix-all-by k (p_2 ...)))])



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
   (matches-in-env ([⋃ k_1 k_3 ...] p-exp ...) (k_2 ...) env)]
  [(matches-in-env ([⋃ k_3 ...] p-exp ...) (k_2 ...) env)
   --------------------------------- "union-other"
   (matches-in-env ([⋃ k_1 k_3 ...] p-exp ...) (k_2 ...) env)]
  [(matches-in-env (p-exp ...) (k_2 ...) env)
   --------------------------------- "wildcard"
   (matches-in-env (* p-exp ...) (k_1 k_2 ...) env)]
  [(script-holds script-op k_3 k_1) (matches-in-env (p-exp ...) (k_2 ...) env)
   --------------------------------- "script"
   (matches-in-env ([script-op k_3] p-exp ...) (k_1 k_2 ...) env)]
  [(env-script-holds script-op k_1 (k ...) env) (matches-in-env (p-exp ...) (k_2 ...) env)
   --------------------------------- "env-script"
   (matches-in-env ([script-op (~ k ...)] p-exp ...) (k_1 k_2 ...) env)])

(define (render-matches-in-env . filepath)
  ;(metafunction-pict-style 'up-down/vertical-side-conditions)
  ;(metafunction-up/down-indent 45)
  ;(metafunction-rule-gap-space 10)
  ;(metafunction-line-gap-space 2)
  (with-compound-rewriter
      'element-of
    (λ (lws)
      (define lhs (list-ref lws 2))
      (define rhs (list-ref lws 3))
      (list "" lhs " ∈ " rhs ""))
    (with-compound-rewriter
        'list-without
      (λ (lws)
        (define lhs (list-ref lws 2))
        (define rhs (list-ref lws 3))
        (list "" lhs "\\" rhs ""))
      (if (empty? filepath)
          (render-judgment-form matches-in-env)
          (render-judgment-form matches-in-env (car filepath))))))
;(render-matches-in-env)

#;(define-metafunction CommonLang
  all-paths-matching : ps json env -> (p ...)
  [(all-paths-matching () d env)
   (())
   (clause-name "Selector consumed -> match any data")]
  [(all-paths-matching () atom env)
   (())
   (clause-name "Selector consumed -> match any atom")]
  [(all-paths-matching (k_2 p-exp ...) (kj_1 ... (k_2 := json_2) kj_3 ...) env)
   (prefix-all-by k_2 (p_result ...))
   (where (p_result ...) (all-paths-matching (p-exp ...) json_2 env))
   (clause-name "Matching literal key -> consume key")]
  [(all-paths-matching (k p-exp ...) (kj ...) env)
   ()
   (clause-name "Non-matching literal key -> fail to match")]
  [(all-paths-matching ([⋃ k_2 k_rest ...] p-exp ...) (kj_1 ... (k_2 := json_2) kj_3 ...) env)
   (p_result-2 ... p_result-rest ...)
   (where (p_result-2 ...) (prefix-all-by k_2 (all-paths-matching (p-exp ...) json_2 env)))
   (where (p_result-rest ...) (all-paths-matching ([⋃ k_rest ...] p-exp ...) (kj_1 ... kj_3 ...) env))
   (clause-name "UNION: FIXME: In Progress!")]
  [(all-paths-matching ([⋃ k k_rest ...] p-exp ...) (kj ...) env)
   (p_result-rest ...)
   (where (p_result-rest ...) (all-paths-matching ([⋃ k_rest ...] p-exp ...) (kj ...) env))
   (clause-name "UNION: FIXME: In Progress! when no match first")]
  [(all-paths-matching ([⋃] p-exp ...) (kj ...) env)
   (())
   (clause-name "UNION: FIXME: In Progress! when none left")]
  [(all-paths-matching (* p-exp ...) ((k_1 := json_1) kj_2 ...) env)
   (p_result-1 ... p_result-2 ...)
   (where (p_result-1 ...) (prefix-all-by k_1 (all-paths-matching (p-exp ...) json_1 env)))
   (where (p_result-2 ...) (all-paths-matching (* p-exp ...) (kj_2 ...) env))
   (clause-name "Wildcard key -> consume first")]
  [(all-paths-matching ([script-op (~ k ...)] p-exp ...) ((k_1 := json_1) kj_2 ...) env)
   (p_result-1 ... p_result-2 ...)
   (judgment-holds (env-script-holds script-op k_1 (k ...) env))
   (where (p_result-1 ...) (prefix-all-by k_1 (all-paths-matching (p-exp ...) json_1 env)))
   (where (p_result-2 ...) (all-paths-matching ([script-op (~ k ...)] p-exp ...) (kj_2 ...) env))
   (clause-name "Script selector segment -> consume first when script-expr holds")]
  [(all-paths-matching ([script-op (~ k ...)] p-exp ...) (kj_1 kj_2 ...) env)
   (all-paths-matching ([script-op (~ k ...)] p-exp ...) (kj_2 ...) env)
   (clause-name "Script selector segment -> skip first when script-expr does not hold")]
  [(all-paths-matching (p-exp ...) () env)
   ()
   (clause-name "Any case with empty object -> fail to match")]
  [(all-paths-matching (p-exp ...) atom env)
   ()
   (clause-name "Any case with atom as data -> fail to match")]
  )
;(current-traced-metafunctions '(all-paths-matching))

;; Metafunctions for reduction relations on CommonLang
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
  [(json-to-keys () (k ...))
   ((k ...))]
  [(json-to-keys d (k ...))
   (data-to-keys d (k ...))])

(define-judgment-form
  CommonLang
  #:mode (element-of O I)
  #:contract (element-of any (any ...))

  [(where (_ ... any_e _ ...) (any_all ...))
   --------------------
   (element-of any_e (any_all ...))])

(define-judgment-form
  CommonLang
  #:mode     (distinct I I)
  #:contract (distinct any any)

  [(distinct any_!_1 any_!_1)])
;(judgment-form->pict distinct)

(define-metafunction
  CommonLang
  list-without : (any ...) any -> (any ...)

  [(list-without (any_l ... any_m any_r ...) any_m)
   (any_l ... any_r ...)]
  [(list-without (any_1 ...) any_2)
   (any_1 ...)])

(require pict)
(require pict/color)
(rule-pict-style 'horizontal)
;(metafunction-pict-style 'left-right/vertical-side-conditions)
(metafunction-pict-style 'up-down/vertical-side-conditions)
(define (save-as p name)
  (send
   (pict->bitmap
    (inset/clip
     (scale
      (lt-superimpose
       (scale-to-fit (white (filled-rectangle 1 1)) p #:mode 'distort)
       p)
      1.5)
     5))
   save-file name 'png))


; FIXME: unused
#;(define-metafunction CommonLang
    dict-lookup : d p -> v
    ;; Reached destination, found number -> return number
    [(dict-lookup number ())
     number]
    ;; Reached destination, found boolean -> return boolean
    [(dict-lookup boolean ())
     boolean]
    ;; Reached destination, found json -> incomplete lookup
    #;[(dict-lookup json ())
       INVALID]
    ;; Not at destination, found json -> recurse
    [(dict-lookup ((k_1 := json_1) ... (k_2 := json_2) (k_3 := json_3) ...)
                  (k_2 k_4 ...))
     (dict-lookup json_2 (k_4  ...))])





; FIXME: Unused, maybe not necessary:
#;(define (permission-for-path path-in-data policy-rwo-rule dict)
    (let ((rwo (car policy-rwo-rule))
          (path-in-rule (cdr policy-rwo-rule)))
      (define (continue-down-paths path-in-data path-in-rule)
        (cond ((null? (cdr path-in-data))
               rwo
               (co-traverse (cdr path-in-data) (cdr path-in-rule)))))
      (define (co-traverse path-in-data path-in-rule)
        (let* ((field-in-data (car path-in-data))
               (descr-in-rule (car path-in-rule))
               (descr-in-rule-str (symbol->string descr-in-rule)))
          (cond
            ((eq? '* descr-in-rule)
             ; Wildcart always matches: continue
             (continue-down-paths path-in-data path-in-rule))
            ((eq? field-in-data descr-in-rule)
             ; Fields match: continue
             (continue-down-paths path-in-data path-in-rule))
            ((eq? (string-ref descr-in-rule-str 0) '=)
             ; Lookup key and see whether it's eq?
             (let ((val (dict-lookup dict (substring descr-in-rule-str 1))))
               (if (eq? val field-in-data)
                   (continue-down-paths path-in-data path-in-rule)
                   'O)))
            ((eq? (string-ref descr-in-rule-str 0) '∈)
             ; Lookup key and see whether it's ∈ the set
             (let ((dict (dict-lookup dict (substring descr-in-rule-str 1))))
               (if (member val field-in-data)
                   (continue-down-paths path-in-data path-in-rule)
                   'O)))
            (else
             ; No match: return rwo-value 'O
             'O))))))











