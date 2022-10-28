#lang racket

(require redex/reduction-semantics
         redex/pict)
(provide CommonLang
         json-write
         matches-in-env is-writable
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
  (p ::= (k ...))
  ;; changes
  (δ ::= (! p atom))
  ; globs
  (g ::= (g-segment ...))
  (g-segment ::= k * (= i) (∈ i))
  
  (role ::= i)
  (p-role ::= role *)

  ; privileges
  (priv ::= (ALLOW p-role r/w OF g))
  ; permissions
  (r/w ::= READ WRITE)

  ; user environment
  (env ::= d)

  (i ::= variable-not-otherwise-mentioned)
  

  ; Other reserved symbols, used in child languages
  (other-reserved-symbols ::=
                          LOGIN GET-REPLICA PUSH-Δ ACCEPT REJECT PUSH-SNAPSHOT LOGIN-SUCCESS
                          if • •! let error
                          + - / * and or not < > =)
  
  
  )



(define-metafunction CommonLang
  json-write : json p atom -> json or (error string_explanation)
  [(json-write atom_old () atom_new)
   atom_new]
  [(json-write atom_old () d_new)
   (error "Write forbidden"#;,(format
           "Writing ~s to data structure currently containing ~s would change schema."
           (term d_new)
           (term atom_old)))]
  [(json-write d_old () atom_new)
   (error "Write forbidden"#;,(format
           "Writing ~s to data structure currently containing ~s would change schema."
           (term atom_new)
           (term d_old)))]
  [(json-write ((k_1 := json_1) ...
                (k_2 := json_2)
                (k_3 := json_3) ...)
               (k_2 k_4 ...)
               atom_new)
   ((k_1 := json_1) ...
    (k_2 := json_new)
    (k_3 := json_3) ...)
   (where json_new (json-write json_2 (k_4 ...) atom_new))]
  [(json-write ((k_1 := json_1) ...
                (k_2 := json_2)
                (k_3 := json_3) ...)
               (k_2 k_4 ...)
               atom_new)
   (error "Write forbidden")])


;; Holds iff WRITE of glob itself.
;; Writing has to be strict, hence uses `matches-in-env`.
(define-judgment-form
  CommonLang
  #:mode     (is-writable I I I)
  #:contract (is-writable p (priv ...) env)

  [(matches-in-env g p env)
   --------------------
   (is-writable p (priv_l ... (ALLOW p-role WRITE OF g) priv_r ...) env)])
;(judgment-form->pict is-writable)

(define-judgment-form
  CommonLang
  #:mode     (matches-in-env I I I)
  #:contract (matches-in-env g p d)

  [(matches-in-env (g-segment_2 ...) (k_2 ...) env)
   -------------------- "Match * wildcard"
   (matches-in-env (* g-segment_2 ...) (k_1 k_2 ...) env)]

  [(matches-in-env (g-segment_2 ...) (k_2 ...) env)
   -------------------- "Match identical key"
   (matches-in-env (k_1 g-segment_2 ...) (k_1 k_2 ...) env)]

  [(matches-in-env (g-segment_2 ...) (k_5 ...) env)
   (where (kj_3 ... (k_1 := atom_2) kj_4 ...) env)
   -------------------- "Match = wildcard atom"
   (matches-in-env ((= k_1) g-segment_2 ...) (atom_2 k_5 ...) env)]

  [(matches-in-env (g-segment_2 ...) (k_5 ...) env)
   (where (kj_3 ... (k_1 := (quote i_2)) kj_4 ...) env)
   -------------------- "Match = wildcard identifier"
   (matches-in-env ((= k_1) g-segment_2 ...) (i_2 k_5 ...) env)]

  [(matches-in-env (g-segment_2 ...) (k_8 ...) env)
   (where (kj_3 ... (k_1 := (kj_5 ... (k_6 := atom_2) kj_7 ...)) kj_4 ...) env)
   -------------------- "Match ∈ wildcard atom"
   (matches-in-env ((∈ k_1) g-segment_2 ...) (atom_2 k_8 ...) env)]

  [(matches-in-env (g-segment_2 ...) (k_8 ...) env)
   (where (kj_3 ... (k_1 := (kj_5 ... (k_6 := (quote i_2)) kj_7 ...)) kj_4 ...) env)
   -------------------- "Match ∈ wildcard identifier"
   (matches-in-env ((∈ k_1) g-segment_2 ...) (i_2 k_8 ...) env)]

  [-------------------- "Empty paths"
   (matches-in-env () () env)])
;(judgment-form->pict matches-in-env)


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











