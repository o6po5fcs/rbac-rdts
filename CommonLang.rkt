#lang racket

(require redex/reduction-semantics
         redex/pict)
(provide CommonLang json-write data-to-paths data-to-keys element-of distinct list-without save-as #;dict-lookup)

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


(define-metafunction CommonLang
  json-write : json p atom -> json
  [(json-write atom_old () atom_new)
   atom_new]
  [(json-write atom_old () d_new)
   ,(error 'json-write
           "Writing ~s to data structure currently containing ~s would change schema."
           (term d_new)
           (term atom_old))]
  [(json-write d_old () atom_new)
   ,(error 'json-write
           "Writing ~s to data structure currently containing ~s would change schema."
           (term atom_new)
           (term d_old))]
  [(json-write ((k_1 := json_1) ...
                (k_2 := json_2)
                (k_3 := json_3) ...)
               (k_2 k_4 ...)
               atom)
   ((k_1 := json_1) ...
    (k_2 := (json-write json_2 (k_4 ...) atom))
    (k_3 := json_3) ...)])

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











