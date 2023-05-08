#lang racket

(require redex/reduction-semantics
         redex/pict)
(require "CommonLang.rkt")
(require "primitive-operations.rkt")
(provide LeaderLang
         projection-red-rel leader-request-red-rel
         handle-request readable-projection
         excerpt-for-role actions-per-session)

;; Language describing how the leader interacts
;; with replicas running ReplicaLang.
;; Runs on the replication leader, and has access
;; to all policy excerpts and projected schemas.
(define-extended-language LeaderLang CommonLang
  ;; Main LeaderLang expression:
  (request ::=
           (LOGIN ιᵘ auth-key)
           (GET-REPLICA ιˢ)
           (PUSH-Δ ιˢ δ))
  (result ::=
          (ACCEPT (action ...))
          (REJECT #;string_reason))
  (action ::=
            (ACCEPT-LOGIN ιˢ)
            (INIT ιˢ (priv ...) d env)
            (PUSH-Δ ιˢ δ))
  (excerpt ::= (role (priv ...)))
  (user ::= (ιᵘ role auth-key env))
  (ιˢ ιᵘ auth-key ::= string) ; session-id, user-id, auth-key
  (s ::= (ιˢ ιᵘ)))



(define-metafunction LeaderLang
  fresh-session-id : ιᵘ -> ιˢ
  [(fresh-session-id ιᵘ)
   ,(format "SESSION#~a" (term ιᵘ))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reduction relations for LeaderLang ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define projection-red-rel
  (reduction-relation
   LeaderLang
   #:domain [d (role ...) (priv ...) (excerpt ...)]
   #:codomain [d (role ...) (priv ...) (excerpt ...)]
   (--> [d (role_1 role_2 ...) (priv_all ...) ((role_done (priv_done ...)) ...)]
        [d (role_2 ...) (priv_all ...) ((role_1 (excerpt-for-role role_1 (priv_all ...))) (role_done (priv_done ...)) ...)]
        "project-role_1")))
;(reduction-relation->pict projection-red-rel)

;; Process list of request in a leader's context
(define leader-request-red-rel
  (reduction-relation
   LeaderLang
   #:domain ((user ...) (excerpt ...) d (s ...) (request ...) (result ...))
   #:codomain ((user ...) (excerpt ...) d (s ...) (request ...) (result ...))
   (--> [(user ...) (excerpt ...) d  (s_i ...) (request request_r ...) (result_r ...)]
        [(user ...) (excerpt ...) d_projected (s_o ...) (request_r ...) (result_r ... result)]
        (where
         (d_projected (s_o ...) result)
         (handle-request (user ...) (excerpt ...) d (s_i ...) request))
        "Requests-to-results")))

   
;; Handle individual request
(define-metafunction LeaderLang
  handle-request : (user ...) (excerpt ...) d (s ...) request -> (d (s ...) result)
  #;[(handle-request (user ...) (excerpt ...) d (s ...) (LOGIN ιᵘ auth-key))
   (d (s ...) (ACCEPT ((ACCEPT-LOGIN ιˢ))))
   (judgment-holds (element-of (ιˢ ιᵘ) (s ...)))
   (judgment-holds (key-is-valid (user ...) ιᵘ auth-key))
   (clause-name "Login existing session")]
  [(handle-request (user ...) (excerpt ...) d (s_old ...) (LOGIN ιᵘ auth-key))
   (d ((ιˢ ιᵘ) s_old ...) (ACCEPT ((ACCEPT-LOGIN ιˢ))))
   (judgment-holds (no-active-session-for ιᵘ (s_old ...)))
   (judgment-holds (key-is-valid (user ...) ιᵘ auth-key))
   ; TODO? where d_2 contains all fields in (k_2 ...)
   ; '-> Or is that the responsibility of LeaderConfigLang, and not to be checked here?
   (where ιˢ (fresh-session-id ιᵘ))
   (clause-name "Login new session")]
  #;[(handle-request (user ...) (excerpt ...) d (s_old ...) (LOGIN ιᵘ auth-key))
   (d (s_old ...) (REJECT "Login failed"))
   (where #f (key-is-valid (user ...) ιᵘ auth-key))
   (clause-name "Authenticate new client fails: auth failed")]
  [(handle-request (user ...) (excerpt ...) d (s ...) (GET-REPLICA ιˢ))
   (d (s ...) (ACCEPT ((INIT ιˢ (priv ...) d_projected env))))
   ; TODO? where d_2 contains all fields in (k_2 ...)
   (judgment-holds (element-of (ιˢ ιᵘ) (s ...)))
   (judgment-holds (element-of (ιᵘ role _ env) (user ...)))
   (judgment-holds (element-of (role (priv ...)) (excerpt ...)))
   (where d_projected (readable-projection d (priv ...) d env ()))
   (clause-name "Get replica snapshot")]
  [(handle-request (user ...) (excerpt ...) d (s ...) (PUSH-Δ ιˢ (! p atom)))
   (d_new (s ...) (ACCEPT (action ...)))
   (judgment-holds (element-of (ιˢ ιᵘ) (s ...)))
   (judgment-holds (element-of (role (priv ...)) (excerpt ...)))
   (judgment-holds (element-of (ιᵘ role _ env) (user ...)))
   (judgment-holds (is-writable d p (priv ...) env))
   (where d_new (json-write d p atom))
   (where (s_other ...) (list-without (s ...) (ιˢ ιᵘ)))
   (where (action ...) (actions-per-session (s_other ...) (user ...) (excerpt ...) d_new (! p atom)))
   (clause-name "Δ from client")]
  #;[(handle-request (user ...) (excerpt ...) d (s ...) (PUSH-Δ ιˢ (! p atom)))
   (d (s_other ...) (REJECT "Changed unwritable path"))
   (judgment-holds (element-of (ιˢ ιᵘ) (s ...)))
   (where (s_other ...) (list-without (s ...) (ιˢ ιᵘ)))
   ;(where (role_2 env) (user-role-and-env (user ...) ιᵘ_2))
   ; Implicitly: where not (judgment-holds (is-writable d p (priv_2 ...) env))
   (clause-name "Δ from client rejected")]
  #;[(handle-request (user ...) (excerpt ...) d (s ...) request)
   (d (s ...) (REJECT "Unknown user (session-id should not exist)"))
   (judgment-holds (element-of (ιˢ ιᵘ) (s ...)))
   (where #f (user-role-and-env (user ...) ιᵘ))
   (clause-name "Missing u-config")]
  #;[(handle-request (user ...) (excerpt ...) d (s ...) request)
   (d (s ...) (REJECT "Unknown session (must log in first)"))
   (clause-name "No valid session")]
  [(handle-request (user ...) (excerpt ...) d (s ...) request)
   (d (s ...) (REJECT))
   (clause-name "Reject request")])
#;(render-reduction-relation-rules
   '("Get replica snapshot"
     "Δ from clent"
     "Δ from client rejected"))

(define (render-handle-request . filepath)
  (metafunction-pict-style 'up-down/vertical-side-conditions)
  (metafunction-up/down-indent 45)
  (metafunction-rule-gap-space 10)
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
          (render-metafunction handle-request)
          (render-metafunction handle-request (car filepath))))))
;(render-handle-request)

(define-metafunction LeaderLang
  excerpt-for-role : role (priv ...) -> (priv ...)
  
  [(excerpt-for-role role ((ALLOW * r/w OF ps) priv_1 ...))
   ((ALLOW role r/w OF ps) priv_2 ...)
   (where (priv_2 ...) (excerpt-for-role role (priv_1 ...)))
   (clause-name "Wildcard")]

  [(excerpt-for-role role ((ALLOW role r/w OF ps) priv_1 ...))
   ((ALLOW role r/w OF ps) priv_2 ...)
   (where (priv_2 ...) (excerpt-for-role role (priv_1 ...)))
   (clause-name "Role Match")]

  [(excerpt-for-role role_1 ((ALLOW role_2 r/w OF ps) priv ...))
   (excerpt-for-role role_1 (priv ...))
   (judgment-holds (distinct role_1 role_2))
   (clause-name "Role Mismatch")]

  [(excerpt-for-role role ())
   ()
   (clause-name "Empty")])
;(metafunction->pict excerpt-for-role)

(define (render-excerpt-for-role . filepath)
  (metafunction-pict-style 'left-right/vertical-side-conditions)
  (metafunction-up/down-indent 0)
  (metafunction-rule-gap-space 10)
  (with-compound-rewriter
      'distinct
    (λ (lws)
      (define lhs (list-ref lws 2))
      (define rhs (list-ref lws 3))
      (list "" lhs " ≠ " rhs ""))
    (if (empty? filepath)
        (render-metafunction excerpt-for-role)
        (render-metafunction excerpt-for-role (car filepath)))))
;(render-excerpt-for-role)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary functions and forms ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Verifies that auth-key_provided is an authenticating key for the stored secret auth-key_stored
(define-judgment-form
  LeaderLang
   #:mode (key-is-valid I I I)
  #:contract (key-is-valid (user ...) ιᵘ auth-key_provided)

  [(where #t ,(key-matches? (term ιᵘ) (term auth-key_stored) (term auth-key_provided)))
   --------------------
   (key-is-valid (user_l ... (ιᵘ role auth-key_stored env) user_r ...)
                 ιᵘ
                 auth-key_provided)])
;(metafunction->pict key-is-valid)




;; Filters change based on whether the change should be visible according to the
;; session's user's role's privileges. Note that a change (i.e., *write*) should
;; be allowed if the path written to is *readable* according to the privileges.
(define-metafunction LeaderLang
  actions-per-session
  : (s ...) (user ...) (excerpt ...) d δ
  -> (action ...)
  [(actions-per-session ((ιˢ ιᵘ) s ...) (user ...) (excerpt ...) d (! p atom))
   ((PUSH-Δ ιˢ (! p atom)) action_other ...)
   (judgment-holds (element-of (ιᵘ role auth-key env) (user ...)))
   (judgment-holds (element-of (role (priv ...)) (excerpt ...)))
   (judgment-holds (is-readable d p (priv ...) env))
   (where (action_other ...)
          (actions-per-session (s ...) (user ...) (excerpt ...) d (! p atom)))]
  [(actions-per-session ((ιˢ ιᵘ) s ...) (user ...) (excerpt ...) d (! p atom))
   (action_other ...)
   (judgment-holds (element-of (ιᵘ role auth-key env) (user ...)))
   (judgment-holds (element-of (role (priv ...)) (excerpt ...)))
   ; Implicitly: where not (judgment-holds (is-readable d p (priv ...) env))
   (where (action_other ...)
          (actions-per-session (s ...) (user ...) (excerpt ...) d (! p atom)))]
  [(actions-per-session () (user ...) (excerpt ...) d δ)
   ()])
;(metafunction->pict actions-per-session)
;(metafunction-pict-style 'up-down/vertical-side-conditions)
;(require pict)
;(scale (metafunction->pict actions-per-session) 1.25)




(define-metafunction LeaderLang
  readable-projection : json (priv ...) d env p -> json
  [(readable-projection json_0 (priv ...) d env (k_accum ...))
   ((k_1 := json_2) kj_3 ...)
   (where ((k_1 := json_1) kj_2 ...) json_0)
   (judgment-holds (is-readable d (k_accum ... k_1) (priv ...) env))
   (where json_2 (readable-projection json_1 (priv ...) d env (k_accum ... k_1)))
   (judgment-holds (distinct json_2 ()))
   (where (kj_3 ...) (readable-projection (kj_2 ...) (priv ...) d env (k_accum ...)))

   or

   (kj_3 ...)
   (where ((k_1 := json_1) kj_2 ...) json_0)
   ; Implicitly: where not (judgment-holds (is-readable d (k_accum ... k_1) (priv ...) env))
   (where (kj_3 ...) (readable-projection (kj_2 ...) (priv ...) d env (k_accum ...)))

   or

   json_0])


(define (render-readable-projection . filepath)
  (metafunction-pict-style 'up-down/vertical-side-conditions)
  (metafunction-up/down-indent 0)
  (metafunction-rule-gap-space 10)
  (with-compound-rewriter
      'distinct
    (λ (lws)
      (define lhs (list-ref lws 2))
      (define rhs (list-ref lws 3))
      (list "" lhs " ≠ " rhs ""))
    (if (empty? filepath)
        (render-metafunction readable-projection)
        (render-metafunction readable-projection (car filepath)))))
;(render-readable-projection)


(define-judgment-form
  LeaderLang
  #:mode     (can-match I I)
  #:contract (can-match ps p)

  [(can-match (p-exp_2 ...) (k_2 ...))
   -------------------- "Match * wildcard"
   (can-match (* p-exp_2 ...) (k_1 k_2 ...))]

  [(can-match (p-exp_2 ...) (k_2 ...))
   -------------------- "Match identical key"
   (can-match (k_1 p-exp_2 ...) (k_1 k_2 ...))]

  [(can-match (p-exp_2 ...) (k_3 ...))
   -------------------- "Match = wildcard"
   (can-match ((= k_1) p-exp_2 ...) (k_2 k_3 ...))]

  [(can-match (p-exp_2 ...) (k_3 ...))
   -------------------- "Match ∈ wildcard"
   (can-match ((∈ k_1) p-exp_2 ...) (k_2 k_3 ...))]

  [-------------------- "Empty paths"
   (can-match () ())])
;(judgment-form->pict can-match)




(define-judgment-form
  LeaderLang
  #:mode     (no-active-session-for I I)
  #:contract (no-active-session-for ιᵘ (s ...))

  [(distinct ιᵘ_1 ιᵘ_2)
   (no-active-session-for ιᵘ_1 (s_3 ...))
   --------------------
   (no-active-session-for ιᵘ_1 ((ιˢ_2 ιᵘ_2) s_3 ...))]

  [--------------------
   (no-active-session-for ιᵘ ())])
;(judgment-form->pict no-active-session-for)






