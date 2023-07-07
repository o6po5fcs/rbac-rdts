#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                        ;;;
;;; LeaderLang                                                             ;;;
;;;                                                                        ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; LeaderLang models the behaviour of the leader which is responsible for ;;;
;;;     - the authentication of users,                                     ;;;
;;;     - projecting the security policy and SRDT data, and                ;;;
;;;     - authorising changes to replicas made by clients.                 ;;;
;;;                                                                        ;;;
;;; More concretely, LeaderLang specifies:                                 ;;;
;;;    - requests that clients can make,                                   ;;;
;;;    - results and actions that need to be returned to clients,          ;;;
;;;    - security policy excerpts,                                         ;;;
;;;    - user information, and                                             ;;;
;;;    - user session data (which tracks authenticated clients).           ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require redex/reduction-semantics
         "CommonLang.rkt"
         "primitive-operations.rkt")

(provide LeaderLang
         projection-red-rel leader-request-red-rel
         handle-request readable-projection
         excerpt-for-role actions-per-session)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The ReplicaLang formal language ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-extended-language LeaderLang CommonLang
  ; Requests
  (request ::=
           (LOGIN ι_^u auth-key)
           (GET-REPLICA ι_^s)
           (PUSH-Δ ι_^s δ))

  ; Results
  (result ::=
          (ACCEPT (action ...))
          (REJECT #;string_reason))

  ; Actions to take
  (action ::=
            (ACCEPT-LOGIN ι_^s)
            (INIT ι_^s (priv ...) d env)
            (PUSH-Δ ι_^s δ))

  ; Policy excerpts (specifies the role it applies to, and that role's projected policy)
  (excerpt ::= (role (priv ...)))
  
  ; User information
  (user ::= (ι_^u role auth-key env))

  ; Identifiers (session id, user id, authentication key)
  (ι auth-key ::= string)

  ; Sessions
  (s ::= (ι_^s ι_^u)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The reduction relation for the projection phase at the leader.             ;;
;;                                                                            ;;
;; Reduces a JSON object, a list of roles, a policy, and an (initially empty) ;;
;; list of policy excerpts until all policy excerpts have been derived.       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define projection-red-rel
  (reduction-relation
   LeaderLang
   #:domain [d (role ...) (priv ...) (excerpt ...)]
   #:codomain [d (role ...) (priv ...) (excerpt ...)]
   (--> [d (role_1 role_2 ...) (priv_all ...) ((role_done (priv_done ...)) ...)]
        [d (role_2 ...) (priv_all ...) ((role_1 (excerpt-for-role role_1 (priv_all ...))) (role_done (priv_done ...)) ...)]
        "project-role_1")))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The reduction relation for the replica management phase at the leader. ;;
;;                                                                        ;;
;; Reduces a list of user objects, policy excerpts, JSON object,          ;;
;; list of sessions, list of requests, and list of results by handling    ;;
;; the first request and appending its result to the list of results.     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Handles one individual request ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction LeaderLang
  handle-request : (user ...) (excerpt ...) d (s ...) request -> (d (s ...) result)
  #;[(handle-request (user ...) (excerpt ...) d (s ...) (LOGIN ι_^u auth-key))
   (d (s ...) (ACCEPT ((ACCEPT-LOGIN ι_^s))))
   (judgment-holds (element-of (ι_^s ι_^u) (s ...)))
   (judgment-holds (key-is-valid (user ...) ι_^u auth-key))
   (clause-name "Login existing session")]
  [(handle-request (user ...) (excerpt ...) d (s_old ...) (LOGIN ι_^u auth-key))
   (d ((ι_^s ι_^u) s_old ...) (ACCEPT ((ACCEPT-LOGIN ι_^s))))
   (judgment-holds (no-active-session-for ι_^u (s_old ...)))
   (judgment-holds (key-is-valid (user ...) ι_^u auth-key))
   (where ι_^s (fresh-session-id ι_^u))
   (clause-name "Login new session")]
  #;[(handle-request (user ...) (excerpt ...) d (s_old ...) (LOGIN ι_^u auth-key))
   (d (s_old ...) (REJECT "Login failed"))
   (where #f (key-is-valid (user ...) ι_^u auth-key))
   (clause-name "Authenticate new client fails: auth failed")]
  [(handle-request (user ...) (excerpt ...) d (s ...) (GET-REPLICA ι_^s))
   (d (s ...) (ACCEPT ((INIT ι_^s (priv ...) d_projected env))))
   (judgment-holds (element-of (ι_^s ι_^u) (s ...)))
   (judgment-holds (element-of (ι_^u role _ env) (user ...)))
   (judgment-holds (element-of (role (priv ...)) (excerpt ...)))
   (where d_projected (readable-projection d (priv ...) d env ()))
   (clause-name "Get replica snapshot")]
  [(handle-request (user ...) (excerpt ...) d (s ...) (PUSH-Δ ι_^s (! p atom)))
   (d_new (s ...) (ACCEPT (action ...)))
   (judgment-holds (element-of (ι_^s ι_^u) (s ...)))
   (judgment-holds (element-of (role (priv ...)) (excerpt ...)))
   (judgment-holds (element-of (ι_^u role _ env) (user ...)))
   (judgment-holds (is-writable d p (priv ...) env))
   (where d_new (json-write d p atom))
   (where (s_other ...) (list-without (s ...) (ι_^s ι_^u)))
   (where (action ...) (actions-per-session (s_other ...) (user ...) (excerpt ...) d_new (! p atom)))
   (clause-name "Δ from client")]
  #;[(handle-request (user ...) (excerpt ...) d (s ...) (PUSH-Δ ι_^s (! p atom)))
   (d (s_other ...) (REJECT "Changed unwritable path"))
   (judgment-holds (element-of (ι_^s ι_^u) (s ...)))
   (where (s_other ...) (list-without (s ...) (ι_^s ι_^u)))
   ; Implicitly: where not (judgment-holds (is-writable d p (priv_2 ...) env))
   (clause-name "Δ from client rejected")]
  #;[(handle-request (user ...) (excerpt ...) d (s ...) request)
   (d (s ...) (REJECT "Unknown user (session-id should not exist)"))
   (judgment-holds (element-of (ι_^s ι_^u) (s ...)))
   (where #f (user-role-and-env (user ...) ι_^u))
   (clause-name "Missing u-config")]
  #;[(handle-request (user ...) (excerpt ...) d (s ...) request)
   (d (s ...) (REJECT "Unknown session (must log in first)"))
   (clause-name "No valid session")]
  [(handle-request (user ...) (excerpt ...) d (s ...) request)
   (d (s ...) (REJECT))
   (clause-name "Reject request")])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Derives the policy excerpt for one role from a complete policy. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Filters change based on whether the change should be visible according to the ;;
;; session's user's role's privileges. Note that a change (i.e., *write*) should ;;
;; be allowed if the path written to is *readable* according to the privileges.  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction LeaderLang
  actions-per-session
  : (s ...) (user ...) (excerpt ...) d δ
  -> (action ...)
  [(actions-per-session ((ι_^s ι_^u) s ...) (user ...) (excerpt ...) d (! p atom))
   ((PUSH-Δ ι_^s (! p atom)) action_other ...)
   (judgment-holds (element-of (ι_^u role auth-key env) (user ...)))
   (judgment-holds (element-of (role (priv ...)) (excerpt ...)))
   (judgment-holds (is-readable d p (priv ...) env))
   (where (action_other ...)
          (actions-per-session (s ...) (user ...) (excerpt ...) d (! p atom)))]
  [(actions-per-session ((ι_^s ι_^u) s ...) (user ...) (excerpt ...) d (! p atom))
   (action_other ...)
   (judgment-holds (element-of (ι_^u role auth-key env) (user ...)))
   (judgment-holds (element-of (role (priv ...)) (excerpt ...)))
   ; Implicitly: where not (judgment-holds (is-readable d p (priv ...) env))
   (where (action_other ...)
          (actions-per-session (s ...) (user ...) (excerpt ...) d (! p atom)))]
  [(actions-per-session () (user ...) (excerpt ...) d δ)
   ()])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructs the readable projection of a JSON object by applying the READ  restrictions ;;
;;imposed by a policy excerpt. Note that the json argument is de-/reconstructed during    ;;
;; recursion, while the d argument keeps referring to the whole object. The path argument ;;
;; is similarly used in recursion, and should initially be empty.                         ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary metafunction: Creates a (human readable) fresh session-id for a user. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction LeaderLang
  fresh-session-id : ι_^u -> ι_^s
  [(fresh-session-id ι_^u)
   ,(format "SESSION#~a" (term ι_^u))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary judgment form: ensures absense of pre-existing session for the user. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-judgment-form
  LeaderLang
  #:mode     (no-active-session-for I I)
  #:contract (no-active-session-for ι_^u (s ...))

  [(distinct ι_1^u ι_2^u)
   (no-active-session-for ι_1^u (s_3 ...))
   --------------------
   (no-active-session-for ι_1^u ((ι_2^s ι_2^u) s_3 ...))]

  [--------------------
   (no-active-session-for ι_^u ())])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary judgment form: verifies the key authenticates using the stored secret. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-judgment-form
  LeaderLang
   #:mode (key-is-valid I I I)
  #:contract (key-is-valid (user ...) ι_^u auth-key_provided)

  [(where #t ,(key-matches? (term ι_^u) (term auth-key_stored) (term auth-key_provided)))
   --------------------
   (key-is-valid (user_l ... (ι_^u role auth-key_stored env) user_r ...)
                 ι_^u
                 auth-key_provided)])
