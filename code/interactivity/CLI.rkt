#lang racket


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                  ;;;
;;; Command-Line Interface                                           ;;;
;;;                                                                  ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; This file implements the command-line interface which integrates ;;;
;;; LeaderLang and ReplicaLang into an interactive process.          ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require redex/reduction-semantics
         (only-in "../formalisation/CommonLang.rkt"
                  json-write)
         (only-in "../formalisation/LeaderLang.rkt"
                  LeaderLang
                  leader-request-red-rel
                  excerpt-for-role)
         (only-in "../formalisation/ReplicaLang.rkt"
                  ReplicaLang
                  red-replica
                  red-replica-malicious))

(provide run-CLI)


;;;;;;;;;;;;;;;;;;;;;;
;; CLI abstractions ;;
;;;;;;;;;;;;;;;;;;;;;;

(define (stored-key->provided-key key)
  (define stored-key-prefix    "stored-")
  (define provided-key-prefix  "provided-")
  
  (string-replace key stored-key-prefix provided-key-prefix #:all? #f))

(define (report str . args)
  (displayln (apply format (cons str args))))
  
(define (report-prompt str . args)
  (newline) (newline)
  (apply report (cons str args)))
  
(define (report-option str . args)
  (apply report (cons (string-append "   " str) args)))

(define (report-output str . args)
  (apply report (cons (string-append ">>> " str) args)))

(define (prompt-user #:prompt [prompt ""])
  (display prompt) (read))

(define (get-user-name user) (first user))
(define (get-user-role user) (second user))
(define (get-user-stored-key user) (third user))
(define (get-user-environment user) (fourth user))

(define LeaderLang-get-users first)
(define LeaderLang-get-policy-excerpts second)
(define LeaderLang-get-data third)
(define LeaderLang-get-sessions fourth)
(define LeaderLang-get-answer (compose first last))
(define (is-LeaderLang-accept-login-response? response)
  (redex-match LeaderLang (ACCEPT ((ACCEPT-LOGIN ι))) response))
(define (get-LeaderLang-accept-login-session-id response)
  (if (is-LeaderLang-accept-login-response? response)
      (last (first (second response)))
      (error "response does not seem to be a correct ACCEPT/ACCEPT-LOGIN response" response)))
(define (is-LeaderLang-init-response? response)
  (redex-match LeaderLang (ACCEPT ((INIT ι (priv ...) d env))) response))
(define (get-LeaderLang-init-values response)
  (if (is-LeaderLang-init-response? response)
      (values (third (first (second response)))
              (fourth (first (second response)))
              (fifth (first (second response))))
      (error "response does not seem to be a correct ACCEPT/INIT response" response)))

(define (ReplicaLang-get-program-replica program)
  (first (first program)))
(define (ReplicaLang-get-program-policy-excerpt program)
  (second (first (first program))))
(define (ReplicaLang-get-program-replica-data program)
  (third (first (first program))))
(define (ReplicaLang-get-program-expression program)
  (second program))
(define (ReplicaLang-get-program-deltas program)
  (define replica (ReplicaLang-get-program-replica program))
  (fifth replica))

(define (ReplicaLang-get-replica-name replica)
  (first replica))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary metafunction: extend cursor c by descending into key k. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction ReplicaLang
  extend-cursor : c k -> c
  [(extend-cursor (ι (k_1 ...)) k)
   (ι (k_1 ... k))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary metafunction: retrieve the path from a cursor. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction ReplicaLang
  cursor-path : c -> (k ...)
  [(cursor-path (ι (k ...)))
   (k ...)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary metafunction: retrieve the data from a replica object. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction ReplicaLang
  replica-data : r -> d
  [(replica-data (ι (priv ...) d env (δ ...)))
   d])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Starts the interactive REPL for a certain configuration. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (run-CLI roles data user-config security-policy)
  (displayln "<<< SRDT Interaction Simulator >>>")
  
  (define (exit)
    (report-output "Stopping program."))



  (define (get-policy-excerpt role security-policy)
    (term (,role (excerpt-for-role ,role ,security-policy))))

  (define all-policy-excerpts (for/list ([role roles])
                                (get-policy-excerpt role security-policy)))
  

  (define LeaderLang-program (term (,user-config ,all-policy-excerpts ,data () () ())))
  (define (run-and-update-LeaderLang-program! program)
    ; take the car because "apply-reduction-relation*" returns a list of responses (if there are multiple, which there should never be)
    (define LeaderLang-response (car (apply-reduction-relation* leader-request-red-rel program)))
    (set! LeaderLang-program LeaderLang-response)
    LeaderLang-program)
      
  
  (define (make-LeaderLang-program old-response new-request)
    (term (,(LeaderLang-get-users           old-response)
           ,(LeaderLang-get-policy-excerpts old-response)
           ,(LeaderLang-get-data            old-response)
           ,(LeaderLang-get-sessions        old-response)
           (,new-request)
           ())))

 
  (define (get-top-level-json-keys json)
    (map car json))
  
  (define (make-new-ReplicaLang-program policy-excerpt data user-env)
    (define replica-name "my-replica")
    (define replicas (term ((,replica-name ,policy-excerpt ,data ,user-env ()))))
    (define program (term (,replicas (root ,replica-name))))
    (car (apply-reduction-relation* red-replica program)))

  (define (ReplicaLang-change-program-data old-program new-data)
    ; (ι (priv ...) d env (δ ...))
    (define-values (replica-name policy-excerpt old-data user-env deltas) (apply values (ReplicaLang-get-program-replica old-program)))
    (define old-expression (ReplicaLang-get-program-expression old-program))
    (define replicas (term ((,replica-name ,policy-excerpt ,new-data ,user-env ,deltas))))
    (define program (term (,replicas ,old-expression)))
    program)

  (define (ReplicaLang-clear-deltas program)
    ; (ι (priv ...) d env (δ ...))
    (define-values (replica-name policy-excerpt data user-env deltas) (apply values (ReplicaLang-get-program-replica program)))
    (define expression (ReplicaLang-get-program-expression program))
    (define replicas (term ((,replica-name ,policy-excerpt ,data ,user-env ()))))
    (term (,replicas ,expression)))
  
  (define (make-ReplicaLang-program old-response new-expression)
    (term (,(first old-response)
           ,new-expression)))

  
  (define (LeaderLang-login user policy-excerpt data)
    (define provided-key (stored-key->provided-key (get-user-stored-key user)))
    (define LOGIN-program
      (make-LeaderLang-program LeaderLang-program (term (LOGIN ,(get-user-name user) ,provided-key))))
    (define LeaderLang-response (run-and-update-LeaderLang-program! LOGIN-program))
    LeaderLang-response)

  (define (LeaderLang-get-replica login-response session-id)
    (define GET-REPLICA-program (make-LeaderLang-program login-response (term (GET-REPLICA ,session-id))))
    ;(pretty-print GET-REPLICA-program)
    (run-and-update-LeaderLang-program! GET-REPLICA-program))


  (define (execute-ReplicaLang-program ReplicaLang-program)
    (define replica (ReplicaLang-get-program-replica ReplicaLang-program))
    ;(pretty-print replica)
    (define replica-name (ReplicaLang-get-replica-name replica))
    ;(println replica-name)
    (define replica-data (term (replica-data ,replica)))
    
    (let program-loop ()
      (report-prompt "Provide a ReplicaLang program expression. The name of the current replica is \"~a\" (with quotes), which can be used in the \"root\" cursor expression.\nCursor expressions use the following symbols: • and •! (for copy-paste purposes)." replica-name)
      (define user-expression (prompt-user #:prompt "Enter a ReplicaLang program >"))
      (if (not (redex-match ReplicaLang e user-expression))
          (begin (report-output "The provided expression is not a correct ReplicaLang expression. Try again.")
                 (program-loop))
          (let* ((program-to-execute (make-ReplicaLang-program ReplicaLang-program user-expression))
                 (new-ReplicaLang-program (car (apply-reduction-relation* red-replica program-to-execute))))
            (report-output "Executing ReplicaLang program... It reduced to:\n ~a" (pretty-format new-ReplicaLang-program))
            (define evaluation-result (ReplicaLang-get-program-expression new-ReplicaLang-program))
            (report-output "The expression evaluated to: ~v" evaluation-result)
            new-ReplicaLang-program))))

  (define (execute-malicious-ReplicaLang-program ReplicaLang-program)   
    (define replica (ReplicaLang-get-program-replica ReplicaLang-program))
    (define replica-name (ReplicaLang-get-replica-name replica))
    (define replica-data (term (replica-data ,replica)))
    
    (let program-loop ()
      (report-prompt "Provide a ReplicaLang program expression. The name of the current replica is \"~a\" (with quotes), which can be used in the \"root\" cursor expression.\nCursor expressions use the following symbols: • and •! (for copy-paste purposes)." replica-name)
      (define user-expression (prompt-user #:prompt "Enter a (malicious) ReplicaLang program >"))
      (if (not (redex-match ReplicaLang e user-expression))
          (begin (report-output "The provided expression is not a correct ReplicaLang expression. Try again.")
                 (program-loop))
          (let* ((program-to-execute (make-ReplicaLang-program ReplicaLang-program user-expression))
                 (reduction-results (apply-reduction-relation* red-replica-malicious program-to-execute))
                 (number-of-reduction-results (length reduction-results))
                 (new-ReplicaLang-program #f))
            ; try to figure out automatically which reduction result is the malicious one
            ; if there is only 1 reduction result, just take that reduction result whatever it is (the program might not have performed a write to a replica)
            ; if there are multiple reduction results, one is potentially a "write forbidden" result, and the other a succesful write.
            ;  - in this case the malicious program is the succesful write and the other is just the well-behaved reduction result.
            ;  - if there are multiple reduction results and both are error or non-error, just complain to the user.
            (cond ((= number-of-reduction-results 1)
                   (set! new-ReplicaLang-program (car reduction-results)))
                  ((= number-of-reduction-results 2)
                   (let* ((first-program (car reduction-results))
                          (first-evaluation-result (ReplicaLang-get-program-expression first-program))
                          (first-is-error? (redex-match ReplicaLang (error string) first-evaluation-result))
                         (second-program (cadr reduction-results))
                         (second-evaluation-result (ReplicaLang-get-program-expression second-program))
                         (second-is-error? (redex-match ReplicaLang (error string) second-evaluation-result)))
                     (cond ((and first-is-error? second-is-error?)
                            (report-output "!!! Unexpected situation: the given ReplicaLang program reduced to 2 alternative results, but the evaluation result of both is an error expression !!!")
                            (set! new-ReplicaLang-program first-program))
                           ((and first-is-error? (not second-is-error?))
                            (set! new-ReplicaLang-program second-program))
                           ((and (not first-is-error?) second-is-error?)
                            (set! new-ReplicaLang-program first-program))
                           ((and (not first-is-error?) (not second-is-error?))
                            (report-output "!!! Unexpected situation: the given ReplicaLang program reduced to 2 alternative results, but neither evaluated to an error expression !!!")
                            (set! new-ReplicaLang-program first-program)))))
                  (else
                   (report-output "!!! Unexpected situation: the given ReplicaLang program reduced to ~a alternative results. Expected 1 or 2, but not ~a !!!" number-of-reduction-results number-of-reduction-results)
                   (set! new-ReplicaLang-program (car reduction-results))))
                               
            (report-output "Executing ReplicaLang program without client-side security checks... It reduced to:\n ~a" (pretty-format new-ReplicaLang-program))
            (define evaluation-result (ReplicaLang-get-program-expression new-ReplicaLang-program))
            (report-output "The expression evaluated to: ~v" evaluation-result)
            new-ReplicaLang-program))))

  (define (push-local-changes-to-leader ReplicaLang-program session-id)
    (define deltas (ReplicaLang-get-program-deltas ReplicaLang-program))
    (define program-data (ReplicaLang-get-program-replica-data ReplicaLang-program))

    (define (find-user-name-from-session-id user-session)
      (define user-name #f)
      (hash-for-each session-table
                     (lambda (name session-id)
                       (when (equal? user-session session-id)
                         (set! user-name name))))
      user-name)
    
    (define leader-changes (make-vector (length deltas)))
    (for ([i (in-range 0 (length deltas))])
      (define delta (list-ref deltas i))
      (define PUSHDELTA-program
        (make-LeaderLang-program LeaderLang-program (term (PUSH-Δ ,session-id ,delta))))
      (define LeaderLang-response (run-and-update-LeaderLang-program! PUSHDELTA-program))
      ; answer is something of the form
      ;'(ACCEPT
      ;  ((PUSH-Δ
      ;    "SESSION#Bob"
      ;    (!
      ;     (team2 sightings 1674814951967 feedback)
      ;     "This is actually an Andrena (solitary bee)"))))
      (define evaluation-result (LeaderLang-get-answer LeaderLang-response))
      (define is-accept? (redex-match LeaderLang (ACCEPT (action ...)) evaluation-result))
      (define response
        (if is-accept?
            (second evaluation-result)
            evaluation-result))
      (when is-accept?
        (for-each (lambda (delta)
                    (let* ((user-session (second delta))
                           (user-name (find-user-name-from-session-id user-session))
                           (existing-deltas (hash-ref leader-deltas-table user-name)))
                      (hash-set! leader-deltas-table user-name (append existing-deltas (list delta)))))
                  response))
      (vector-set! leader-changes i response))
    
    (define report (string-join
                    (for/list ([i (in-range 0 (vector-length leader-changes))])
                      (define delta (list-ref deltas i))
                      (define response (vector-ref leader-changes i))
                      (if (redex-match LeaderLang (REJECT) response)
                          (format "~v\n   -Rejected by the leader-" delta)
                          (string-append
                           (format "~v\n" delta)
                           (if (empty? response)
                               "   -Sent to no other clients-"
                               (string-join (for/list ([push-delta response])
                                              (define user-session (second push-delta))
                                              (define user-name #f)
                                              (hash-for-each session-table
                                                             (lambda (name session-id)
                                                               (when (equal? user-session session-id)
                                                                 (set! user-name name))))
                                              (define delta (third push-delta))
                                              (format "    Sent to: ~a (when they next synchronize with the leader)" user-name))
                                            "\n")))))
                    "\n"))

    (report-output "~a changes pushed to the leader" (length deltas))
    (unless (empty? deltas)
        (report-output "Leader updates:\n~a" report))
    (ReplicaLang-clear-deltas ReplicaLang-program))

  (define (pull-changes-from-leader initial-ReplicaLang-program user-name)
    (define deltas (hash-ref leader-deltas-table user-name))
    (define new-ReplicaLang-program
      (foldl (lambda (delta latest-ReplicaLang-program)
               (define-values (_ path value) (apply values (last delta)))
               (define data (ReplicaLang-get-program-replica-data latest-ReplicaLang-program))
               (define new-data (term (json-write ,data ,path ,value)))
               (ReplicaLang-change-program-data latest-ReplicaLang-program new-data))
             initial-ReplicaLang-program
             deltas))
    (report-output "~a changes pulled from the leader" (length deltas))
    (hash-set! leader-deltas-table user-name '())
    new-ReplicaLang-program)
  
  (define (interact-with-replica user-name)
    (let main-replica-interaction-loop ()
      (define ReplicaLang-program (hash-ref user-table user-name))
      (define session-id (hash-ref session-table user-name))
      (define number-of-offline-changes (length (ReplicaLang-get-program-deltas ReplicaLang-program)))
      (report-prompt "*** Breadcrumb (navigation): Main menu -> Interact as ~a ***\nWhat do you want to do?" user-name)
      (report-option "[~a] Display ~a's replica data" 0 user-name)
      (report-option "[~a] Display ~a's security policy excerpt" 1 user-name)
      (report-option "[~a] Display ~a's offline changes to their local replica (~a changes)" 2 user-name number-of-offline-changes)
      (report-option "[~a] Execute a ReplicaLang program as ~a" 3 user-name)
      (report-option "[~a] Execute a malicious ReplicaLang program as ~a" 4 user-name)
      (report-option "[~a] Push ~a's offline changes to the leader (~a changes)" 5 user-name number-of-offline-changes)
      (report-option "[~a] Pull changes for ~a from the leader (~a changes)" 6 user-name (length (hash-ref leader-deltas-table user-name)))
      (report-option "[~a] Go back to the main menu" 7)

      (let ((input (prompt-user #:prompt "Enter a number >")))
        (cond ((not (number? input))
               (report-prompt "Input must be a number.")
               (main-replica-interaction-loop))
              ((= input 0)
               (report-output "~a's replica's data is: ~n~a" user-name (pretty-format (ReplicaLang-get-program-replica-data ReplicaLang-program)))
               (main-replica-interaction-loop))
              ((= input 1)
               (define policy-excerpt (ReplicaLang-get-program-policy-excerpt ReplicaLang-program))
               (report-output "~a's security policy excerpt is: ~n~a" user-name (pretty-format policy-excerpt))
               (main-replica-interaction-loop))
              ((= input 2)
               (report-output "~a's unsynchronized (offline) changes are: ~n~a" user-name (pretty-format (ReplicaLang-get-program-deltas ReplicaLang-program)))
               (main-replica-interaction-loop))
              ((= input 3)
               (define new-ReplicaLang-program (execute-ReplicaLang-program ReplicaLang-program))
               (hash-set! user-table user-name new-ReplicaLang-program)
               (main-replica-interaction-loop))
              ((= input 4)
               (define new-ReplicaLang-program (execute-malicious-ReplicaLang-program ReplicaLang-program))
               (hash-set! user-table user-name new-ReplicaLang-program)
               (main-replica-interaction-loop))
              ((= input 5)
               (define new-ReplicaLang-program (push-local-changes-to-leader ReplicaLang-program session-id))
               (hash-set! user-table user-name new-ReplicaLang-program)
               (main-replica-interaction-loop))
              ((= input 6)
               (define new-ReplicaLang-program (pull-changes-from-leader ReplicaLang-program user-name))
               (hash-set! user-table user-name new-ReplicaLang-program)
               (main-replica-interaction-loop))
              ((= input 7)
               #t)
              (else (report-output "Unknown input.")
                    (main-replica-interaction-loop))))))

  (define (login-user user)
    (define user-name (get-user-name user))
    (let* ((policy-excerpt (get-policy-excerpt (get-user-role user) security-policy))
           (login-response (LeaderLang-login user policy-excerpt data)))
      (define LOGIN-answer (LeaderLang-get-answer login-response))
      (define session-id (get-LeaderLang-accept-login-session-id LOGIN-answer))
      (define GET-REPLICA-response (LeaderLang-get-replica login-response session-id))
      (define GET-REPLICA-answer (LeaderLang-get-answer GET-REPLICA-response))
      (define-values (policy-excerpt replica-data user-environment) (get-LeaderLang-init-values GET-REPLICA-answer))
      (values session-id (make-new-ReplicaLang-program policy-excerpt replica-data user-environment))))

  (define user-table (make-hash))
  (define session-table (make-hash))
  (define leader-deltas-table (make-hash))
    
  (for-each (lambda (user)
              (define-values (session-id ReplicaLang-program) (login-user user))
              (hash-set! user-table (get-user-name user) ReplicaLang-program)
              (hash-set! session-table (get-user-name user) session-id)
              (hash-set! leader-deltas-table (get-user-name user) '()))
            user-config)

  (define (display-leader-data)
    (define data (LeaderLang-get-data LeaderLang-program))
    (report-output "Leader's master copy of the data:\n~a" (pretty-format data)))

  (define (display-leader-pending-changes)
    (hash-for-each leader-deltas-table
                   (lambda (user-name deltas)
                     (displayln (format "~a (~a changes stored on the leader that have not yet been pulled by ~a): \n~a" user-name (length deltas) user-name (pretty-format deltas))))))

  (report-output "The full program data is:\n~a\n" (pretty-format data))
  (report-output "The full security policy is:\n~a\n" (pretty-format security-policy))
  
  (let main-interaction-loop ()
    (define number-of-users (length user-config))
    (report-prompt "Select an option.")

    (let print-options ((i 0))
      (when (< i number-of-users)
        (let* ((user (list-ref user-config i))
               (name (get-user-name user))
               (role (get-user-role user))
               (user-env (get-user-environment user)))
          (report-option "[~a] Interact as ~a (role: \"~a\", user environment: ~v)." i name role user-env)
          (print-options (+ i 1)))))
    (report-option "[~a] Display the leader's replica data" number-of-users)
    (define number-of-leader-changes (foldl (lambda (lst acc) (+ (length lst) acc)) 0 (hash-values leader-deltas-table)))
    (report-option "[~a] Display the leader's changes which are not yet pulled by a user (~a changes)" (+ number-of-users 1) number-of-leader-changes)
    (report-option "[~a] Exit program" (+ number-of-users 2))

    (let loop ()
      (define selected (prompt-user #:prompt "Enter a number >"))
      (if (not (number? selected))
          (loop)
          (cond ((< selected number-of-users)
                 (define user-name (get-user-name (list-ref user-config selected)))
                 (interact-with-replica user-name)
                 (main-interaction-loop))
                ((= selected (+ number-of-users 0))
                 (display-leader-data)
                 (main-interaction-loop))
                ((= selected (+ number-of-users 1))
                 (display-leader-pending-changes)
                 (main-interaction-loop))
                ((= selected (+ number-of-users 2))
                 (exit))
                (else (report-output "Unknown input ~a. Try again." selected)
                      (loop)))))))