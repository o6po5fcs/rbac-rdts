#lang racket

(require redex/reduction-semantics
         redex/pict
         "LeaderLang.rkt"
         "Common.rkt"
         "ReplicaLang.rkt"
         racket/generator
         racket/random
         racket/pretty
         racket/struct)

;; Clean up invalid (but randomly generatable) json, with:
;;   - duplicate keys at the same level,
;;   - empty objects
(define-metafunction CommonLang
  cleanup-data : json (k ...) -> json
  [(cleanup-data atom (k_seen ...))
   atom]
  [(cleanup-data () (k_seen ...))
   ()]
  [(cleanup-data ((k_1 := ()) (k_2 := json_2) ...) (k_seen ...))
   (cleanup-data ((k_1 := ,(generate-term CommonLang atom 1)) (k_2 := json_2) ...) (k_seen ...))]
  [(cleanup-data ((k_1 := json_1) (k_2 := json_2) ...) (k_seen ...))
   ((k_1 := json_1′) (k_2′ := json_2′) ...)
   (side-condition (not (member (term k_1) (term (k_seen ...)))))
   (where json_1′ (cleanup-data json_1 ()))
   (where ((k_2′ := json_2′) ...) (cleanup-data ((k_2 := json_2) ...) (k_1 k_seen ...)))]
  [(cleanup-data ((k_1 := json_1) (k_2 := json_2) ...) (k_seen ...))
   ((k_2′ := json_2′) ...)
   (where ((k_2′ := json_2′) ...) (cleanup-data ((k_2 := json_2) ...) (k_seen ...)))])


(define (remove-last l)
  (if (empty? l)
      '()
      (drop-right l 1)))

(define (gen-array-object #:max-size [size 10] #:must-include-val [must-include (void)])
  (define (gen-atoms)
    (for/list ([i (in-range 1 size)])
      (term (quote ,(gensym)))))
  (define arr-values (shuffle (if (void? must-include) (gen-atoms) (cons must-include (gen-atoms)))))
  (define naturals (stream->list (in-range 0 (length arr-values))))
  (map (lambda (idx val) (term (,idx := ,val))) naturals arr-values))


(define (remove-readable-paths paths privilege-paths user-env)
  (define (keep? path)
    (define (does-not-match? path privilege-path)
      (not (term (matches-in-env ,privilege-path ,path ,user-env))))
    (andmap (curry does-not-match? path) privilege-paths))
  (filter keep? paths))

(define (remove-non-readable-paths paths privilege-paths user-env)
  (define (keep? path)
    (define (matches? path privilege-path)
      (term (matches-in-env ,privilege-path ,path ,user-env)))
    (ormap (curry matches? path) privilege-paths))
  (filter keep? paths))

(define (keep-writable-paths paths privileges user-env)
  (define (keep? path)
    (term (is-writable ,path ,privileges ,user-env)))
  (filter keep? paths))

; "mutate-paths" arguments
;   - paths: the list of paths to potentially mutate
; keyword arguments:
;   - #:path-segment-mutation-chance: the chance (in percent) to mutate any particular path segment of a path.
;                                     All path segments of a path are considered and individually subject to this chance.
;   - #:make-unreadable-percent: the chance (in percent) that, when a mutation occurs,
;                                the path becomes unreadable by not including the required field in the user environment
; "mutate-maths" return values:
;   - maybe-mutated-paths: all paths that are potentially mutated
;   - user-environment: the user environment which does or does not include the necessary fields to gain access to a path
;   - paths-made-unreadable: list of (flat) paths that were made unreadable by chance, e.g.,
;                            because the mutation (= of ∈) did not include the necessary field in the user's env   
(define (mutate-paths paths #:path-segment-mutation-chance [mutation-percent 10] #:make-unreadable-percent [unreadable-percent 20])
  (define paths-made-unreadable '())
  (define d_user '())

  (define (mutate-path path)
    (define (mutate-= path-segment make-unreadable?)
      (define symbol (gensym))
      (define replacement-path-segment (term (= ,symbol)))
      (define kv? (if make-unreadable? #f (term (,symbol := ,path-segment))))
      (values replacement-path-segment kv?))
    
    (define (mutate-∈ path-segment make-unreadable?)
      (define symbol (gensym))
      (define replacement-path-segment (term (∈ ,symbol)))
      (define kv (if make-unreadable?
                     (term (,symbol := ,(gen-array-object)))
                     (term (,symbol := ,(gen-array-object #:must-include-val path-segment)))))
      (values replacement-path-segment kv))
    
    (define (mutate-* path-segment make-unreadable?)
      (define replacement-path-segment '*)
      (values replacement-path-segment #f))
    
    (define mutations (list mutate-= mutate-∈ mutate-*))

    
    (define (maybe-mutate-path-segment path-segment)
      (if (redex-match? CommonLang k path-segment)
          (let ((mutate? (< (random 0 100) mutation-percent)))
            (if mutate?
                (let ((mutate (random-ref mutations))
                      (make-unreadable? (< (random 0 100) unreadable-percent)))
                  (when (and make-unreadable? (not (eq? mutate mutate-*)))
                    (set! paths-made-unreadable (cons path paths-made-unreadable)))
                  (define-values (replacement-path-segment kv?)
                    (let ((safe-path-segment (if (symbol? path-segment)
                                                 (term ',path-segment)
                                                 path-segment)))
                      (mutate safe-path-segment make-unreadable?)))
                  (when kv?
                    (set! d_user (cons kv? d_user)))
                  replacement-path-segment)
                path-segment))
          path-segment))

    (define maybe-mutated-path (map maybe-mutate-path-segment path))
    maybe-mutated-path)

  (define maybe-mutated-paths (map mutate-path paths))
  (values maybe-mutated-paths d_user paths-made-unreadable))


(define (generate-object #:depth [depth 4])
  ;; generate objects
  (define dirty-obj (generate-term CommonLang d depth))
  (define obj (term (cleanup-data ,dirty-obj ())))
  obj)


; returns all possible paths through an object (tree) from the root object to leaves (fields that contain plain data, i.e., atoms)
(define (get-all-paths object)
  (term (data-to-paths ,object)))


(define (generate-paths object #:keep-flat-minimum-percent [keep-flat-min-percent 0])
  ;; generate correct paths in the this object
  ;; shuffle the list of paths to remove any potential ordering of them
  (define all-paths (shuffle (get-all-paths object)))
  (display "all-paths: ") (displayln all-paths)
  
  (define-values (flat-readable-paths initial-nonreadable-paths) (split-at all-paths (round (/ (length all-paths) 2))))
  (define nr-of-paths (length flat-readable-paths))
  (define nr-of-paths-to-keep-flat (round (* (/ nr-of-paths 100) keep-flat-min-percent)))
  (define-values (paths-to-keep-flat paths-to-possibly-mutate) (split-at flat-readable-paths nr-of-paths-to-keep-flat))
  
  (define-values (maybe-mutated-paths user-environment paths-made-unreadable) (mutate-paths paths-to-possibly-mutate))
  (define readable-paths (append paths-to-keep-flat maybe-mutated-paths))
  (display "maybe-mutated-paths: ") (displayln maybe-mutated-paths)
  (display "paths-made-unreadable: ") (displayln paths-made-unreadable)
  (display "user-environment: ") (displayln user-environment)
  (define nonreadable-paths (remove-readable-paths
                             (append paths-made-unreadable initial-nonreadable-paths)
                             readable-paths
                             user-environment))

  (values flat-readable-paths readable-paths nonreadable-paths user-environment))

(define (path->privilege path role permission)
  (term (ALLOW ,role ,permission OF ,path)))

(define (paths->privileges role paths #:permissions [permissions '(READ WRITE)])
  (define privileges
    (map (lambda (path)
           (path->privilege path role (random-ref permissions)))
         paths))
  privileges)

(define (project-object object privileges user-environment)
  (term (readable-projection ,object ,privileges ,object ,user-environment ())))

(define generate-role gensym)


(define (generate-nonsense-random-paths nr-of-paths #:path-depth [path-depth 4])
  (for/list ([i (in-range 0 nr-of-paths)])
    (generate-term ReplicaLang p path-depth)))

(define (execute-read-tests #:object-depth [object-depth 4])

  ;; generate objects
  (define obj (generate-object #:depth object-depth))
  (display "obj: ") (pretty-print obj)

  ;; generate correct paths in the this object
  ;; shuffle the list of paths to remove any potential ordering of them

  (define-values (flat-readable-paths privilege-paths nonreadable-paths user-environment)
    (generate-paths obj))
  (display "readable-paths: ") (displayln privilege-paths)
  (display "nonreadable-paths: ") (displayln nonreadable-paths)
  (display "user-env: ") (displayln user-environment)

  (define random-generated-paths (generate-nonsense-random-paths (length privilege-paths) #:path-depth object-depth))

  (define role (generate-role))
  (define privileges (paths->privileges role privilege-paths #:permissions '(READ)))
  (display "privileges: ") (pretty-print privileges)

  (define projected-obj (project-object obj privileges user-environment))
  (display "projected-obj: ") (pretty-print projected-obj)

  (define (generate-program replica-name writable-paths rdt-data user-data body)
    (define deltas '())
    (define replica-data (term (,replica-name ,writable-paths ,rdt-data ,user-data ,deltas)))
    (term ((,replica-data) ,body)))

  (define (path->read-expression replica-name path)
    (if (empty? path)
        (term (• (,replica-name ()) 0))
        (let ((key (last path))
              (cursor (term (,replica-name ,(remove-last path)))))
          (term (• ,cursor ,key)))))

  (define (path->write-expression replica-name path)
    (define value-to-write (generate-term ReplicaLang v 1))
    (if (empty? path)
        (term (•! (,replica-name ()) 0 ,value-to-write))
        (let ((key (last path))
              (cursor (term (,replica-name ,(remove-last path)))))
          (term (•! ,cursor ,key ,value-to-write)))))

  
  (define (test-programs paths property?)
    (define replica-name (gensym))
    (define all-read-expressions
      (for/list ([path paths])
        (path->read-expression replica-name path)))

    (define all-programs
      (for/list ([expr all-read-expressions])
        (generate-program replica-name '() projected-obj '() expr)))
    ;(display "all-programs: ") (displayln all-programs)

    (for/list ([program all-programs])
      ;(display "checking: ") (displayln program)
      (define reduction-results (apply-reduction-relation* red-replica program))
      ;(display "==> reduced to: ") (displayln reduction-results)
      (unless (and (= 1 (length reduction-results))
                   (property? (first reduction-results)))
        (error (string-append "counterexample found: ") program reduction-results)))
    )

  (define (is-read-value? expr)
    (redex-match? ReplicaLang ((r ...) v expr)))

  (define (is-error? expr)
    (redex-match? ReplicaLang ((r ...) (error string)) expr))


  (define (is-value-or-error? expr)
    (or (is-read-value? expr)
        (is-error? expr)))
  
  (displayln "### --- testing programs with readable paths --- ###")
  ; use the original flat readable paths because those are the ones that should still be readable after we did permutations
  (test-programs flat-readable-paths is-read-value?)

  (displayln "### --- testing programs with nonreadable paths --- ###")
  (test-programs nonreadable-paths is-error?)

  (displayln "### --- testing programs with randomly generated paths --- ###")
  (test-programs random-generated-paths is-value-or-error?)
  
  )

;;;;;;;;;;;;;;;;;;;;;;;
;; Utility functions ;;
;;;;;;;;;;;;;;;;;;;;;;;

(define (report name t)
  (printf "*** ~a:~n" name)
  (pretty-print t))



(define (execute-write-tests #:object-depth [object-depth 5])
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Data generation (`d`) ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;; generate objects
  (define obj (generate-object #:depth object-depth))
  (report "obj" obj)

  ;; generate correct paths in this object
  ;; shuffle the list of paths to remove any potential ordering of them
  (define all-paths (get-all-paths obj))
  (report "all-paths" all-paths)

  (define selected-paths (random-sample all-paths (round (* (length all-paths) 2/3))))

  ;;;;;;;;;;;;;;;;;;;;;
  ;; Role generation ;;
  ;;;;;;;;;;;;;;;;;;;;;

  ;(define all-roles (generate-term CommonLang (role_1 role_2 ...) object-depth))
  (define wildcard-role '*)
  (define all-roles
    (cons wildcard-role (for/list ([i (in-range (random 1 (* object-depth 2)))])
                          (string->symbol (format "role#~s" i)))))
  (report "all-roles" all-roles)


  ;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Privilege generation ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;(define privileges (map (lambda (path) (term (ALLOW ,role ,(generate-term CommonLang )path role))) readable-paths))
  (struct role (mutated-readable-paths mutated-writable-paths [user-environment #:mutable])
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (lambda (obj) 'role)
        (lambda (obj) (list (role-mutated-readable-paths obj) (role-mutated-writable-paths obj) (role-user-environment obj)))))])
  (define roles (make-immutable-hash
                 (for/list ([role-name all-roles])
                   (define sample-size (if (eq? role-name wildcard-role) 1/10 1/3))
                   (define flat-readable-paths (random-sample selected-paths (round (* (length selected-paths) sample-size))))
                   (define flat-writable-paths (random-sample selected-paths (round (* (length selected-paths) sample-size))))
                   (define-values (mutated-readable-paths read-env _1) (mutate-paths flat-readable-paths))
                   (define-values (mutated-writable-paths write-env _2) (mutate-paths flat-writable-paths))
                   (define user-environment (append read-env write-env))
                   (cons role-name (role mutated-readable-paths mutated-writable-paths user-environment)))))
  (define roles-without-wildcard (hash-remove roles wildcard-role))
  ;(display "roles: ") (pretty-print roles)

  ; add the user environment of the wildcard role to the environment of all other roles
  (define wildcard-user-env (role-user-environment (hash-ref roles wildcard-role)))
  (hash-for-each roles (lambda (role-name obj)
                         (set-role-user-environment! obj (append (role-user-environment obj) wildcard-user-env))))
  (report "roles after adding wildcard's user env" roles)

  ; collect a hashmap of all privileges per role
  (define privileges-per-role
    (hash-map/copy roles
                   (lambda (role-name obj)
                     (define mutated-readable-paths (role-mutated-readable-paths obj))
                     (define mutated-writable-paths (role-mutated-writable-paths obj))
                     (define read-privileges (paths->privileges role-name mutated-readable-paths #:permissions '(READ)))
                     (define write-privileges (paths->privileges role-name mutated-writable-paths #:permissions '(WRITE)))
                     (values role-name (append read-privileges write-privileges)))))

  ;the security policy entails a list of all privileges for all roles
  (define security-policy (apply append (hash-values privileges-per-role)))
  (report "security-policy" security-policy)

  ; get the privileges for a specific role, taking into account the wildcard privileges which are also apply to a particular role 
  (define (get-privileges-for-role privileges-per-role role-name)
    (define wildcard-privileges (hash-ref privileges-per-role wildcard-role))
    (define role-privileges (hash-ref privileges-per-role role-name))
    (append wildcard-privileges role-privileges))

  (struct paths (non-readable strictly-readable writable)
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (lambda (obj) 'paths)
        (lambda (obj) (list (paths-non-readable obj) (paths-strictly-readable obj) (paths-writable obj)))))])

  ; for each role, compile a list of flat paths (i.e., paths that only contain symbols) which:
  ;   - cannot be read
  ;   - can strictly be read (i.e., read but not written)
  ;   - can be written to
  (define paths-per-role
    (hash-map/copy roles
                   (lambda (role-name obj)
                     (define privileges (get-privileges-for-role privileges-per-role role-name))
                     (define user-environment (role-user-environment obj))
                     (define privilege-paths (map last privileges))
                     (define non-readable (remove-readable-paths all-paths privilege-paths user-environment))
                     (define readable (remove-non-readable-paths all-paths privilege-paths user-environment))
                     (define writable (keep-writable-paths all-paths privileges user-environment))
                     (define strictly-readable (remove* writable readable equal?))
                     (values role-name (paths non-readable strictly-readable writable)))))
  (report "flat paths per role (non-readable, strictly readable, writable)" paths-per-role)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Privilege projection ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;

  (struct user (uid sid role auth-key config)
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (lambda (obj) 'user)
        (lambda (obj) (list (user-uid obj) (user-sid obj) (user-role obj) (user-auth-key obj) (user-config obj)))))])


  (define (generate-users roles)
    (define count 1)
    (hash-map/copy
     roles
     (lambda (role-name role-data)
       (let* ((u-id (format "user-~s" count))
              (s-id (format "session-~s" count))
              (auth-key (format "~a-password" u-id)))
         (set! count (+ count 1))
         (values role-name (user u-id s-id role-name auth-key (term (,u-id ,role-name ,auth-key ,(role-user-environment role-data)))))))))


  (define users (generate-users roles-without-wildcard))


  ;; Generates term of the form
  ;; `(u-configs (r-config ...) d_rdt (s ...) (request ...) (result ...))`
  (define (generate-LRL-input d_rdt roles privileges sessions u-configs requests)
    (let* ((role-names (hash-keys roles))
           (projection-input (term [,d_rdt ,role-names ,privileges ()]))
           (projection-result (apply-reduction-relation* projection-red-rel projection-input))
           (r-configs (cadddr (car projection-result))))
      (term (,u-configs ,r-configs ,d_rdt ,sessions ,requests (#;no-results)))))


  (define (generate-program object roles security-policy requests)
    (generate-LRL-input obj
                        roles-without-wildcard
                        security-policy
                        all-user-session-terms
                        all-u-configs
                        requests))

  
  (define (test-programs programs property?)
    ;(display "all-programs: ") (displayln all-programs)

    (for/list ([program programs])
      ;(display "checking: ") (pretty-print program)
      (define reduction-results (apply-reduction-relation* leader-request-red-rel program))
      ;(display "==> reduced to: ") (pretty-print reduction-results)
      (unless (property? reduction-results)
        (error (string-append "counterexample found: ") program reduction-results)))
    )

 
  #;(define requests (for/list ([i (in-range 1 (hash-count roles))])
                       `(GET-REPLICA ,(format "SESSION#~a" i))))

  (define (get-user-from-session s-id)
    ;(report "s-id" s-id)
    ;(report "(hash-values users)" (hash-values users))
    (car (memf (lambda (user) (equal? (user-sid user) s-id)) (hash-values users))))

  (define (get-session-term user)
    (term (,(user-sid user) ,(user-uid user))))
  (define all-user-session-terms (hash-map users (lambda (_ user) (get-session-term user))))
  (define all-u-configs (hash-map users (lambda (_ user) (user-config user))))

   (define (are-deltas-correct? response)
     (define (is-delta-allowed? delta)
       ;(display "checking if delta is allowed: ") (displayln delta)
       (define s-id (second delta))
       (define written-term (last delta))
       (define value-written (last written-term))
       (define path-written (second written-term))

       (define user (get-user-from-session s-id))
       (define role (user-role user))
       (define role-paths (hash-ref paths-per-role role))
       (define allowed-read-paths (paths-strictly-readable role-paths))
       (define allowed-write-paths (paths-writable role-paths))
       (or (member path-written allowed-write-paths)
           (member path-written allowed-read-paths)))
    (define deltas (last response))
    (andmap is-delta-allowed? deltas))
  
  (define (is-accepted? reduction-result)
    (define responses (get-LRL-response reduction-result))
    ;(display "checking response: ") (pretty-print responses)
    (and (= (length responses) 1)
         (let ((response (first responses)))
           (and (eq? (first response) 'ACCEPT)
                (are-deltas-correct? response)))))

  (define (is-rejected? reduction-result)
    (define responses (get-LRL-response reduction-result))
    (and (= (length responses) 1)
         (eq? (first (first responses)) 'REJECT)))
  

  (define (get-LRL-response output) (cadr (cddddr (car output))))


  (define (generate-write s-id path)
    (define new-value (generate-term CommonLang atom 1))
    (define delta (term (! ,path ,new-value)))
    (term (PUSH-Δ ,s-id ,delta)))


  (hash-for-each
   users
   (lambda (role-name user)
     (define role-paths (hash-ref paths-per-role role-name))
     (define non-readable-paths (paths-non-readable role-paths))
     (define strictly-readable-paths (paths-strictly-readable role-paths))
     (define writable-paths (paths-writable role-paths))

     (define current-user-sid (user-sid user))

     (define (generate-programs paths)
       (for/list ([path paths])
         (define write-request (generate-write current-user-sid path))
         (define program (generate-program obj roles-without-wildcard security-policy (list write-request)))
         program))
     (define disallowed-write-programs1 (generate-programs non-readable-paths))
     (define disallowed-write-programs2 (generate-programs strictly-readable-paths))    
     (define allowed-write-programs (generate-programs writable-paths))
     ;(report (format "allowed write programs for user ~a" (user-uid user)) allowed-write-programs)

     (test-programs (append disallowed-write-programs1 disallowed-write-programs2) is-rejected?)
     (test-programs allowed-write-programs is-accepted?)

     )))

#;(define (test-policy-overlap #:number-of-users [nr-of-users 2])
  (define obj (generate-object #:depth 4))
  (define all-paths (get-all-paths obj))
  
  (define user-data (for/list ([i (in-range 0 nr-of-users)])
                      (define role (generate-role))
                      (define-values (flat-readable-paths maybe-mutated-readable-paths nonreadable-paths user-environment)
                        (generate-paths obj))
                      (define privileges (paths->privileges role maybe-mutated-readable-paths))
                      (define readable-paths (remove-non-readable-paths all-paths maybe-mutated-readable-paths user-environment))
                      (printf "user ~s: \n" i) (pretty-print readable-paths)
                      (list role privileges readable-paths)))

  (define intersection (apply set-intersect (map caddr user-data)))
  (displayln "intersection: ") (pretty-print intersection))


(define projection-red-rel-coverage (make-coverage projection-red-rel))
(define red-replica-coverage (make-coverage red-replica))
(define leader-request-red-rel-coverage (make-coverage leader-request-red-rel))
(define readable-projection-coverage (make-coverage readable-projection))
(define excerpt-for-role-coverage (make-coverage excerpt-for-role))
(define handle-request-coverage (make-coverage handle-request))
(define actions-per-session-coverage (make-coverage actions-per-session))

(relation-coverage
 (list projection-red-rel-coverage
       red-replica-coverage
       leader-request-red-rel-coverage
       readable-projection-coverage
       excerpt-for-role-coverage
       handle-request-coverage))

(define (print-all-covered-cases)
  (for-each (lambda (coverage) (pretty-print (covered-cases coverage))) (relation-coverage)))

(define max-attempts 10000)
(for/list ([i (in-range 0 (+ max-attempts 1))])
    (displayln (string-append "### --- attempt " (number->string i) " --- ###"))
    (execute-read-tests #:object-depth 6))


#;(for/list ([i (in-range 0 (+ max-attempts 1))])
    (displayln (string-append "### --- attempt " (number->string i) " --- ###"))
    (execute-write-tests #:object-depth 5))




  
;(execute-write-tests)

#;(test-policy-overlap #:number-of-users 2)

