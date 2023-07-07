#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                              ;;;
;;; Randomized Testing                           ;;;
;;;                                              ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; This file implements the randomized testing. ;;;
;;;                                              ;;;
;;; More concretely, this file specifies:        ;;;
;;;    - the read tests, and                     ;;;
;;;    - the write tests.                        ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require redex/reduction-semantics
         "../formalisation/LeaderLang.rkt"
         "../formalisation/CommonLang.rkt"
         "../formalisation/ReplicaLang.rkt"
         racket/random
         racket/pretty
         racket/struct)

(provide run-read-tests run-write-tests)

;;;;;;;;;;;;;;;;;;;;;;;
;; Utility functions ;;
;;;;;;;;;;;;;;;;;;;;;;;

(define wildcard-role '*)
(define wildcard-path-expression '*)

(define (report name t)
  (printf "*** ~a:~n" name)
  (pretty-print t))

(define (remove-last l)
  (if (empty? l)
      '()
      (drop-right l 1)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Clean up invalid (but randomly generatable) json, with: ;;
;;   - duplicate keys at the same level, and               ;;
;;   - empty objects.                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generate an object in CommonLang that represents a      ;;
;; valid array, i.e., an object where the keys are indices ;;
;; (from 0 to size) and the values are the array's values. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (gen-array-object #:max-size [size 10] #:must-include-val [must-include (void)])
  (define (gen-atoms)
    (for/list ([i (in-range 1 size)])
      (term (quote ,(gensym)))))
  (define arr-values (shuffle (if (void? must-include) (gen-atoms) (cons must-include (gen-atoms)))))
  (define naturals (stream->list (in-range 0 (length arr-values))))
  (map (lambda (idx val)
         (term (,idx := ,(if (symbol? val)
                             (term ',val)
                             val))))
       naturals arr-values))

(define (list-has-path? path paths)
  (member path paths))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Given a list of paths, a list of path selectors that       ;;
;; represent read privileges, and a user environment needed   ;;
;; by those path selectors, return the list of paths that     ;;
;; match those path selectors for the given user environment. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (remove-readable-paths paths path-selectors user-env)
  (define (keep? path)
    (define (does-not-match? path path-selector)
      (not (term (matches-in-env ,path-selector ,path ,user-env))))
    (andmap (curry does-not-match? path) path-selectors))
  (filter keep? paths))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Given a list of paths, a list of path selectors that     ;;
;; represent read privileges, and a user environment needed ;;
;; by those path selectors, return the list of paths that   ;;
;; *do not* match those path selectors for the given user   ;;
;; environment.                                             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (remove-non-readable-paths paths path-expressions user-env)
  (define (keep? path)
    (define (matches? path path-expression)
      (term (matches-in-env ,path-expression ,path ,user-env)))
    (ormap (curry matches? path) path-expressions))
  (filter keep? paths))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Given a list of paths, a list of privileges, and a user environment   ;;
;; needed by those privileges, return the list of paths that are allowed ;;
;; to be written to according to the privileges and user environment.    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (keep-writable-paths obj paths privileges user-env)
  (define (keep? path)
    (term (is-writable ,obj ,path ,privileges ,user-env)))
  (filter keep? paths))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Given a list of provileges, a user environment, and a   ;;
;; flat path, return whether the path is readable          ;;
;; according to the given privileges and user environment. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (is-readable-path? path-expressions user-env path)
  (define (matches? path path-expression)
    (term (matches-in-env ,path-expression ,path ,user-env)))
  (ormap (curry matches? path) path-expressions))


(struct union-candidate (path-prefix path-full path-expression)
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (obj) 'union-candidate)
      (lambda (obj) (list (union-candidate-path-prefix obj) (union-candidate-path-full obj) (union-candidate-path-expression obj)))))])

(define (create-unions obj #:introduce-union-chance [union-chance 20])
  (define (top-level-kvs json)
    (if (redex-match CommonLang atom json)
        '()
        (map (lambda (kv) (cons (first kv) (last kv)))
             json)))

  (define (unionify-1-kv! current-path key json)
    (define should-unionify? (< (random 0 100) union-chance))
    (define full-old-path (append current-path (list key)))
    (define unionified-children (unionify! full-old-path json))
    (if should-unionify?
        (let* ((new-key (gensym))
               (full-new-path (append current-path (list new-key))))
          (set! obj (term (json-write-compound ,obj ,full-new-path ,json)))
          (cons (union-candidate current-path full-old-path (term [∪ ,key ,new-key]))
                (unionify! full-old-path json)))
        unionified-children))
          
 
  (define (unionify! current-path current-obj)
    (if (list? current-obj)
        (let ((kvs-on-current-level (top-level-kvs current-obj)))
          (define union-candidates (map (lambda (kv)
                                          (define key (car kv))
                                          (define json (cdr kv))
                                          (unionify-1-kv! current-path key json))
                                        kvs-on-current-level))
          union-candidates)
        '()))

  (define union-candidates (flatten (unionify! '() obj)))
  (report "union-candidates" union-candidates)
  (values union-candidates obj))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; "mutate-paths" arguments                                                                                                ;;
;;   - paths: the list of paths to potentially mutate                                                                      ;;
;; keyword arguments:                                                                                                      ;;
;;   - #:path-segment-wildcard-chance: the chance (in percent) to put a wildcard in any particular path segment of a path. ;;
;;                                     All path segments of a path are considered and individually subject to this chance. ;;
;;   - #:make-unreadable-percent: the chance (in percent) that, when a mutation occurs,                                    ;;
;;                                the path becomes unreadable by not including the required field in the user environment  ;;
;; "mutate-paths" return values:                                                                                           ;;
;;   - path-selectors: all paths that potentially contain wildcards                                                        ;;
;;   - user-environment: the user environment which does or does not include the necessary fields to gain access to a path ;;
;;   - paths-made-unreadable: list of field access paths that were made unreadable though random chance, e.g.,             ;;
;;                            because the mutation (= of ∈) did not include the necessary field in the user's env          ;;
;;   - flat-path-suggestions: a list of flat paths that didn't exist in the object, but that now exist due to              ;;
;;                            the introduction of path expressions                                                         ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (expressionify-paths paths union-candidates
                             #:path-segment-wildcard-chance [wildcard-chance 10]
                             #:make-unreadable-percent [unreadable-percent 20]
                             #:use-union-path-chance [use-union-chance 30])
  (define paths-made-unreadable '())
  (define flat-path-suggestions '())
  (define user-environment '())

  ; turn a single path into a path selector that potentially includes various kinds of path expressions
  ;; returns a path expression, and modifies the user-environment found in scope
  (define (path->path-selector path)
    ; replace a single path  by an "=" wildcard
    (define (mutate-= path-segment make-unreadable?)
      (define symbol (gensym))
      (define kv-for-user-env #f)
      (define replacement-path-segment
        (let ((rand (random 0 100)))
          (cond ((< rand 10)
                 (term [> ,rand]))
                ((< rand 20)
                 (term [< ,rand]))
                ((< rand 30)
                 (term [= ,symbol]))
                ((< rand 40)
                 (term [= ,path-segment]))
                (else
                 (unless make-unreadable?
                   (set! kv-for-user-env
                         (term (,symbol := ,(if (symbol? path-segment)
                                                (term ',path-segment)
                                                path-segment)))))
                 (term [= [~ ,symbol]])))))
      (report "symbol" symbol)
      (report "symbol?" (symbol? symbol))
      (report "path-segment" path-segment)
      (report "symbol? path-segment" (symbol? path-segment))

      (report "replacement-path-segment" replacement-path-segment)
      (values replacement-path-segment kv-for-user-env))

    ; replace a single path segment by a "∈" wildcard
    (define (mutate-∈ path-segment make-unreadable?)
      (define symbol (gensym))
      (define replacement-path-segment (term (∈ [~ ,symbol])))
      (define kv-for-user-env (if make-unreadable?
                                  (term (,symbol := ,(gen-array-object)))
                                  (term (,symbol := ,(gen-array-object #:must-include-val path-segment)))))
      (values replacement-path-segment kv-for-user-env))

    ; replace a single path segment by a "*" wildcard
    (define (mutate-* path-segment make-unreadable?)
      (values wildcard-path-expression #f))

    ; list all possible wildcard mutate procedures
    (define mutations (list mutate-= mutate-∈ mutate-*))


    ; potentially transform a path segment into a random wildcard
    (define (path-segment->key-or-path-expression path-segment)
      ; replace only keys, not path expressions that already exist
      (if (redex-match? CommonLang k path-segment)
          (let ((replace-with-path-expression? (< (random 0 100) wildcard-chance)))
            (if replace-with-path-expression?
                (let ((mutate (random-ref mutations))
                      (make-unreadable? (< (random 0 100) unreadable-percent)))
                  (when (and make-unreadable? (not (eq? mutate mutate-*)))
                    (set! paths-made-unreadable (cons path paths-made-unreadable)))
                  (define-values (replacement-path-segment kv-for-user-env?)
                    (mutate path-segment make-unreadable?))
                  (when kv-for-user-env?
                    (set! user-environment (cons kv-for-user-env? user-environment)))
                  replacement-path-segment)
                path-segment))
          path-segment))

    (define (maybe-invent-new-path! path-expression flat-path position)
      (define invented-path
        (cond ((eq? path-expression wildcard-path-expression) (list-set flat-path position (gensym)))
              (else #f)))
      (when invented-path
        (set! flat-path-suggestions (cons invented-path flat-path-suggestions))))

    (define (maybe-unionify path)
      (define should-use-union? (< (random 0 100) use-union-chance))
      (if should-use-union?
          (let ((union-candidate (findf (lambda (union-candidate)
                                          (list-prefix? (union-candidate-path-full union-candidate) path))
                                        union-candidates)))
            (if union-candidate
                (let ((result (list-set path (length (union-candidate-path-prefix union-candidate)) (union-candidate-path-expression union-candidate))))
                  result)
                path))
          path))
                                        

    (define maybe-unionified-path (maybe-unionify path))
    (define path-selector
      (for/list ([position (in-range 0 (length maybe-unionified-path))])
        (define current-path-key (list-ref maybe-unionified-path position))
        (define replacement-expression (path-segment->key-or-path-expression current-path-key))
        ; not: maybe invent a new path based on the _original_ path (!). This is because the invented path is expected to be flat,
        ; rather than a path selector
        (maybe-invent-new-path! replacement-expression path position)
        replacement-expression))
    path-selector)
 

  (define path-selectors (map path->path-selector paths))
  (values path-selectors user-environment paths-made-unreadable flat-path-suggestions))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generate an object whose size is bounded by the given a particular  ;;
;; depth. The depth is defined by Redex as the size of the parse tree. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (generate-object #:depth [depth 4])
  (define dirty-obj (generate-term CommonLang d depth))
  (define obj (term (cleanup-data ,dirty-obj ())))
  obj)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Returns all possible field access paths of an object from the root ;;
;; object to leaves (fields that contain plain data, i.e., atoms).    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (get-all-paths object)
  (term (data-to-paths ,object)))




(define (path-selector->privilege path-selector role permission)
  (term (ALLOW ,role ,permission OF ,path-selector)))

(define (path-selectors->privileges role path-selectors permission)
  (map (lambda (path-selector) (path-selector->privilege path-selector role permission))
       path-selectors))

(define (project-object object privileges user-environment)
  (term (readable-projection ,object ,privileges ,object ,user-environment ())))

(define generate-role gensym)


(define (generate-nonsense-random-paths nr-of-paths #:path-depth [path-depth 4])
  (for/list ([i (in-range 0 nr-of-paths)])
    (generate-term CommonLang p path-depth)))

(define (execute-read-tests #:object-depth [object-depth 4])
  (define (generate-paths object union-candidates #:keep-flat-minimum-percent [keep-flat-min-percent 0])
    ;; generate correct paths in the this object
    ;; shuffle the list of paths to remove any potential ordering of them
    (define all-paths (shuffle (get-all-paths object)))
    (report "all-paths" all-paths)
  
    (define-values (readable-field-access-paths initial-nonreadable-paths) (split-at all-paths (round (/ (length all-paths) 2))))
    (define nr-of-paths (length readable-field-access-paths))
    (define nr-of-paths-to-keep-flat (round (* (/ nr-of-paths 100) keep-flat-min-percent)))
    (define-values (paths-to-keep-flat paths-to-expressionify) (split-at readable-field-access-paths nr-of-paths-to-keep-flat))
  
    (define-values (path-selectors user-environment paths-made-unreadable _ignored) (expressionify-paths paths-to-expressionify union-candidates))
    (define readable-path-selectors (append paths-to-keep-flat path-selectors))
    (report "path-selectors" path-selectors)
    (report "paths-made-unreadable" paths-made-unreadable)
    (report "user-environment" user-environment)
    (define nonreadable-field-access-paths (remove-readable-paths
                                            (append paths-made-unreadable initial-nonreadable-paths)
                                            readable-path-selectors
                                            user-environment))

    (values (remove-non-readable-paths all-paths readable-path-selectors user-environment)
            readable-path-selectors
            nonreadable-field-access-paths
            user-environment))

  
  ;; generate objects
  (define obj (generate-object #:depth object-depth))
  (report "generated object" obj)

  ; insert possible unions into the object
  (define-values (union-candidates new-obj) (create-unions obj))
  (set! obj new-obj)
  (report "generated object after modifications for adding unions" obj)
  
  ;; generate correct paths in the this object
  ;; shuffle the list of paths to remove any potential ordering of them

  (define-values (flat-readable-paths path-selectors nonreadable-paths user-environment) (generate-paths obj union-candidates))
  (report "readable path-selectors" path-selectors)
  (report "nonreadable-paths" nonreadable-paths)
  (report "user-environment" user-environment)

  (define random-generated-paths (generate-nonsense-random-paths (length path-selectors) #:path-depth object-depth))

  (define role (generate-role))
  (define privileges (path-selectors->privileges role path-selectors 'READ))
  (report "privileges" privileges)

  (define projected-obj (project-object obj privileges user-environment))
  (report "projected-obj" projected-obj)

  (define (generate-program replica-name writable-paths rdt-data user-data body)
    (define deltas '())
    (define replica-data (term (,replica-name ,writable-paths ,rdt-data ,user-data ,deltas)))
    (term ((,replica-data) ,body)))

  (define (path->read-expression replica-name path)
    (if (empty? path)
        (term (,replica-name ()))
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
    (define replica-name (symbol->string (gensym)))
    (define all-read-expressions
      (for/list ([path paths])
        (path->read-expression replica-name path)))

    (define all-programs
      (for/list ([expr all-read-expressions])
        (generate-program replica-name '() projected-obj '() expr)))
    
    (for/list ([program all-programs])
      (define reduction-results


        (apply-reduction-relation* red-replica program))
      (unless (and (= 1 (length reduction-results))
                   (property? (first reduction-results)))
        (error (string-append "counterexample found: ") program reduction-results)))
    )

  ; check whether an expression in ReplicaLang is a value
  (define (is-atom? expr)
    (redex-match? ReplicaLang ((r ...) atom) expr))

  (define (is-value? expr)
    (redex-match? ReplicaLang ((r ...) v) expr))
  
  (define (is-error? expr)
    (redex-match? ReplicaLang ((r ...) (error string)) expr))


  (define (is-value-or-error? expr)
    (or (is-value? expr)
        (is-error? expr)))
  
  (displayln "### --- testing programs with readable paths --- ###")
  ; use the original flat readable paths because those are the ones that should still be readable after we did permutations
  (test-programs flat-readable-paths is-atom?)

  (displayln "### --- testing programs with nonreadable paths --- ###")
  (test-programs nonreadable-paths is-error?)

  (displayln "### --- testing programs with randomly generated paths --- ###")
  (test-programs random-generated-paths is-value-or-error?))



(define (execute-write-tests #:object-depth [object-depth 5])
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Data generation (`d`) ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;; generate objects
  (define obj (generate-object #:depth object-depth))
  (report "obj" obj)

  ; insert possible unions into the object
  (define-values (union-candidates new-obj) (create-unions obj))
  (set! obj new-obj)
  (report "generated object after modifications for adding unions" obj)
  
  ;; generate correct paths in this object
  ;; shuffle the list of paths to remove any potential ordering of them
  (define all-paths (get-all-paths obj))
  (report "all-paths" all-paths)

  (define selected-paths (random-sample all-paths (round (* (length all-paths) 2/3))))

  
  ;;;;;;;;;;;;;;;;;;;;;
  ;; Role generation ;;
  ;;;;;;;;;;;;;;;;;;;;;

  ;(define all-roles (generate-term CommonLang (role_1 role_2 ...) object-depth))
  (define all-roles
    (cons wildcard-role (for/list ([i (in-range (random 1 (* object-depth 2)))])
                          (string->symbol (format "role#~s" i)))))
  (report "all-roles" all-roles)


  ;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Privilege generation ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;

  (struct role (readable-path-selectors writable-path-selectors writable-path-suggestions [user-environment #:mutable])
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (lambda (obj) 'role)
        (lambda (obj) (list (role-readable-path-selectors obj) (role-writable-path-selectors obj) (role-user-environment obj)))))])
  (define roles (make-immutable-hash
                 (for/list ([role-name all-roles])
                   (define sample-size (if (eq? role-name wildcard-role) 1/10 1/3))
                   (define readable-access-paths (random-sample selected-paths (round (* (length selected-paths) sample-size))))
                   (define writable-access-paths (random-sample selected-paths (round (* (length selected-paths) sample-size))))
                   (define-values (readable-path-selectors read-env _ignored1 _ignored2) (expressionify-paths readable-access-paths union-candidates))
                   (define-values (writable-path-selectors write-env _ignored3 writable-path-suggestions) (expressionify-paths writable-access-paths union-candidates))
                   (define user-environment (append read-env write-env))
                   (cons role-name (role readable-path-selectors writable-path-selectors writable-path-suggestions user-environment)))))
  (define roles-without-wildcard (hash-remove roles wildcard-role))
  
  ; add the user environment of the wildcard role to the environment of all other roles
  (define wildcard-user-env (role-user-environment (hash-ref roles wildcard-role)))
  (hash-for-each roles (lambda (role-name obj)
                         (set-role-user-environment! obj (append (role-user-environment obj) wildcard-user-env))))
  (report "roles after adding wildcard's user env" roles)

  ; collect a hashmap of all privileges per role
  (define privileges-per-role
    (hash-map/copy roles
                   (lambda (role-name obj)
                     (define readable-path-selectors (role-readable-path-selectors obj))
                     (define writable-path-selectors (role-writable-path-selectors obj))
                     (define read-privileges (path-selectors->privileges role-name readable-path-selectors 'READ))
                     (define write-privileges (path-selectors->privileges role-name writable-path-selectors 'WRITE))
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
                   (lambda (role-name role-struct)
                     (define privileges (get-privileges-for-role privileges-per-role role-name))
                     (define user-environment (role-user-environment role-struct))
                     (define writable-path-suggestions (role-writable-path-suggestions role-struct))
                     (define all-paths-extended (append all-paths writable-path-suggestions))
                     (define path-selectors (map last privileges))
                     (define non-readable-paths (remove-readable-paths all-paths-extended path-selectors user-environment))
                     (define readable-paths (remove-non-readable-paths all-paths-extended path-selectors user-environment))
                     (define writable-paths (keep-writable-paths obj all-paths-extended privileges user-environment))
                     (define strictly-readable-paths (remove* writable-paths readable-paths equal?))
                     (define role-name-str (symbol->string role-name))
                     (report (string-append role-name-str ": readable-paths") readable-paths)
                     (report (string-append role-name-str ": writable-paths") writable-paths)
                     (values role-name (paths non-readable-paths strictly-readable-paths writable-paths)))))

  
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
  (define (generate-LeaderLang-input d_rdt roles privileges sessions u-configs requests)
    (let* ((role-names (hash-keys roles))
           (projection-input (term [,d_rdt ,role-names ,privileges ()]))
           (projection-result (apply-reduction-relation* projection-red-rel projection-input))
           (r-configs (cadddr (car projection-result))))
      (term (,u-configs ,r-configs ,d_rdt ,sessions ,requests (#;no-results)))))


  (define (generate-program object roles security-policy requests)
    (generate-LeaderLang-input obj
                               roles-without-wildcard
                               security-policy
                               all-user-session-terms
                               all-u-configs
                               requests))

  
  (define (test-programs programs property?)
    (for/list ([program programs])
      (define reduction-results (apply-reduction-relation* leader-request-red-rel program))
      (unless (property? reduction-results)
        (report "tested program: " program)
        (report "reduction results: " reduction-results)
        (error (string-append "counterexample found: ") program reduction-results))))

 
  (define (get-user-from-session s-id)
    (car (memf (lambda (user) (equal? (user-sid user) s-id)) (hash-values users))))

  (define (get-session-term user)
    (term (,(user-sid user) ,(user-uid user))))
  (define all-user-session-terms (hash-map users (lambda (_ user) (get-session-term user))))
  (define all-u-configs (hash-map users (lambda (_ user) (user-config user))))

  (define (are-deltas-correct? response)
    (define (is-delta-allowed? delta)
      (display "checking if delta is allowed: ") (displayln delta)
      (define s-id (second delta))
      (define written-term (last delta))
      (define value-written (last written-term))
      (define path-written (second written-term))

      (define user (get-user-from-session s-id))
      (define role-name (user-role user))
      (define role-struct (hash-ref roles role-name))
      (define user-environment (role-user-environment role-struct))
      (define all-privileges (get-privileges-for-role privileges-per-role role-name))
      (define path-selectors-that-can-be-read (map last all-privileges))

     (define is-allowed? (is-readable-path? path-selectors-that-can-be-read user-environment path-written))
      (display "checking if delta is allowed: ") (display delta) (display " ==> ") (displayln is-allowed?)
      is-allowed?)
    (define deltas (last response))
    (andmap is-delta-allowed? deltas))
  
  (define (is-accepted? reduction-result)
    (define responses (get-LeaderLang-response reduction-result))
    (and (= (length responses) 1)
         (let ((response (first responses)))
           (and (redex-match? LeaderLang (ACCEPT (action ...)) response)
                (are-deltas-correct? response)))))

  (define (is-rejected? reduction-result)
    (define responses (get-LeaderLang-response reduction-result))
    (redex-match? LeaderLang ((REJECT)) responses))
  

  (define (get-LeaderLang-response output) (cadr (cddddr (car output))))


  (define (generate-pushdelta s-id path)
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
         (define write-request (generate-pushdelta current-user-sid path))
         (define program (generate-program obj roles-without-wildcard security-policy (list write-request)))
         program))
     (define disallowed-write-programs1 (generate-programs non-readable-paths))
     (define disallowed-write-programs2 (generate-programs strictly-readable-paths))    
     (define allowed-write-programs (generate-programs writable-paths))
     
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


(define (run-read-tests max-attempts #:complexity [complexity 6])
  (for ([i (in-range 0 (+ max-attempts 1))])
    (displayln (string-append "### --- attempt " (number->string i) " --- ###"))
    (execute-read-tests #:object-depth complexity))
  (print-all-covered-cases)
  (displayln "OK"))


(define (run-write-tests max-attempts #:complexity [complexity 5])
  (for ([i (in-range 0 (+ max-attempts 1))])
    (displayln (string-append "### --- attempt " (number->string i) " --- ###"))
    (execute-write-tests #:object-depth complexity))
  (print-all-covered-cases)
  (displayln "OK"))



  
;(execute-write-tests)

#;(test-policy-overlap #:number-of-users 2)

