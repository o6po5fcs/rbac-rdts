#lang racket

(require redex/reduction-semantics
         redex/pict "LeaderLang.rkt" "Common.rkt" "ReplicaLang.rkt")
(require racket/random)

(pretty-print-columns 100)


;;;;;;;;;;;;;;;;;;;;;;;
;; Utility functions ;;
;;;;;;;;;;;;;;;;;;;;;;;

(define (report name t)
  (printf "*** ~a:~n" name)
  (pretty-print t))

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
   ((,(gensym) := json_1′) (k_2′ := json_2′) ...)
   (where json_1′ (cleanup-data json_1 ()))
   (where ((k_2′ := json_2′) ...) (cleanup-data ((k_2 := json_2) ...) (k_seen ...)))])

#;(define (generate-replica-object replica-name
                                 complete-rdt-data
                                 writable-globs rdt-data user-data)
    (define deltas '())
    (term (,replica-name ,writable-globs ,rdt-data ,user-data ,deltas)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Data generation (`d`) ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; generate objects
(define object-depth 5)
(define obj
  (term
   (cleanup-data
    ,(generate-term CommonLang ((k_1 := d_1 ) (k_2 := d_2 ) ...) object-depth)
    ())))
(report "obj" obj)

;; generate correct paths in the this object
;; shuffle the list of paths to remove any potential ordering of them
(define correct-paths (shuffle (term (data-to-paths ,obj))))
(report "correct-paths" correct-paths)

(define-values (selected-paths nonreadable-paths)
  (split-at correct-paths (round (/ (length correct-paths) 2))))
(define-values (readable-paths writable-paths)
  (split-at selected-paths (round (/ (length selected-paths) 2))))
(report "nonreadable-paths" nonreadable-paths)
(report "readable-paths" readable-paths)
(report "writable-paths" writable-paths)


;;;;;;;;;;;;;;;;;;;;;
;; Role generation ;;
;;;;;;;;;;;;;;;;;;;;;

;(define all-roles (generate-term CommonLang (role_1 role_2 ...) object-depth))
(define all-roles
  (let loop ((cnt 1))
    (if (> cnt object-depth)
        '()
        (cons (string->symbol (format "role#~s" cnt))
              (loop (+ cnt 1))))))
(report "all-roles" all-roles)


;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Privilege generation ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

;(define privileges (map (lambda (path) (term (ALLOW ,role ,(generate-term CommonLang )path role))) readable-paths))

(define all-roles-and-readable-paths (cartesian-product (cons '* all-roles) readable-paths))
(define all-roles-and-writable-paths (cartesian-product (cons '* all-roles) writable-paths))
(define (generate-privileges roles paths permission up-to-num)
  (let* ((l (shuffle (cartesian-product (cons '* roles) paths)))
         (pos (max (- (length l) up-to-num) 0))
         (size-limited-l (list-tail l pos))
         (max-number (min (length size-limited-l) object-depth))
         (random-sample (random-sample size-limited-l max-number)))
    (map (λ (role-and-path)
           `(ALLOW ,(car role-and-path) ,permission OF ,(cadr role-and-path)))
         random-sample)))
    

#;(define initial-policy
  (generate-term LeaderLang
                 ((ALLOW p-role r/w OF p-path) ...)
                 object-depth))
(define privileges
  (shuffle (append (generate-privileges all-roles readable-paths 'READ object-depth)
                   (generate-privileges all-roles writable-paths 'WRITE object-depth))))
(report "privileges" privileges)


;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Privilege projection ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

; FIXME: Link between generated u-envs and the users' roles has to be established <-> privileges
(define (generate-u-configs u-envs roles)
  (define cnt 1)
  (map (λ (d_user)
         (let* ((u-id (format "user#~s" cnt))
                (role (random-ref roles))
                (auth-key (format "~a-stored" u-id)))
           (set! cnt (+ cnt 1))
           (term (,u-id := (,role ,auth-key ,d_user)))))
       u-envs))

(define (generate-sessions u-configs)
  (map (λ (u-config)
         (let ((u-id (car u-config)))
           (term (,(format "SESSION#~a" (cadr (string-split u-id "#")))
                  ,u-id))))
       u-configs))

;; Generates term of the form
;; `(u-configs (r-config ...) d_rdt (s ...) (request ...) (result ...))`
(define (generate-LRL-input u-envs d_rdt roles privileges requests)
  (let* ((projection-input (term [,d_rdt ,roles ,privileges ()]))
         (projection-result (apply-reduction-relation* projection-red-rel projection-input))
         (u-configs (generate-u-configs u-envs roles))
         (r-configs (cadddr (car projection-result)))
         (sessions (generate-sessions u-configs)))
    (term (,u-configs ,r-configs ,d_rdt ,sessions ,requests (#;no-results)))))

; FIXME:
(define u-envs '(((a := 1)) ((b := 2)) ((c := 3)) ((d := 4))))

; FIXME:
(define requests '((GET-REPLICA "SESSION#1")))

(define LRL-input (generate-LRL-input u-envs obj all-roles privileges requests))
(report "LRL-input" LRL-input)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Get a replica running... ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (assert-no-more-results results)
  (when (not (null? results))
    (error 'assert-no-more-results "Expected no more results, got ~s" results)))

(define (take-accepted-response results)
  (let* ((head (car results))
         (head-kind (car head))
         (head-body (cadr head))
         (tail (cdr results)))
    (if (not (eq? head-kind 'ACCEPT))
        (error 'take-accepted-response
               "Expected accepted result, got ~s"
               head)
        (values head-body tail))))

(define LRL-state (car (apply-reduction-relation* leader-request-red-rel LRL-input)))
(report "LRL-state after asking for replica" LRL-state)

(define results (sixth LRL-state))
(report "results after asking for replica" results)

(define-values (response other-results) (take-accepted-response results))
(report "response" response)
(report "other results" other-results)
(assert-no-more-results other-results)

(define replica-1 (term (replica-1 FIXME)))
;(generate-term ReplicaLang ((r ...) e) object-depth)
