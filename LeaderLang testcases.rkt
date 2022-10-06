#lang racket

(require redex/reduction-semantics
         redex/pict)
(require "LeaderLang.rkt")
(require "motivating-example.rkt")


;;;;;;;;;;;;;;;;;;;;;;
;; Projection phase ;;
;;;;;;;;;;;;;;;;;;;;;;

(define projection-result
  (apply-reduction-relation* projection-red-rel
                             (term [,RDT-data
                                    (student teacher edu-admin)
                                    ,all-privileges
                                    ()])))
(printf ">> Project motivating example~n")
(pretty-print projection-result)
(unless (eq? (length projection-result) 1)
  (error "Expected exactly one valid projection"))
(set! projection-result (car projection-result))
(unless (equal? (car projection-result) RDT-data)
  (error "Expected RDT-data to be unchanged by projection"))
(unless (equal? (cadr projection-result) '())
  (error "Expected all roles to be consumed by projection"))
(unless (equal? (caddr projection-result) all-privileges)
  (error "Expected privileges to be unchanged by projection"))
(define privs-for-role (cadddr projection-result))


;;;;;;;;;;;;;;;;;;;
;; Running phase ;;
;;;;;;;;;;;;;;;;;;;

(define example-δ
  (term (! (courses c1 registrations 99991 first-session-score) 20)))

(redex-match? LeaderLang (user ...) user-config)
(redex-match? LeaderLang (excerpt ...) privs-for-role)
(redex-match? LeaderLang (priv ...) all-privileges)
(redex-match? LeaderLang d RDT-data)
(redex-match? LeaderLang δ example-δ)

(define (report t)
  #;(pretty-print t)
  (pretty-print (caddr t)))

(printf ">> (LOGIN \"alice\" \"provided-wrong\")~n")
(report (term
         (handle-request
          ,user-config
          ,privs-for-role
          ,RDT-data
          (#;session...)
          (LOGIN "alice" "provided-wrong"))))

(printf ">> (LOGIN \"alice\" \"provided1\")~n")
(report (term
         (handle-request
          ,user-config
          ,privs-for-role
          ,RDT-data
          (#;session...)
          (LOGIN "alice" "provided-alice"))))

(printf ">> (LOGIN \"alice\" \"provided1\") ; Already has session~n")
(report (term
         (handle-request
          ,user-config
          ,privs-for-role
          ,RDT-data
          (("SESSION#1" "alice"))
          (LOGIN "alice" "provided-alice"))))

(printf ">> (GET-REPLICA \"SESSION#0\") ; No session exists~n")
(report (term
         (handle-request
          ,user-config
          ,privs-for-role
          ,RDT-data
          ()
          (GET-REPLICA "SESSION#0"))))

(printf ">> (GET-REPLICA \"SESSION#0\") ; Session#0 doesn't exists~n")
(report (term
         (handle-request
          ,user-config
          ,privs-for-role
          ,RDT-data
          (("SESSION#1" "alice"))
          (GET-REPLICA "SESSION#0"))))


(printf ">> (GET-REPLICA \"SESSION#1\")~n")
(report (term
         (handle-request
          ,user-config
          ,privs-for-role
          ,RDT-data
          (("SESSION#1" "alice"))
          (GET-REPLICA "SESSION#1"))))


(printf ">> (GET-REPLICA \"SESSION#2\")~n")
(report (term
         (handle-request
          ,user-config
          ,privs-for-role
          ,RDT-data
          (("SESSION#2" "charlie"))
          (GET-REPLICA "SESSION#2"))))

(printf ">> (PUSH-Δ~n\t\"SESSION#1\"~n\t~a)~n"
        example-δ)
(report (term
         (handle-request
          ,user-config
          ,privs-for-role
          ,RDT-data
          (("SESSION#1" "alice"))
          (PUSH-Δ
           "SESSION#1"
           ,example-δ))))

(printf ">> (PUSH-Δ~n\t\"SESSION#2\"~n\t(~s))~n"
        example-δ)
(report (term
         (handle-request
          ,user-config
          ,privs-for-role
          ,RDT-data
          (("SESSION#1" "alice") ; student, allowed to see own (alice's) credits
           ("SESSION#2" "charlie"); teacher, allowed to see own courses' credits
           ("SESSION#3" "erin") ; student, but not allowed to see alice's credits
           ("SESSION#4" "frank")) ;edu-admin, allowed to see everything
          (PUSH-Δ
           "SESSION#2"
           ,example-δ))))
