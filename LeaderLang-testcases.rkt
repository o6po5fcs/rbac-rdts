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
                                    (student teacher SAC)
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
  (term (! (courses c1 registrations 99991 grade) 20)))

(redex-match? LeaderLang (user ...) user-config)
(redex-match? LeaderLang (excerpt ...) privs-for-role)
(redex-match? LeaderLang (priv ...) all-privileges)
(redex-match? LeaderLang d RDT-data)
(redex-match? LeaderLang δ example-δ)

(define (test-request-handling requests expected-sessions expected-results)
  (test-request-handling-w/-data requests expected-sessions expected-results RDT-data))

(define (test-request-handling-w/-data requests expected-sessions expected-results expected-data)
  ; ((user ...) (excerpt ...) d (s ...) (request ...) (result ...))
  (test-->>
   leader-request-red-rel
   (term (,user-config ,privs-for-role ,RDT-data () ,requests ()))
   (term (,user-config ,privs-for-role ,expected-data ,expected-sessions () ,expected-results))))



; Login with wrong credentials
(test-request-handling
 (term ((LOGIN "alice" "provided-wrong")))
 (term ())
 (term ((REJECT))))

; Login with correct credentials
(test-request-handling
 (term ((LOGIN "alice" "provided-alice")))
 (term (("SESSION#alice" "alice")))
 (term ((ACCEPT ((ACCEPT-LOGIN "SESSION#alice"))))))

; Login with session for user already existing
(test-request-handling
 (term ((LOGIN "alice" "provided-alice")
        (LOGIN "alice" "provided-alice")))
 (term (("SESSION#alice" "alice")))
 (term ((ACCEPT ((ACCEPT-LOGIN "SESSION#alice")))
        (REJECT))))

; Getting replica without existing session
(test-request-handling
 (term ((GET-REPLICA "SESSION#alice")))
 (term ())
 (term ((REJECT))))

; Getting replica without matching session
(test-request-handling
 (term ((LOGIN "alice" "provided-alice")
        (GET-REPLICA "SESSION#charlie")))
 (term (("SESSION#alice" "alice")))
 (term ((ACCEPT ((ACCEPT-LOGIN "SESSION#alice")))
        (REJECT))))

; Getting replica with matching session: student role
(test-request-handling
 (term ((LOGIN "alice" "provided-alice")
        (GET-REPLICA "SESSION#alice")))
 (term (("SESSION#alice" "alice")))
 (term ((ACCEPT ((ACCEPT-LOGIN "SESSION#alice")))
        (ACCEPT
         ((INIT
           "SESSION#alice"
           ((ALLOW student READ OF (courses * name))
            (ALLOW student READ OF (courses * credits))
            (ALLOW student READ OF (courses * registrations [= (~ student-id)] *)))
           ((courses
             :=
             ((c1
               :=
               ((name := "Structure of Computer Programs 1")
                (credits := 6)
                (registrations
                 :=
                 ((99991
                   :=
                   ((grade := #f)
                    (credits-acquired? := #f)))))))
              (c2
               :=
               ((name := "Algorithms and Datastructures 1")
                (credits := 6)
                (registrations
                 :=
                 ((99991
                   :=
                   ((grade := #f)
                    (credits-acquired? := #f))))))))))
           ((student-id := 99991))))))))

; Getting replica with matching session: teacher role
(test-request-handling
 (term ((LOGIN "charlie" "provided-charlie")
        (GET-REPLICA "SESSION#charlie")))
 (term (("SESSION#charlie" "charlie")))
 (term ((ACCEPT ((ACCEPT-LOGIN "SESSION#charlie")))
        (ACCEPT
         ((INIT
           "SESSION#charlie"
           ((ALLOW teacher READ OF (courses * name))
            (ALLOW teacher READ OF (courses * credits))
            (ALLOW
             teacher
             WRITE
             OF
             (courses [∈ (~ own-courses)] registrations * grade)))
           ((courses
             :=
             ((c1
               :=
               ((name := "Structure of Computer Programs 1")
                (credits := 6)
                (registrations
                 :=
                 ((99991 := ((grade := #f)))
                  (99992 := ((grade := #f)))
                  (99993 := ((grade := #f)))))))
              (c2
               :=
               ((name := "Algorithms and Datastructures 1")
                (credits := 6)
                (registrations
                 :=
                 ((99991 := ((grade := #f)))
                  (99992 := ((grade := #f)))
                  (99994 := ((grade := #f))))))))))
           ((own-courses := ((0 := 'c1) (1 := 'c2))))))))))

; Push illegal writes (student cannot write grades)
(test-request-handling
 (term ((LOGIN "alice" "provided-alice")
        (GET-REPLICA "SESSION#alice")
        (PUSH-Δ "SESSION#alice" ,example-δ)))
 (term (("SESSION#alice" "alice")))
 (term ((ACCEPT ((ACCEPT-LOGIN "SESSION#alice")))
        (ACCEPT
         ((INIT
           "SESSION#alice"
           ((ALLOW student READ OF (courses * name))
            (ALLOW student READ OF (courses * credits))
            (ALLOW student READ OF (courses * registrations [= (~ student-id)] *)))
           ((courses
             :=
             ((c1
               :=
               ((name := "Structure of Computer Programs 1")
                (credits := 6)
                (registrations
                 :=
                 ((99991
                   :=
                   ((grade := #f)
                    (credits-acquired? := #f)))))))
              (c2
               :=
               ((name := "Algorithms and Datastructures 1")
                (credits := 6)
                (registrations
                 :=
                 ((99991
                   :=
                   ((grade := #f)
                    (credits-acquired? := #f))))))))))
           ((student-id := 99991)))))
        (REJECT))))

; Push permitted writes (teacher can write grades)
; session#alice`:  student, allowed to see own (alice's) grades
; session#charlie: teacher, allowed to see own courses' grades
; session#erin:    student, but not allowed to see alice's grades
; session#frank:   SAC, allowed to see all grades
(test-request-handling-w/-data
 (term ((LOGIN "alice" "provided-alice")
        (LOGIN "charlie" "provided-charlie")
        (LOGIN "erin" "provided-erin")
        (LOGIN "frank" "provided-frank")
        (GET-REPLICA "SESSION#charlie")
        (PUSH-Δ "SESSION#charlie" ,example-δ)))
 (term (("SESSION#frank" "frank")
        ("SESSION#erin" "erin")
        ("SESSION#charlie" "charlie")
        ("SESSION#alice" "alice")))
 (term ((ACCEPT ((ACCEPT-LOGIN "SESSION#alice")))
        (ACCEPT ((ACCEPT-LOGIN "SESSION#charlie")))
        (ACCEPT ((ACCEPT-LOGIN "SESSION#erin")))
        (ACCEPT ((ACCEPT-LOGIN "SESSION#frank")))
        (ACCEPT
         ((INIT
           "SESSION#charlie"
           ((ALLOW teacher READ OF (courses * name))
            (ALLOW teacher READ OF (courses * credits))
            (ALLOW
             teacher
             WRITE
             OF
             (courses [∈ (~ own-courses)] registrations * grade)))
           ((courses
             :=
             ((c1
               :=
               ((name := "Structure of Computer Programs 1")
                (credits := 6)
                (registrations
                 :=
                 ((99991 := ((grade := #f)))
                  (99992 := ((grade := #f)))
                  (99993 := ((grade := #f)))))))
              (c2
               :=
               ((name := "Algorithms and Datastructures 1")
                (credits := 6)
                (registrations
                 :=
                 ((99991 := ((grade := #f)))
                  (99992 := ((grade := #f)))
                  (99994 := ((grade := #f))))))))))
           ((own-courses := ((0 := 'c1) (1 := 'c2)))))))
        (ACCEPT
         ((PUSH-Δ
           "SESSION#frank"
           (! (courses c1 registrations 99991 grade) 20))
          (PUSH-Δ
           "SESSION#alice"
           (! (courses c1 registrations 99991 grade) 20))))))
 (term ((courses
         := ((c1 := ((name := "Structure of Computer Programs 1")
                     (credits := 6)
                     (registrations :=
                                    ((99991 :=
                                            ((grade := 20)
                                             (credits-acquired? := #f)))
                                     (99992 :=
                                            ((grade := #f)
                                             (credits-acquired? := #f)))
                                     (99993 :=
                                            ((grade := #f)
                                             (credits-acquired? := #f)))))))
             (c2 := ((name := "Algorithms and Datastructures 1")
                     (credits := 6)
                     (registrations :=
                                    ((99991 :=
                                            ((grade := #f)
                                             (credits-acquired? := #f)))
                                     (99992 :=
                                            ((grade := #f)
                                             (credits-acquired? := #f)))
                                     (99994 :=
                                            ((grade := #f)
                                             (credits-acquired? := #f))))))))))))


(test-results)
