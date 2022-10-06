#lang racket

(require redex/reduction-semantics
         redex/pict)
(provide all-roles
         RDT-data
         user-config
         all-privileges)

;;;;;;;;;;;;;;;;;;;;
;; Security roles ;;
;;;;;;;;;;;;;;;;;;;;

(define all-roles
  (term (student teacher edu-admin)))

;;;;;;;;;;;;;;;;;;;;;;;
;; Data to replicate ;;
;;;;;;;;;;;;;;;;;;;;;;;

(define RDT-data
  (term ((courses
          := ((c1 := ((name := "Structuur 1")
                      (credits := 6)
                      (registrations :=
                                     ((99991 :=
                                             ((first-session-score := #f)
                                              (second-session-score := #f)
                                              (credits-acquired? := #f)))
                                      (99992 :=
                                             ((first-session-score := #f)
                                              (second-session-score := #f)
                                              (credits-acquired? := #f)))
                                      (99993 :=
                                             ((first-session-score := #f)
                                              (second-session-score := #f)
                                              (credits-acquired? := #f)))))))
              (c2 := ((name := "Algo & Data 1")
                      (credits := 6)
                      (registrations :=
                                     ((99991 :=
                                             ((first-session-score := #f)
                                              (second-session-score := #f)
                                              (credits-acquired? := #f)))
                                      (99992 :=
                                             ((first-session-score := #f)
                                              (second-session-score := #f)
                                              (credits-acquired? := #f)))
                                      (99994 :=
                                             ((first-session-score := #f)
                                              (second-session-score := #f)
                                              (credits-acquired? := #f))))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Read-only data (on leader) ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define user-config
  (term (("alice"   student   "stored-alice"   ((student-id := 99991)))
         ("bob"     student   "stored-bob"     ((student-id := 99992)))
         ("charlie" teacher   "stored-charlie" ((own-courses := ((0 := 'c1) (1 := 'c2)))))
         ("dan"     student   "stored-dan"     ((student-id := 99993)))
         ("erin"    student   "stored-erin"    ((student-id := 99994)))
         ("frank"   edu-admin "stored-frank"   ()))))


;;;;;;;;;;;;;;;;;;;;;
;; Security policy ;;
;;;;;;;;;;;;;;;;;;;;;

(define priv1 (term (ALLOW * READ OF (courses * name))))
(define priv2 (term (ALLOW * READ OF (courses * credits)))) 
(define priv3 (term (ALLOW student READ OF (courses * registrations (= student-id) *))))
(define priv4 (term (ALLOW teacher WRITE OF (courses (∈ own-courses) registrations * first-session-score))))
(define priv5 (term (ALLOW teacher WRITE OF (courses (∈ own-courses) registrations * second-session-score))))
(define priv6 (term (ALLOW edu-admin WRITE OF (courses * registrations * credits-acquired?))))
(define priv7 (term (ALLOW edu-admin READ OF (courses * registrations * first-session-score))))
(define priv8 (term (ALLOW edu-admin READ OF (courses * registrations * second-session-score))))
(define all-privileges (term (,priv1 ,priv2 ,priv3 ,priv4 ,priv5 ,priv6 ,priv7 ,priv8)))
