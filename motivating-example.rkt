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
  (term (student teacher SAC)))

;;;;;;;;;;;;;;;;;;;;;;;
;; Data to replicate ;;
;;;;;;;;;;;;;;;;;;;;;;;

(define RDT-data
  (term ((courses
          := ((c1 := ((name := "Structure of Computer Programs 1")
                      (credits := 6)
                      (registrations :=
                                     ((99991 :=
                                             ((grade := #f)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Read-only data (on leader) ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define user-config
  (term (("alice"   student   "stored-alice"   ((student-id := 99991)))
         ("bob"     student   "stored-bob"     ((student-id := 99992)))
         ("charlie" teacher   "stored-charlie" ((own-courses := ((0 := 'c1) (1 := 'c2)))))
         ("dan"     student   "stored-dan"     ((student-id := 99993)))
         ("erin"    student   "stored-erin"    ((student-id := 99994)))
         ("frank"   SAC       "stored-frank"   ()))))


;;;;;;;;;;;;;;;;;;;;;
;; Security policy ;;
;;;;;;;;;;;;;;;;;;;;;

(define priv1 (term (ALLOW * READ OF (courses * name))))
(define priv2 (term (ALLOW * READ OF (courses * credits)))) 
(define priv3 (term (ALLOW student READ OF  (courses * registrations (= student-id) *))))
(define priv4 (term (ALLOW teacher WRITE OF (courses (∈ own-courses) registrations * grade))))
(define priv5 (term (ALLOW SAC READ OF  (courses * registrations * *))))
(define priv6 (term (ALLOW SAC WRITE OF (courses * registrations * credits-acquired?))))
(define all-privileges (term (,priv1 ,priv2 ,priv3 ,priv4 ,priv5 ,priv6)))
