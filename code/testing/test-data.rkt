#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                                                    ;;;
;;; Test data                                                                                 ;;;
;;;                                                                                                    ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; This file implements the (old and new) motivating example, mainly for use in the testcases.        ;;;
;;;                                                                                                    ;;;
;;; More concretely, this file specifies:                                                              ;;;
;;;    - the data that will be in the SRDT,                                                            ;;;
;;;    - the user data that will be used to authenticate users and to populate their user environment, ;;;
;;;    - the list of roles,                                                                            ;;;
;;;    - the security policy, as a list of privileges, and                                             ;;;
;;;    - (commented out, to copy into the CLI) some suggestions of ReplicaLang programs to try.        ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require redex/reduction-semantics)
(provide all-roles
         RDT-data
         user-config
         all-privileges)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Courses Use Case: Security roles ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define all-roles
  (term (student teacher SAC)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Courses Use Case: Data to replicate ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Courses Use Case: Read-only data (on leader) ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define user-config
  (term (("alice"   student   "stored-alice"   ((student-id := 99991)))
         ("bob"     student   "stored-bob"     ((student-id := 99992)))
         ("charlie" teacher   "stored-charlie" ((own-courses := ((0 := 'c1) (1 := 'c2)))))
         ("dan"     student   "stored-dan"     ((student-id := 99993)))
         ("erin"    student   "stored-erin"    ((student-id := 99994)))
         ("frank"   SAC       "stored-frank"   ()))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Courses Use Case: Security policy ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define priv1 (term (ALLOW * READ OF (courses * name))))
(define priv2 (term (ALLOW * READ OF (courses * credits)))) 
(define priv3 (term (ALLOW student READ OF  (courses * registrations [= (~ student-id)] *))))
(define priv4 (term (ALLOW teacher WRITE OF (courses [∈ (~ own-courses)] registrations * grade))))
(define priv5 (term (ALLOW SAC READ OF  (courses * registrations * *))))
(define priv6 (term (ALLOW SAC WRITE OF (courses * registrations * credits-acquired?))))
(define all-privileges (term (,priv1 ,priv2 ,priv3 ,priv4 ,priv5 ,priv6)))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Collaborative Spotting App Use Case: Security roles ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define all-roles_new
  (term (student user biologist)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Collaborative Spotting App Use Case: Data to replicate ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define RDT-data_new
  (term ((team1
          := ((name := "The Fantastical Scouts")
              (sightings := ((1674813931967 :=
                                     ((location := ((lat := 51.06038) (lng := 4.67201)))
                                      (species := "Fly Agaric")
                                      (photo := "blob:...")
                                      (points := 3)
                                      (feedback := "Do not eat this!")))))))
         (team2 := "omitted for brevity"))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Collaborative Spotting App Use Case: Read-only data (on leader) ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define user-config_new
  (term (("alice"   user        "stored-alice"   ((my-team := 'team1)))
         ("bob"     user        "stored-bob"     ((my-team := 'team1)))
         ("charlie" user        "stored-charlie" ((my-team := 'team1)))
         ("dan"     biologist   "stored-dan"     ())
         ("erin"    biologist   "stored-erin"    ())
         ("frank"   user        "stored-frank"   ()))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Collaborative Spotting App Use Case: Security policy ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define all-privileges_new
  (term ((ALLOW biologist READ OF  (* sightings * *))
         (ALLOW biologist READ OF  (* sightings * location *))
         (ALLOW biologist WRITE OF (* sightings * [∪ points feedback]))
         (ALLOW user      READ OF  (* sightings * [∪ photo points]))
         (ALLOW user      READ OF  ([= (~ my-team)] sightings * feedback))
         (ALLOW user      WRITE OF ([= (~ my-team)] sightings * [∪ name type photo]))
         (ALLOW user      WRITE OF ([= (~ my-team)] sightings * location [∪ lat lng])))))
