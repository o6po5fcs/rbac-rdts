#lang racket

(require redex/reduction-semantics
         redex/pict)
(require "ReplicaLang.rkt"
         (only-in "CommonLang.rkt" json-write))

;;; This file contains tests to quickly check the basic functionality of ReplicaLang.
;;; 


(define (make-replica name privileges data delta)
  (term (,name ,privileges ,data () ,delta)))

;; Some sample terms for use in tests
(define r*-empty-delta (term ()))
(define r1-data (term ((a := 110))))
(define r1-name (term replica-1))
(define r1-privileges (term ((ALLOW the-role WRITE OF (a)))))
(define r1 (make-replica r1-name r1-privileges r1-data r*-empty-delta))

(define r2-name (term replica-2))
(define r2-privileges (term ((ALLOW the-role WRITE OF (b))
                             (ALLOW the-role WRITE OF (c))
                             (ALLOW the-role WRITE OF (c cc)))))
(define r2-data (term ((a := 210)
                       (b := 220)
                       (c :=
                          ((ca := 230)
                           (cb := 231)
                           (cc := 233))))))
(define r2 (make-replica r2-name r2-privileges r2-data r*-empty-delta))
(define r3 (term (replica-3 () ((a := 310)) () ())))

(define r4-name (term replica-4))
(define r4-privileges (term ((ALLOW the-role WRITE OF  (* 31)))))
(define r4-data (term ((0 := 400)
                       (1 := 401)
                       (2 := 402)
                       (3 := ((30 := 4030)
                              (31 := 4031)
                              (32 := 4032)))
                       (4 := 404)
                       (5 := 405))))
(define r4 (make-replica r4-name r4-privileges r4-data r*-empty-delta))
(define r5 (term (replica-5 ((ALLOW the-role WRITE OF (*)))
                            ((0 := 500)
                             (1 := 501)
                             (2 := 502)
                             (3 := 503)
                             (4 := 504)
                             (5 := 505))
                            ()
                            ())))
(define r6 (term (replica-6 ((ALLOW the-role WRITE OF (0 key)))
                            ((0 := ((key := 600)))
                             (1 := ((key := 601)))
                             (2 := ((key := 602)))
                             (3 := ((key := 603)))
                             (4 := ((key := 604)))
                             (5 := ((key := 605))))
                            ()
                            ())))
(define r7 (term (replica-7 ((ALLOW the-role WRITE OF (a))) ((a := ())) () ())))

#;(define e1 (term
              (let ((some-var (• replica-1 a)))
                (•! (• replica-2 c)
                    cc
                    some-var))))


;; Some quick lang spec tests
(define (assert-matched t p?)
  (if (or (not p?)
          (null? p?))
      (error "Did not match, but expected to match: " t)
      (void)))

(assert-matched r1 (redex-match ReplicaLang r r1))
(assert-matched r2 (redex-match ReplicaLang r r2))
(assert-matched r3 (redex-match ReplicaLang r r3))
(assert-matched r4 (redex-match ReplicaLang r r4))
(assert-matched r5 (redex-match ReplicaLang r r5))
(assert-matched r6 (redex-match ReplicaLang r r6))
(assert-matched r7 (redex-match ReplicaLang r r7))



(define (make-program env expr)
  (term (,env ,expr)))

(test-->> red-replica
          (make-program '() (term ((λ (x) x) 1)))
          (make-program '() (term 1)))
(test-->> red-replica
          (make-program '() (term (((λ (x) (λ (y) x)) 1) 2)))
          (make-program '() 1))
(test-->> red-replica
          (make-program '() (term (((λ (x) (λ (y) y)) 1) 2)))
          (make-program '() 2))
(test-->> red-replica
          (make-program '() (term (((λ (x) (λ (x) x)) 1) 2)))
          (make-program '() 2))
(test-->> red-replica
          (make-program '() (term ((λ (x) (+ x x)) 2)))
          (make-program '() 4))
(test-->> red-replica
          (make-program '() (term (let ((x 1)) (+ x x))))
          (make-program '() 2))
(test-->> red-replica
          (make-program '() (term ((λ (x y) (+ x y)) 1 2)))
          (make-program '() 3))
(test-->> red-replica
          (make-program '() (term ((λ (x) (if x x (+ x 1))) 2)))
          (make-program '() 2))
(test-->> red-replica
          (make-program '() (term ((λ (x) (if x 0 1)) #t)))
          (make-program '() 0))
(test-->> red-replica
          (make-program '() (term ((λ (x) (if x 0 1)) #f)))
          (make-program '() 1))
(test-->> red-replica
          (term (() (+ (+ 1 2) (+ 3 4))))
          (term (() 10)))





;; Some quick reduction relation tests
(define repl1-3 (term (,r1 ,r2 ,r3)))
(define repl4-4 (term (,r4)))
(define repl5-5 (term (,r5)))
(test-->> red-replica
          (make-program repl1-3 (term (if #t 1 2)))
          (make-program repl1-3 (term 1)))
(test-->> red-replica
          (make-program repl1-3 (term (if #f 1 2)))
          (make-program repl1-3 (term 2)))
(test-->> red-replica
          (make-program repl1-3 (term (+ 1 2)))
          (make-program repl1-3 (term 3)))
(test-->> red-replica
          (make-program repl1-3 (term (let ((x (if #f 2 3))) (+ 1 x))))
          (make-program repl1-3 (term 4)))
(test-->> red-replica
          (make-program repl1-3 (term (let ((x 1)
                                            (y 2)) (+ x y))))
          (make-program repl1-3 (term 3)))
(test-->> red-replica
          (make-program repl1-3 (term (let ((x 1))
                                        (let ((x 2)
                                              (y (+ x 1)))
                                          y))))
          (make-program repl1-3 (term 2)))
(test-->> red-replica
          (make-program repl1-3 (term (• (replica-1 ()) a)))
          (make-program repl1-3 (term 110)))
(test-->> red-replica
          (make-program repl1-3 (term (• (replica-1 ()) non-existant)))
          (make-program repl1-3 (term (error "Read forbidden"))))
(test-->> red-replica
          (make-program repl1-3 (term (• (root replica-1) a)))
          (make-program repl1-3 (term 110)))
(test-->> red-replica
          (make-program repl1-3 (term (• (replica-2 ()) a)))
          (make-program repl1-3 (term 210)))
(test-->> red-replica
          (make-program repl1-3 (term (• (replica-2 (c)) cb)))
          (make-program repl1-3 (term 231)))
(test-->> red-replica
          (make-program repl1-3 (term (• (• (replica-2 ()) c) cb)))
          (make-program repl1-3 (term 231)))

(let* ((r1-data-modified (term (json-write ,r1-data (a) 1000)))
       (r1-modified (make-replica r1-name r1-privileges r1-data-modified (term ((! (a) 1000))))))
  (test-->> red-replica
            (make-program repl1-3 (term (•! (replica-1 ()) a 1000)))
            (make-program (term (,r1-modified ,r2 ,r3)) (term 1000))))

(test-->> red-replica
          (make-program repl1-3 (term (•! (replica-2 ()) a 2100)))
          (make-program repl1-3 (term (error "Write forbidden"))))

(let* ((r2-data-modified (term (json-write ,r2-data (b) 2200)))
       (r2-modified (make-replica r2-name r2-privileges r2-data-modified (term ((! (b) 2200))))))
  (test-->> red-replica
            (make-program repl1-3 (term (•! (replica-2 ()) b 2200)))
            (make-program (term (,r2-modified ,r1 ,r3)) (term 2200))))

(test-->> red-replica
          (make-program repl1-3 (term (•! (• (replica-2 ()) c) cb 2320)))
          (make-program repl1-3 (term (error "Write forbidden"))))

(let* ((r2-data-modified (term (json-write ,r2-data (c cc) 2330)))
       (r2-modified (make-replica r2-name r2-privileges r2-data-modified (term ((! (c cc) 2330))))))
  (test-->> red-replica
            (make-program repl1-3 (term (•! (• (replica-2 ()) c) cc 2330)))
            (make-program (term (,r2-modified ,r1 ,r3)) (term 2330))))

(test-->> red-replica
          (make-program repl4-4 (term (•! (• (replica-4 ()) 3) 30 5031)))
          (make-program repl4-4 (term (error "Write forbidden"))))

(test-->> red-replica
          (make-program repl4-4 (term (•! (replica-4 (3)) 30 5031)))
          (make-program repl4-4 (term (error "Write forbidden"))))

(let* ((r4-data-modified (term (json-write ,r4-data (3 31) 5031)))
       (r4-modified (make-replica r4-name r4-privileges r4-data-modified (term ((! (3 31) 5031))))))
  (test-->> red-replica
            (make-program repl4-4 (term (•! (• (replica-4 ()) 3) 31 5031)))
            (make-program (term (,r4-modified)) (term 5031))))

(let* ((r1-data-modified (term (json-write ,r1-data (a) 111)))
       (r1-modified (make-replica r1-name r1-privileges r1-data-modified (term ((! (a) 111))))))
  (test-->> red-replica
            (make-program repl1-3 (term (•! (replica-1 ()) a (+ 1 (• (replica-1 ()) a)))))
            (make-program (term (,r1-modified ,r2 ,r3)) (term 111))))

(test-->> red-replica
          (make-program repl4-4 (term (if #t (•! (• (replica-4 ()) 3) 30 5031) "wrong")))
          (make-program repl4-4 (term (error "Write forbidden"))))



(let* ((replica-name (term curriculum))
       (rdt-data (term
                  ((courses := 
                            ((c1 := ((name := "Structure of Computer Programs 1")
                                     (credits := 6)
                                     (registrations :=
                                                    ((100781 := ((grade := 11) 
                                                                 (credits-acquired? := #f))))))))))))
       (rdt-data-modified (term (json-write ,rdt-data (courses c1 registrations 100781 credits-acquired?) #t)))
       (rdt-delta (term ((! (courses c1 registrations 100781 credits-acquired?) #t))))
       (privs (term ((ALLOW SAC READ OF (courses * registrations * *))
                     (ALLOW SAC WRITE OF (courses * registrations * credits-acquired?)))))
       (replica (term (,(make-replica replica-name privs rdt-data r*-empty-delta))))
       (replica-modified (term (,(make-replica replica-name privs rdt-data-modified rdt-delta)))))
  (test-->> red-replica
            (make-program replica (term (let ((cr (root curriculum)))
                                          (let ((regs (• (• (• (• cr courses) c1) registrations) 100781)))
                                            (if (> (• regs grade) 9.5)
                                                (•! regs credits-acquired? #t)
                                                #f)))))
                                            
            (make-program replica-modified (term #t))))


(let* ((replica-name (term teams))
       (rdt-data (term
                  ((team1
                    := ((name := "The Fantastical Scouts")
                        (sightings := ((1674813931967 :=
                                                      ((location := ((lat := 51.06038) (lng := 4.67201)))
                                                       (species := "Fly Agaric")
                                                       (photo := "blob:...")
                                                       (points := 3))))))))))
       (rdt-data-modified (term (json-write ,rdt-data (team1 sightings 1674813931967 feedback) "Do not eat this!")))
       (rdt-delta (term ((! (team1 sightings 1674813931967 feedback) "Do not eat this!"))))
       (privs (term ((ALLOW biologist WRITE OF (* sightings * [⋃ points feedback])))))
       (replica (term (,(make-replica replica-name privs rdt-data r*-empty-delta))))
       (replica-modified (term (,(make-replica replica-name privs rdt-data-modified rdt-delta)))))
  (test-->> red-replica
            (make-program replica (term (let ((cr (root teams)))
                                          (let ((sighting (• (• (• cr team1) sightings) 1674813931967)))
                                            (•! sighting feedback "Do not eat this!")))))
            (make-program replica-modified (term "Do not eat this!"))))


(test-results)