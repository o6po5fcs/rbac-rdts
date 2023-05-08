#lang racket

(require redex/reduction-semantics
         "interactivity/CLI.rkt")





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LeaderLang's initial data ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define data
  (term ((team1 := ((name := "The Fantastical Scouts")
                    (sightings := ((1674813931967 :=
                                                  ((location := ((lat := 51.06038) (lng := 4.67201)))
                                                   (species := "???")
                                                   (photo := "blob:...")
                                                   (points := 3)
                                                   (feedback := "Do not eat this!")))))))
         (team2 := ((name := "The Brilliant Bunch")
                    (sightings := ((1674814951967 :=
                                                  ((location := ((lat := 51.06066005703071) (lng := 4.674296375850668)))
                                                   (species := "Spicy fly")
                                                   (photo := "blob:..."))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LeaderLang's user configuration ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define user-config
  (term (("Alice"   user        "stored-AliceKey"   ((my-team := 'team1)))
         ("Bob"     user        "stored-BobKey"     ((my-team := 'team2)))
         ("Erin"    biologist   "stored-ErinKey"    ()))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LeaderLang's Security policy ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define roles (term (user biologist)))

(define security-policy
  (term ((ALLOW biologist READ OF  (* sightings * *))
         (ALLOW biologist READ OF  (* sightings * location *))
         (ALLOW biologist WRITE OF (* sightings * [⋃ points feedback]))
         (ALLOW *         READ OF  (* name))
         (ALLOW user      READ OF  (* sightings * [⋃ photo points]))
         (ALLOW user      READ OF  ([= (~ my-team)] sightings * feedback))
         (ALLOW user      WRITE OF ([= (~ my-team)] sightings * [⋃ species photo]))
         (ALLOW user      WRITE OF ([= (~ my-team)] sightings * location [⋃ lat lng])))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Example ReplicaLang programs ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#;
(let ((cr (root my-replica)))
  (let ((sighting (• (• (• cr team1) sightings) 1674813931967)))
    (•! sighting species "Fly Agaric")))


#;
(let ((cr (root my-replica)))
  (let ((sighting (• (• (• cr team2) sightings) 1674814951967)))
    (•! sighting points 1)))

#;
(let ((cr (root my-replica)))
  (let ((sighting (• (• (• cr team2) sightings) 1674814951967)))
    (•! sighting feedback "This is actually an Andrena (solitary bee)")))


#;
(let ((cr (root my-replica)))
  (let ((sighting (• (• (• cr team2) sightings) 1674814951967)))
    (•! sighting points 0)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Start interacting w/ program ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(run-CLI roles data user-config security-policy)