;; Transcription of Running_Example.thy `my_problem`.
;; (batmobile is deliberately absent from init, as in the theory.)
(define (problem running-example-1)
  (:domain running-example)
  (:objects
    c1 c2 c3 - Car
    t - Train
    p1 p2 - Parcel
    batmobile - Batmobile)
  (:init
    (at c1 A) (at c2 B) (at c3 G)
    (at t E)
    (at p1 C) (at p2 F)
    (road A D) (road B D) (road C D)
    (rails D E)
    (road E F) (road F G) (road G E))
  (:goal (and (at p1 G) (at p2 E))))
