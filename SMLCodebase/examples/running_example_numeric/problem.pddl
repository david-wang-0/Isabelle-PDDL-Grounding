;; Numeric variant of problem.pddl (Running_Example.thy `my_problem`): each Car
;; starts with 10 units of fuel. (batmobile is deliberately absent from init, as
;; in the theory.)
(define (problem running-example-numeric-1)
  (:domain running-example-numeric)
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
    (road E F) (road F G) (road G E)
    (= (fuel c1) 10) (= (fuel c2) 10) (= (fuel c3) 10))
  (:goal (and (at p1 G) (at p2 E))))
