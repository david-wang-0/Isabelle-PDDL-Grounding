;; Numeric variant of domain.pddl (Running_Example.thy `my_domain`): adds a
;; `fuel` numeric fluent per Car. `drive` now requires fuel >= 1 and consumes 1
;; unit of fuel. Everything else is unchanged. Threading this through the
;; grounding pipeline exercises definedness normalization (definedness of
;; `(fuel ?c)` made explicit) + definedness translation (the numeric condition
;; and the `decrease` effect are compiled to the propositional `def(fuel,...)`
;; predicate), so the reachability datalog stays numeric-free (ops_no_num) while
;; the numeric grounder retains the `fuel` function declaration and the
;; `def(fuel, c)` fluent-state atoms in the grounded (pre-STRIPS) output.
(define (domain running-example-numeric)
  (:requirements :strips :typing :disjunctive-preconditions :numeric-fluents)
  (:types
    City Movable - object
    Vehicle Parcel - Movable
    Car Train - Vehicle
    R - L
    L - R
    Batmobile - Car
    Batmobile - Train)
  (:constants A B C D E F G - City)
  (:predicates
    (at ?m - Movable ?c - City)
    (in ?p - Parcel ?v - (either Car Train))
    (road ?x - City ?y - City)
    (rails ?x - City ?y - City))
  (:functions (fuel ?c - Car))

  (:action drive
    :parameters (?c - Car ?from - City ?to - City)
    :precondition (and (at ?c ?from)
                       (>= (fuel ?c) 1)
                       (or (road ?from ?to) (road ?to ?from)))
    :effect (and (at ?c ?to) (not (at ?c ?from))
                 (decrease (fuel ?c) 1)))

  (:action choochoo
    :parameters (?t - Train ?from - City ?to - City)
    :precondition (and (at ?t ?from)
                       (or (rails ?from ?to) (rails ?to ?from)))
    :effect (and (at ?t ?to) (not (at ?t ?from))))

  (:action load
    :parameters (?what - Parcel ?where - City ?into - (either Car Train))
    :precondition (and (at ?into ?where) (at ?what ?where))
    :effect (and (in ?what ?into) (not (at ?what ?where))))

  (:action unload
    :parameters (?what - Parcel ?from - (either Car Train) ?where - City)
    :precondition (and (at ?from ?where) (in ?what ?from))
    :effect (and (at ?what ?where) (not (in ?what ?from)))))
