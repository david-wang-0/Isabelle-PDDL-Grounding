;; Transcription of Running_Example.thy `my_domain` (Helmert 2009, modified):
;; type hierarchy, Either-typed parameters, multiple inheritance (Batmobile),
;; circular type graph (R/L), disjunctive preconditions.
(define (domain running-example)
  (:requirements :strips :typing :disjunctive-preconditions)
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

  (:action drive
    :parameters (?c - Car ?from - City ?to - City)
    :precondition (and (at ?c ?from)
                       (or (road ?from ?to) (road ?to ?from)))
    :effect (and (at ?c ?to) (not (at ?c ?from))))

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
