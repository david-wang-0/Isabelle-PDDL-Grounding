(* Naive DPLL SAT solver over DIMACS-style clause lists (int list list).

   This is the *untrusted* SAT oracle `g` handed to the exported
   `plan_by_cert`: any bug here only loses completeness, because the verified
   kernel re-checks the returned assignment against the original encoding
   (`A |= Phi_forall PS t`) before decoding a plan from it.

   Unit propagation + chronological branching on the first literal of the
   first clause.  Returns a satisfying assignment as a list of literals
   (positive = true, negative = false); unassigned variables default to
   false on the Isabelle side (`dimacs_model_to_abs _ (%_. False)`). *)

structure SatSolver :
sig
  (* SOME literals if satisfiable, NONE if unsatisfiable *)
  val solve : IntInf.int list list -> IntInf.int list option
  (* like solve, but [] on UNSAT -- the shape plan_by_cert's g expects *)
  val solveOrEmpty : IntInf.int list list -> IntInf.int list
end =
struct
  (* Assign literal l: drop satisfied clauses, strip ~l; NONE on empty clause. *)
  fun assign (l : IntInf.int) (cs : IntInf.int list list) =
    let
      fun upd ([], acc) = SOME (List.rev acc)
        | upd (c :: rest, acc) =
            if List.exists (fn x => x = l) c then upd (rest, acc)
            else
              let val c' = List.filter (fn x => x <> ~l) c
              in if List.null c' then NONE else upd (rest, c' :: acc) end
    in upd (cs, []) end

  fun findUnit [] = NONE
    | findUnit ([l] :: _) = SOME (l : IntInf.int)
    | findUnit (_ :: rest) = findUnit rest

  fun dpll (cs, model) =
    case findUnit cs of
      SOME l =>
        (case assign l cs of
           NONE => NONE
         | SOME cs' => dpll (cs', l :: model))
    | NONE =>
        (case cs of
           [] => SOME model
         | (c :: _) =>
             let
               val l = List.hd c
               fun tryLit lit =
                 case assign lit cs of
                   NONE => NONE
                 | SOME cs' => dpll (cs', lit :: model)
             in
               case tryLit l of
                 SOME m => SOME m
               | NONE => tryLit (~l)
             end)

  fun solve cs =
    (* drop tautological clauses ([~1, 1] from `Not Bot`) up front *)
    let val cs' = List.filter (fn c => not (List.exists (fn x => List.exists (fn y => y = ~x) c) c)) cs
    in dpll (cs', []) end

  fun solveOrEmpty cs = case solve cs of SOME m => m | NONE => []
end
