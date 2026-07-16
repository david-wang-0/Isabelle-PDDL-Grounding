theory Grounder_Timing
  imports Main
begin

text \<open>A semantically-transparent per-stage timing combinator for the exported grounding pipeline.

  \<open>time_it\<close> is \<^emph>\<open>the identity\<close> in HOL (\<open>time_it s (\<lambda>_. e) = e\<close>), so wrapping any
  sub-computation of the verified grounder in it leaves the grounder's HOL value --- and hence
  every soundness / plan-preservation theorem --- unchanged. There is no decomposition of the
  verified function and no untrusted SML stitching: the composition stays inside the verified
  function, and the timing is provably transparent.

  In generated SML it is bound to a small self-contained \<^verbatim>\<open>GrounderTiming\<close> module (emitted below via
  \<^theory_text>\<open>code_printing code_module\<close>) that brackets each thunk with the SML basis \<^verbatim>\<open>Time\<close> clock and
  accumulates \<open>(label, ms)\<close> pairs. Being self-contained (no external structure), it compiles under
  both Isabelle's Poly/ML (the \<^theory_text>\<open>value\<close> commands) and MLton (the harness binary); the CLI
  harness reads \<^verbatim>\<open>GrounderTiming.get ()\<close> when \<open>GROUND_PROFILE\<close> is set. Pattern: AFP
  \<^verbatim>\<open>Munta_Model_Checker/library/Trace_Timing\<close>, minus its \<^verbatim>\<open>Refine_Imperative_HOL\<close> (heap-monad) import.\<close>

definition time_it :: "String.literal \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "time_it s f = f ()"

lemma time_it_id [simp]: "time_it s (\<lambda>_. e) = e"
  by (simp add: time_it_def)

code_printing code_module "GrounderTiming" \<rightharpoonup> (SML)
\<open>
structure GrounderTiming : sig
  val time_it : string -> (unit -> 'a) -> 'a
  val get : unit -> (string * IntInf.int) list
  val reset : unit -> unit
end = struct
  (* A 1-element Array is the mutable cell: `Array` is available in both Isabelle's
     Poly/ML (the `value` evaluator) and MLton, unlike plain `ref` (hidden by Poly/ML). *)
  val cell = Array.array (1, [] : (string * IntInf.int) list);
  fun reset () = Array.update (cell, 0, []);
  fun time_it s f =
    let
      val t0 = Time.now ();
      val r = f ();
      val dt = Time.toMilliseconds (Time.- (Time.now (), t0));
    in
      Array.update (cell, 0, (s, dt) :: Array.sub (cell, 0)); r
    end;
  fun get () = Array.sub (cell, 0);
end
\<close>

code_reserved (SML) GrounderTiming

code_printing
  constant time_it \<rightharpoonup> (SML) "GrounderTiming.time'_it"

end
