# WIP: Numeric Definedness Tracking

This document captures the design and outstanding work for extending the verified PDDL grounder to numeric PDDL by translating numeric definedness into propositional predicates. This simpler definedness-tracking approach replaces the earlier bound-splitting approach.

## Goal

Extend the grounder to handle definedness of Primitive Numeric Expressions (PNEs) properly under delete relaxation. 
Instead of complex bound splitting, we introduce a new step (`Definedness_Translation`) right before precondition relaxation. This step converts definedness requirements and assignments into regular propositional atoms.

## Pipeline (Target Order)

```text
detype (Type_Normalization)
  -> degoal (Goal_Normalization)
  -> explicate_def (Definedness_Normalization) 
  -> split (Precondition_Normalization)
  -> def_translate (NEW — Definedness_Translation)
  -> relax (PDDL_Relaxation)
  -> reach (semi_naive_eval on the relaxed problem)
  -> ground (existing grounder)
  -> as_strips
```

## The Definedness_Translation Step

The `Definedness_Translation` step transforms actions as follows:

1. **Preconditions:**
   - Strips out the `(Atom (numericEqAtm (FunctionExpr p) (FunctionExpr p)))` checks that were added during `explicate_def`.
   - Adds a new propositional predicate `(predAtm (Pred "Defined_f") args)` for all PNEs that were in that original `numericEqAtm` prefix.
   - Also adds `(predAtm (Pred "Defined_f") args)` for any PNE that appears on the **RHS** of any numeric effects in the action, as the action cannot execute if the RHS is undefined.

2. **Effects:**
   - For any PNE that is assigned on the **LHS** of a numeric effect, adds `(predAtm (Pred "Defined_f") args)` to the propositional `adds` of the action to indicate that the PNE has become defined.

Because this step translates numeric definedness fully into propositional atoms, the subsequent `relax` step (which destroys numeric atoms) can be left completely unchanged!

## Concrete Work Items

1. **Create `Definedness_Translation/ROOT` and skeleton `Definedness_Translation.thy`**.
2. **Implement AST transformations** for `Definedness_Translation` (preconditions and effects as described above).
3. **Wire into `Grounding_Pipeline.thy`** between `split` and `relax`.
