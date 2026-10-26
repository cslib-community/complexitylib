/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Semifilter

/-!
# Semifilter bounds for Boolean computations

The true sets of supplied Boolean functions and a designated target output define a semifilter
cover problem. Its minimum pair count bounds the AND cost of every native monotone circuit
computing the target from those functions. Both raw input variables and positive/negative
literals are ordinary source families in this interface; no problem or model wrapper is needed.

Supplied functions are free in `ecomplexityFrom`. In particular, supplying negative literals
does not charge their construction. The circuit itself has only constants, AND and OR gates.
Circuits with internal NOT gates are handled in
`Complexity/Computability/Circuit/Fusion/DeMorgan.lean`, through the dual-rail
translation. The translated circuit has twice as many total gates and exactly one AND gate per
original binary gate, so the pair-cover complexity bounds the original binary-gate cost and its
ordinary size.

## Main results

* `Cslib.Circuits.Fusion.pairCover_lowerBound_of_computesFrom`: transfer a combinatorial bound
  to a concrete circuit computing from supplied Boolean functions.
* `Cslib.Circuits.Fusion.pairCoverComplexity_le_ecomplexityFrom_bool`: transfer to minimum
  supplied-source complexity, retaining all designated outputs.

## References

* Adapted from LowerBound/Fusion/Boolean.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits.Fusion

variable {U : Type*} {n m : ℕ}

/-- A lower bound on covers of the true-set problem bounds every Boolean implementation. -/
theorem pairCover_lowerBound_of_computesFrom (sources : U → Fin n → Bool)
    (target : U → Fin m → Bool) (o : Fin m)
    {admissible : Semifilter ↥({x | target x o = true}ᶜ) → Prop} {k : ℕ}
    (hbound : ∀ c : PairCover {x | target x o = true}
      (fun i => {x | sources x i = true}) admissible, k ≤ c.pairs.length)
    (c : Circuit Monotone.signature n m)
    (hc : c.ComputesFrom Monotone.interpretation target sources) :
    k ≤ c.program.cost Monotone.andCost :=
  pairCover_lowerBound hbound c o
    (congrFun ((Monotone.eval_setOf_iff_computesFrom c sources target).mpr hc) o)

/-- The true-set pair-cover complexity bounds native Boolean source complexity. Sources may
be arbitrary supplied functions, including raw variables, helpers and negative literals. -/
theorem pairCoverComplexity_le_ecomplexityFrom_bool (sources : U → Fin n → Bool)
    (target : U → Fin m → Bool) (o : Fin m)
    (admissible : Semifilter ↥({x | target x o = true}ᶜ) → Prop := fun _ => True) :
    pairCoverComplexity {x | target x o = true} (fun i => {x | sources x i = true}) admissible ≤
      ecomplexityFrom Monotone.interpretation Monotone.andCost target sources :=
  le_ecomplexityFrom_iff.mpr fun c hc => pairCoverComplexity_le_cost c _ o
    (congrFun ((Monotone.eval_setOf_iff_computesFrom c sources target).mpr hc) o) admissible

end Cslib.Circuits.Fusion
