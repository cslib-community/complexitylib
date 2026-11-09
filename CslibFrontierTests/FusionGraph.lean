/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Fusion.Graph.Inequality

/-!
# Graph Fusion clients

These examples check nonempty witnesses, the zero-bit convention, exact positive costs, and
transport of the semi-ultrafilter subclass.
-/

namespace CslibFrontierTests.FusionGraph

open Cslib.Circuits Cslib.Circuits.Fusion Cslib.Circuits.Fusion.Graph

private def edge : CanonicalEdge (inequality Bool) := inequalityEdge false true (by decide)

-- The lower-bound witness class really is inhabited, and violates the two diagonal singletons.
example : Nonempty (SemifilterWitness (inequality Bool) sources
    (canonicalClass (inequality Bool))) :=
  ⟨canonicalWitness _ edge⟩

example : ¬ (canonicalFilter (inequality Bool) edge).PreservesPair
    ({diagonal false}, {diagonal true}) := by
  have hd : diagonal false ≠ diagonal true :=
    fun h => Bool.false_ne_true (congrArg (fun x => x.val.1) h)
  simp [edge, Semifilter.PreservesPair, canonicalFilter_inequality, hd, Ne.symm hd]

example : (canonicalFilter (inequality Bool) edge).IsUltra :=
  canonicalFilter_inequality_isUltra false true (by decide)

-- Empty inequality is available for zero AND cost through the false constant.
example : pairCoverComplexity (inequality (Fin 0 → Bool)) sources = 0 :=
  (inequality_complexities 0).2.1

-- Eight vertices per side give exactly three pairs and three intersections.
example : pairCoverComplexity (inequality (Fin 3 → Bool)) sources = 3 :=
  (inequality_complexities 3).2.1

example : ∃ c : Circuit Monotone.signature (Fintype.card (Fin 3 → Bool) +
    Fintype.card (Fin 3 → Bool)) 1,
    c.eval (Monotone.setInterpretation ((Fin 3 → Bool) × (Fin 3 → Bool))) sources 0 =
      inequality (Fin 3 → Bool) ∧ c.program.cost Monotone.andCost = 3 :=
  exists_inequality_circuit 3

example {n : ℕ} (G : Set ((Fin n → Bool) × (Fin n → Bool))) :
    pairCoverComplexity G sources Semifilter.IsUltra ≤
      pairCoverComplexity G (fun i => {x | literals x i = true}) Semifilter.IsUltra :=
  pairCoverComplexity_le_literals G Semifilter.IsUltra

end CslibFrontierTests.FusionGraph
