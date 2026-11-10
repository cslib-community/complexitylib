/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Circuit.CompositionDepth
import CslibFrontier.Foundations.Data.BitString.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Fixing the random seed of a circuit with several outputs

A randomized circuit reads an input `x` of `n` bits followed by a seed `r` of `p` bits, and its
outputs should satisfy a specification `Correct x` that may allow several answers, as for an
approximate count. If, at every input, fewer than a `2 ^ (-n)` fraction of the seeds make it fail,
then by the union bound over the `2 ^ n` inputs some seed makes it correct at every input at once
(`Circuit.exists_seed_forall`). Hardwiring that seed costs two gates for the constants and one
level of depth (`Boolean.exists_circuit_of_card_bad_lt`). This is the nonuniform derandomization
of Adleman's theorem without amplification [Arora and Barak, Theorem 7.14][AroraBarak09],
[Adleman1978], for circuits with any number of outputs.

## Main results

* `Cslib.Circuits.Circuit.exists_seed_forall`: a seed that is good for every input, over any
  basis.
* `Cslib.Circuits.Boolean.exists_circuit_of_card_bad_lt`: a deterministic De Morgan circuit with the
  seed hardwired.
* `Cslib.Circuits.Boolean.exists_computes_of_card_bad_lt`: the same when the specification is a
  function.

This recovers the earlier Complexitylib `Classes/Randomized/CircuitHardwiring` formalization
by Samuel Schlesinger, using the current shared-constant substitution circuit.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 7.5][AroraBarak09]
* [L. Adleman, *Two theorems on random polynomial time*][Adleman1978]
-/

public section

namespace Cslib.Circuits

open Finset

variable {n p m : ℕ}

/-- **A seed good for every input.** If, at every input `x` of `n` bits, fewer than a `2 ^ (-n)`
fraction of the seeds `r` make the outputs on `x ++ r` violate `Correct x`, then one seed makes
them satisfy it at every input. -/
theorem Circuit.exists_seed_forall {σ : Signature} {I : Interpretation σ Bool}
    (C : Circuit σ (n + p) m) (Correct : BitString n → BitString m → Prop)
    [∀ x y, Decidable (Correct x y)]
    (h : ∀ x, 2 ^ n * #{r : BitString p | ¬Correct x (C.eval I (Fin.append x r))} < 2 ^ p) :
    ∃ r : BitString p, ∀ x, Correct x (C.eval I (Fin.append x r)) := by
  set bad : BitString n → Finset (BitString p) :=
    fun x => {r : BitString p | ¬Correct x (C.eval I (Fin.append x r))}
  have hsum : 2 ^ n * ∑ x, #(bad x) < 2 ^ n * 2 ^ p := by
    rw [mul_sum]
    calc ∑ x, 2 ^ n * #(bad x) < ∑ _x : BitString n, 2 ^ p :=
          sum_lt_sum_of_nonempty univ_nonempty fun x _ => h x
      _ = 2 ^ n * 2 ^ p := by simp
  have hunion : #(univ.biUnion bad) < Fintype.card (BitString p) := by
    rw [BitString.card]
    exact card_biUnion_le.trans_lt (Nat.lt_of_mul_lt_mul_left hsum)
  obtain ⟨r, -, hr⟩ := exists_mem_notMem_of_card_lt_card hunion
  refine ⟨r, fun x => ?_⟩
  by_contra hx
  exact hr (mem_biUnion.2 ⟨x, mem_univ x, mem_filter.2 ⟨mem_univ r, hx⟩⟩)

namespace Boolean

/-- **Fixing the seed of a De Morgan circuit.** If, at every input `x` of `n` bits, fewer than a
`2 ^ (-n)` fraction of the seeds `r` make the outputs on `x ++ r` violate `Correct x`, then a
deterministic circuit with at most two more gates, and at most one more level, satisfies `Correct x`
at every input. -/
theorem exists_circuit_of_card_bad_lt (C : Circuit signature (n + p) m)
    (Correct : BitString n → BitString m → Prop) [∀ x y, Decidable (Correct x y)]
    (h : ∀ x, 2 ^ n *
      #{r : BitString p | ¬Correct x (C.eval interpretation (Fin.append x r))} < 2 ^ p) :
    ∃ D : Circuit signature n m, (∀ x, Correct x (D.eval interpretation x)) ∧
      D.size ≤ C.size + 2 ∧ D.depth ≤ C.depth + 1 := by
  obtain ⟨r, hr⟩ := C.exists_seed_forall Correct h
  refine ⟨C.comp (substituteCircuit (appendInputs r)), fun x => ?_, ?_, ?_⟩
  · rw [Circuit.eval_comp, eval_substituteCircuit, substitute_appendInputs]
    exact hr x
  · rw [Circuit.size_comp, size_substituteCircuit, Nat.add_comm]
  · exact (Circuit.depth_comp_le _ _).trans
      (Nat.add_le_add_left (depth_substituteCircuit_le _) _)

/-- **Fixing the seed of a De Morgan circuit computing a function.** If, at every input `x` of `n`
bits, the outputs on `x ++ r` differ from `f x` for fewer than a `2 ^ (-n)` fraction of the seeds
`r`, then a deterministic circuit with at most two more gates, and at most one more level, computes
`f`. -/
theorem exists_computes_of_card_bad_lt (C : Circuit signature (n + p) m)
    (f : BitString n → BitString m)
    (h : ∀ x, 2 ^ n * #{r : BitString p | C.eval interpretation (Fin.append x r) ≠ f x} < 2 ^ p) :
    ∃ D : Circuit signature n m, D.Computes interpretation f ∧
      D.size ≤ C.size + 2 ∧ D.depth ≤ C.depth + 1 :=
  exists_circuit_of_card_bad_lt C (fun x y => y = f x) h

end Boolean

end Cslib.Circuits
