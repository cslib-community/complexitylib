/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Padding.Language
public import CslibFrontier.Computability.Complexity.Classes.Space.Basic
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Complexity.Classes.Space.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolynomialPadding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Foundations.Data.Nat.AffineBound

/-!
# Polynomial padding for deterministic space

The polynomially padded language `Cslib.Complexity.polynomialPadded A k` consists of the words `x`
carrying a word `y = unframe x` of `A` framed at their start, with `(y.length + 1) ^ k ≤ x.length`
(`CslibFrontier.Computability.Complexity.Classes.Padding.Language`). If `A` is in deterministic
space `O((n + 1) ^ (b * k))`, then its padded language is in deterministic space `O((n + 1) ^ b)`
(`Cslib.Complexity.polynomialPadded_mem_DSPACE`). The decider tests the padding in linear space
(`Turing.MultiTapeTM.computableInO_polynomialPaddingGuard`). When the test passes, it writes `y`
(`Turing.MultiTapeTM.ComputableInO.unframe`) and decides it within space
`O((|y| + 1) ^ (b * k)) ≤ O(|x| ^ b)`; otherwise it rejects. The padding map
`y ↦ frame y ++ 1^((|y| + 1) ^ k)` is computable in polynomial time
(`Cslib.Complexity.polyTimeReducible_polynomialPadded`), so every problem reduces to its padded
language.

Space is measured by visited work cells, as in `Cslib.Complexity.DSPACE`. The proof moves between
`DSPACE` and the quantitative calculus through
`CslibFrontier.Computability.Complexity.Classes.Space.Quantitative`.

This is the padding technique of [Arora and Barak, §2.6.2][AroraBarak07] for space. With the space
hierarchy theorem it shows that `DSPACE n` is not closed under polynomial-time reductions
(`CslibFrontier.Computability.Complexity.Classes.Space.Separation`).

## Main results

* `Cslib.Complexity.polynomialPadded_mem_DSPACE`: padding into deterministic space.
* `Cslib.Complexity.polyTimeReducible_polynomialPadded`: every problem reduces to its padded
  language.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **Every problem reduces to its padded language**, by the polynomial-time padding map
`y ↦ frame y ++ 1^((|y| + 1) ^ k)`, for `k ≥ 1`. -/
theorem polyTimeReducible_polynomialPadded (A : Set (List Bool)) {k : ℕ} (hk : 1 ≤ k) :
    PolyTimeReducible encBits encBits A (polynomialPadded A k) :=
  ⟨_, (computableInO_polynomialPadding hk).computableInPolyTime
    ⟨fun n => (n + 1) ^ (2 * k), by fun_prop, fun _ => le_rfl⟩
    ⟨fun n => (n + 1) ^ k, by fun_prop, fun _ => le_rfl⟩,
    fun _ => (frame_append_replicate_mem_polynomialPadded_iff le_rfl).symm⟩

/-- **Padding into deterministic space.** If `A` is in deterministic space `O((n + 1) ^ (b * k))`,
with `1 ≤ b`, then its padded language with exponent `k` is in deterministic space
`O((n + 1) ^ b)`. -/
theorem polynomialPadded_mem_DSPACE {A : Set (List Bool)} {b k : ℕ} (hb : 1 ≤ b)
    (hA : A ∈ DSPACE encBits (fun n => (n + 1) ^ (b * k))) :
    polynomialPadded A k ∈ DSPACE encBits (fun n => (n + 1) ^ b) := by
  classical
  obtain ⟨T, hT⟩ := computableInO_indicator_of_mem_DSPACE hA
  have hdec := (computableInO_polynomialPaddingGuard k).ite (hT.comp ComputableInO.unframe)
    (ComputableInO.const (encIn := encBits) (encMid := encBool) false)
  have hset : polynomialPadded A k = {x | (if decide (((unframe x).length + 1) ^ k ≤ x.length)
      then indicator A (unframe x) else false) = true} := by
    ext x
    by_cases hg : ((unframe x).length + 1) ^ k ≤ x.length <;>
      simp [hg, indicator]
  rw [hset]
  refine DSPACE_mono_of_le_mul_add (s₁ := fun n => 3 * (n + 1) ^ b) (C := 3) (fun n => by omega)
    (setOf_mem_DSPACE_of_computableInO hdec fun x => ?_)
  have hlin : x.length + 1 ≤ (x.length + 1) ^ b := Nat.le_self_pow (by omega) _
  simp only [encBits_apply]
  split_ifs with hg
  · have hpad : ((unframe x).length + 1) ^ (b * k) ≤ (x.length + 1) ^ b := by
      rw [Nat.mul_comm, pow_mul]
      exact Nat.pow_le_pow_left ((of_decide_eq_true hg).trans (Nat.le_succ _)) b
    have hu := length_unframe_le x
    omega
  · omega

end Cslib.Complexity
