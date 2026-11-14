/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Constructible
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Tactic.EncLen

/-!
# Closure of space-constructible bounds

Space-constructible bounds (`Cslib.Complexity.SpaceConstructible`) are closed under sums and
constant multiples, adding the two values in binary. A bound computed in logarithmic space is
space-constructible when it is at least `⌊log₂ n⌋`; so `⌊log₂ n⌋` and its powers are
space-constructible, the bounds of the space hierarchy at the logarithmic threshold.

## Main results

* `Cslib.Complexity.SpaceConstructible.add`, `Cslib.Complexity.SpaceConstructible.const_mul`: sums
  and constant multiples.
* `Cslib.Complexity.SpaceConstructible.of_computableInLogSpace`: a bound at least `⌊log₂ n⌋`
  computed in logarithmic space.
* `Cslib.Complexity.spaceConstructible_log2`, `Cslib.Complexity.spaceConstructible_log2_pow`:
  `⌊log₂ n⌋` and its positive powers.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Definition 9.1][Sipser2013]
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

/-- **Sums of space-constructible bounds are space-constructible**: compute both values in binary
and add them. -/
theorem SpaceConstructible.add {s₁ s₂ : ℕ → ℕ} (h₁ : SpaceConstructible s₁)
    (h₂ : SpaceConstructible s₂) : SpaceConstructible fun n => s₁ n + s₂ n := by
  obtain ⟨T₁, h₁⟩ := h₁.computableInO
  obtain ⟨T₂, h₂⟩ := h₂.computableInO
  refine SpaceConstructible.of_computableInO 4 (ComputableInO.natAdd.comp (h₁.prod h₂))
    fun x => ?_
  have e₁ := length_encNat_le_self (s₁ x.length)
  have e₂ := length_encNat_le_self (s₂ x.length)
  enc_len

/-- **Constant multiples of space-constructible bounds are space-constructible.** -/
theorem SpaceConstructible.const_mul {s : ℕ → ℕ} (hs : SpaceConstructible s) (c : ℕ) :
    SpaceConstructible fun n => c * s n := by
  induction c with
  | zero => simpa using spaceConstructible_const 0
  | succ c ih => simpa only [Nat.succ_mul] using ih.add hs

/-- **A bound computed in logarithmic space is space-constructible** when it is at least
`⌊log₂ n⌋`: the logarithmic work space is then within `O(s n)`. -/
theorem SpaceConstructible.of_computableInLogSpace {s : ℕ → ℕ}
    (h : ComputableInLogSpace (fun x : List Bool => s x.length) encBits encNat)
    (hs : ∀ n, Nat.log2 n ≤ s n) : SpaceConstructible s := by
  obtain ⟨t, c, h⟩ := h
  obtain ⟨t', h'⟩ := ComputableInTimeAndSpace.exists_time_of_length (s := fun n => c * s n + c)
    (h.mono (fun _ => le_rfl) fun x => by
      have := hs x.length
      simp only [encBits_apply]
      nlinarith)
  exact ⟨c, t', h'⟩

/-- **`⌊log₂ n⌋ ^ (k + 1)` is space-constructible**: compute `⌊log₂ n⌋` in unary from the length,
multiply in unary and convert to binary, in logarithmic space. -/
theorem spaceConstructible_log2_pow (k : ℕ) :
    SpaceConstructible fun n => Nat.log2 n ^ (k + 1) := by
  have hlog : ComputableInLogSpace (fun x : List Bool => Nat.log2 x.length) encBits encUnary :=
    ComputableInLogSpace.unaryLog2 ComputableInLogSpace.bitsLength
  refine SpaceConstructible.of_computableInLogSpace (ComputableInLogSpace.unaryToBinary ?_)
    fun n => Nat.le_self_pow (by omega) _
  induction k with
  | zero => simpa using hlog
  | succ k ih => simpa only [pow_succ] using ComputableInLogSpace.unaryMul ih hlog

/-- **`⌊log₂ n⌋` is space-constructible.** -/
theorem spaceConstructible_log2 : SpaceConstructible Nat.log2 := by
  simpa using spaceConstructible_log2_pow 0

end Cslib.Complexity
