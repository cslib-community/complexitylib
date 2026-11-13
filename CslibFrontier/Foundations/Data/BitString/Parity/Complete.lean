/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Parity

/-!
# Completing a word to a prescribed parity

The final bit uniquely completes a word to a chosen parity. These declarations are extracted
unchanged from the XOR sampling application for reuse by parity-constrained distributions.

## Main definitions

* `Cslib.BitString.parityComplete`: append the unique parity-completing bit.
* `Cslib.BitString.parityCompleteEquiv`: the bijection onto a prescribed parity fiber.

## Main results

* `Cslib.BitString.parity_parityComplete`: the completed word has the chosen parity.
-/

@[expose] public section

namespace Cslib.BitString

open Finset

/-- The completion of `j` bits `r` to the `j + 1` bits of parity `c` extending them: the last bit
is `c ⊕ parity r`. -/
def parityComplete (c : Bool) {j : ℕ} (r : BitString j) : BitString (j + 1) :=
  Fin.snoc r (c ^^ parity j r)

/-- The completion of `r` to parity `c` has parity `c`. -/
theorem parity_parityComplete (c : Bool) {j : ℕ} (r : BitString j) :
    parity (j + 1) (parityComplete c r) = c := by
  rw [parityComplete, parity_snoc]
  cases c <;> cases parity j r <;> rfl

/-- Completion to parity `c` is an equivalence onto the bit strings of parity `c`; the inverse
drops the last bit. -/
def parityCompleteEquiv (c : Bool) (j : ℕ) :
    BitString j ≃ {b : BitString (j + 1) // b ∈ ({b | parity (j + 1) b = c} : Finset _)} where
  toFun r := ⟨parityComplete c r, by simp [parity_parityComplete]⟩
  invFun b := Fin.init b.1
  left_inv r := by simp [parityComplete]
  right_inv b := by
    obtain ⟨b, hb⟩ := b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    apply Subtype.ext
    simp only [parityComplete]
    conv_rhs => rw [← Fin.snoc_init_self b]
    congr 1
    rw [← Fin.snoc_init_self b, parity_snoc] at hb
    rw [← hb]
    cases parity j (Fin.init b) <;> cases b (Fin.last j) <;> rfl

/-- A prescribed parity fiber is nonempty in positive dimension. -/
theorem parity_fiber_nonempty {n : ℕ} (hn : 0 < n) (b : Bool) :
    ({x : BitString n | parity n x = b} : Finset _).Nonempty := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact ⟨parityComplete b (fun _ => false), by simp [parity_parityComplete]⟩

end Cslib.BitString
