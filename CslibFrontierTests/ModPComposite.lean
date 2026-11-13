/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

import CslibFrontier.Computability.Complexity.Classes.ModP.Composite
import CslibFrontier.Computability.Complexity.Classes.SharpP.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

namespace Cslib.Complexity.Tests

open Turing.MultiTapeTM Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool}

example (A B : Set α) (hA : A ∈ ParityP enc) (hB : B ∈ ModP 3 enc) : A ∪ B ∈ ModP 6 enc := by
  have hA2 : A ∈ ModP 2 enc := ModP_two ▸ hA
  have hA6 : A ∈ ModP 6 enc := ModP_subset_ModP_of_dvd (by decide) (by decide) hA2
  have hB6 : B ∈ ModP 6 enc := ModP_subset_ModP_of_dvd (by decide) (by decide) hB
  exact supClosed_ModP 6 hA6 hB6

example (A B : Set α) (hA : A ∈ ModP 6 enc) (hB : B ∈ ModP 6 enc) : A ∪ B ∈ ModP 6 enc :=
  supClosed_ModP 6 hA hB

example : ModP 12 enc = ModP 6 enc := by
  have hk : 12 ≠ 0 := by decide
  have h : ModP 12 enc = ModP (∏ p ∈ (12 : ℕ).primeFactors, p) enc :=
    ModP_eq_ModP_prod_primeFactors hk
  have h_prod : (∏ p ∈ (12 : ℕ).primeFactors, p) = 6 := by
    have h_factors : (12 : ℕ).primeFactors = {2, 3} := by
      ext x
      simp only [Nat.mem_primeFactors, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hp, hdvd, _⟩
        have : x ≤ 12 := Nat.le_of_dvd (by decide) hdvd
        revert hdvd hp
        rcases Nat.eq_zero_or_pos x with rfl | hpos
        · decide
        · interval_cases x <;> decide
      · rintro (rfl | rfl)
        · exact ⟨Nat.prime_two, by decide, by decide⟩
        · exact ⟨Nat.prime_three, by decide, by decide⟩
    rw [h_factors]
    exact rfl
  rw [h_prod] at h
  exact h

example : ModP 0 enc = NP enc := ModP_zero

example : ModP 1 enc = { ∅ } := by
  ext A
  simp only [Set.mem_singleton_iff]
  exact mem_ModP_one

/-- The language of lists of booleans where the number of `true` elements is not divisible by 6.
This acts as a concrete count example for `ModP 6`. -/
def trueCount (w : List Bool) : ℕ := w.count true
def notDiv6Lang : Set (List Bool) := {w | trueCount w % 6 ≠ 0}

instance (w : List Bool) : Decidable (w ∈ notDiv6Lang) :=
  inferInstanceAs (Decidable (trueCount w % 6 ≠ 0))

theorem trueCount_mem_SharpP : trueCount ∈ SharpP encBits := by
  apply mem_SharpP_of_polyTime
  have hcount : ComputableInPolyTime (fun x : List Bool => x.count true) encBits encUnary :=
    ComputableInPolyTime.bitsCountWithInput ComputableInPolyTime.id' (.const true)
  exact (ComputableInPolyTime.unary_to_binary.comp hcount).of_enc_eq (fun _ => rfl)

example : notDiv6Lang ∈ ModP 6 encBits :=
  ⟨trueCount, trueCount_mem_SharpP, fun _ => Iff.rfl⟩

/-- Concrete evaluation of accepted input: count is 7, 7 % 6 = 1 ≠ 0, so it is accepted. -/
example : [true, true, true, true, true, true, true] ∈ notDiv6Lang := by decide

/-- Concrete evaluation of rejected input: count is 6, 6 % 6 = 0, so it is rejected. -/
example : [true, true, true, true, true, true] ∉ notDiv6Lang := by decide

end Cslib.Complexity.Tests
