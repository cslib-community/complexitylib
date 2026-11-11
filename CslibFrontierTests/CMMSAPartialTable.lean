/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.MCSP.PartialHardness.Completeness
public import CslibFrontier.Foundations.Data.Nat.AlignedPacking

/-! Tests for the CMMSA partial truth table and its Yes completeness. -/

public section

namespace CslibFrontierTests.CMMSAPartialTable

open Cslib Cslib.Complexity Cslib.PartialMCSP.FromCMMSA

/-! Aligned packing: blocks of sizes `1`, `2` and `4` fit in `[0, 7)` at aligned starts. -/

example : ∃ o : ℕ → ℕ, (∀ i ∈ ({0, 1, 2} : Finset ℕ), 2 ^ i ∣ o i ∧ o i + 2 ^ i ≤ 7) := by
  obtain ⟨o, hfit, -⟩ := Nat.exists_aligned_packing 2 id ({0, 1, 2} : Finset ℕ)
  exact ⟨o, fun i hi => by simpa using hfit i hi⟩

/-! The smallest instance: one variable of weight `1`, threshold `1` and the formula `x₀`. At
scale `λ = 1` its function has no inputs, there are no seed bits, and the only input bit is the
mask of slot `(0, 0)`. -/

/-- One variable, threshold `1`, one formula `x₀`. -/
def tiny : CMMSAInstance := ⟨[1], 1, [[[(0, true)]]]⟩

example : inputLength tiny 1 1 1 = 1 := by
  simp [inputLength, indexWidth, slotWidth, seedWidth, varLength, tiny]

/-! A defined entry fixes the parity of every term of the indexed formula. -/

example {I : CMMSAInstance} {Δ k lam : ℕ} {f : VarFunctions I lam}
    {x : BitString (inputLength I Δ k lam)} {b : Bool} (h : entry f x = some b) (t : Fin Δ)
    (ht : (t : ℕ) < (I.formulas.getD (formulaIndex x) []).length) :
    formulaIndex x < I.formulas.length ∧ termParity f x t = b :=
  ⟨formulaIndex_lt_of_entry_eq_some h, termParity_eq_of_entry_eq_some h t ht⟩

/-! How a reduction uses Yes completeness: with `λ = λ₀ (N + 1) ²` for any `N ≥ m`, such as the
input length, every Yes instance maps into partial MCSP for every choice of the functions. -/

example (Δ k P : ℕ) (hP : 0 < P) :
    ∃ lam₀, ∀ (I : CMMSAInstance), I ∈ (GapCMMSA Δ 2 1).yes → ∀ N, I.formulas.length ≤ N →
      ∀ f : VarFunctions I (lam₀ * (N + 1) ^ 2),
        toInstance I Δ k (lam₀ * (N + 1) ^ 2) P f ∈ PartialMCSP := by
  obtain ⟨lam₀, h⟩ := exists_toInstance_mem_PartialMCSP Δ k P hP
  exact ⟨lam₀, fun I hI N hN f => h 2 1 I hI _ (by gcongr) f⟩

end CslibFrontierTests.CMMSAPartialTable
