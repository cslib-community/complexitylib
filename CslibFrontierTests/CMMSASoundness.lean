/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.MCSP.PartialHardness.Soundness

/-! Tests for No soundness of the CMMSA table. -/

public section

namespace CslibFrontierTests.CMMSASoundness

open Cslib Cslib.Complexity Cslib.PartialMCSP.FromCMMSA Finset

/-! The seeded form a randomized reduction uses: at least two thirds of the functions `f` give a
No instance of partial MCSP. -/

open scoped Classical in
example (Δ k P : ℕ) (hP : 0 < P) (hk : Odd k) {δ₀ g : ℝ} (hδ₀ : 0 ≤ δ₀) (hδ₀' : δ₀ ≤ 1 / 2)
    (hkδ : (1 - 2 * δ₀) ^ k ≤ 1 / (2 * Δ ^ 2))
    (hg : 8 * (1 + 2 / P) * Real.log 2 < g * (Real.log 2 - Real.binEntropy δ₀)) :
    ∃ lam₀ : ℕ, ∀ I ∈ (GapCMMSA Δ g 1).no, ∀ N : ℕ, I.formulas.length ≤ N →
      I.weights.length ≤ N → (∀ w ∈ I.weights, w ≤ N) →
      ∀ lam, lam₀ * (N + 1) ^ 2 ≤ lam →
        2 * Fintype.card (VarFunctions I lam) ≤
          3 * #{f : VarFunctions I lam | toInstance I Δ k lam P f ∉ PartialMCSP} := by
  obtain ⟨lam₀, h⟩ := three_mul_card_toInstance_mem_PartialMCSP_le Δ k P hP hk hδ₀ hδ₀' hkδ hg
  refine ⟨lam₀, fun I hI N hm hn hw lam hlam => ?_⟩
  have h1 := h I hI N hm hn hw lam hlam
  have h2 := card_filter_add_card_filter_not (s := (univ : Finset (VarFunctions I lam)))
    (fun f => toInstance I Δ k lam P f ∈ PartialMCSP)
  rw [card_univ] at h2
  omega

/-! Concrete parameters `Δ = k = P = 1` and `δ₀ = 1 / 4`, where `(1 - 2 δ₀) ^ k = 1 / (2 Δ ²)`,
with a gap `g` just above the threshold `8 (1 + 2 / P) log 2 / (log 2 - H(δ₀))`. -/

open scoped Classical in
example : ∃ lam₀ : ℕ,
    ∀ I ∈ (GapCMMSA 1 (25 * Real.log 2 / (Real.log 2 - Real.binEntropy (1 / 4))) 1).no,
      ∀ N : ℕ, I.formulas.length ≤ N → I.weights.length ≤ N → (∀ w ∈ I.weights, w ≤ N) →
        ∀ lam, lam₀ * (N + 1) ^ 2 ≤ lam →
          3 * #{f : VarFunctions I lam | toInstance I 1 1 lam 1 f ∈ PartialMCSP} ≤
            Fintype.card (VarFunctions I lam) := by
  have hγ : 0 < Real.log 2 - Real.binEntropy (1 / 4) :=
    sub_pos.2 (Real.binEntropy_lt_log_two.2 (by norm_num))
  refine three_mul_card_toInstance_mem_PartialMCSP_le 1 1 1 one_pos odd_one (δ₀ := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) ?_
  rw [div_mul_cancel₀ _ hγ.ne']
  have := Real.log_pos (one_lt_two (α := ℝ))
  norm_num
  linarith

/-! Odd `k > 1`: `Δ = 2`, `k = 3`, `P = 1` and `δ₀ = 1 / 4`, where
`(1 - 2 δ₀) ^ k = 1 / 8 = 1 / (2 Δ ²)`, with the same gap `g`. -/

open scoped Classical in
example : ∃ lam₀ : ℕ,
    ∀ I ∈ (GapCMMSA 2 (25 * Real.log 2 / (Real.log 2 - Real.binEntropy (1 / 4))) 1).no,
      ∀ N : ℕ, I.formulas.length ≤ N → I.weights.length ≤ N → (∀ w ∈ I.weights, w ≤ N) →
        ∀ lam, lam₀ * (N + 1) ^ 2 ≤ lam →
          3 * #{f : VarFunctions I lam | toInstance I 2 3 lam 1 f ∈ PartialMCSP} ≤
            Fintype.card (VarFunctions I lam) := by
  have hγ : 0 < Real.log 2 - Real.binEntropy (1 / 4) :=
    sub_pos.2 (Real.binEntropy_lt_log_two.2 (by norm_num))
  refine three_mul_card_toInstance_mem_PartialMCSP_le 2 3 1 one_pos (by decide) (δ₀ := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) ?_
  rw [div_mul_cancel₀ _ hγ.ne']
  have := Real.log_pos (one_lt_two (α := ℝ))
  norm_num
  linarith

end CslibFrontierTests.CMMSASoundness
