/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Kolmogorov.MINKTStar.Hardness

/-! # Tests for the `NP`-hardness of `MINKT*` -/

public section

namespace CslibFrontierTests.KolmogorovMINKTStarHardness

open Cslib Cslib.Complexity Cslib.Complexity.PromiseProblem Cslib.Kolmogorov
  Cslib.Kolmogorov.MINKTStar Cslib.PartialMCSP.FromCMMSA

/-- `rpHard` instantiated at `MINKT*` itself, which is in `NP` (`MINKTStar.mem_NP`). -/
example : RPReducible enc enc (PromiseProblem.ofSet MINKTStar) (PromiseProblem.ofSet MINKTStar) :=
  rpHard MINKTStar mem_NP

/-- The gap condition of the reduction is implied by the stronger condition of the parameters of
`exists_hard_params`, so the reduction applies to an `NP`-hard `GapCMMSA`. -/
example : ∃ (Δ : ℕ) (g : ℝ), NPHard CMMSAInstance.encoding (GapCMMSA Δ g 1) ∧
    RPReducible CMMSAInstance.encoding enc (GapCMMSA Δ g 1) (PromiseProblem.ofSet MINKTStar) := by
  obtain ⟨Δ, k, δ₀, g, hk, hδ₀, hδ₀', hkδ, hg, hNP⟩ := exists_hard_params
  exact ⟨Δ, g, hNP,
    rpReducible_GapCMMSA_MINKTStar hk hδ₀ hδ₀' hkδ (by linarith [Real.log_pos one_lt_two])⟩

open Classical in
/-- The soundness count holds for every step budget, and the scale `λ₀ (|I| + 1)²` of the seeded
reduction is above its threshold `λ₀ (|I| + 1)`. -/
example (Δ k : ℕ) (hk : Odd k) {δ₀ g : ℝ} (hδ₀ : 0 ≤ δ₀) (hδ₀' : δ₀ ≤ 1 / 2)
    (hkδ : (1 - 2 * δ₀) ^ k ≤ 1 / (2 * Δ ^ 2))
    (hg : 6 * Real.log 2 < g * (Real.log 2 - Real.binEntropy δ₀)) (c : ℕ) :
    ∃ lam₀ : ℕ, ∀ I ∈ (GapCMMSA Δ g 1).no,
      ∀ lam, lam₀ * ((CMMSAInstance.encoding I).length + 1) ^ 2 ≤ lam → ∀ t : ℕ,
        3 * (Finset.univ.filter fun f : VarFunctions I lam =>
            toMINKTStar I Δ k lam f t (GenWitness.sizeBound Δ I lam + c) ∈ MINKTStar).card ≤
          Fintype.card (VarFunctions I lam) := by
  obtain ⟨lam₀, -, h⟩ := exists_three_mul_card_toMINKTStar_mem_le Δ k hk hδ₀ hδ₀' hkδ hg c
  exact ⟨lam₀, fun I hI lam hlam t =>
    h I hI lam ((Nat.mul_le_mul_left _ (Nat.le_self_pow two_ne_zero _)).trans hlam) t⟩

/-- **The `BPP` corollary.** If `MINKT*` were in `BPP`, then `NP ⊆ BPP` over every encoding. -/
example {α : Type} {encA : α ↪ List Bool} (h : MINKTStar ∈ BPP enc) : NP encA ⊆ BPP encA :=
  NP_subset_BPP_of_mem_BPP h

/-- **The `coRP` corollary.** If `MINKT*` were in `coRP`, then `NP ⊆ coRP`. -/
example {α : Type} {encA : α ↪ List Bool} (h : MINKTStar ∈ coRP enc) : NP encA ⊆ coRP encA :=
  NP_subset_coRP_of_mem_coRP h

end CslibFrontierTests.KolmogorovMINKTStarHardness
