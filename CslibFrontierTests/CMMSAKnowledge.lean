/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.MCSP.PartialHardness.Knowledge

/-! Tests for the knowledge sets of a circuit for the CMMSA table. -/

public section

namespace CslibFrontierTests.CMMSAKnowledge

open Cslib Cslib.Complexity Cslib.Logic.PL Cslib.PartialMCSP Cslib.PartialMCSP.FromCMMSA Finset

/-! The form No soundness uses: a circuit that agrees with the table of a No instance makes the
function of some variable one of its candidates, since the knowledge set weighs more than
`g θ ≥ 0`. -/

example {I : CMMSAInstance} {Δ k lam P : ℕ} {g : ℝ} (hI : I ∈ (GapCMMSA Δ g 1).no)
    (f : VarFunctions I lam) (h : BooleanFunction (inputLength I Δ k lam))
    (hh : (toInstance I Δ k lam P f).AgreesWith h) :
    ∃ v : Fin I.weights.length, f v ∈ cand h v := by
  have hlt := lt_weight_cand hI P f h hh
  have hg : 0 ≤ g * I.threshold :=
    mul_nonneg (zero_le_one.trans (mem_no_GapCMMSA_one.1 hI).2.1) (Nat.cast_nonneg _)
  by_contra hnone
  push Not at hnone
  have hempty : (univ.filter fun v : Fin I.weights.length => f v ∈ cand h v) = ∅ :=
    filter_eq_empty_iff.2 fun v _ => hnone v
  simp [hempty, CMMSAInstance.weight] at hlt
  linarith

/-! A concrete No instance: one variable of weight `2`, threshold `1`, and the one formula `x₀`.
At `g = 3 / 2`, every assignment of weight at most `3 / 2` leaves `x₀` false. A circuit that agrees
with the table, here the canonical completion, makes `f 0` a candidate. -/

/-- The instance `⟨[2], 1, [[[(0, true)]]]⟩`. -/
abbrev noInstance : CMMSAInstance := ⟨[2], 1, [[[(0, true)]]]⟩

theorem noInstance_mem_no : noInstance ∈ (GapCMMSA 1 (3 / 2) 1).no := by
  refine mem_no_GapCMMSA_one.2 ⟨⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩,
    by norm_num, fun S hS hw => ⟨_, List.mem_singleton_self _, ?_⟩⟩
  have h0 : 0 ∉ S := fun h0 => by
    have : S = {0} := Finset.eq_singleton_iff_unique_mem.2
      ⟨h0, fun v hv => by simpa using hS hv⟩
    simp [this, CMMSAInstance.weight] at hw
    norm_num at hw
  simp [DNF.eval, Term.eval, Literal.eval, h0]

example {lam k P : ℕ} (f : VarFunctions noInstance lam) :
    f 0 ∈ cand (toInstance noInstance 1 k lam P f).completion 0 := by
  have hlt := lt_weight_cand noInstance_mem_no P f (toInstance noInstance 1 k lam P f).completion
    (Instance.agreesWith_completion _)
  by_contra hf
  have hempty : (univ.filter fun v : Fin noInstance.weights.length =>
      f v ∈ cand (toInstance noInstance 1 k lam P f).completion v) = ∅ :=
    filter_eq_empty_iff.2 fun v _ => by
      obtain ⟨_ | n, hn⟩ := v
      · exact hf
      · simp at hn
  simp [hempty, CMMSAInstance.weight] at hlt
  norm_num at hlt

/-! The candidate count at `Δ = 2`, `k = 3` and `δ₀ = 1 / 4`, where
`(1 - 2 δ₀) ^ k = 1 / 8 = 1 / (2 Δ ^ 2)` and `H(δ₀) < log 2`, so the bound is below the trivial
count `2 ^ 2 ^ ℓ` once `ℓ` is large. -/

example {I : CMMSAInstance} {lam : ℕ} (h : BooleanFunction (inputLength I 2 3 lam))
    (v : Fin I.weights.length) :
    (#(cand h v) : ℝ) ≤ 64 * 2 ^ inputLength I 2 3 lam *
      Real.exp (2 ^ varLength I lam v * Real.binEntropy (1 / 4)) := by
  have := card_cand_le (Δ := 2) (by decide) two_pos (δ₀ := 1 / 4) (by norm_num) (by norm_num)
    (by norm_num) h v
  norm_num at this ⊢
  exact this

end CslibFrontierTests.CMMSAKnowledge
