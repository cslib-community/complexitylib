/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Foundations.Probability.PilotTasks
import Complexity.Foundations.Probability.HierarchySampling
import Complexity.Probability.PairwiseIndependentHash.DetectorChannels
import Mathlib.Tactic.NormNum.Prime

/-!
# Concrete pilot recipes and channel-derived correction means

The pilot score has distinct zero and saturated entries on a nonempty affine channel. Its
constructor edges pay for both an endpoint-scale change and a source reset on the integer
schedule. A correction sampler is constructed from actual affine laws and the hierarchy's
detector bound; no incoming-count certificate or mean identity is supplied.
-/

namespace ComplexityTests.PilotTasks

open Finset Matrix Matrix.HierarchyParams Cslib.Probability Cslib.LogSpaceEstimation
open scoped BigOperators

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

private abbrev Seed := Matrix (Fin 1) (Fin 1) (ZMod 3) × (Fin 1 → ZMod 3)
private abbrev retains (s : Seed) (v : ZMod 3) : Prop := affineRetains 3 1 1 s v

private noncomputable def C : Matrix (ZMod 3) (ZMod 3) ℝ :=
  fun x y => if x = 0 ∧ y = 1 then 1 / 6 else 0

private theorem C_nonneg (x y : ZMod 3) : 0 ≤ C x y := by
  unfold C
  split_ifs <;> norm_num

private theorem C_row : C *ᵥ 1 ≤ 1 := by
  intro x
  simp only [mulVec, dotProduct, Pi.one_apply, mul_one]
  by_cases hx : x = 0
  · simp only [C, hx, true_and, sum_ite_eq', mem_univ, ↓reduceIte]
    norm_num
  · simp [C, hx]

private theorem channels : RetentionChannels retains retains (1 / 3) (1 / 3) 1 2 2 4 := by
  convert retentionChannels_affineRetains (P := 3) (H := 1) (ident := id)
    Function.injective_id (a := 1 / 3) (by norm_num) (by norm_num) using 1 <;> norm_num
  all_goals
    funext s v
    simp [retains, affineRetains, mem_retentionBox]

private theorem gate_eq_one (P : FourthRootHierarchyParams 2 1 2 2 4)
    (t : Seed) (x : ZMod 3) : rowGate P.ρ P.K (1 / 3) C {w | retains t w} x = 1 := by
  have hK : 3 < P.K := by
    have hg := P.gate
    have hnonneg : (0 : ℝ) ≤ 2 * P.k / P.η := div_nonneg (by positivity) P.η_pos.le
    have hreal : (3 : ℝ) < P.K := by linarith
    exact_mod_cast hreal
  have hrank : kthLargest P.K {w | retains t w} (fun w => C x w / (1 / 3)) = 0 := by
    apply le_antisymm _ kthLargest_nonneg
    apply le_of_not_gt
    intro hh
    have hc := (lt_kthLargest_iff (by omega : 0 < P.K) (le_refl (0 : ℝ))).mp hh
    have hb : #{w ∈ {w | retains t w} | 0 < C x w / (1 / 3)} ≤ 3 := by
      calc
        _ ≤ Fintype.card (ZMod 3) := card_le_univ _
        _ = 3 := ZMod.card 3
    omega
  rw [rowGate, hrank]
  exact P.ρ_one 0 P.η_pos.le

-- Actual score rows have distinct entries, using the nonempty regular hierarchy witness.
example : ∃ P : FourthRootHierarchyParams 2 1 2 2 4, ∀ t : Seed,
    PilotTask.value P.toHierarchyParams retains retains (1 / 3) C (.score 0) t 0 0 = 0 ∧
    PilotTask.value P.toHierarchyParams retains retains (1 / 3) C (.score 0) t 0 1 = 1 := by
  obtain ⟨P⟩ := FourthRootHierarchyParams.nonempty (q := 2) (cπ := 1)
    (Cπ := 2) (Cpair := 2) (Cvar := 4) (by norm_num) (by norm_num)
  refine ⟨P, fun t => ?_⟩
  have hinput : PilotTask.value P.toHierarchyParams retains retains (1 / 3) C (.input 0) =
      C := by
    simp [PilotTask.value, pilotInput, pilotCorrection_zero]
  rw [PilotTask.value_score, PilotTask.value_score, hinput, gate_eq_one, mul_one, mul_one]
  constructor
  · simpa [C] using P.ϕ_zero 0 P.δ₀_pos.le
  · have hδ : P.δ₁ ≤ 1 / 2 := by
      have h1 := P.δ₁_lt
      have h2 := P.θ_lt_θ₂
      have h3 := P.θ₂_lt
      norm_num at h3
      linarith
    norm_num [C]
    exact P.ϕ_one (1 / 2) hδ

-- The just-completed maximum is an actual child of correction, not a supplied rank premise.
example : (PilotTask.maximum 3).rank < (PilotTask.correction 3).rank :=
  PilotTask.rank_lt_of_mem_children (by simp [PilotTask.children])

-- The actual right factor of `C + Ê₂ C`: endpoint 1/8 → 1/4, source 1/16 → 1/4.
example (M d : ℕ) :
    binNormCost 4 1 * (2 : ℝ) ^ (Real.logb 2 ((1 / 4) / (1 / 16)) / 4) *
        (2 : ℝ) ^ (-precision 16 2 (lastBudget M d 1 1) PilotTask.base.rank
          (1 / 4) (1 / 4)) ≤
      (2 : ℝ) ^ (-precision 16 2 M (PilotTask.input 2).rank (1 / 8) (1 / 16) - 2 +
        (d : ℝ) / 16 + 1 / 16) * scaleMajorant 1 := by
  have hscale : Real.logb 2 ((1 / 4 : ℝ) / (1 / 8)) = (1 : ℤ) := by norm_num
  have hbound := PilotTask.input_request_cost_le
    (r := ⟨.base, 1 / 4, 1 / 4⟩) (i := 2) (f := 1 / 4) (u := 1 / 16)
    (by simp [PilotTask.inputRequests]) (A := 2) (a := 1 / 8)
    (by norm_num) M d 1 (by norm_num) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hscale
  simpa only [Nat.cast_one, Int.cast_one, mul_one] using hbound

-- Budget zero really is inactive, and every positive parent budget strictly drops.
example : precision 16 2 0 (PilotTask.detector 2).rank (1 / 4) (1 / 8) ≤ 0 :=
  precision_zero_nonpos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _

example : lastBudget 0 1 1 1 = 0 ∧ lastBudget 10 1 1 1 < 10 := by decide

private theorem detector_rank (P : FourthRootHierarchyParams 2 1 2 2 4) : 3 < P.J := by
  have hk : (1 : ℝ) ≤ P.k := by exact_mod_cast P.k_pos
  have hm : (1 : ℝ) ≤ P.m := by
    have h := P.copies_strict
    have hnat : 1 ≤ P.m := by
      by_contra hn
      have hm0 : P.m = 0 := by omega
      simp only [hm0, Nat.cast_zero, zero_add] at h
      linarith
    exact_mod_cast hnat
  have hδ : P.δ₀ < 1 := by
    have h1 := P.δ₀_lt_δ₁
    have h2 := P.δ₁_lt
    have h3 := P.θ_lt_θ₂
    have h4 := P.θ₂_lt
    norm_num at h4
    linarith
  have hlower : (8 : ℝ) ≤ 2 * 2 * P.m * P.k * (P.k + 1) := by
    calc
      (8 : ℝ) = 2 * 2 * 1 * 1 * (1 + 1) := by norm_num
      _ ≤ _ := by gcongr
  have hrank := P.rank
  by_contra hn
  have hJ : (P.J : ℝ) ≤ 3 := by exact_mod_cast (le_of_not_gt hn)
  have hδJ : P.δ₀ * P.J ≤ 3 :=
    (mul_le_mul_of_nonneg_right hδ.le (Nat.cast_nonneg _)).trans (by simpa using hJ)
  linarith

-- The true target in the affine sampling example is positive, rather than a zero-atom identity.
example (P : FourthRootHierarchyParams 2 1 2 2 4) :
    0 < P.toHierarchyParams.correctionIter retains retains (1 / 3) C 1 0 1 := by
  have hJ : Fintype.card (ZMod 3) < P.J := by simpa only [ZMod.card] using detector_rank P
  have hmax := PilotTask.value_maximum_eq_zero P.toHierarchyParams retains retains
    (1 / 3) C hJ P.k
  rw [PilotTask.value_maximum_last] at hmax
  have hinput : P.toHierarchyParams.correctionInput retains retains (1 / 3) C 0 = C := by
    simp [HierarchyParams.correctionInput, HierarchyParams.correctionIter, cutoffCorrectionIter]
  rw [HierarchyParams.correctionIter_succ_apply, hinput, hmax]
  have hγ := P.γ_one 0 (by norm_num)
  have hQ : 0 < P.Q (1 / 2) := by
    have hbound := P.le_Q (1 / 2)
    have hθ := P.θ₂_lt
    norm_num at hθ
    linarith
  norm_num [C, hγ]
  positivity

-- Channel/detector-derived sampling data feeds the existing exact actual-correction mean.
example (P : FourthRootHierarchyParams 2 1 2 2 4) (i : ℕ) (hi : i < P.k)
    (x z : ZMod 3) :
    let A := HierarchyParams.CorrectionSampling.ofChannels P retains retains channels channels
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) C_nonneg C_row hi
      (fun _ _ => 0) (fun _ => 1) (fun _ => 1) 0
      (fun _ _ => rfl) (fun _ => zero_le_one) (fun _ => le_rfl) (le_refl _)
      (fun _ _ => rfl) (fun _ _ _ => rfl)
    (𝔼 σ ∈ ({s | retains s x} : Finset Seed) ×ˢ (univ : Finset Seed),
      ((1 / 3) / (1 / 3)) * A.atom σ x z) =
      P.toHierarchyParams.correctionIter retains retains (1 / 3) C (i + 1) x z := by
  intro A
  apply A.expect_atom (by norm_num) C_nonneg C_row
  apply dens_ne_zero.mp
  intro hz
  have hd := channels.dens_X x
  rw [hz] at hd
  norm_num at hd

end ComplexityTests.PilotTasks
