/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Computability.LogSpaceDerandomization.PilotRowTasks
import Complexity.Computability.LogSpaceDerandomization.CorrectionRowTasks
import Complexity.Computability.LogSpaceDerandomization.HierarchySampling
import Complexity.Computability.LogSpaceDerandomization.PairwiseIndependentHash.DetectorChannels
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

private theorem C_le (x y : ZMod 3) : C x y ≤ 1 / 3 := by
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
    (t : Seed) (x : ZMod 3) (input : Matrix (ZMod 3) (ZMod 3) ℝ := C) :
    rowGate P.ρ P.K (1 / 3) input {w | retains t w} x = 1 := by
  have hK : 3 < P.K := by
    have hg := P.gate
    have hnonneg : (0 : ℝ) ≤ 2 * P.k / P.η := div_nonneg (by positivity) P.η_pos.le
    have hreal : (3 : ℝ) < P.K := by linarith
    exact_mod_cast hreal
  have hrank : kthLargest P.K {w | retains t w} (fun w => input x w / (1 / 3)) = 0 := by
    apply le_antisymm _ kthLargest_nonneg
    apply le_of_not_gt
    intro hh
    have hc := (lt_kthLargest_iff (by omega : 0 < P.K) (le_refl (0 : ℝ))).mp hh
    have hb : #{w ∈ {w | retains t w} | 0 < input x w / (1 / 3)} ≤ 3 := by
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
private theorem correction_pos (P : FourthRootHierarchyParams 2 1 2 2 4) :
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

-- The preparation and the final pilot are actual dependencies of the normalized row.
example : (CorrectionRowTask.preparation 2).rank 4 <
    (CorrectionRowTask.normalized 2).rank 4 ∧
    (CorrectionRowTask.pilot (.pilot (.maximum 4))).rank 4 <
      (CorrectionRowTask.normalized 2).rank 4 := by
  constructor <;> apply CorrectionRowTask.rank_lt_of_mem_children <;>
    simp [CorrectionRowTask.children]

private noncomputable def sampler (P : FourthRootHierarchyParams 2 1 2 2 4) :=
  HierarchyParams.CorrectionSampling.ofChannels P retains retains channels channels
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) C_nonneg C_row P.k_pos
    (fun _ _ => 0) (fun _ => 1) (fun _ => 1) 0
    (fun _ _ => rfl) (fun _ => zero_le_one) (fun _ => le_rfl) (le_refl _)
    (fun _ _ => rfl) (fun _ _ _ => rfl)

private theorem source_nonempty (x : ZMod 3) : ({s | retains s x} : Finset Seed).Nonempty := by
  apply dens_ne_zero.mp
  intro hz
  have hd := channels.dens_X x
  rw [hz] at hd
  norm_num at hd

-- A positive target and a zero target force the normalized affine row to be nonconstant.
-- This exercises the complete recipe, not a supplied mean certificate.
example (P : FourthRootHierarchyParams 2 1 2 2 4) :
    ∃ σ : Seed × Seed, (sampler P).value 0 (.normalized 0) σ 0 1 ≠
      (sampler P).value 0 (.normalized 0) σ 0 0 := by
  let A := sampler P
  have hinput : P.toHierarchyParams.correctionInput retains retains (1 / 3) C 0 = C := by
    simp [HierarchyParams.correctionInput, HierarchyParams.correctionIter, cutoffCorrectionIter]
  have hzero (σ : Seed × Seed) : A.value 0 (.normalized 0) σ 0 0 = 0 := by
    simp only [HierarchyParams.CorrectionSampling.value,
      HierarchyParams.CorrectionSampling.normalizedRecipe,
    CorrectionRowRecipe.normalized, hinput, C]
    norm_num [HierarchyParams.atomCutoff_eq_zero _ (le_refl (0 : ℝ))]
  have hmean := A.expect_normalizedRecipe (by norm_num) C_nonneg C_row C_le
    (Nat.zero_le _) (source_nonempty 0) 1
  have hpos := correction_pos P
  by_contra hn
  have heq : ∀ σ : Seed × Seed, A.value 0 (.normalized 0) σ 0 1 = 0 := by
    intro σ
    have he : A.value 0 (.normalized 0) σ 0 1 = A.value 0 (.normalized 0) σ 0 0 := by
      by_contra hne
      exact hn ⟨σ, hne⟩
    rw [he, hzero]
  change (𝔼 σ ∈ ({s | retains s 0} : Finset Seed) ×ˢ (univ : Finset Seed),
    ((1 / 3) / A.π) * A.value 0 (.normalized 0) σ 0 1) = _ at hmean
  simp only [heq, mul_zero, expect_const_zero] at hmean
  linarith

-- Replacing the preparatory child changes normalization before the outer sample mean.
example (P : FourthRootHierarchyParams 2 1 2 2 4) (σ : Seed × Seed) (x y : ZMod 3) :
    (sampler P).normalizedRecipe C (fun _ _ _ => 0) (fun _ => 0) σ x y =
      2 * (sampler P).normalizedRecipe C (fun _ _ _ => 1) (fun _ => 0) σ x y := by
  have hS := (source_nonempty x).product ((sampler P).usage_nonempty y)
  simp only [HierarchyParams.CorrectionSampling.normalizedRecipe,
    CorrectionRowRecipe.normalized,
    CorrectionRowRecipe.normalizer, expect_const hS]
  norm_num
  split_ifs <;> ring

-- The preparation child receives the same inherited channel functions (including fixed suffixes).
-- Different source and terminal suffixes select different draws; neither may be silently reset.
example :
    CorrectionRowRecipe.normalizer
      ((fun (suffix : Bool) (s x : Bool) => s = (x != suffix)) true)
      ((fun (suffix : Bool) (t y : Bool) => t = (y != suffix)) false)
      (fun (σ : Bool × Bool) (x y : Bool) => if σ = (false, true) ∧ x = true ∧ y = true
        then (7 : ℝ) else 0) true true = 7 := by
  norm_num [CorrectionRowRecipe.normalizer,
    Finset.expect_eq_sum_div_card, Fintype.sum_bool, Finset.filter_insert,
    Finset.filter_empty, Finset.filter_singleton]

-- Oversized and negative entries coexist in a nonconstant estimated row. The gate still
-- reads this whole raw table, while only Q's scalar argument is clipped. Changing the
-- preparatory estimate changes the denominator; it does not alter the cap or the usage mask.
private theorem oversized_estimates (P : FourthRootHierarchyParams 2 1 2 2 4) :
    let B := P.toHierarchyParams.atomCap
    let raw : Matrix (ZMod 3) (ZMod 3) ℝ :=
      fun x y => if x = 0 ∧ y = 1 then (B + 2) / 3 else -1
    let A := sampler P
    A.normalizedRecipe raw (fun _ _ _ => -7) (fun _ => 0) (0, 0) 0 1 = 2 * P.Q B ∧
      A.normalizedRecipe raw (fun _ _ _ => -7) (fun _ => 0) (0, 0) 0 0 = 0 ∧
      0 < A.normalizedRecipe raw (fun _ _ _ => -7) (fun _ => 0) (0, 0) 0 1 := by
  intro B raw A
  have hB : 0 < B := by
    have h := P.toHierarchyParams.atomCap_gt
    have hm := le_max_left ((P.k : ℝ) + 1) P.θ₂
    have hk : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
    dsimp [B]
    linarith
  have hcut : P.toHierarchyParams.atomCutoff ((B + 2) / 3 / (1 / 3)) = P.Q B := by
    have harg : (B + 2) / 3 / (1 / 3 : ℝ) = B + 2 := by ring
    rw [harg, HierarchyParams.atomCutoff, max_eq_right (by linarith : 0 ≤ B + 2),
      min_eq_left (by dsimp [B]; linarith : P.toHierarchyParams.atomCap ≤ B + 2)]
  have hpos : 0 < P.Q B := by
    have h := P.toHierarchyParams.atomCap_gt
    have hm := le_max_right ((P.k : ℝ) + 1) P.θ₂
    have hq := P.le_Q B
    dsimp [B] at hq ⊢
    linarith
  have hS := (source_nonempty (0 : ZMod 3)).product (A.usage_nonempty 1)
  have hret : retains (0 : Seed) (1 : ZMod 3) := by
    norm_num [retains, affineRetains, mem_retentionBox, affineHash]
  have hval : A.normalizedRecipe raw (fun _ _ _ => -7) (fun _ => 0)
      (0, 0) 0 1 = 2 * P.Q B := by
    simp only [HierarchyParams.CorrectionSampling.normalizedRecipe,
    CorrectionRowRecipe.normalized, hret, ↓reduceIte]
    have hr := gate_eq_one P (0 : Seed) 0 raw
    change rowGate A.ρ A.K (1 / 3) raw {w | retains (0 : Seed) w} 0 = 1 at hr
    rw [hr]
    simp only [CorrectionRowRecipe.normalizer, expect_const hS]
    change P.toHierarchyParams.atomCutoff (raw 0 1 / (1 / 3)) *
      (1 * 1) / max (1 / 2) (min 1 (-7)) * P.γ 0 = _
    have hraw : raw 0 1 = (B + 2) / 3 := by norm_num [raw]
    rw [hraw, hcut, P.γ_one 0 (by norm_num)]
    ring_nf
    norm_num
  refine ⟨hval, ?_, by rw [hval]; positivity⟩
  apply A.normalizedRecipe_eq_zero_of_nonpos
  norm_num [raw]

-- The bounded recursive-task constructor retains its exact affine true mean.
example (P : FourthRootHierarchyParams 2 1 2 2 4) (x y : ZMod 3) :
    (𝔼 σ ∈ ({s | retains s x} : Finset Seed) ×ˢ (univ : Finset Seed),
      ((1 / 3) / (sampler P).π) * (sampler P).value 0 (.normalized 0) σ x y) =
      P.toHierarchyParams.correctionIter retains retains (1 / 3) C 1 x y :=
  (sampler P).expect_normalizedRecipe (by norm_num) C_nonneg C_row C_le
    (Nat.zero_le _) (source_nonempty x) y

private noncomputable def pilotSampler (P : FourthRootHierarchyParams 2 1 2 2 4) :=
  HierarchyParams.PilotSampling.ofChannels P retains retains channels channels
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) C_nonneg C_row P.k_pos
    (fun _ _ => 0) (fun _ => 1) (fun _ => 1) 0
    (fun _ _ => rfl) (fun _ => zero_le_one) (fun _ => le_rfl) (le_refl _)
    (fun _ _ => rfl) (fun _ _ _ => rfl)

-- The two real clients share the identical arbitrary-child assembly, even though their true
-- maxima differ. There is no second normalization theory hidden behind the pilot interface.
example (P : FourthRootHierarchyParams 2 1 2 2 4)
    (raw : Matrix (ZMod 3) (ZMod 3) ℝ) (prep : Seed × Seed → Matrix (ZMod 3) (ZMod 3) ℝ)
    (maximum : ZMod 3 → ℝ) :
    (pilotSampler P).normalizedRecipe raw prep maximum =
      (sampler P).normalizedRecipe raw prep maximum := rfl

-- Primitive affine laws supply the current-pilot mean; no desired mean is passed to the builder.
example (P : FourthRootHierarchyParams 2 1 2 2 4) (x y : ZMod 3) :
    (𝔼 σ ∈ ({s | retains s x} : Finset Seed) ×ˢ ({t | retains t y} : Finset Seed),
      (1 / 3) * (pilotSampler P).value (.normalized 0) σ x y) =
        PilotTask.value P.toHierarchyParams retains retains (1 / 3) C (.correction 1) x y :=
  (pilotSampler P).expect_normalizedRecipe (by norm_num) C_nonneg C_row C_le
    (Nat.zero_le _) (source_nonempty x) y

private theorem pilot_correction_pos (P : FourthRootHierarchyParams 2 1 2 2 4) :
    0 < PilotTask.value P.toHierarchyParams retains retains (1 / 3) C (.correction 1) 0 1 := by
  have hJ : Fintype.card (ZMod 3) < P.J := by simpa only [ZMod.card] using detector_rank P
  have hmax := PilotTask.value_maximum_eq_zero P.toHierarchyParams retains retains
    (1 / 3) C hJ 1
  have hinput : PilotTask.value P.toHierarchyParams retains retains (1 / 3) C (.input 0) =
      C := by simp [PilotTask.value, pilotInput, pilotCorrection_zero]
  rw [PilotTask.value_correction_succ, hmax, hinput]
  have hγ := P.γ_one 0 (by norm_num)
  have hQ : 0 < P.Q (1 / 2) := by
    have hbound := P.le_Q (1 / 2)
    have hθ := P.θ₂_lt
    norm_num at hθ
    linarith
  norm_num [C, hγ]
  positivity

-- An actual pilot row is nonconstant on the affine seed space and has positive true target.
example (P : FourthRootHierarchyParams 2 1 2 2 4) :
    ∃ σ : Seed × Seed, (pilotSampler P).value (.normalized 0) σ 0 1 ≠
      (pilotSampler P).value (.normalized 0) σ 0 0 := by
  let A := pilotSampler P
  have hinput : PilotTask.value P.toHierarchyParams retains retains (1 / 3) C (.input 0) =
      C := by simp [PilotTask.value, pilotInput, pilotCorrection_zero]
  have hzero (σ : Seed × Seed) : A.value (.normalized 0) σ 0 0 = 0 := by
    change A.normalizedRecipe _ _ _ σ 0 0 = 0
    apply A.normalizedRecipe_eq_zero_of_nonpos
    rw [hinput]
    norm_num [C]
  have hm := A.value_correction_mean (by norm_num) C_nonneg C_row C_le
    (Nat.zero_le _) (source_nonempty 0) 1
  have hp := pilot_correction_pos P
  by_contra hn
  have heq (σ : Seed × Seed) : A.value (.normalized 0) σ 0 1 = 0 := by
    have he : A.value (.normalized 0) σ 0 1 = A.value (.normalized 0) σ 0 0 := by
      by_contra hne
      exact hn ⟨σ, hne⟩
    rw [he, hzero]
  simp only [heq, mul_zero, expect_const_zero] at hm
  change PilotTask.value P.toHierarchyParams retains retains (1 / 3) C (.correction 1) 0 1 = 0
    at hm
  linarith

-- Both signs and arbitrary magnitude are allowed in every child, including the maximum.
example (P : FourthRootHierarchyParams 2 1 2 2 4) (R S : ℝ) (σ : Seed × Seed) (x y : ZMod 3) :
    let raw : Matrix (ZMod 3) (ZMod 3) ℝ := fun x y => if x = y then R else -S
    (pilotSampler P).normalizedRecipe raw (fun _ _ _ => -R) (fun _ => S) σ x y ∈
      Set.Icc 0 (2 * P.Q P.toHierarchyParams.atomCap) :=
  (pilotSampler P).normalizedRecipe_mem_Icc _ _ _ σ x y

-- Preparation precedes normalization, which precedes the actual correction mean client.
example : (PilotRowTask.pilot (.maximum 3)).rank < (PilotRowTask.normalized 2).rank ∧
    (PilotRowTask.normalized 2).rank < (PilotRowTask.pilot (.correction 3)).rank := by
  constructor <;> apply PilotRowTask.rank_lt_of_mem_children <;> simp [PilotRowTask.children]

-- The zero-budget boundary survives the expanded actual constructor ranks.
example : precision 16 2 0 (PilotRowTask.normalized 2).rank (1 / 4) (1 / 8) ≤ 0 :=
  precision_zero_nonpos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _

-- Input is an actual whole-row call: the right base is evaluated at the midpoint, not old x.
example (P : FourthRootHierarchyParams 2 1 2 2 4) :
    (pilotSampler P).value (.pilot (.input 1)) 0 2 =
      C 0 2 + ∑ z, (pilotSampler P).value (.pilot (.correction 1)) 0 z * C z 2 := rfl

-- Distinct direct/right estimates really are accepted. At x=false the right row at z=true
-- contributes 7; retaining the old source in that right call would incorrectly contribute 0.
example : CorrectionRowRecipe.input (fun (_ _ : Bool) => (0 : ℝ))
    (fun x z => if x = false ∧ z = true then 1 else 0)
    (fun z y => if z = true ∧ y = false then 7 else 0) false false = 7 := by
  norm_num [CorrectionRowRecipe.input, Fintype.sum_bool]

-- An incoming gate recomputes ranks from the raw child, independently of the prep child.
-- Raising the raw entry closes the gate, rather than merely clipping Q's scalar argument.
example :
    CorrectionRowRecipe.normalized (fun v _ => v) (fun r => if r < 1 then 1 else 0)
      (fun _ => 1) (fun d => min 1 (max 0 d)) (fun _ => 1) 1 1 1
      (fun (_ _ : Unit) => True) (fun (_ _ : Unit) => True) (fun (_ _ : Unit) => True)
      (fun _ _ => 1 / 2) (fun _ _ _ => 1) (fun _ => 0) ((), ()) () () = 1 / 2 ∧
    CorrectionRowRecipe.normalized (fun v _ => v) (fun r => if r < 1 then 1 else 0)
      (fun _ => 1) (fun d => min 1 (max 0 d)) (fun _ => 1) 1 1 1
      (fun (_ _ : Unit) => True) (fun (_ _ : Unit) => True) (fun (_ _ : Unit) => True)
      (fun _ _ => 100) (fun _ _ _ => -7) (fun _ => 0) ((), ()) () () = 0 := by
  norm_num [CorrectionRowRecipe.normalized, CorrectionRowRecipe.normalizer, rowGate,
    incomingGate, auxScore, kthLargest, orderEmbOfFin, Finset.expect_eq_sum_div_card]

-- The expanded ranks also pay the right child's actual endpoint and source-rate change.
example (M d : ℕ) :
    binNormCost 4 1 * (2 : ℝ) ^ (Real.logb 2 ((1 / 4) / (1 / 16)) / 4) *
        (2 : ℝ) ^ (-precision 16 2 (lastBudget M d 1 1) (PilotRowTask.pilot .base).rank
          (1 / 4) (1 / 4)) ≤
      (2 : ℝ) ^ (-precision 16 2 M (PilotRowTask.pilot (.input 2)).rank
        (1 / 8) (1 / 16) - 2 + (d : ℝ) / 16 + 1 / 16) * scaleMajorant 1 := by
  have hbound := PilotRowTask.input_request_cost_le
    (r := ⟨.base, 1 / 4, 1 / 4⟩) (i := 2) (f := 1 / 4) (u := 1 / 16)
    (by simp [PilotTask.inputRequests]) (A := 2) (a := 1 / 8)
    (by norm_num) M d 1 (by norm_num) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa only [Nat.cast_one, Int.cast_one, mul_one] using hbound

-- The pilot client reaches the same sharp upper bound with a negative preparatory estimate,
-- while its negative raw entry vanishes. This uses the genuine arbitrary-child recipe.
example (P : FourthRootHierarchyParams 2 1 2 2 4) :
    let B := P.toHierarchyParams.atomCap
    let raw : Matrix (ZMod 3) (ZMod 3) ℝ :=
      fun x y => if x = 0 ∧ y = 1 then (B + 2) / 3 else -1
    let A := pilotSampler P
    A.normalizedRecipe raw (fun _ _ _ => -7) (fun _ => 0) (0, 0) 0 1 = 2 * P.Q B ∧
      A.normalizedRecipe raw (fun _ _ _ => -7) (fun _ => 0) (0, 0) 0 0 = 0 ∧
      0 < A.normalizedRecipe raw (fun _ _ _ => -7) (fun _ => 0) (0, 0) 0 1 :=
  oversized_estimates P

-- Estimated vector assembly clips at both ends; it is not just a deterministic-value index.
example : PilotRowRecipe.maximum (fun (_ : Bool) => -100) (fun _ => -7) true = 0 ∧
    PilotRowRecipe.maximum (fun (_ : Bool) => -100) (fun _ => 100) false = 1 := by
  norm_num [PilotRowRecipe.maximum]

-- Exact pilot bases are available even with no statistical budget.
example (P : FourthRootHierarchyParams 2 1 2 2 4) :
    (pilotSampler P).value (.pilot (.correction 0)) = 0 ∧
      (pilotSampler P).value (.pilot (.maximum 0)) = 0 := by
  constructor
  · exact pilotCorrection_zero
  · exact pilotMax_zero

-- The pilot normalization edge survives embedding in the actual family. This was absent
-- from the old deterministic-only pilot embedding.
example : (CorrectionRowTask.pilot (.normalized 2)).rank 4 <
    (CorrectionRowTask.pilot (.pilot (.correction 3))).rank 4 :=
  CorrectionRowTask.rank_lt_of_mem_children (by
    simp [CorrectionRowTask.children, PilotRowTask.children])

-- Identical primitive recipe choices interpret the embedded stochastic pilot exactly as
-- its standalone family; each family's mean proof still uses its own input-specific laws.
example (P : FourthRootHierarchyParams 2 1 2 2 4) :
    (sampler P).value 0 (.pilot (.normalized 0)) =
      (pilotSampler P).value (.normalized 0) :=
  (sampler P).value_pilot 0 (pilotSampler P) rfl rfl (.normalized 0)

-- Finite iteration bounds include preparation and normalization, not only the old tasks.
example : (PilotRowTask.normalized 4).rank ≤ 15 * 4 + 20 :=
  PilotRowTask.rank_le (by decide)

-- The copy/reward client's real requests keep inherited suffixes and reset the right
-- reward call to the midpoint role/rate/suffix. No endpoint value is a task parameter.
private noncomputable def inherited : CorrectionRowTask.Channel Bool (List ℕ) :=
  ⟨false, 1 / 16, [7, 9]⟩
private noncomputable def broad : CorrectionRowTask.Channel Bool (List ℕ) := ⟨false, 1 / 4, [7, 9]⟩
private noncomputable def midpoint : CorrectionRowTask.Channel Bool (List ℕ) :=
  ⟨true, 1 / 4, [3, 9]⟩

example : (CorrectionRowTask.rewardRequests inherited broad midpoint 2)[3]?.map
    (fun r => (r.source.role, r.source.rate, r.source.suffix)) =
      some (true, (1 / 4 : ℝ), [3, 9]) := by rfl

example (M d : ℕ) :
    binNormCost 4 0 * (2 : ℝ) ^ (Real.logb 2 ((1 / 4) / (1 / 16)) / 4) *
        (2 : ℝ) ^ (-precision 16 2 (lastBudget M d 1 0)
          (CorrectionRowTask.previousReward.rank 4) (1 / 4) (1 / 4)) ≤
      (2 : ℝ) ^ (-precision 16 2 M (CorrectionRowTask.projectedReward 3 |>.rank 4)
        (1 / 4) (1 / 16) - 2 + (d : ℝ) / 16 + 1 / 16) * scaleMajorant 0 := by
  have h := CorrectionRowTask.reward_request_cost_le (k := 4)
    (r := ⟨.previousReward, midpoint, none, none⟩)
    (source := inherited) (broadSource := broad) (midpoint := midpoint) (i := 2) (f := 1 / 4)
    (by simp [CorrectionRowTask.rewardRequests]) (by rfl) (by rfl)
    (A := 2) (by norm_num) M d 1 (by decide)
    (by norm_num) (by norm_num [inherited]) (by norm_num [inherited])
  simpa only [midpoint, inherited, Nat.cast_one, mul_one] using h

end ComplexityTests.PilotTasks
