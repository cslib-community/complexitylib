/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (regression tests of canonical-support inference)
import all ComplexityTests.HierarchyCorrectionStability
import Complexity.Foundations.Probability.HierarchySignedMean
import Mathlib.Topology.Order.IntermediateValue

/-!
# A local obstruction to canonical-support inference

An admissible correction request can pass its actual normalization gates and have
arbitrarily small positive own-mask rooted error against its genuine zero-base
canonical child, yet fail canonical support containment. The raw and preparation
children are supplied here. They are not asserted recursively accurate or available.
This refutes only the inference from the output scalar moment and gates to canonical
support; it is neither an estimator counterexample nor an obstruction to every
possible relative endpoint payment. No independence is used.
-/
set_option linter.privateModule false
open CorrectionMaximumRegression
open Finset Cslib Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace CorrectionSupportObstruction

private def endpointRequest (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    HierarchyTask.Request HP.k (Fin 2) (ZMod 5) :=
  { request HP with task := HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k) }

/-- The request uses distinct actual roles and inherited suffixes. -/
theorem request_admissible (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    Admissible (endpointRequest HP) := ⟨by change (0 : Fin 2) ≠ 1; decide, rfl, rfl⟩

-- On this singleton vertex domain both actual incoming ranks are exhausted.
-- Thus the production count gives the same executed recipe as the earlier fixture.
private theorem value_production_count (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (a : ℝ) (σ : Environment 5 2) :
    correctionRequest 1 (fun _ : Unit => 0) (endpointRequest HP)
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
      HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ (fun _ _ _ => 1) (fun _ _ _ => 1)
      (fun _ _ => a) σ () () = value HP a σ := by
  have hr := request_admissible HP
  have hr0 : Admissible (request HP) := ⟨by change (0 : Fin 2) ≠ 1; decide, rfl, rfl⟩
  have hR : 0 ≤ HP.R := by have h := HP.R_var; norm_num at h; linarith
  have hc : 1 < ⌈4 * (1 + 32 * HP.R)⌉₊ := by
    have h := Nat.le_ceil (4 * (1 + 32 * HP.R))
    have hh : (1 : ℝ) < ⌈4 * (1 + 32 * HP.R)⌉₊ := by linarith
    exact_mod_cast hh
  have hs : side 5 0 = 5 := by norm_num [side]
  unfold value correctionRequest
  rw [dite_eq_left hr, dite_eq_left hr0]
  simp only [CorrectionRowRecipe.normalized, endpointRequest, coordinate, request, gridChannel,
    semanticSide_grid, hs, full_retains, ↓reduceIte]
  norm_num [incomingGate, kthLargest, Finset.univ_unique, not_le.mpr hc]
  exact Or.inl rfl

/-- The reference is the genuine canonical child of the zero substochastic base,
not a freely supplied zero table. At the final normalized correction its raw input
is zero, so the actual atom cutoff annihilates it. -/
theorem canonical_zero (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (σ : Environment 5 2) :
    canonicalRequestChild HP 1 (fun _ : Unit => 0) 0
      HP.toHierarchyParams.atomCutoff (fun _ => 1) HP.ρ HP.K
      (endpointRequest HP) σ () () = 0 := by
  have hr := request_admissible HP
  have htask : (endpointRequest HP).task = .row 0 (.normalized
      ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩) :=
    HierarchyTask.correctionAtomTask_last HP.k_pos 0
  simp only [canonicalRequestChild, htask]
  change (if hr : Admissible (endpointRequest HP) then
    sourceChild HP 1 (fun _ : Unit => 0) (endpointRequest HP) hr 0 (HP.k - 1) σ else 0) () () = 0
  rw [dite_eq_left hr]
  unfold sourceChild correctionRequest
  rw [dite_eq_left hr]
  have hz : stageRaw HP 1 (fun _ : Unit => 0) (endpointRequest HP) hr 0 (HP.k - 1) = 0 := by
    simp [stageRaw, correctionInput]
  simp only [hz, CorrectionRowRecipe.normalized]
  simp [HP.toHierarchyParams.atomCutoff_eq_zero (le_refl 0)]

/-- Arbitrarily accurate local output moments do not imply canonical support.
The actual raw/preparation gates see constant one, while the pilot multiplier is
chosen continuously. This statement deliberately makes no recursive IH claim
about those supplied raw/preparation/maximum children. -/
theorem exists_small_error_without_canonical_support
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ Set.Icc (0 : ℝ) 1,
      (∀ σ : Environment 5 2, 0 < value HP a σ) ∧
      rootDistPow 4 5 1
        (fun σ (_ : Unit) => (endpointRequest HP).source.retains (channels 1) σ 0)
        (fun σ (_ : Unit) => (endpointRequest HP).usage.retains (channels 1) σ 0)
        (fun σ _ _ => value HP a σ)
        (canonicalRequestChild HP 1 (fun _ : Unit => 0) 0
          HP.toHierarchyParams.atomCutoff (fun _ => 1) HP.ρ HP.K
          (endpointRequest HP)) ≤ ε ^ 4 := by
  let q := HP.Q 1 ^ (4⁻¹ : ℝ)
  have hQ : 0 < HP.Q 1 := by
    have h := HP.le_Q 1
    have ht := HP.θ₂_lt
    norm_num at ht
    linarith
  have hq : 0 < q := Real.rpow_pos_of_pos hQ _
  let t := min (1 / 2 : ℝ) (ε / q)
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε hq)
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  obtain ⟨K, hK⟩ := (HP.cutoff_roots HP.γ (by simp)).1
  have hends : (fun a => HP.γ a ^ (4⁻¹ : ℝ)) 1 = 0 ∧
      (fun a => HP.γ a ^ (4⁻¹ : ℝ)) 0 = 1 := by
    simp [HP.γ_zero 1 (by norm_num), HP.γ_one 0 (by norm_num)]
  obtain ⟨a, ha, hat⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    hK.continuous.continuousOn (show t ∈ Set.Icc _ _ by
      change t ∈ Set.Icc ((fun a => HP.γ a ^ (4⁻¹ : ℝ)) 1)
        ((fun a => HP.γ a ^ (4⁻¹ : ℝ)) 0)
      rw [hends.1, hends.2]; exact ⟨ht.le, ht1⟩)
  change HP.γ a ^ (4⁻¹ : ℝ) = t at hat
  have hγ : 0 < HP.γ a := by
    by_contra hn
    have hz : HP.γ a = 0 := le_antisymm (not_lt.mp hn) (HP.γ_nonneg _)
    simp only [hz, Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0)] at hat
    linarith
  refine ⟨a, ha, (fun σ => by rw [value_eq]; exact mul_pos hQ hγ), ?_⟩
  have hrt : (HP.Q 1 * HP.γ a) ^ (4⁻¹ : ℝ) = q * t := by
    rw [Real.mul_rpow hQ.le (HP.γ_nonneg _), hat]
  have hle : q * t ≤ ε := by
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hq.le).trans_eq
      (mul_div_cancel₀ ε hq.ne')
  have hpow := pow_le_pow_left₀ (mul_pos hq ht).le hle 4
  have hs : side 5 0 = 5 := by norm_num [side]
  simp only [rootDistPow, rowNormPow]
  have hcan : canonicalRequestChild HP 1 (fun _ : Unit => 0) 0
      HP.toHierarchyParams.atomCutoff (fun _ => 1) HP.ρ HP.K (endpointRequest HP) = 0 := by
    funext σ x y
    cases x; cases y
    exact canonical_zero HP σ
  rw [hcan]
  simp only [endpointRequest, request, gridChannel, CorrectionRowTask.Channel.retains,
    channels, semanticSide_grid, hs, full_retains, value_eq, Pi.zero_apply]
  norm_num [Finset.univ_unique, Matrix.zero_apply]
  rw [show (1 / 4 : ℝ) = 4⁻¹ by norm_num, hrt, abs_of_pos (mul_pos hq ht)]
  nlinarith [pow_nonneg (mul_pos hq ht).le 4]

-- Arbitrary positive requested scalar precision, with the production incoming
-- count and genuine final canonical correction. Supplied children remain explicit.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (p : ℤ) :
    ∃ a ∈ Set.Icc (0 : ℝ) 1,
      let A := correctionRequest 1 (fun _ : Unit => 0) (endpointRequest HP)
        (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
        HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ => a)
      let C := canonicalRequestChild HP 1 (fun _ : Unit => 0) 0
        HP.toHierarchyParams.atomCutoff (fun _ => 1) HP.ρ HP.K (endpointRequest HP)
      (∀ σ x y, A σ x y ∈ Set.Icc 0 (2 * HP.Q HP.toHierarchyParams.atomCap)) ∧
      (∀ σ K, K * C σ () () < A σ () ()) ∧
      rootDistPow 4 5 1
        (fun σ (_ : Unit) => (endpointRequest HP).source.retains (channels 1) σ 0)
        (fun σ (_ : Unit) => (endpointRequest HP).usage.retains (channels 1) σ 0)
        A C ≤ ((2 : ℝ) ^ (-p)) ^ 4 := by
  obtain ⟨a, ha, hpos, herr⟩ := exists_small_error_without_canonical_support HP
    ((2 : ℝ) ^ (-p)) (by positivity)
  refine ⟨a, ha, ?_, ?_, ?_⟩
  · intro σ x y
    exact correctionRequest_mem_Icc HP 1 (fun _ : Unit => 0) (endpointRequest HP)
      _ _ _ _ σ x y
  · intro σ K
    rw [canonical_zero, mul_zero, value_production_count]
    exact hpos σ
  · have he : correctionRequest 1 (fun _ : Unit => 0) (endpointRequest HP)
        (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
        HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ => a) =
        (fun σ _ _ => value HP a σ) := by
      funext σ x y
      cases x; cases y
      exact value_production_count HP a σ
    rw [he]
    exact herr

-- The zero matrix reference obeys the ordinary substochastic and entry bounds.
example : (∀ x y : Unit, 0 ≤ (0 : Matrix Unit Unit ℝ) x y) ∧
    (0 : Matrix Unit Unit ℝ) *ᵥ 1 ≤ 1 ∧
    (∀ x y : Unit, (0 : Matrix Unit Unit ℝ) x y ≤ 1) := by
  simp

end CorrectionSupportObstruction
