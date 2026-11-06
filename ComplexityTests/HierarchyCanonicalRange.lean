/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of canonical input range)
import Complexity.Foundations.Probability.HierarchyCanonicalRange
import all ComplexityTests.HierarchyWeightedPreparation
import all Complexity.Foundations.Probability.DetectedHierarchy

/-!
Aligned canonical targets reuse the weighted PREP fixture. The counterexample uses
literal later input/pilotInput tasks, valid horizon, distinct roles and inherited
suffixes, nonnegative substochastic base, and positive request precision. It refutes
uniform reference range over these admissible requests, not estimator accuracy or
recursive successful availability. A genuine hierarchy must align its stage entry
cap with the rate before using the structural range theorem.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
namespace CanonicalRangeRegression

private lemma later_iteration (HP : FourthRootHierarchyParams 16 1 16 32 8) : 1 < HP.k := by
  have hθ : HP.θ < 1 / 512 := by linarith [HP.θ_lt_θ₂, HP.θ₂_lt]
  have hq0 : HP.Q 0 = 0 := le_antisymm
    ((HP.Q_le 0).trans_eq (max_eq_right (by linarith [HP.θ_pos]))) (HP.Q_nonneg 0)
  have hl := HP.Q_lipschitz 0 1 (by norm_num)
  rw [hq0] at hl
  have hL : 1 / 2 < HP.L := by linarith [HP.le_Q 1, HP.θ₂_lt]
  have hr : 1 < HP.L / HP.θ := (lt_div_iff₀ HP.θ_pos).mpr (by linarith)
  have he : 1 ≤ Real.exp (1 / HP.θ) := Real.one_le_exp (le_of_lt (one_div_pos.mpr HP.θ_pos))
  by_contra hn
  have hk : HP.k = 1 := by have := HP.k_pos; omega
  have ht := HP.tail_small
  simp only [hk, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at ht
  have hm := mul_le_mul_of_nonneg_right he (le_of_lt (lt_trans zero_lt_one hr))
  norm_num only [one_div] at hm
  norm_num at ht
  nlinarith

variable {P : ℕ} [Fact P.Prime]

private def data (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) : BudgetData HP P :=
  { DecoderRateObstruction.data HP ka with base := single 0 1 1 }

private def request (HP : FourthRootHierarchyParams 16 1 16 32 8) (pilot : Bool) (ka : ℕ) :
    HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
  { DecoderRateObstruction.request HP ka with
    task := .row 0 (if pilot then .pilotInput ⟨1, later_iteration HP⟩
      else .input ⟨1, later_iteration HP⟩) }

private lemma nonneg (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) :
    ∀ x y, 0 ≤ (data (P := P) HP ka).base x y :=
  (DecoderRateObstruction.entry_substochastic 0 1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl).1

private lemma substochastic (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) :
    (data (P := P) HP ka).base *ᵥ 1 ≤ 1 := by
  intro x
  change ∑ y, single (0 : ZMod P) 1 (1 : ℝ) x y * 1 ≤ 1
  simpa only [mul_one] using
    (DecoderRateObstruction.entry_substochastic (0 : ZMod P) 1
      (by norm_num : (0 : ℝ) ≤ 1) le_rfl).2 x

-- The counterexample base is the relabelled stage zero of the existing radix
-- hierarchy, with a strictly upper triangular seed. Later-stage channel coverage
-- is not claimed by this identity.
private lemma genuine_stage_zero (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) :
    ∃ S : Matrix (Fin P) (Fin P) ℝ, S.IsStrictUpperTriangular ∧
      (data (P := P) HP ka).base =
        (hierarchy HP.toHierarchyParams (radixCopyEquiv P HP.m)
          (fun l (σ : FrameChannel P 4 1) (v : Fin (P * (HP.m + 1) ^ l)) =>
            canonicalChannel (fun w => (w.val : ZMod P)) (rate l) σ v)
          (fun l (σ : FrameChannel P 4 1) (v : Fin (P * (HP.m + 1) ^ l)) =>
            canonicalChannel (fun w => (w.val : ZMod P)) (rate l) σ v)
          (S.submatrix (finCongr (by simp)) (finCongr (by simp))) 0).submatrix
              (fun v => finCongr (by simp) ((ZMod.finEquiv P).symm v))
              (fun v => finCongr (by simp) ((ZMod.finEquiv P).symm v)) := by
  have hP : 1 < P := (Fact.out : P.Prime).one_lt
  let a : Fin P := ⟨0, by omega⟩
  let b : Fin P := ⟨1, hP⟩
  refine ⟨single a b 1, ?_, ?_⟩
  · intro x y hyx
    simp only [single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      have hab : a < b := by change (0 : ℕ) < 1; decide
      exact False.elim (hyx hab)
    · rfl
  · rw [hierarchy]
    simp only [submatrix_submatrix, Function.comp_def, finCongr_apply, Fin.cast_cast,
      Fin.cast_refl]
    change single (0 : ZMod P) 1 (1 : ℝ) =
      (single a b 1).submatrix (ZMod.finEquiv P).symm (ZMod.finEquiv P).symm
    have ha : (ZMod.finEquiv P) a = 0 := by
      change (ZMod.finEquiv P) 0 = 0
      exact map_zero _
    have hb : (ZMod.finEquiv P) b = 1 := by
      have hb' : b = (1 : Fin P) := by
        apply Fin.ext
        simp [b, Nat.mod_eq_of_lt hP]
      rw [hb']
      exact map_one _
    convert (submatrix_single_equiv (ZMod.finEquiv P).toEquiv.symm
      (ZMod.finEquiv P).toEquiv.symm a b (1 : ℝ)).symm using 1 <;>
      first | rfl | (congr 1 <;> first | exact ha.symm | exact hb.symm)

private lemma admissible (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (pilot : Bool) (ka : ℕ) : Admissible (request (P := P) HP pilot ka) := by
  exact ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩

private lemma precision_positive (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (pilot : Bool) (ka : ℕ) :
    0 < (data (P := P) HP ka).requestPrecision (64 * (ka + 1)) (request HP pilot ka) := by
  rw [BudgetData.requestPrecision_grid _ _ 0 ka _ rfl rfl]
  norm_num [data, DecoderRateObstruction.data]
  linarith

-- No HP-only d bounds the later actual or pilot target over all admissible
-- terminal rates. The field is chosen AFTER d and ka, so the horizon remains valid.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (d : ℝ) :
    ∃ ka P : ℕ, 0 < ka ∧ P.Prime ∧ 2 ^ ka ≤ P ∧
    ∀ (_hP : Fact P.Prime),
      let B := data (P := P) HP ka
      ∃ H : Horizon P, H.maxExponent = ka ∧
      (∀ x y, 0 ≤ B.base x y) ∧ B.base *ᵥ 1 ≤ 1 ∧
      (∀ pilot : Bool,
        let r := request (P := P) HP pilot ka
        Admissible r ∧ r.source.rate ≠ r.terminal.rate ∧
        0 < B.requestPrecision (64 * (ka + 1)) r ∧
        d * r.terminal.rate < B.canonicalPreparationInput pilot ⟨1, later_iteration HP⟩ r 0 1) := by
  obtain ⟨ka, hk⟩ := pow_unbounded_of_one_lt (max d 1) (by norm_num : (1 : ℝ) < 16)
  have hka : 0 < ka := by
    by_contra hn
    have hz : ka = 0 := by omega
    simp only [hz, pow_zero] at hk
    exact not_lt_of_ge (le_max_right _ _) hk
  have hsmall : d * rate ka < 1 := by
    rw [rate_eq_source_grid, inv_pow, mul_inv_lt_iff₀ (by positivity : (0 : ℝ) < 16 ^ ka)]
    simpa only [one_mul] using (lt_of_le_of_lt (le_max_left d 1) hk)
  obtain ⟨P, hp, hprime⟩ := Nat.exists_infinite_primes (2 ^ ka + 1)
  have hPbound : 2 ^ ka ≤ P := by omega
  refine ⟨ka, P, hka, hprime, hPbound, ?_⟩
  intro instP
  dsimp only
  refine ⟨⟨ka, P - 1, hPbound, by have := hprime.pos; omega⟩, rfl,
    nonneg HP ka, substochastic HP ka, ?_⟩
  intro pilot
  refine ⟨admissible HP pilot ka, ?_, precision_positive HP pilot ka, ?_⟩
  · change rate 0 ≠ rate ka
    have hh : rate ka < 1 := by
      rw [rate_eq_source_grid]
      exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    simpa only [show rate 0 = 1 by norm_num [rate]] using ne_of_gt hh
  · have hb := (data (P := P) HP ka).base_le_canonicalPreparationInput
      pilot ⟨1, later_iteration HP⟩ (request HP pilot ka) (rate_pos ka) (nonneg HP ka) 0 1
    have he : (data (P := P) HP ka).base 0 1 = 1 := by simp [data]
    rw [he] at hb
    exact hsmall.trans_le hb


-- The aligned initial target attains the range boundary and has a zero entry.
-- This retains the unequal-rate request and the actual canonical constructor.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) (pilot : Bool) :
    let B := DecoderRateObstruction.data (P := P) HP ka
    let r := DecoderRateObstruction.request (P := P) HP ka
    B.canonicalPreparationInput pilot ⟨0, HP.k_pos⟩ r 0 0 = rate ka ∧
      B.canonicalPreparationInput pilot ⟨0, HP.k_pos⟩ r 1 1 = 0 := by
  dsimp only
  rw [DecoderRateObstruction.canonical_input]
  simp

-- The misaligned later targets still have a finite ordinary range. It is the
-- conversion to a uniform multiple of f, rather than boundedness, that fails.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) (pilot : Bool)
    (x y : ZMod P) :
    (data HP ka).canonicalPreparationInput pilot ⟨1, later_iteration HP⟩
      (request HP pilot ka) x y ∈ Set.Icc 0 ((HP.k : ℝ) + 1) := by
  have hc : ∀ x y, (data (P := P) HP ka).base x y ≤ 1 := by
    intro x y
    simp only [data, single_apply]
    split_ifs <;> norm_num
  simpa only [mul_one] using
    (data (P := P) HP ka).canonicalPreparationInput_range_of_base_cap pilot
      ⟨1, later_iteration HP⟩ (request HP pilot ka) (rate_pos ka) (nonneg HP ka)
      (substochastic HP ka) zero_le_one hc x y

section AlignedConsumer
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
open InitialPilotScoreRegression IncomingPreparationBiasRegression WeightedPreparationRegression
-- Range is now derived from the actual base and hierarchy sequence; relative
-- accuracy is still NEW information, supplied by the checked own-child fixture.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧
    let B := halfData HP
    let r := PreparationExecutionRegression.prepRequest HP
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    let output := fun prep => correctionRequest B.padding id r
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
      HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ halfTable prep (fun _ _ => 0)
    let V := B.incomingPreparation r (fun _ => base)
    rowNormPow 4 5 r.source.rate X U (fun σ x y =>
      correctionNumerator HP B.padding id r halfTable (fun _ _ => 0) σ x y ^ (4⁻¹ : ℝ) *
        (FourthRootHierarchyParams.NormalizedRow.clip (rowSliceMean X U completedTable x y) -
          FourthRootHierarchyParams.NormalizedRow.clip (rowSliceMean X U V x y))) ≤
      HP.Q HP.toHierarchyParams.atomCap * (L * (1 + ((HP.k : ℝ) + 1))) ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision 33 (budgetRequest HP))) ^ 4 ∧
    rootDistPow 4 5 r.source.rate X U (output completedTable) (output V) ≤
      HP.Q HP.toHierarchyParams.atomCap / 8 * (L * (1 + ((HP.k : ℝ) + 1))) ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision 33 (budgetRequest HP))) ^ 4 := by
  obtain ⟨L, hL, h⟩ := BudgetData.evaluate_preparation_relative_root (HP := HP)
  refine ⟨L, hL, ?_⟩
  have ht : (PreparationExecutionRegression.prepRequest HP).terminal.rate = 1 := by
    norm_num [PreparationExecutionRegression.prepRequest, budgetRequest,
      InitialPilotScoreRegression.request,
      gridChannel, rate]
  have hg := (halfData HP).canonicalPreparationInput_range true ⟨0, HP.k_pos⟩
    (PreparationExecutionRegression.prepRequest HP) (by rw [ht]; exact zero_lt_one)
    (fun x y => by
      by_cases hxy : x = y <;> norm_num [halfData, budgetData, base, Matrix.one_apply, hxy])
    (by change (1 : Matrix (ZMod 5) (ZMod 5) ℝ) *ᵥ 1 ≤ 1; simp)
    (fun x y => by rw [ht]; by_cases hxy : x = y <;>
      norm_num [halfData, budgetData, base, Matrix.one_apply, hxy])
  have hp : 0 < (halfData HP).requestPrecision 33 (budgetRequest HP) := by
    rw [precision]; norm_num
  have hr := h 5 (halfData HP) 34 true ⟨0, HP.k_pos⟩
    (PreparationExecutionRegression.prepRequest HP) rfl
    (InitialPilotScoreRegression.admissible HP) (prep_active HP)
    ((halfData HP).childBudget_lt (by decide)) rfl (rate_pos 1).le (rate_pos 0)
    halfTable completedTable hp (half_evaluated HP) (prep_evaluated HP)
    ((HP.k : ℝ) + 1)
    ((2 : ℝ) ^ (-(halfData HP).requestPrecision 33 (budgetRequest HP))) (by positivity)
  rw [ht] at hr
  have hr' := hr (fun x y => by simpa only [ht] using hg x y)
  simp only [canonical_zero] at hr'
  simpa only [Nat.cast_ofNat] using
    (hr' (relative_accuracy HP) 0 2 (by decide) 1 0 [1] [2, 3] rfl rfl
      halfTable (fun _ _ => 0))

end AlignedConsumer

end CanonicalRangeRegression
