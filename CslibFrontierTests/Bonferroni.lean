/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests for Probability.Bonferroni)

public import CslibFrontier.Foundations.Probability.Bonferroni
public import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Tactic

/-!
# Worked instances for `ProbabilityTheory` Bonferroni and Brun-sieve lemmas

These kernel-checked theorems verify `CslibFrontier.Foundations.Probability.Bonferroni`:
* finite inclusion-exclusion upper and lower bounds (`measureReal_natCard_eq_le_bonferroni`,
  `bonferroni_le_measureReal_natCard_eq`, `measureReal_forall_notMem_le_bonferroni`,
  `bonferroni_le_measureReal_forall_notMem`) on `Fin 3 → Bool` under the uniform probability
  measure (where depth `2` strictly brackets `1 / 8` between `-1 / 2` and `1 / 4` for `k = 0`, and
  depth `3` is exact `3 / 8` for `k = 1`),
* measurability (`measurableSet_natCard_eq`), and
* Brun's sieve (`tendsto_measureReal_natCard_eq_poisson_of_factorialMoments`) on a shrinking
  single-coin sequence.
-/

public section

namespace CslibFrontierTests.Bonferroni

open MeasureTheory ProbabilityTheory Finset Filter
open scoped Topology ENNReal

/-- Uniform probability measure on three independent Boolean coins. -/
noncomputable def coinMeasure : Measure (Fin 3 → Bool) :=
  (1 / 8 : ℝ≥0∞) • Measure.count

/-- The event that the `i`-th coin lands `true`. -/
def coinEvent (i : Fin 3) : Set (Fin 3 → Bool) := {f | f i = true}

private theorem isFiniteMeasure_coinMeasure : IsFiniteMeasure coinMeasure :=
  ⟨by
    rw [coinMeasure, Measure.smul_apply, smul_eq_mul, Measure.count_univ, ENat.card_eq_coe_natCard,
      Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    exact ENNReal.mul_lt_top (by simp) (by simp)⟩

private theorem coinMeasure_real_coe (s : Finset (Fin 3 → Bool)) :
    coinMeasure.real (s : Set (Fin 3 → Bool)) = (s.card : ℝ) / 8 := by
  rw [measureReal_def, coinMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.count_apply_finset' (Finset.measurableSet s), ENNReal.toReal_mul,
    ENNReal.toReal_natCast, one_div, ENNReal.toReal_inv]
  norm_num
  ring

private theorem measurable_coinEvent (i : Fin 3) : MeasurableSet (coinEvent i) :=
  MeasurableSet.of_discrete

private theorem coinMeasure_iInter (s : Finset (Fin 3)) :
    coinMeasure.real (⋂ i ∈ s, coinEvent i) = ((2 : ℝ) ^ (3 - #s)) / 8 := by
  classical
  have hdec : ∀ f : Fin 3 → Bool, f ∈ (⋂ i ∈ s, coinEvent i) ↔ ∀ i ∈ s, f i = true :=
    fun f => by simp [coinEvent]
  let A : Finset (Fin 3 → Bool) := Finset.univ.filter fun f => f ∈ ⋂ i ∈ s, coinEvent i
  have hcoe : (A : Set (Fin 3 → Bool)) = ⋂ i ∈ s, coinEvent i := by
    ext f
    simp [A]
  have hcard : A.card = 2 ^ (3 - #s) := by
    have hbij : A =
        (Finset.univ : Finset ({i : Fin 3 // i ∉ s} → Bool)).image
          (fun g i => if hi : i ∈ s then true else g ⟨i, hi⟩) := by
      ext f
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, hdec, Finset.mem_image]
      constructor
      · intro hf
        refine ⟨fun ⟨i, _⟩ => f i, ?_⟩
        ext i
        by_cases hi : i ∈ s
        · simp [hi, hf i hi]
        · simp [hi]
      · rintro ⟨g, rfl⟩ i hi
        simp [hi]
    have hinj : Function.Injective
        (fun (g : {i : Fin 3 // i ∉ s} → Bool) i => if hi : i ∈ s then true else g ⟨i, hi⟩) := by
      intro g₁ g₂ h
      ext ⟨i, hi⟩
      have hi_eq := congrFun h i
      simpa [hi] using hi_eq
    rw [hbij, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_coe,
      Fintype.card_fin]
  rw [← hcoe, coinMeasure_real_coe, hcard]
  norm_num

private theorem sum_powersetCard_coinEvent (r : ℕ) :
    ∑ s ∈ (Finset.univ : Finset (Fin 3)).powersetCard r,
        coinMeasure.real (⋂ i ∈ s, coinEvent i) =
      ((Nat.choose 3 r : ℝ) * (2 : ℝ) ^ (3 - r)) / 8 := by
  simp_rw [coinMeasure_iInter]
  rw [Finset.sum_congr rfl fun s hs => by rw [(Finset.mem_powersetCard.mp hs).2],
    Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_div_assoc]

/-- Exact-count event `{f | #{i | f i = true} = 1}` is measurable. -/
theorem measurableSet_coin_count_eq_one :
    MeasurableSet {f : Fin 3 → Bool | Nat.card {i : Fin 3 // f i = true} = 1} :=
  measurableSet_natCard_eq measurable_coinEvent 1

/-- Depth-2 Bonferroni lower and upper bounds bracket `P(all three coins false) = 1/8` strictly
between `-1/2` and `1/4`. -/
theorem coinMeasure_all_false_bonferroni_bounds :
    -(1 / 2 : ℝ) ≤ coinMeasure.real {f : Fin 3 → Bool | ∀ i, f ∉ coinEvent i} ∧
      coinMeasure.real {f : Fin 3 → Bool | ∀ i, f ∉ coinEvent i} ≤ 1 / 4 := by
  let _ := isFiniteMeasure_coinMeasure
  have hlo := bonferroni_le_measureReal_forall_notMem coinMeasure measurable_coinEvent 1
  have hhi := measureReal_forall_notMem_le_bonferroni coinMeasure measurable_coinEvent 1
  simp_rw [sum_powersetCard_coinEvent] at hlo hhi
  rw [show 2 * 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one] at hlo
  rw [show 2 * 1 + 1 = 3 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one] at hhi
  norm_num at hlo hhi
  exact ⟨hlo, hhi⟩

/-- Depth-2 lower and depth-3 upper Bonferroni bounds give `0 ≤ P(exactly 1 true) ≤ 3/8`. -/
theorem coinMeasure_count_one_bonferroni_bounds :
    (0 : ℝ) ≤ coinMeasure.real {f : Fin 3 → Bool | Nat.card {i : Fin 3 // f i = true} = 1} ∧
      coinMeasure.real {f : Fin 3 → Bool | Nat.card {i : Fin 3 // f i = true} = 1} ≤ 3 / 8 := by
  let _ := isFiniteMeasure_coinMeasure
  have hlo := bonferroni_le_measureReal_natCard_eq coinMeasure measurable_coinEvent 1 1
  have hhi := measureReal_natCard_eq_le_bonferroni coinMeasure measurable_coinEvent 1 1
  simp_rw [sum_powersetCard_coinEvent] at hlo hhi
  rw [show 2 * 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one] at hlo
  rw [show 2 * 1 + 1 = 3 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one] at hhi
  norm_num at hlo hhi
  exact ⟨hlo, hhi⟩

/-- Shrinking Bernoulli measure on `Bool` with `P(true) = 1 / (n + 2)`. -/
noncomputable def shrinkingCoinMeasure (n : ℕ) : Measure Bool :=
  (ENNReal.ofReal (1 / ((n : ℝ) + 2))) • Measure.dirac true +
    (ENNReal.ofReal (1 - 1 / ((n : ℝ) + 2))) • Measure.dirac false

/-- Brun's sieve converges to `exp 0 * 1 = 1` for `k = 0` on `shrinkingCoinMeasure`. -/
theorem tendsto_shrinkingCoinMeasure_zero :
    Tendsto (fun n : ℕ =>
        (shrinkingCoinMeasure n).real {b : Bool | Nat.card { _i : Fin 1 // b = true } = 0})
      atTop (𝓝 1) := by
  have hfin : ∀ n, IsFiniteMeasure (shrinkingCoinMeasure n) := fun n => by
    refine ⟨by simp [shrinkingCoinMeasure]⟩
  have huniv : ∀ n : ℕ, (shrinkingCoinMeasure n).real Set.univ = 1 := fun n => by
    have hp0 : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
    have hp1 : 1 / ((n : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    rw [shrinkingCoinMeasure, measureReal_def, Measure.add_apply, Measure.smul_apply,
      Measure.smul_apply, smul_eq_mul, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _),
      Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one, mul_one,
      ← ENNReal.ofReal_add hp0 (by linarith)]
    ring_nf
    simp
  have h := tendsto_measureReal_natCard_eq_poisson_of_factorialMoments
    (Ω := fun _ => Bool) (ι := fun _ => Fin 1) shrinkingCoinMeasure
    (fun _ _ => ({true} : Set Bool)) (fun _ _ => MeasurableSet.of_discrete)
    (lam := 0) (fun r => ?_) 0
  · simpa using h
  · rcases r with _ | r
    · simp only [Finset.powersetCard_zero, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one]
      have hemp : (⋂ i ∈ (∅ : Finset (Fin 1)), ({true} : Set Bool)) = Set.univ := by
        ext b
        cases b <;> simp
      simp only [hemp, huniv, tendsto_const_nhds]
    · rcases r with _ | r
      · have heq : ∀ n : ℕ,
            ∑ s ∈ (Finset.univ : Finset (Fin 1)).powersetCard 1,
              (shrinkingCoinMeasure n).real (⋂ _ ∈ s, ({true} : Set Bool)) =
            (1 : ℝ) / ((n : ℝ) + 2) := fun n => by
          rw [show (Finset.univ : Finset (Fin 1)).powersetCard 1 = {Finset.univ} from by decide,
            Finset.sum_singleton]
          have hinter : (⋂ _ ∈ (Finset.univ : Finset (Fin 1)), ({true} : Set Bool)) = {true} := by
            ext b
            simp
          rw [hinter, shrinkingCoinMeasure, measureReal_def, Measure.add_apply, Measure.smul_apply,
            Measure.smul_apply, smul_eq_mul, smul_eq_mul,
            Measure.dirac_apply' _ (MeasurableSet.of_discrete),
            Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
          simp only [Set.indicator_apply, Set.mem_singleton_iff, ↓reduceIte, Pi.one_apply,
            mul_one, Bool.false_eq_true, mul_zero, add_zero]
          exact ENNReal.toReal_ofReal (by positivity)
        simp_rw [heq, pow_succ, mul_zero, zero_div]
        have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa [one_div] using hinv
      · have hempty : (Finset.univ : Finset (Fin 1)).powersetCard (r + 1 + 1) = ∅ :=
          Finset.powersetCard_eq_empty.mpr (by rw [Finset.card_univ, Fintype.card_fin]; omega)
        rw [hempty]
        simp

end CslibFrontierTests.Bonferroni

end
