/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.PACLearning.MDL
import CslibFrontier.MachineLearning.PACLearning.Nonuniform
import CslibFrontierTests.RealizablePAC

/-! Checks for nonuniform learnability, structural risk minimization and the MDL bound on the
threshold concepts `x ↦ decide (t ≤ x)` on `ℕ`, a countable class of VC dimension `1`: the
geometric weighting, an SRM learner and a learner that fails the SRM rule, a nonvacuous SRM bound
for `m = 10000` and `δ = 1/20` with an explicit gap, the unary prefix-free description of the
thresholds and its MDL bound, a description that is injective but not prefix-free, and
nonuniform learnability of the thresholds and of the indicators of finite sets of naturals, a
class of infinite VC dimension. -/

namespace CslibFrontierTests.NonuniformPAC

open Cslib.MachineLearning.PACLearning MeasureTheory
open CslibFrontierTests.RealizablePAC (thresholds)
open scoped NNReal ENNReal

/-- The threshold concept at `t`. -/
def threshold (t : ℕ) : ℕ → Bool := fun x => decide (t ≤ x)

theorem threshold_injective : Function.Injective threshold := by
  intro s t hst
  have hs := congrFun hst s
  have ht := congrFun hst t
  simp only [threshold, le_refl, decide_true] at hs ht
  have h1 : t ≤ s := by simpa using hs.symm
  have h2 : s ≤ t := by simpa using ht
  omega

theorem thresholds_eq_range : thresholds = Set.range threshold := by
  ext c
  exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩

theorem measurableSet_misclassified_nat (h : ℕ → Bool) :
    MeasurableSet {p : ℕ × Bool | h p.1 ≠ p.2} :=
  measurableSet_misclassified (measurable_of_countable _)

/-! ### Weightings -/

example : Weighting.geometric 0 = 1 / 2 := by norm_num

example : Weighting.geometric 3 = 1 / 16 := by norm_num

/-! ### The SRM rule -/

/-- The learner that always outputs the threshold at `0`. -/
def alwaysZero : Learner ℕ Bool 1 := fun _ => threshold 0

/-- With penalty `t` for the class `{threshold t}`, outputting `threshold 0` follows the SRM rule
on one example: its bound is at most `1 + 0`, and every other class pays at least `1`. -/
example : IsSRM alwaysZero (fun t => {threshold t}) (fun t => (t : ℝ)) := by
  intro S
  refine ⟨0, rfl, fun j h hh => ?_⟩
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hle : empiricalMiscount (alwaysZero S) S ≤ 1 :=
    (Finset.card_filter_le _ _).trans_eq (by simp)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact le_rfl
  · have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have : (empiricalMiscount (alwaysZero S) S : ℝ) ≤ 1 := by exact_mod_cast hle
    have : (0 : ℝ) ≤ empiricalMiscount (threshold j) S := by positivity
    simp only [Nat.cast_one, div_one, Nat.cast_zero, add_zero]
    linarith

/-- With equal penalties, `alwaysZero` violates the SRM rule on the example `(0, false)`, where
`threshold 1` is correct and `threshold 0` is not. -/
example : ¬ IsSRM alwaysZero (fun t => {threshold t}) (fun _ => (0 : ℝ)) := by
  intro hA
  obtain ⟨i, -, hmin⟩ := hA ![(0, false)]
  have := hmin 1 (threshold 1) rfl
  have h0 : empiricalMiscount (alwaysZero ![(0, false)]) ![(0, false)] = 1 := by decide
  have h1 : empiricalMiscount (threshold 1) ![(0, false)] = 0 := by decide
  rw [h0, h1] at this
  norm_num at this

/-- Penalties that grow along the indices give an SRM learner for the thresholds. -/
example (m : ℕ) : ∃ A : Learner ℕ Bool m, IsSRM A (fun t => {threshold t}) (fun t => (t : ℝ)) :=
  exists_isSRM ⟨0, threshold 0, rfl⟩ (Nat.cofinite_eq_atTop ▸ tendsto_natCast_atTop_atTop)

/-! ### The SRM bound -/

/-- `√(log (2 / (2⁻¹ · (1/20))) / (2 · 10000)) ≤ 1/50`, since `log 80 ≤ 7 log 2 < 8`. -/
theorem srm_gap_le :
    √(Real.log (2 / (Weighting.geometric 0 * (1 / 20))) / (2 * (10000 : ℕ))) ≤ 1 / 50 := by
  have hlog : Real.log (2 / (Weighting.geometric 0 * (1 / 20))) ≤ 7 * Real.log 2 := by
    have h7 : Real.log ((2 : ℝ) ^ 7) = 7 * Real.log 2 := by
      rw [Real.log_pow]
      norm_num
    rw [← h7]
    refine Real.log_le_log (by norm_num) ?_
    norm_num
  rw [show (1 / 50 : ℝ) = √((1 / 50) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_iff₀ (by norm_num)]
  push_cast
  linarith [Real.log_two_lt_d9]

/-- **A nonvacuous SRM bound** for the thresholds with the geometric weighting: under every
distribution, `10000` examples give, with probability at least `19/20`, `L_D(h) ≤ L_S(h) + 1/50`
for `h = threshold 0`, simultaneously with the corresponding bounds for every other threshold. -/
example (D : Measure (ℕ × Bool)) [IsProbabilityMeasure D] :
    Measure.pi (fun _ : Fin 10000 => D)
        {S | (empiricalMiscount (threshold 0) S : ℝ) / (10000 : ℕ) + 1 / 50 <
          (error D (threshold 0)).toReal} ≤ ENNReal.ofReal (1 / 20) := by
  refine (measure_mono fun S hS => ?_).trans (Weighting.geometric.measure_pi_exists_lt_error_le
    (H := fun t => {threshold t})
    (fun t => hasUniformConvergenceRate_singleton (measurableSet_misclassified_nat _))
    D (Set.mem_univ D) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 20))
  exact ⟨0, threshold 0, rfl, lt_of_le_of_lt (by linarith [srm_gap_le]) hS⟩

/-! ### Prefix-free descriptions and the MDL bound -/

/-- The unary codeword `1^t 0` of length `t + 1`. -/
def unary (t : ℕ) : List Bool := List.replicate t true ++ [false]

theorem unary_prefix {s t : ℕ} (h : unary s <+: unary t) : s = t := by
  have hlen := h.length_le
  simp only [unary, List.length_append, List.length_replicate, List.length_singleton,
    add_le_add_iff_right] at hlen
  by_contra hne
  have hlt : s < t := lt_of_le_of_ne hlen hne
  have hs : s < (unary s).length := by simp [unary]
  have := h.getElem hs
  simp [unary, hlt] at this

open Classical in
/-- The unary description of a hypothesis: `unary t` for `threshold t`, and `[]` otherwise. -/
noncomputable def thresholdCode (h : ℕ → Bool) : List Bool :=
  if hh : ∃ t, threshold t = h then unary (Classical.choose hh) else []

theorem thresholdCode_threshold (t : ℕ) : thresholdCode (threshold t) = unary t := by
  have hh : ∃ s, threshold s = threshold t := ⟨t, rfl⟩
  rw [thresholdCode, dite_eq_left hh, threshold_injective (Classical.choose_spec hh)]

/-- The unary codes form a prefix-free description of the thresholds, of length `t + 1` at
`threshold t`. -/
theorem isPrefixFreeDescription_thresholdCode :
    IsPrefixFreeDescription thresholds thresholdCode := by
  rw [thresholds_eq_range]
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ h
  rw [thresholdCode_threshold, thresholdCode_threshold] at h
  rw [unary_prefix h]

/-- The Kraft weights of the unary description are the geometric weights. -/
example (t : ℕ) :
    isPrefixFreeDescription_thresholdCode.weighting
      ⟨threshold t, thresholds_eq_range ▸ ⟨t, rfl⟩⟩ = Weighting.geometric t := by
  simp [thresholdCode_threshold, unary]

/-- **The MDL bound for thresholds**: under every distribution, with probability at least
`1 - δ`, every threshold satisfies `L_D(threshold t) ≤ L_S(threshold t) +
√(((t + 1) log 2 + log (2 / δ)) / (2 m))`. -/
example (D : Measure (ℕ × Bool)) [IsProbabilityMeasure D] {m : ℕ} (hm : 0 < m) {δ : ℝ}
    (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D)
        {S | ∃ t : ℕ, (empiricalMiscount (threshold t) S : ℝ) / m +
          √(((t + 1 : ℕ) * Real.log 2 + Real.log (2 / δ)) / (2 * m)) <
            (error D (threshold t)).toReal} ≤ ENNReal.ofReal δ := by
  refine (measure_mono fun S => ?_).trans
    (isPrefixFreeDescription_thresholdCode.mdl_bound
      (fun h _ => measurableSet_misclassified_nat h) D hm hδ)
  rintro ⟨t, ht⟩
  refine ⟨threshold t, thresholds_eq_range ▸ ⟨t, rfl⟩, ?_⟩
  rwa [thresholdCode_threshold, unary, List.length_append, List.length_replicate,
    List.length_singleton]

/-- The description `[]` of `fun _ => false` is a prefix of the description `[true]` of
`fun _ => true`: it is injective but not prefix-free, so Kraft's inequality does not apply. -/
example : ¬ IsPrefixFreeDescription ({fun _ => false, fun _ => true} : ConceptClass ℕ Bool)
    fun h => if h 0 then [true] else [] := by
  intro hd
  have := hd (fun _ => false) (by simp) (fun _ => true) (by simp) (by simp)
  have := congrFun this 0
  simp at this

/-! ### Nonuniform learnability -/

/-- **The thresholds are nonuniformly learnable** over all distributions. -/
example : IsNonuniformLearnable thresholds Set.univ :=
  isNonuniformLearnable_of_countable (thresholds_eq_range ▸ Set.countable_range _)
    fun h _ => measurableSet_misclassified_nat h

/-- The indicators of finite sets of naturals. -/
def finsetIndicators : ConceptClass ℕ Bool := Set.range fun s : Finset ℕ => fun x => decide (x ∈ s)

/-- The finite-set indicators shatter every finite set, so they have infinite VC dimension and are
not covered by the finite-VC theory. -/
theorem not_hasFiniteVCDim_finsetIndicators : ¬ HasFiniteVCDim finsetIndicators := by
  rw [hasFiniteVCDim_iff]
  rintro ⟨N, hN⟩
  have hsh : SetShatters finsetIndicators ↑(Finset.range (N + 1)) := by
    intro W' hW'
    have hfin : W'.Finite := (Finset.range (N + 1)).finite_toSet.subset hW'
    refine ⟨fun x => decide (x ∈ hfin.toFinset), ⟨hfin.toFinset, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq,
      Set.Finite.mem_toFinset]
    exact ⟨fun h => h.1, fun h => ⟨h, hW' h⟩⟩
  have := hN _ hsh
  simp at this

/-- **The indicators of finite sets of naturals are nonuniformly learnable** over all
distributions, although their VC dimension is infinite. -/
example : IsNonuniformLearnable finsetIndicators Set.univ :=
  isNonuniformLearnable_of_countable (Set.countable_range _)
    fun h _ => measurableSet_misclassified_nat h

end CslibFrontierTests.NonuniformPAC
