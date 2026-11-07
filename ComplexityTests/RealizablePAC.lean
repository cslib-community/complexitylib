/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.MachineLearning.PACLearning.FiniteClass
import Complexity.MachineLearning.PACLearning.GrowthFunction
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Checks for distribution-free realizable PAC learning: realizability, consistency and empirical
risk minimization on concrete distributions and learners; the finite-class Occam bound with
explicit parameters, including a matching nonvacuity check that zero examples do not suffice; and
the growth function and VC dimension of threshold concepts on `ℕ` and of all Boolean concepts. -/

namespace ComplexityTests.RealizablePAC

open Cslib.MachineLearning.PACLearning MeasureTheory
open scoped NNReal ENNReal

/-! ### Realizability, consistency and ERM -/

/-- The two constant hypotheses on `Bool`. -/
def constants : Finset (Bool → Bool) := {fun _ => false, fun _ => true}

theorem card_constants : constants.card = 2 := by
  decide

theorem const_mem_constants (b : Bool) : (fun _ => b) ∈ (constants : Set (Bool → Bool)) := by
  cases b <;> simp [constants]

/-- A point mass on a correctly labeled example is realizable by the constants. -/
example : IsRealizableBy (Measure.dirac ((true, true) : Bool × Bool))
    (constants : Set (Bool → Bool)) :=
  ⟨fun _ => true, const_mem_constants true, by simp [error]⟩

/-- A distribution that labels one point both ways is realizable by no class at all. -/
example (C : ConceptClass Bool Bool) :
    ¬ IsRealizableBy (Measure.dirac ((false, false) : Bool × Bool) +
      Measure.dirac (false, true)) C := by
  rintro ⟨h, -, hh⟩
  cases hf : h false <;> simp [error, hf] at hh

/-- Labeling a domain distribution by a threshold concept is realizable by thresholds. -/
example (P : Measure ℕ) (t : ℕ) :
    IsRealizableBy (P.map fun x => (x, decide (t ≤ x)))
      {c : ℕ → Bool | ∃ t : ℕ, c = fun x => decide (t ≤ x)} :=
  isRealizableBy_map_graph P ⟨t, rfl⟩ measurable_from_nat

/-- The learner that copies the label of its single example into a constant hypothesis. -/
def copyLabel : Learner Bool Bool 1 := fun S _ => (S 0).2

/-- `copyLabel` is an empirical risk minimizer for the constants: it makes no sample errors. -/
theorem isERM_copyLabel : IsERM copyLabel (constants : Set (Bool → Bool)) := by
  intro S
  refine ⟨const_mem_constants _, fun h _ => ?_⟩
  have h0 : empiricalMiscount (copyLabel S) S = 0 :=
    Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun i _ => by
      fin_cases i
      simp [copyLabel])
  rw [h0]
  exact Nat.zero_le _

example : IsConsistent copyLabel (constants : Set (Bool → Bool)) :=
  isERM_copyLabel.isConsistent

/-- The learner that always predicts `true` is not consistent with the constants, since it errs
on a sample labeled by the constant `false`; hence it is not an empirical risk minimizer. -/
theorem not_isConsistent_alwaysTrue :
    ¬ IsConsistent (fun _ _ => true : Learner Bool Bool 1) (constants : Set (Bool → Bool)) := by
  intro h
  have := (h (fun _ => (false, false)) ⟨fun _ => false, const_mem_constants false,
    fun _ => rfl⟩).2 0
  simp at this

example : ¬ IsERM (fun _ _ => true : Learner Bool Bool 1) (constants : Set (Bool → Bool)) :=
  fun h => not_isConsistent_alwaysTrue h.isConsistent

/-! ### The finite-class Occam bound -/

/-- `1 / 2` as an accuracy or confidence parameter. -/
noncomputable def half : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

theorem measurableSet_misclassified_constants :
    ∀ h ∈ constants, MeasurableSet {p : Bool × Bool | h p.1 ≠ p.2} :=
  fun _ _ => measurableSet_misclassified (measurable_of_countable _)

/-- Three examples suffice to learn the constants to accuracy and confidence `1 / 2`, because
`log 2 + log 2 ≤ (1 / 2) * 3`. -/
theorem isPACLearnerFor_constants_three : IsPACLearnerFor 3 half half
    (constants : Set (Bool → Bool)) (realizableDistributions (constants : Set (Bool → Bool))) := by
  refine isPACLearnerFor_realizableDistributions_of_log_card_add_log_inv_le
    measurableSet_misclassified_constants ⟨_, const_mem_constants true⟩ ?_
  simp only [card_constants, half, Nat.cast_ofNat, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat, inv_div, div_one]
  linarith [Real.log_two_lt_d9]

/-- Zero examples do not suffice: the hypothesis output on the empty sample is wrong with
probability one under a point mass labeled by the opposite constant. -/
theorem not_isPACLearnerFor_constants_zero : ¬ IsPACLearnerFor 0 half half
    (constants : Set (Bool → Bool)) (realizableDistributions (constants : Set (Bool → Bool))) := by
  rintro ⟨A, hA⟩
  set h0 := A fun i => i.elim0
  set D : Measure (Bool × Bool) := Measure.dirac (true, !h0 true)
  have hD : D ∈ realizableDistributions (constants : Set (Bool → Bool)) :=
    ⟨fun _ => !h0 true, const_mem_constants _, by simp [D, error]⟩
  have key := hA D hD
  rw [IsRealizableBy.optimalError_eq_zero hD, zero_add] at key
  have hset : {S : LabeledSample Bool Bool 0 | ((half.val : ℝ≥0) : ℝ≥0∞) < error D (A S)} =
      Set.univ := by
    refine Set.eq_univ_of_forall fun S => ?_
    have hS : S = fun i => i.elim0 := Subsingleton.elim _ _
    have herr : error D (A S) = 1 := by
      rw [hS]
      simp [D, error, h0]
    change ((half.val : ℝ≥0) : ℝ≥0∞) < error D (A S)
    rw [herr, half]
    exact_mod_cast (by norm_num : (1 / 2 : ℝ≥0) < 1)
  rw [hset, measure_univ, half] at key
  exact absurd key (by exact_mod_cast (by norm_num : ¬ (1 : ℝ≥0) ≤ 1 / 2))

/-- The Occam sample-complexity bound `⌈(log 2 + log 2) / (1 / 2)⌉ = 3` together with the
nonvacuity lower bound: the realizable sample complexity of the constants at `(1/2, 1/2)` lies in
`[1, 3]`. -/
example : 1 ≤ sampleComplexity IsPACLearnerFor (constants : Set (Bool → Bool)) half half
      (realizableDistributions (constants : Set (Bool → Bool))) ∧
    sampleComplexity IsPACLearnerFor (constants : Set (Bool → Bool)) half half
      (realizableDistributions (constants : Set (Bool → Bool))) ≤ 3 := by
  refine ⟨Nat.one_le_iff_ne_zero.2 fun h0 => not_isPACLearnerFor_constants_zero ?_, ?_⟩
  · have hmem := Nat.sInf_mem (⟨3, isPACLearnerFor_constants_three⟩ :
      {m | IsPACLearnerFor m half half (constants : Set (Bool → Bool))
        (realizableDistributions (constants : Set (Bool → Bool)))}.Nonempty)
    unfold sampleComplexity at h0
    rwa [h0] at hmem
  · refine (sampleComplexity_realizableDistributions_le_of_finite
      measurableSet_misclassified_constants ⟨_, const_mem_constants true⟩ half half).trans ?_
    refine Nat.ceil_le.2 ?_
    simp only [card_constants, half, Nat.cast_ofNat, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat, inv_div, div_one]
    rw [div_le_iff₀ (by norm_num)]
    linarith [Real.log_two_lt_d9]

/-! ### Growth function and VC dimension -/

/-- Threshold concepts `x ↦ (t ≤ x)` on `ℕ`. -/
def thresholds : ConceptClass ℕ Bool := {c | ∃ t : ℕ, c = fun x => decide (t ≤ x)}

/-- Thresholds cannot label a smaller point positive and a larger point negative. -/
private theorem false_of_setShatters_thresholds {W : Finset ℕ} (hW : SetShatters thresholds ↑W)
    {a b : ℕ} (ha : a ∈ W) (hb : b ∈ W) (hab : a < b) : False := by
  obtain ⟨c, ⟨t, rfl⟩, hc⟩ := hW {a} (Set.singleton_subset_iff.2 (Finset.mem_coe.2 ha))
  have ha' : a ∈ (fun x => decide (t ≤ x)) ⁻¹' {true} ∩ ↑W := by
    rw [hc]
    exact Set.mem_singleton a
  have hb' : b ∉ (fun x => decide (t ≤ x)) ⁻¹' {true} ∩ ↑W := by
    rw [hc]
    exact hab.ne'
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq,
    Finset.mem_coe, not_and] at ha' hb'
  exact hb' (ha'.1.trans hab.le) hb

/-- Thresholds shatter no two-point set. -/
theorem card_le_one_of_setShatters_thresholds {W : Finset ℕ} (hW : SetShatters thresholds ↑W) :
    W.card ≤ 1 := by
  by_contra hlt
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (not_le.1 hlt)
  rcases lt_or_gt_of_ne hab with h | h
  · exact false_of_setShatters_thresholds hW ha hb h
  · exact false_of_setShatters_thresholds hW hb ha h

/-- Thresholds shatter the singleton `{0}`. -/
theorem setShatters_thresholds_singleton : SetShatters thresholds ↑({0} : Finset ℕ) := by
  intro W' hW'
  rw [Finset.coe_singleton] at hW'
  rcases Set.subset_singleton_iff_eq.1 hW' with rfl | rfl
  · refine ⟨fun x => decide (1 ≤ x), ⟨1, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq,
      Finset.coe_singleton, Set.mem_empty_iff_false, iff_false, not_and]
    omega
  · exact ⟨fun x => decide (0 ≤ x), ⟨0, rfl⟩, by ext x; simp⟩

theorem growthFunction_thresholds_one : growthFunction thresholds 1 = 2 := by
  simpa using growthFunction_eq_two_pow_of_setShatters setShatters_thresholds_singleton

/-- Sauer's lemma for thresholds, whose shattered sets have at most one point. -/
example (m : ℕ) : growthFunction thresholds m ≤ m + 1 := by
  simpa using growthFunction_le_add_one_pow (fun W hW => card_le_one_of_setShatters_thresholds hW) m

/-- Sauer's lemma is attained by thresholds at two points: `growthFunction thresholds 2 = 3`. -/
example : growthFunction thresholds 2 = 3 := by
  have hle := growthFunction_le_add_one_pow
    (fun W hW => card_le_one_of_setShatters_thresholds hW) (C := thresholds) 2
  refine le_antisymm (by simpa using hle) ?_
  have hsub : (({![true, true], ![false, true], ![false, false]} : Finset (Fin 2 → Bool)) :
      Set (Fin 2 → Bool)) ⊆ restrictions thresholds ![0, 1] := by
    intro v hv
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hv
    rw [mem_restrictions]
    rcases hv with rfl | rfl | rfl
    · exact ⟨fun x => decide (0 ≤ x), ⟨0, rfl⟩, by decide⟩
    · exact ⟨fun x => decide (1 ≤ x), ⟨1, rfl⟩, by decide⟩
    · exact ⟨fun x => decide (2 ≤ x), ⟨2, rfl⟩, by decide⟩
  calc 3 = (({![true, true], ![false, true], ![false, false]} : Finset (Fin 2 → Bool)) :
        Set (Fin 2 → Bool)).ncard := by rw [Set.ncard_coe_finset]; decide
    _ ≤ (restrictions thresholds ![0, 1]).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ growthFunction thresholds 2 := ncard_restrictions_le_growthFunction _ _

theorem hasFiniteVCDim_thresholds : HasFiniteVCDim thresholds :=
  hasFiniteVCDim_iff.2 ⟨1, fun _ hW => card_le_one_of_setShatters_thresholds hW⟩

example : vcDim thresholds = 1 := by
  unfold vcDim
  refine le_antisymm (csSup_le ⟨1, {0}, rfl, setShatters_thresholds_singleton⟩ ?_)
    (le_csSup hasFiniteVCDim_thresholds ⟨{0}, rfl, setShatters_thresholds_singleton⟩)
  rintro _ ⟨W, rfl, hW⟩
  exact card_le_one_of_setShatters_thresholds hW

/-- Sauer's lemma in `vcDim` form for thresholds. -/
example (m : ℕ) : growthFunction thresholds m ≤ ∑ i ∈ Finset.range (vcDim thresholds + 1),
    m.choose i :=
  growthFunction_le_sum_choose_vcDim hasFiniteVCDim_thresholds m

/-- The class of all Boolean concepts shatters every set. -/
theorem setShatters_univ {α : Type*} (W : Set α) :
    SetShatters (Set.univ : ConceptClass α Bool) W := by
  classical
  intro W' hW'
  refine ⟨fun x => decide (x ∈ W'), Set.mem_univ _, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, hW' h⟩⟩

/-- Without a bound on shattered sets the growth function is `2 ^ m`, so the hypothesis of
Sauer's lemma cannot be dropped. -/
example (m : ℕ) : growthFunction (Set.univ : ConceptClass ℕ Bool) m = 2 ^ m := by
  simpa using growthFunction_eq_two_pow_of_setShatters
    (setShatters_univ ((Finset.range m : Finset ℕ) : Set ℕ))

/-- A finite class realizes at most as many labelings as it has concepts. -/
example (m : ℕ) : growthFunction (constants : Set (Bool → Bool)) m ≤ 2 :=
  card_constants ▸ growthFunction_le_card constants m

end ComplexityTests.RealizablePAC
