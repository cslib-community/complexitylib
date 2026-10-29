/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.AC0
import Complexity.MachineLearning.UniformLearning.AC0
import Complexity.MachineLearning.UniformLearning.KushilevitzMansour

/-! Nonvacuity checks for learning from uniform random examples and the low-degree algorithm, and
for learning with membership queries and the Kushilevitz–Mansour algorithm. -/

namespace ComplexityTests.FourierLearning

open Cslib Cslib.MachineLearning Cslib.MachineLearning.UniformLearning Cslib.BitString
  Cslib.Circuits.Boolean Cslib.Probability
open Finset
open scoped NNReal

/-- The parities of at most `t` coordinates have no Fourier weight above degree `t`. -/
theorem parities_weight {n t : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∀ f ∈ ({f | ∃ U : Finset (Fin n), #U ≤ t ∧ f = parityOn U} :
      PACLearning.ConceptClass (BitString n) Bool),
      ∑ S with t < #S, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤ ε / 2 := by
  rintro f ⟨U, hU, rfl⟩
  refine le_of_eq_of_le (sum_eq_zero fun S hS => ?_) (by positivity)
  have hSU : S ≠ U := by
    rintro rfl
    have := (mem_filter.1 hS).2
    omega
  simp [fourierCoeff_signVal_parityOn, hSU]

/-! ### The low-degree algorithm and AC⁰ learning -/

example (n t d g m : ℕ) (b : Bool) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (εIoo δIoo : Set.Ioo (0 : ℝ≥0) 1)
    {εNeg δNeg : ℝ} (hεNeg : εNeg < 1 / 2) (hδNeg : δNeg < 1)
    (hm : 4 * #{S : Finset (Fin n) | #S ≤ 783} / (1 / 2) *
      Real.log (2 * #{S : Finset (Fin n) | #S ≤ 783} / δ) ≤ m) :
    (signRound (fun _ : Fin 1 → Bool => (-1 / 2 : ℝ)) 0 = true ∧
      signRound (fun _ : Fin 1 → Bool => (0 : ℝ)) 0 = false) ∧
    (#{S : Finset (Fin 3) | #S ≤ 1} = 4 ∧
      #{S : Finset (Fin 3) | #S ≤ 1} ≤ (Fintype.card (Fin 3) + 1) ^ 1) ∧
    Learns (lowDegreeLearner (Fin n) t ⌈4 * #{S : Finset (Fin n) | #S ≤ t} / ε *
      Real.log (2 * #{S : Finset (Fin n) | #S ≤ t} / δ)⌉₊)
      {f | ∃ U : Finset (Fin n), #U ≤ t ∧ f = parityOn U} ε δ ∧
    PACLearning.IsPACLearnerFor ⌈4 * #{S : Finset (Fin n) | #S ≤ t} / (εIoo.val : ℝ) *
      Real.log (2 * #{S : Finset (Fin n) | #S ≤ t} / (δIoo.val : ℝ))⌉₊ εIoo δIoo
      {f | ∃ U : Finset (Fin n), #U ≤ t ∧ f = parityOn U}
      (uniformRealizable {f | ∃ U : Finset (Fin n), #U ≤ t ∧ f = parityOn U}) ∧
    ¬ Learns (fun _ : PACLearning.LabeledSample (Fin 1 → Bool) Bool m => fun _ => false)
      {fun x : Fin 1 → Bool => x 0} εNeg δNeg ∧
    ((PMF.uniformOfFintype (Fin 1 → Bool)).toMeasure.map fun x => (x, x 0)) ∈
      uniformRealizable {fun x : Fin 1 → Bool => x 0} ∧
    (let m₀ := ⌈4 * #{S : Finset (Fin n) | #S ≤ t} / ε *
      Real.log (2 * #{S : Finset (Fin n) | #S ≤ t} / δ)⌉₊
    (QueryLearner.ofLearner (lowDegreeLearner (Fin n) t m₀)).Learns (PMF.uniformOfFintype _)
      {f | ∃ U : Finset (Fin n), #U ≤ t ∧ f = parityOn U} ε δ ∧
      (QueryLearner.ofLearner (lowDegreeLearner (Fin n) t m₀)).QueriesAtMost m₀) ∧
    (fun _ : BitString n => b) ∈ circuitClass n 1 1 ∧
    Learns (lowDegreeLearner (Fin n) (lmnDegree d g ε)
      ⌈4 * #{S : Finset (Fin n) | #S ≤ lmnDegree d g ε} / ε *
        Real.log (2 * #{S : Finset (Fin n) | #S ≤ lmnDegree d g ε} / δ)⌉₊)
      (circuitClass n d g) ε δ ∧
    Learns (lowDegreeLearner (Fin n) 783 m) (circuitClass n 1 1) (1 / 2) δ ∧
    (PMF.uniformOfFintype (Fin m → BitString n)).toOuterMeasure
      {x | 1 / 2 < uniformError (fun _ => true)
        (lowDegreeHypothesis t (examples (fun _ => true) x))} ≤
        ENNReal.ofReal (2 * #{S : Finset (Fin n) | #S ≤ t} *
          Real.exp (-(m * (1 / 2)) / (4 * #{S : Finset (Fin n) | #S ≤ t}))) := by
  refine ⟨⟨by norm_num [signRound], by simp [signRound]⟩,
    ⟨by decide, card_filter_card_le_le_pow 1⟩,
    lowDegreeLearner_learns hε hδ (Nat.le_ceil _) (parities_weight hε),
    Learns.isPACLearnerFor (lowDegreeLearner_learns (by exact_mod_cast εIoo.2.1)
      (by exact_mod_cast δIoo.2.1) (Nat.le_ceil _) (parities_weight (by exact_mod_cast εIoo.2.1))),
    ?_,
    mem_uniformRealizable_iff.2 ⟨_, rfl, rfl⟩,
    ⟨QueryLearner.learns_ofLearner_iff.2
      (lowDegreeLearner_learns hε hδ (Nat.le_ceil _) (parities_weight hε)),
      QueryLearner.queriesAtMost_ofLearner _⟩,
    ⟨Unbounded.constCircuit (Circuits.Signature.Hom.id _) b, fun x => by
      funext j
      simp [Circuits.single], Unbounded.depth_constCircuit_le _,
      (Unbounded.size_constCircuit _).le⟩,
    lowDegreeLearner_learns_lmnDegree hε hδ (Nat.le_ceil _),
    lowDegreeLearner_learns_circuitClass (s := 3) (by norm_num) hδ (by norm_num)
      (by norm_num) (by norm_num) hm,
    ?_⟩
  · intro h
    have herr : uniformError (fun x : Fin 1 → Bool => x 0) (fun _ => false) = 1 / 2 := by
      have : hammingDist (fun _ : Fin 1 → Bool => false) (fun x : Fin 1 → Bool => x 0) = 1 := by
        decide
      simp [uniformError, this]
    have h1 := h _ rfl
    have huniv : {S : PACLearning.LabeledSample (Fin 1 → Bool) Bool m |
        εNeg < uniformError (fun x : Fin 1 → Bool => x 0) (fun _ => false)} = Set.univ :=
      Set.eq_univ_of_forall fun _ => by
        rw [Set.mem_ofPred_eq, herr]
        exact hεNeg
    rw [huniv, (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)] at h1
    exact absurd (ENNReal.one_le_ofReal.1 h1) (not_le.2 hδNeg)
  · refine uniform_lt_uniformError_lowDegreeHypothesis_le (ι := Fin n) (ε := 1 / 2) _ t m
      (by norm_num) ?_
    refine le_of_eq_of_le (sum_eq_zero fun S hS => ?_) (by norm_num)
    have hS : S ≠ ∅ := by
      rintro rfl
      simp at hS
    simp [fourierCoeff_const, hS]

/-! ### The Kushilevitz–Mansour algorithm -/

example (n m L : ℕ) (b : Bool) (θ : ℝ) (F : BitString 3 → ℝ) (S : Finset (Fin 3))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {εNeg δNeg : ℝ} (hεNeg : εNeg < 1 / 2) (hδNeg : δNeg < 1) :
    bucketWeight F univ S = fourierCoeff F S ^ 2 ∧
    (searchLevels (List.finRange 3)).length = 4 ∧
    (kmLearner (Fin n) m θ).QueriesAtMost (m * (2 * n + 3)) ∧
    (kmLearner (Fin n) ⌈512 * 1 ^ 4 / ε ^ 4 * Real.log (2 * (n + 2) * 2 ^ n / δ)⌉₊
      (ε / (2 * 1))).Learns (PMF.uniformOfFintype _) {f | ∃ U, f = parityOn U} ε δ ∧
    ¬ QueryLearner.Learns (fun _ : Unit => DecisionTree.leaf fun _ : Fin 1 → Bool => false)
      (PMF.pure ()) {fun x : Fin 1 → Bool => x 0} εNeg δNeg ∧
    (fun x : Fin 1 → Bool => x 0) ∈ decisionTreeClass (Fin 1) 2 ∧
    (fun _ : BitString n => b) ∈ decisionTreeClass (Fin n) 1 ∧
    (let mL := ⌈512 * (L : ℝ) ^ 4 / ε ^ 4 * Real.log (2 * (n + 2) * 2 ^ n / δ)⌉₊
    (kmLearner (Fin n) mL (ε / (2 * L))).Learns (PMF.uniformOfFintype _)
      (decisionTreeClass (Fin n) L) ε δ ∧
      (kmLearner (Fin n) mL (ε / (2 * L))).QueriesAtMost (mL * (2 * n + 3))) := by
  refine ⟨bucketWeight_univ F S, by simp,
    by simpa using kmLearner_queriesAtMost (ι := Fin n) (m := m) θ,
    ?_, ?_,
    ⟨.node 0 (.leaf false) (.leaf true), fun x => by cases h : x 0 <;> simp [h], le_of_eq rfl⟩,
    ⟨.leaf b, fun _ => rfl, le_rfl⟩, ?_⟩
  · refine (kmLearner_learns (L := 1) hε hδ (by simpa using Nat.le_ceil _)).mono ?_ le_rfl le_rfl
    rintro f ⟨U, rfl⟩
    simp [spectralNormClass, fourierCoeff_signVal_parityOn, apply_ite]
  · intro h
    have herr : uniformError (fun x : Fin 1 → Bool => x 0) (fun _ => false) = 1 / 2 := by
      have : hammingDist (fun _ : Fin 1 → Bool => false) (fun x : Fin 1 → Bool => x 0) = 1 := by
        decide
      simp [uniformError, this]
    have h1 := QueryLearner.learns_iff.1 h _ rfl
    have huniv : {ω : Unit | εNeg < uniformError (fun x : Fin 1 → Bool => x 0)
        ((DecisionTree.leaf fun _ : Fin 1 → Bool => false).eval fun x : Fin 1 → Bool => x 0)} =
        Set.univ :=
      Set.eq_univ_of_forall fun _ => by
        rw [Set.mem_ofPred_eq, DecisionTree.eval_leaf, herr]
        exact hεNeg
    rw [huniv, (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)] at h1
    exact absurd (ENNReal.one_le_ofReal.1 h1) (not_le.2 hδNeg)
  · simpa using kmLearner_learns_decisionTree_and_queriesAtMost (ι := Fin n) hε hδ
      (by simpa using Nat.le_ceil _)

end ComplexityTests.FourierLearning
