/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.LocalitySensitiveHash
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real

/-!
# Measure-theoretic locality-sensitive hashing

The base module `CslibFrontier.Probability.LocalitySensitiveHash` defines collision probabilities
and AND/OR amplification for discrete seed laws `seed : PMF ι`. Continuous LSH families such as
SimHash (`stdGaussian E`) and `p`-stable LSH (Gaussian/Cauchy projections paired with a uniform
shift) draw seeds from a probability measure `seed : Measure ι` on a measurable space.

This module extends keyed collision probability (`Cslib.Probability.measureCollisionProb`),
Charikar's triangle inequality (`measureCollisionProb_triangle`), and AND/OR/banding amplification
to arbitrary probability measures using Mathlib's finite product measure `Measure.pi`, reusing
`IsLocalitySensitive`, `andHash`, `sCurve`, and `exists_sCurve_gap` from
`CslibFrontier.Probability.LocalitySensitiveHash`.

## Main definitions

* `Cslib.Probability.measureCollisionProb`: collision probability
  `seed.real {i | hash i x = hash i x'}`.
* `Cslib.Probability.measureOrCollisionProb`: collision probability across `L` independent draws
  under `Measure.pi`.

## Main results

* `Cslib.Probability.measureCollisionProb_toMeasure`: agreement with `collisionProb` for `PMF`.
* `Cslib.Probability.measureCollisionProb_triangle`: Charikar's triangle inequality for measurable
  collision events.
* `Cslib.Probability.measureCollisionProb_andHash`,
  `Cslib.Probability.measureOrCollisionProb_eq`,
  `Cslib.Probability.measureOrCollisionProb_andHash`: exact AND, OR, and banded collision laws.
* `Cslib.Probability.IsLocalitySensitive.measureAnd`,
  `Cslib.Probability.IsLocalitySensitive.measureOr`,
  `Cslib.Probability.IsLocalitySensitive.measureBanded`,
  `Cslib.Probability.IsLocalitySensitive.exists_measureBanded`: sensitivity preservation and
  amplification under `Measure.pi`.

## References

* [P. Indyk, R. Motwani, *Approximate nearest neighbors: towards removing the curse of
  dimensionality*][IndykMotwani1998]
* [M. S. Charikar, *Similarity estimation techniques from rounding algorithms*][Charikar2002]
-/

public section

namespace Cslib.Probability

open MeasureTheory
open scoped ENNReal

variable {ι X Y : Type*} [MeasurableSpace ι]

/-! ### Collision probability under a probability measure -/

/-- The probability that `x` and `x'` collide under `hash` when the seed is drawn from `seed`. -/
@[expose] noncomputable def measureCollisionProb (seed : Measure ι) (hash : ι → X → Y)
    (x x' : X) : ℝ :=
  seed.real {i | hash i x = hash i x'}

theorem measureCollisionProb_nonneg (seed : Measure ι) (hash : ι → X → Y) (x x' : X) :
    0 ≤ measureCollisionProb seed hash x x' :=
  measureReal_nonneg

theorem measureCollisionProb_le_one (seed : Measure ι) [IsProbabilityMeasure seed]
    (hash : ι → X → Y) (x x' : X) : measureCollisionProb seed hash x x' ≤ 1 :=
  measureReal_le_one

@[simp]
theorem measureCollisionProb_self (seed : Measure ι) [IsProbabilityMeasure seed]
    (hash : ι → X → Y) (x : X) : measureCollisionProb seed hash x x = 1 := by
  simp only [measureCollisionProb, Set.ofPred_true, measureReal_def, measure_univ,
    ENNReal.toReal_one]

theorem measureCollisionProb_comm (seed : Measure ι) (hash : ι → X → Y) (x x' : X) :
    measureCollisionProb seed hash x x' = measureCollisionProb seed hash x' x := by
  simp only [measureCollisionProb, eq_comm]

/-- A discrete seed law `PMF` converted via `PMF.toMeasure` has the same collision probability
when the collision event is measurable. -/
theorem measureCollisionProb_toMeasure (seed : PMF ι) (hash : ι → X → Y) {x x' : X}
    (hmeas : MeasurableSet {i | hash i x = hash i x'}) :
    measureCollisionProb seed.toMeasure hash x x' = collisionProb seed hash x x' := by
  rw [measureCollisionProb, measureReal_def, seed.toMeasure_apply_eq_toOuterMeasure_apply hmeas,
    collisionProb]

/-- **Charikar's triangle inequality** ([Charikar2002], Lemma 1) for a measure-valued seed law:
`1 - measureCollisionProb` satisfies the triangle inequality whenever the collision events are
measurable. -/
theorem measureCollisionProb_triangle (seed : Measure ι) [IsProbabilityMeasure seed]
    (hash : ι → X → Y) {x y z : X}
    (hxy : MeasurableSet {i | hash i x = hash i y})
    (hyz : MeasurableSet {i | hash i y = hash i z})
    (hxz : MeasurableSet {i | hash i x = hash i z}) :
    1 - measureCollisionProb seed hash x z ≤
      (1 - measureCollisionProb seed hash x y) + (1 - measureCollisionProb seed hash y z) := by
  have hcompl (a b : X) (hab : MeasurableSet {i | hash i a = hash i b}) :
      1 - measureCollisionProb seed hash a b = seed.real {i | hash i a ≠ hash i b} := by
    rw [measureCollisionProb, ← probReal_compl_eq_one_sub hab]
    rfl
  rw [hcompl x z hxz, hcompl x y hxy, hcompl y z hyz]
  have hsub : {i | hash i x ≠ hash i z} ⊆
      {i | hash i x ≠ hash i y} ∪ {i | hash i y ≠ hash i z} := by
    intro i hi
    by_contra hno
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hi hno
    exact hi (hno.1.trans hno.2)
  exact (measureReal_mono hsub).trans (measureReal_union_le _ _)

/-! ### AND and OR amplification under `Measure.pi` -/

omit [MeasurableSpace ι] in
/-- Box representation of the collision set for the AND construction. -/
theorem setOf_andHash_eq (hash : ι → X → Y) (k : ℕ) (x x' : X) :
    {s : Fin k → ι | andHash hash k s x = andHash hash k s x'} =
      Set.pi Set.univ fun _ : Fin k => {i | hash i x = hash i x'} := by
  ext s
  simp only [andHash, funext_iff, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]

/-- Single-draw measurability of the collision event passes to the `k`-fold AND construction. -/
theorem measurableSet_andHash_eq (hash : ι → X → Y) (k : ℕ) {x x' : X}
    (hmeas : MeasurableSet {i : ι | hash i x = hash i x'}) :
    MeasurableSet {s : Fin k → ι | andHash hash k s x = andHash hash k s x'} := by
  rw [setOf_andHash_eq]
  exact MeasurableSet.univ_pi fun _ => hmeas

/-- `k` independent draws from a probability measure `seed` all yield a collision with probability
`measureCollisionProb seed hash x x' ^ k`. -/
theorem measureCollisionProb_andHash (seed : Measure ι) [IsProbabilityMeasure seed]
    (hash : ι → X → Y) (k : ℕ) (x x' : X) :
    measureCollisionProb (Measure.pi fun _ : Fin k => seed) (andHash hash k) x x' =
      measureCollisionProb seed hash x x' ^ k := by
  rw [measureCollisionProb, measureReal_def, setOf_andHash_eq, Measure.pi_pi, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow, ← measureReal_def,
    measureCollisionProb]

/-- The AND construction on a `(p₁, p₂)`-sensitive family under a probability measure `seed` is
`(p₁ ^ k, p₂ ^ k)`-sensitive under `Measure.pi`. -/
theorem IsLocalitySensitive.measureAnd {seed : Measure ι} [IsProbabilityMeasure seed]
    {hash : ι → X → Y} {near far : X → X → Prop} {p₁ p₂ : ℝ}
    (h : IsLocalitySensitive (measureCollisionProb seed hash) near far p₁ p₂)
    (hp₁ : 0 ≤ p₁) (k : ℕ) :
    IsLocalitySensitive
      (measureCollisionProb (Measure.pi fun _ : Fin k => seed) (andHash hash k))
      near far (p₁ ^ k) (p₂ ^ k) where
  le_of_near x x' hx := by
    rw [measureCollisionProb_andHash]
    exact pow_le_pow_left₀ hp₁ (h.le_of_near x x' hx) k
  le_of_far x x' hx := by
    rw [measureCollisionProb_andHash]
    exact pow_le_pow_left₀ (measureCollisionProb_nonneg _ _ _ _) (h.le_of_far x x' hx) k

/-- The probability that at least one of `L` independent seeds drawn from `Measure.pi` yields a
collision between `x` and `x'`. -/
noncomputable def measureOrCollisionProb (seed : Measure ι) (hash : ι → X → Y) (L : ℕ)
    (x x' : X) : ℝ :=
  (Measure.pi fun _ : Fin L => seed).real {s | ∃ j, hash (s j) x = hash (s j) x'}

/-- One of `L` independent draws from a probability measure collides with probability
`1 - (1 - p) ^ L`, provided the single-draw collision event is measurable. -/
theorem measureOrCollisionProb_eq (seed : Measure ι) [IsProbabilityMeasure seed]
    (hash : ι → X → Y) (L : ℕ) {x x' : X}
    (hmeas : MeasurableSet {i | hash i x = hash i x'}) :
    measureOrCollisionProb seed hash L x x' =
      1 - (1 - measureCollisionProb seed hash x x') ^ L := by
  set E : Set ι := {i | hash i x = hash i x'}
  have hEc : {s : Fin L → ι | ∃ j, hash (s j) x = hash (s j) x'} =
      (Set.pi Set.univ fun _ : Fin L => Eᶜ)ᶜ := by
    ext s
    simp only [Set.mem_compl_iff, Set.mem_pi, Set.mem_univ, true_implies, not_forall,
      not_not, Set.mem_ofPred_eq, E]
  have hEm : MeasurableSet (Set.pi Set.univ fun _ : Fin L => Eᶜ) :=
    MeasurableSet.univ_pi fun _ => hmeas.compl
  rw [measureOrCollisionProb, hEc, probReal_compl_eq_one_sub hEm, measureReal_def, Measure.pi_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow, ← measureReal_def,
    probReal_compl_eq_one_sub hmeas, measureCollisionProb]

/-- The OR construction under `Measure.pi` turns a `(p₁, p₂)`-sensitive family into a
`(1 - (1 - p₁) ^ L, 1 - (1 - p₂) ^ L)`-sensitive one. -/
theorem IsLocalitySensitive.measureOr {seed : Measure ι} [IsProbabilityMeasure seed]
    {hash : ι → X → Y} {near far : X → X → Prop} {p₁ p₂ : ℝ}
    (h : IsLocalitySensitive (measureCollisionProb seed hash) near far p₁ p₂)
    (hmeas : ∀ x x', MeasurableSet {i | hash i x = hash i x'}) (hp₂ : p₂ ≤ 1) (L : ℕ) :
    IsLocalitySensitive (measureOrCollisionProb seed hash L) near far (1 - (1 - p₁) ^ L)
      (1 - (1 - p₂) ^ L) where
  le_of_near x x' hx := by
    rw [measureOrCollisionProb_eq _ _ _ (hmeas x x')]
    exact one_sub_one_sub_pow_le_one_sub_one_sub_pow
      (h.le_of_near x x' hx) (measureCollisionProb_le_one _ _ _ _) L
  le_of_far x x' hx := by
    rw [measureOrCollisionProb_eq _ _ _ (hmeas x x')]
    exact one_sub_one_sub_pow_le_one_sub_one_sub_pow (h.le_of_far x x' hx) hp₂ L

/-- `L` bands of `k` independent draws from a probability measure collide in some band with
probability `sCurve k L (measureCollisionProb seed hash x x')`. -/
theorem measureOrCollisionProb_andHash (seed : Measure ι) [IsProbabilityMeasure seed]
    (hash : ι → X → Y) (k L : ℕ) {x x' : X}
    (hmeas : MeasurableSet {i | hash i x = hash i x'}) :
    measureOrCollisionProb (Measure.pi fun _ : Fin k => seed) (andHash hash k) L x x' =
      sCurve k L (measureCollisionProb seed hash x x') := by
  rw [measureOrCollisionProb_eq _ _ _ (measurableSet_andHash_eq hash k hmeas),
    measureCollisionProb_andHash, sCurve]

/-- Banding turns a `(p₁, p₂)`-sensitive family under a probability measure into an
`(sCurve k L p₁, sCurve k L p₂)`-sensitive family. -/
theorem IsLocalitySensitive.measureBanded {seed : Measure ι} [IsProbabilityMeasure seed]
    {hash : ι → X → Y} {near far : X → X → Prop} {p₁ p₂ : ℝ}
    (h : IsLocalitySensitive (measureCollisionProb seed hash) near far p₁ p₂)
    (hmeas : ∀ x x', MeasurableSet {i | hash i x = hash i x'})
    (hp₁ : 0 ≤ p₁) (hp₂ : p₂ ≤ 1) (k L : ℕ) :
    IsLocalitySensitive
      (measureOrCollisionProb (Measure.pi fun _ : Fin k => seed) (andHash hash k) L)
      near far (sCurve k L p₁) (sCurve k L p₂) where
  le_of_near x x' hx := by
    rw [measureOrCollisionProb_andHash _ _ _ _ (hmeas x x')]
    exact sCurve_mono hp₁ (h.le_of_near x x' hx) (measureCollisionProb_le_one _ _ _ _)
  le_of_far x x' hx := by
    rw [measureOrCollisionProb_andHash _ _ _ _ (hmeas x x')]
    exact sCurve_mono (measureCollisionProb_nonneg _ _ _ _) (h.le_of_far x x' hx) hp₂

/-- **Banded amplification for probability-measure seed laws**: a `(near, far, p₁, p₂)`-sensitive
family with `0 ≤ p₂ < p₁ ≤ 1` amplifies via `k` AND-rows and `L = ⌈log (1/δ) / p₁ ^ k⌉₊`
OR-bands to error `δ` on near pairs and `δ'` on far pairs. -/
theorem IsLocalitySensitive.exists_measureBanded {seed : Measure ι} [IsProbabilityMeasure seed]
    {hash : ι → X → Y} {near far : X → X → Prop} {p₁ p₂ δ δ' : ℝ}
    (h : IsLocalitySensitive (measureCollisionProb seed hash) near far p₁ p₂)
    (hmeas : ∀ x x', MeasurableSet {i | hash i x = hash i x'})
    (hp₂ : 0 ≤ p₂) (hp₁₂ : p₂ < p₁) (hp₁ : p₁ ≤ 1) (hδ : 0 < δ) (hδ' : 0 < δ') :
    ∃ k : ℕ, ∃ L : ℕ, L = ⌈Real.log δ⁻¹ / p₁ ^ k⌉₊ ∧
      IsLocalitySensitive
        (measureOrCollisionProb (Measure.pi fun _ : Fin k => seed) (andHash hash k) L)
        near far (1 - δ) δ' := by
  obtain ⟨k, L, hL, hnear, hfar⟩ := exists_sCurve_gap hp₂ hp₁₂ hp₁ hδ hδ'
  refine ⟨k, L, hL, fun x x' hx => ?_, fun x x' hx => ?_⟩
  · rw [measureOrCollisionProb_andHash _ _ _ _ (hmeas x x')]
    exact hnear _ (h.le_of_near x x' hx) (measureCollisionProb_le_one _ _ _ _)
  · rw [measureOrCollisionProb_andHash _ _ _ _ (hmeas x x')]
    exact hfar _ (measureCollisionProb_nonneg _ _ _ _) (h.le_of_far x x' hx)

end Cslib.Probability
