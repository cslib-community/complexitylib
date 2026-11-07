/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Probability.PMF
public import Mathlib.Probability.ProductMeasure

/-!
# Fair coin flips

`Cslib.Probability.coinFlips` is the probability measure on infinite bit tapes `ℕ → Bool` under
which the bits are independent fair coins: the product `MeasureTheory.Measure.infinitePi` of
uniform distributions on `Bool`. An event determined by the first `N` bits of the tape has
probability equal to the fraction of the `2 ^ N` words of length `N` that it contains
(`coinFlips_setOf_eq_card_mul`); a word `y : Fin N → Bool` is read as a tape by padding it with
`false`, as `Function.extend Fin.val y fun _ => false`. This reduces probabilistic statements about
algorithms reading a bounded prefix of a random tape to counting words.

## Main definitions

* `Cslib.Probability.coinFlips`: independent fair coin flips.
* `Cslib.Probability.prefixCylinder`: the tapes beginning with a given word.

## Main results

* `Cslib.Probability.coinFlips_prefixCylinder`: a given word of length `N` begins the tape with
  probability `2⁻ᴺ`.
* `Cslib.Probability.measurableSet_setOf_of_prefix`,
  `Cslib.Probability.coinFlips_setOf_eq_card_mul`: events determined by a prefix of the tape are
  measurable, with probability the fraction of the words in them.
-/

public section

namespace Cslib.Probability

open MeasureTheory Finset

/-- Independent fair coin flips: the product of uniform distributions on `Bool`. -/
noncomputable def coinFlips : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ => (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure coinFlips := by
  unfold coinFlips
  infer_instance

private theorem toMeasure_uniformOfFintype_bool_singleton (b : Bool) :
    (PMF.uniformOfFintype Bool).toMeasure {b} = 2⁻¹ := by
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton b), PMF.uniformOfFintype_apply,
    Fintype.card_bool, Nat.cast_ofNat]

/-- The tapes beginning with the word `y`. -/
def prefixCylinder {N : ℕ} (y : Fin N → Bool) : Set (ℕ → Bool) := {x | ∀ i : Fin N, x i = y i}

theorem mem_prefixCylinder {N : ℕ} {y : Fin N → Bool} {x : ℕ → Bool} :
    x ∈ prefixCylinder y ↔ ∀ i : Fin N, x i = y i :=
  Iff.rfl

private theorem extend_val_of_lt {N : ℕ} (y : Fin N → Bool) {i : ℕ} (hi : i < N) :
    Function.extend Fin.val y (fun _ => false) i = y ⟨i, hi⟩ :=
  Fin.val_injective.extend_apply y _ ⟨i, hi⟩

theorem prefixCylinder_eq_pi {N : ℕ} (y : Fin N → Bool) :
    prefixCylinder y =
      Set.pi (range N : Set ℕ) fun i => {Function.extend Fin.val y (fun _ => false) i} := by
  ext x
  simp only [mem_prefixCylinder, Set.mem_pi, coe_range, Set.mem_Iio, Set.mem_singleton_iff]
  constructor
  · intro h i hi
    rw [extend_val_of_lt y hi]
    exact h ⟨i, hi⟩
  · intro h i
    rw [h i i.2, extend_val_of_lt y i.2]

theorem measurableSet_prefixCylinder {N : ℕ} (y : Fin N → Bool) :
    MeasurableSet (prefixCylinder y) := by
  rw [prefixCylinder_eq_pi]
  exact MeasurableSet.pi (range N).countable_toSet fun _ _ => MeasurableSet.singleton _

/-- A given word of length `N` begins the tape with probability `2⁻ᴺ`. -/
theorem coinFlips_prefixCylinder {N : ℕ} (y : Fin N → Bool) :
    coinFlips (prefixCylinder y) = (2 ^ N)⁻¹ := by
  rw [prefixCylinder_eq_pi, coinFlips, Measure.infinitePi_pi _ fun _ _ => MeasurableSet.singleton _]
  simp only [toMeasure_uniformOfFintype_bool_singleton, prod_const, card_range, ENNReal.inv_pow]

/-- An event determined by the first `N` bits of the tape is the union of the cylinders of the words
of length `N` in it. -/
theorem setOf_eq_biUnion_prefixCylinder {N : ℕ} {P : (ℕ → Bool) → Prop} [DecidablePred P]
    (hP : ∀ x y : ℕ → Bool, (∀ i < N, x i = y i) → (P x ↔ P y)) :
    {x | P x} = ⋃ y ∈ ({y : Fin N → Bool | P (Function.extend Fin.val y fun _ => false)} :
      Finset _), prefixCylinder y := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, mem_filter, mem_univ, true_and,
    mem_prefixCylinder]
  constructor
  · intro hx
    refine ⟨fun i => x i, (hP _ _ fun i hi => ?_).1 hx, fun i => rfl⟩
    rw [extend_val_of_lt _ hi]
  · rintro ⟨y, hy, hx⟩
    refine (hP _ _ fun i hi => ?_).2 hy
    rw [extend_val_of_lt _ hi]
    exact hx ⟨i, hi⟩

/-- An event determined by the first `N` bits of the tape is measurable. -/
theorem measurableSet_setOf_of_prefix {N : ℕ} {P : (ℕ → Bool) → Prop}
    (hP : ∀ x y : ℕ → Bool, (∀ i < N, x i = y i) → (P x ↔ P y)) : MeasurableSet {x | P x} := by
  classical
  rw [setOf_eq_biUnion_prefixCylinder hP]
  exact Finset.measurableSet_biUnion _ fun y _ => measurableSet_prefixCylinder y

/-- The probability of an event determined by the first `N` bits of the tape is the fraction of the
words of length `N` in it. -/
theorem coinFlips_setOf_eq_card_mul {N : ℕ} {P : (ℕ → Bool) → Prop} [DecidablePred P]
    (hP : ∀ x y : ℕ → Bool, (∀ i < N, x i = y i) → (P x ↔ P y)) :
    coinFlips {x | P x} =
      #{y : Fin N → Bool | P (Function.extend Fin.val y fun _ => false)} * (2 ^ N)⁻¹ := by
  rw [setOf_eq_biUnion_prefixCylinder hP, measure_biUnion_finset]
  · simp only [coinFlips_prefixCylinder, sum_const, nsmul_eq_mul]
  · intro y _ y' _ hyy'
    refine Set.disjoint_left.2 fun x hx hx' => hyy' (funext fun i => ?_)
    rw [← mem_prefixCylinder.1 hx i, ← mem_prefixCylinder.1 hx' i]
  · exact fun y _ => measurableSet_prefixCylinder y

end Cslib.Probability
