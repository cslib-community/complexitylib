/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Map
public import CslibFrontier.Probability.Conditioning
public import Mathlib.Probability.Independence.Basic
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi

/-!
# Independent finite PMF products

A product of finite distributions assigns each tuple the product of its coordinate masses.
Its induced measure is Mathlib's product measure, so its coordinates satisfy the
independence and concentration theorems. Mapping coordinates commutes with this product.
Replacing one coordinate of a uniform tuple by a fresh uniform sample preserves its law.

## Main definitions

* `Cslib.Probability.PMF.pi`: independent finite products with dependent coordinate types.

## Main results

* `Cslib.Probability.PMF.toMeasure_pi`, `.toMeasure_bind_pair`, `.iIndepFun_pi`: product-measure
  and independence laws.
* `Cslib.Probability.PMF.sum_pi_mul_eval`, `Cslib.Probability.PMF.sum_pi_mul_sum`: expectation of
  coordinate functions and their sums under `pi p`.
* `Cslib.Probability.PMF.uniformOfFintype_update`, `.bind_uniformOfFintype_update`: replacing one
  coordinate of a uniform tuple by an independent uniform sample.
* `Cslib.Probability.PMF.pi_bind_update_pair`: reveal a coordinate and retain the entire tuple.
* `Cslib.Probability.PMF.pi_map`, `.pi_bind`: coordinatewise mapping and sampling laws.
* `Cslib.Probability.PMF.conditionalSnd_pi_joint`: coordinatewise conditioning.

## References

Adapted from Probability/Product.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`. The measure and independence results reuse Mathlib.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open MeasureTheory ProbabilityTheory

/-- Independent PMF samples induce the product of their measures. -/
theorem toMeasure_bind_pair {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Countable α] [Countable β] (p : PMF α) (q : PMF β) :
    (p.bind (fun a => q.map (fun b => (a, b)))).toMeasure =
      p.toMeasure.prod q.toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    bind_map_prodMk_apply]

variable {ι : Type*} [Fintype ι] {α β : ι → Type*} [∀ i, Finite (α i)]

open Classical in
/-- Draw each coordinate independently from its specified finite distribution. -/
noncomputable def pi (p : ∀ i, PMF (α i)) : PMF (∀ i, α i) :=
  let (i : ι) := Fintype.ofFinite (α i)
  PMF.ofFintype (fun outcome => ∏ i, p i (outcome i)) (by
    have hsum (i : ι) : ∑ a, p i a = 1 := by simpa only [tsum_fintype] using (p i).tsum_coe
    rw [← Fintype.prod_sum (fun i a => p i a)]
    simp only [hsum, Finset.prod_const_one])

/-- Independent tuple masses are products of their coordinate masses. -/
@[simp] theorem pi_apply (p : ∀ i, PMF (α i)) (outcome : ∀ i, α i) :
    pi p outcome = ∏ i, p i (outcome i) := rfl

/-- A tuple can occur precisely when every coordinate can occur. -/
theorem mem_support_pi_iff (p : ∀ i, PMF (α i)) (outcome : ∀ i, α i) :
    outcome ∈ (pi p).support ↔ ∀ i, outcome i ∈ (p i).support := by
  classical
  simp only [PMF.mem_support_iff, pi_apply, Finset.prod_ne_zero_iff, Finset.mem_univ,
    forall_const]

/-- The PMF product agrees with the measure-theoretic product. -/
theorem toMeasure_pi [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (p : ∀ i, PMF (α i)) :
    (pi p).toMeasure = Measure.pi (fun i => (p i).toMeasure) := by
  apply Measure.ext_of_singleton
  intro outcome
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), Measure.pi_singleton,
    pi_apply]

/-- Coordinate projections of the product are mutually independent. -/
theorem iIndepFun_pi [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (p : ∀ i, PMF (α i)) :
    iIndepFun (fun i (outcome : ∀ i, α i) => outcome i) (pi p).toMeasure := by
  rw [toMeasure_pi]
  exact ProbabilityTheory.iIndepFun_pi (fun _ => measurable_id.aemeasurable)

/-- Each coordinate of the independent product has its specified distribution. -/
@[simp] theorem pi_map_eval (p : ∀ i, PMF (α i)) (i : ι) :
    (pi p).map (fun outcome => outcome i) = p i := by
  let (i : ι) : MeasurableSpace (α i) := ⊤
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_pi_apply i), toMeasure_pi]
  exact (measurePreserving_eval (fun i => (p i).toMeasure) i).map_eq

/-- The expectation of a function of coordinate `i` under the product distribution `pi p` is its
expectation under `p i`. -/
theorem sum_pi_mul_eval [DecidableEq ι] [∀ i, Fintype (α i)] (p : ∀ i, PMF (α i)) (i : ι)
    (f : α i → ℝ) :
    ∑ x, (pi p x).toReal * f (x i) = ∑ a, (p i a).toReal * f a := by
  rw [← sum_map_mul (pi p) (fun x => x i) f, pi_map_eval]

/-- Linearity of expectation for a sum of coordinate functions under the product distribution
`pi p`. -/
theorem sum_pi_mul_sum [DecidableEq ι] [∀ i, Fintype (α i)] (p : ∀ i, PMF (α i))
    (score : ∀ i, α i → ℝ) :
    ∑ x, (pi p x).toReal * ∑ i, score i (x i) =
      ∑ i, ∑ a, (p i a).toReal * score i a := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => sum_pi_mul_eval p i (score i)

/-- Independent uniform coordinates give the uniform distribution on tuples. -/
theorem pi_uniformOfFintype [DecidableEq ι] [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] :
    pi (fun i => PMF.uniformOfFintype (α i)) = PMF.uniformOfFintype (∀ i, α i) := by
  ext outcome
  simp only [pi_apply, PMF.uniformOfFintype_apply, Fintype.card_pi, Nat.cast_prod]
  symm
  exact ENNReal.prod_inv_distrib (by intro i hi j hj hij; right; simp)

/-- Replacing one coordinate of a uniform tuple by a fresh uniform draw preserves its law.
The other coordinates stay independent of the replacement. -/
theorem uniformOfFintype_update [DecidableEq ι] {γ : Type*} [Fintype γ] [Nonempty γ] (i : ι) :
    (PMF.uniformOfFintype γ).bind (fun value =>
      (PMF.uniformOfFintype (ι → γ)).map (fun values => Function.update values i value)) =
        PMF.uniformOfFintype (ι → γ) := by
  let swap (pair : γ × (ι → γ)) := (pair.2 i, Function.update pair.2 i pair.1)
  have hswap : Function.Involutive swap := by
    rintro ⟨value, values⟩
    simp [swap]
  have h := congrArg (PMF.map Prod.snd)
    (uniformOfFintype_map_equiv hswap.toPerm)
  simpa [PMF.map_comp, ← uniformOfFintype_prod, PMF.map_bind, Function.comp_def, swap,
    PMF.map, PMF.bind_const] using h

/-- Replacing one coordinate of a uniform tuple by an independent uniform value preserves the law
of any experiment on the tuple. -/
theorem bind_uniformOfFintype_update [DecidableEq ι] {γ δ : Type*} [Fintype γ] [Nonempty γ]
    (i : ι) (F : (ι → γ) → PMF δ) :
    (PMF.uniformOfFintype (ι → γ)).bind F =
      (PMF.uniformOfFintype γ).bind fun value =>
        (PMF.uniformOfFintype (ι → γ)).bind fun values =>
          F (Function.update values i value) := by
  conv_lhs => rw [← uniformOfFintype_update i]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]

/-- Applying a separate function to each coordinate preserves the product structure. -/
theorem pi_map [∀ i, Finite (β i)] (p : ∀ i, PMF (α i)) (f : ∀ i, α i → β i) :
    pi (fun i => (p i).map (f i)) = (pi p).map (fun outcome i => f i (outcome i)) := by
  classical
  let (i : ι) := Fintype.ofFinite (α i)
  let (i : ι) := Fintype.ofFinite (β i)
  ext result
  simp only [pi_apply, PMF.map_apply, tsum_fintype]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases h : result = fun i => f i (outcome i)
  · subst result
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, result i ≠ f i (outcome i) := by
      simpa only [funext_iff, not_forall] using h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Independent conditional samples can be drawn after the complete tuple of their inputs. -/
theorem pi_bind [∀ i, Finite (β i)] (p : ∀ i, PMF (α i))
    (kernel : ∀ i, α i → PMF (β i)) :
    pi (fun i => (p i).bind (kernel i)) =
      (pi p).bind (fun outcome => pi (fun i => kernel i (outcome i))) := by
  classical
  let (i : ι) := Fintype.ofFinite (α i)
  let (i : ι) := Fintype.ofFinite (β i)
  ext result
  simp only [pi_apply, PMF.bind_apply, tsum_fintype]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

/-- One coordinate of an independent product may be sampled first and then held fixed. -/
theorem pi_bind_update [DecidableEq ι] (p : ∀ i, PMF (α i)) (i : ι) :
    (p i).bind (fun value => pi (Function.update p i (PMF.pure value))) = pi p := by
  classical
  ext outcome
  have mass (value : α i) :
      pi (Function.update p i (PMF.pure value)) outcome =
        PMF.pure value (outcome i) * ∏ j ∈ Finset.univ.erase i, p j (outcome j) := by
    rw [pi_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    exact Finset.prod_congr rfl (fun j hj => by
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1])
  rw [PMF.bind_apply, tsum_eq_single (outcome i)]
  · simp only [mass, PMF.pure_apply_self, one_mul, pi_apply]
    exact Finset.mul_prod_erase _ (fun j => p j (outcome j)) (Finset.mem_univ i)
  · intro value hvalue
    simp [mass, PMF.pure_apply, hvalue.symm]

/-- Revealing one coordinate and retaining the tuple is equivalent to sampling that coordinate
first, then independently completing the remaining coordinates. -/
theorem pi_bind_update_pair [DecidableEq ι] (p : ∀ i, PMF (α i)) (i : ι) :
    (p i).bind (fun value =>
      (pi (Function.update p i (PMF.pure value))).map (value, ·)) =
        (pi p).map (fun outcome => (outcome i, outcome)) := by
  conv_rhs => rw [← pi_bind_update p i, PMF.map_bind]
  congr 1
  funext value
  apply map_congr_on_support
  intro outcome houtcome
  have h := (mem_support_pi_iff _ _).mp houtcome i
  simp only [Function.update_self, PMF.mem_support_pure_iff] at h
  rw [h]

/-- Sampling one coordinate `v ← p i` and completing the remaining coordinates via
`pi (Function.update p i (PMF.pure v))` equals sampling `G ← pi p` and reading `(G i, G)`. -/
theorem bind_pi_update {γ : Type*} [DecidableEq ι] (p : ∀ i, PMF (α i)) (i : ι)
    (F : α i → (∀ j, α j) → PMF γ) :
    (p i).bind (fun value => (pi (Function.update p i (PMF.pure value))).bind (F value)) =
      (pi p).bind (fun outcome => F (outcome i) outcome) := by
  have h := congrArg (fun q : PMF (α i × ∀ j, α j) => q.bind (fun x => F x.fst x.snd))
    (pi_bind_update_pair p i)
  simpa only [PMF.bind_bind, PMF.bind_map, Function.comp_def] using h

/-- Split an independent finite sequence into its first draw and its remaining draws. -/
theorem pi_fin_succ {γ : Type*} [Finite γ] (count : ℕ) (p : PMF γ) :
    pi (fun _ : Fin (count + 1) => p) =
      p.bind (fun first => (pi (fun _ : Fin count => p)).map (Fin.cons first)) := by
  let e := Fin.consEquiv (fun _ : Fin (count + 1) => γ)
  calc
    _ = (p.bind (fun first => (pi (fun _ : Fin count => p)).map (first, ·))).map e := by
      ext outcome
      rw [map_equiv_apply, bind_map_prodMk_apply]
      exact Fin.prod_univ_succ (fun i => p (outcome i))
    _ = _ := by
      simp [PMF.map_bind, PMF.map_comp, Function.comp_def, e, Fin.consEquiv]

/-- Independent pairs can be sampled by drawing their first components, then drawing each
second component conditionally and independently. -/
theorem pi_bind_pair [∀ i, Finite (β i)] (p : ∀ i, PMF (α i))
    (kernel : ∀ i, α i → PMF (β i)) :
    (pi (fun i => (p i).bind (fun a => (kernel i a).map (a, ·)))).map
        (fun outcome => (fun i => (outcome i).1, fun i => (outcome i).2)) =
      (pi p).bind (fun outcome => (pi (fun i => kernel i (outcome i))).map (outcome, ·)) := by
  rw [pi_bind, PMF.map_bind]
  congr 1
  funext outcome
  rw [pi_map, PMF.map_comp]
  rfl

/-- Independent joint samples can be drawn by first drawing all observations and then drawing
the hidden coordinates independently from their conditional distributions. -/
theorem pi_joint_eq_bind_conditionalSnd [∀ i, Finite (β i)]
    (joint : ∀ i, PMF (α i × β i)) :
    (pi joint).map (fun outcome => (fun i => (outcome i).1, fun i => (outcome i).2)) =
      (pi (fun i => (joint i).map Prod.fst)).bind (fun observed =>
        (pi (fun i => conditionalSnd (joint i) (observed i))).map (observed, ·)) := by
  simpa only [bind_conditionalSnd] using
    pi_bind_pair (fun i => (joint i).map Prod.fst) (fun i => conditionalSnd (joint i))

/-- Conditioning independent joint samples on a possible observation tuple preserves independence
of their hidden coordinates. -/
theorem conditionalSnd_pi_joint [∀ i, Finite (β i)]
    (joint : ∀ i, PMF (α i × β i)) (observed : ∀ i, α i)
    (hobserved : observed ∈ (pi (fun i => (joint i).map Prod.fst)).support) :
    conditionalSnd ((pi joint).map
      (fun outcome => (fun i => (outcome i).1, fun i => (outcome i).2))) observed =
        pi (fun i => conditionalSnd (joint i) (observed i)) := by
  rw [pi_joint_eq_bind_conditionalSnd, conditionalSnd_bind_pair _ _ _ hobserved]

end Cslib.Probability.PMF
