/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Product
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Probability.Moments.SubGaussian
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.Product.Resample
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# McDiarmid's bounded-differences inequality

A real function of several coordinates has bounded differences `c` when changing coordinate `i`
alone changes its value by at most `c i`. If the coordinates are independent, such a function
concentrates around its mean: it exceeds the mean by `ε`, or falls short of it by `ε`, each with
probability at most `exp (-2 ε² / ∑ i, c i ^ 2)` [McDiarmid, Lemma 1.2][McDiarmid1989]. For a sum
of bounded independent scores this is Hoeffding's inequality [Hoeffding1963].

The proof bounds the moment generating function of `f - 𝔼 f` by `exp (t² ∑ i, c i ^ 2 / 8)`, by
induction on the set of coordinates already averaged out. Averaging out one more coordinate `i`
changes the partial average by a mean-zero amount that lies in an interval of length `c i`, so
Hoeffding's lemma (Mathlib's `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`) bounds its
contribution by `exp (t² c i ^ 2 / 8)`. This is the Doob martingale argument, with the martingale
written as iterated finite averages. The tail bounds are finite-PMF event probabilities;
`HasBoundedDifferences.hasSubgaussianMGF_pi` records the sub-Gaussian bound in Mathlib's form.

## Main definitions

* `Cslib.Probability.HasBoundedDifferences`: changing one coordinate changes the value boundedly.

## Main results

* `Cslib.Probability.hasBoundedDifferences_sum`: sums of bounded coordinate scores.
* `Cslib.Probability.HasBoundedDifferences.ciSup`, `Cslib.Probability.HasBoundedDifferences.expect`:
  pointwise suprema and uniform averages of families with bounded differences.
* `Cslib.Probability.HasBoundedDifferences.sum_pi_mul_exp_le`: the moment generating function
  bound.
* `Cslib.Probability.HasBoundedDifferences.hasSubgaussianMGF_pi`: the sub-Gaussian form.
* `Cslib.Probability.HasBoundedDifferences.pi_ge_mean_add`,
  `Cslib.Probability.HasBoundedDifferences.pi_le_mean_sub`: McDiarmid's inequality for the upper
  and lower tails.
* `Cslib.Probability.HasBoundedDifferences.pi_abs_sub_mean_ge`: the two-sided bound.

## References

* [C. McDiarmid, *On the method of bounded differences*][McDiarmid1989], Lemma 1.2
* [W. Hoeffding, *Probability inequalities for sums of bounded random
  variables*][Hoeffding1963]
-/

@[expose] public section

namespace Cslib.Probability

open MeasureTheory ProbabilityTheory Cslib.Probability.PMF
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι] {α : ι → Type*}

/-- A function of several coordinates has bounded differences `c` if changing coordinate `i`
alone changes its value by at most `c i`. -/
def HasBoundedDifferences (f : (∀ i, α i) → ℝ) (c : ι → ℝ) : Prop :=
  ∀ x i (a : α i), |f (Function.update x i a) - f x| ≤ c i

namespace HasBoundedDifferences

variable {f : (∀ i, α i) → ℝ} {c : ι → ℝ}

/-- Negation preserves bounded differences. -/
theorem neg (hf : HasBoundedDifferences f c) : HasBoundedDifferences (fun x => -f x) c :=
  fun x i a => by simpa only [neg_sub_neg, abs_sub_comm] using hf x i a

/-- A pointwise supremum of a family of functions with bounded differences `c` has bounded
differences `c`, provided the family is bounded above at every point. -/
theorem ciSup {κ : Type*} {g : κ → (∀ i, α i) → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hg : ∀ k, HasBoundedDifferences (g k) c) (hbdd : ∀ x, BddAbove (Set.range fun k => g k x)) :
    HasBoundedDifferences (fun x => ⨆ k, g k x) c := by
  intro x i a
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simpa only [Real.iSup_of_isEmpty, sub_self, abs_zero] using hc i
  rw [abs_sub_le_iff, sub_le_iff_le_add, sub_le_iff_le_add]
  constructor
  · refine ciSup_le fun k => ?_
    linarith [(abs_sub_le_iff.1 (hg k x i a)).1, le_ciSup (hbdd x) k]
  · refine ciSup_le fun k => ?_
    linarith [(abs_sub_le_iff.1 (hg k x i a)).2, le_ciSup (hbdd (Function.update x i a)) k]

/-- A uniform average of functions with bounded differences `c` has bounded differences `c`. -/
theorem expect {κ : Type*} [Fintype κ] {g : κ → (∀ i, α i) → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hg : ∀ k, HasBoundedDifferences (g k) c) :
    HasBoundedDifferences (fun x => 𝔼 k, g k x) c := by
  intro x i a
  rw [← Finset.expect_sub_distrib]
  refine (Finset.abs_expect_le _ _).trans ?_
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simpa only [Finset.univ_eq_empty, Finset.expect_empty] using hc i
  · exact Finset.expect_le Finset.univ_nonempty fun k _ => hg k x i a

end HasBoundedDifferences

/-- A sum of coordinate scores whose `i`-th score varies by at most `c i` has bounded
differences `c`. -/
theorem hasBoundedDifferences_sum [Fintype ι] {score : ∀ i, α i → ℝ} {c : ι → ℝ}
    (hscore : ∀ i a b, |score i a - score i b| ≤ c i) :
    HasBoundedDifferences (fun x => ∑ i, score i (x i)) c := by
  intro x i a
  have hrest : ∑ j ∈ Finset.univ.erase i, score j (Function.update x i a j) =
      ∑ j ∈ Finset.univ.erase i, score j (x j) :=
    Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  change |∑ j, score j (Function.update x i a j) - ∑ j, score j (x j)| ≤ c i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self, hrest,
    add_sub_add_right_eq_sub]
  exact hscore i a (x i)

/-! ### Hoeffding's lemma and partial averages -/

/-- Hoeffding's lemma for a finite distribution: a score with values in `[a, b]` has centered
moment generating function at most `exp (t² (b - a)² / 8)`. -/
private theorem sum_mul_exp_sub_mean_le {β : Type*} [Fintype β] (q : PMF β) (g : β → ℝ)
    {a b : ℝ} (hg : ∀ v, g v ∈ Set.Icc a b) (t : ℝ) :
    ∑ v, (q v).toReal * Real.exp (t * (g v - ∑ w, (q w).toReal * g w)) ≤
      Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by
  let _ : MeasurableSpace β := ⊤
  have h := (hasSubgaussianMGF_of_mem_Icc (μ := q.toMeasure)
    (measurable_of_countable g).aemeasurable (ae_of_all _ hg)).mgf_le t
  simp only [mgf, PMF.integral_eq_sum, smul_eq_mul] at h
  refine h.trans_eq (congrArg Real.exp ?_)
  simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat,
    div_pow, sq_abs]
  ring

/-- The coordinates of `y` outside `s` do not affect `s.piecewise y z`. -/
private theorem piecewise_update_left {s : Finset ι} {i : ι} (hi : i ∉ s) (y z : ∀ i, α i)
    (v : α i) : s.piecewise (Function.update y i v) z = s.piecewise y z :=
  s.piecewise_congr (fun _ hj => Function.update_of_ne (ne_of_mem_of_not_mem hj hi) ..)
    fun _ _ => rfl

variable [Fintype ι] [∀ i, Fintype (α i)]

/-- Averaging over a product while overwriting the coordinates in `insert i s` is averaging
first over coordinate `i` and then over the coordinates in `s`. -/
private theorem sum_pi_piecewise_insert (p : ∀ i, PMF (α i)) {s : Finset ι} {i : ι}
    (hi : i ∉ s) (x : ∀ i, α i) (F : (∀ i, α i) → ℝ) :
    ∑ y, (pi p y).toReal * F ((insert i s).piecewise y x) =
      ∑ v, (p i v).toReal *
        ∑ y, (pi p y).toReal * F (s.piecewise y (Function.update x i v)) := by
  have hsplit (y : ∀ i, α i) :
      (insert i s).piecewise y x = s.piecewise y (Function.update x i (y i)) := by
    rw [Finset.piecewise_insert, Finset.update_piecewise_of_notMem _ _ _ hi]
  simp only [hsplit]
  conv_lhs => rw [← pi_bind_update p i]
  rw [sum_bind_mul]
  refine Finset.sum_congr rfl fun v _ => congrArg _ ?_
  rw [pi_update_pure, sum_map_mul]
  simp only [Function.update_self, piecewise_update_left hi]

/-- The moment generating function bound after averaging out the coordinates in `s`, with the
remaining coordinates fixed to those of `x`. -/
private theorem sum_mul_exp_piecewise_le {f : (∀ i, α i) → ℝ} {c : ι → ℝ}
    (hf : HasBoundedDifferences f c) (p : ∀ i, PMF (α i)) (t : ℝ) (s : Finset ι)
    (x : ∀ i, α i) :
    ∑ y, (pi p y).toReal * Real.exp (t * (f (s.piecewise y x) -
      ∑ z, (pi p z).toReal * f (s.piecewise z x))) ≤
        Real.exp (t ^ 2 * (∑ i ∈ s, c i ^ 2) / 8) := by
  induction s using Finset.induction_on generalizing x with
  | empty =>
    simp only [Finset.piecewise_empty, ← Finset.sum_mul, sum_toReal, one_mul, sub_self,
      mul_zero, Real.exp_zero, Finset.sum_empty, zero_div, le_refl]
  | insert i s hi ih =>
    let g (v : α i) := ∑ z, (pi p z).toReal * f (s.piecewise z (Function.update x i v))
    have hrange (v w : α i) : g v ≤ g w + c i := by
      have hdiff : g v - g w = ∑ z, (pi p z).toReal *
          (f (s.piecewise z (Function.update x i v)) -
            f (s.piecewise z (Function.update x i w))) := by
        simp only [g, ← Finset.sum_sub_distrib, mul_sub]
      have hle : g v - g w ≤ c i := by
        rw [hdiff]
        refine sum_mul_le _ _ _ fun z => ?_
        rw [← Finset.update_piecewise_of_notMem _ _ _ hi,
          ← Finset.update_piecewise_of_notMem _ _ _ hi,
          ← Function.update_idem w v (s.piecewise z x)]
        exact (le_abs_self _).trans (hf _ i v)
      linarith
    obtain ⟨least, -, hleast⟩ := Finset.univ.exists_min_image g
      (Finset.univ_nonempty_iff.mpr ⟨(p i).support_nonempty.some⟩)
    have hhoeffding := sum_mul_exp_sub_mean_le (p i) g
      (fun v => ⟨hleast v (Finset.mem_univ v), hrange v least⟩) t
    rw [add_sub_cancel_left] at hhoeffding
    have hstep (v : α i) : ∑ y, (pi p y).toReal * Real.exp (t * (f (s.piecewise y
        (Function.update x i v)) - ∑ w, (p i w).toReal * g w)) ≤
          Real.exp (t * (g v - ∑ w, (p i w).toReal * g w)) *
            Real.exp (t ^ 2 * (∑ j ∈ s, c j ^ 2) / 8) := by
      calc
        _ = Real.exp (t * (g v - ∑ w, (p i w).toReal * g w)) * ∑ y, (pi p y).toReal *
            Real.exp (t * (f (s.piecewise y (Function.update x i v)) - g v)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [mul_left_comm, ← Real.exp_add]
          ring_nf
        _ ≤ _ := mul_le_mul_of_nonneg_left (ih (Function.update x i v)) (Real.exp_pos _).le
    rw [sum_pi_piecewise_insert p hi x f,
      sum_pi_piecewise_insert p hi x fun z => Real.exp (t * (f z - ∑ v, (p i v).toReal * g v))]
    calc
      _ ≤ ∑ v, (p i v).toReal * (Real.exp (t * (g v - ∑ w, (p i w).toReal * g w)) *
          Real.exp (t ^ 2 * (∑ j ∈ s, c j ^ 2) / 8)) :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hstep v) ENNReal.toReal_nonneg
      _ = (∑ v, (p i v).toReal * Real.exp (t * (g v - ∑ w, (p i w).toReal * g w))) *
          Real.exp (t ^ 2 * (∑ j ∈ s, c j ^ 2) / 8) := by
        rw [Finset.sum_mul]
        simp only [mul_assoc]
      _ ≤ Real.exp (t ^ 2 * c i ^ 2 / 8) * Real.exp (t ^ 2 * (∑ j ∈ s, c j ^ 2) / 8) :=
        mul_le_mul_of_nonneg_right hhoeffding (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add, Finset.sum_insert hi]
        ring_nf

/-! ### McDiarmid's inequality -/

namespace HasBoundedDifferences

variable {f : (∀ i, α i) → ℝ} {c : ι → ℝ}

/-- **The bounded-differences moment bound.** For independent coordinates, a function with
bounded differences `c` has centered moment generating function at most
`exp (t² ∑ i, c i ^ 2 / 8)`. -/
theorem sum_pi_mul_exp_le (hf : HasBoundedDifferences f c) (p : ∀ i, PMF (α i)) (t : ℝ) :
    ∑ x, (pi p x).toReal * Real.exp (t * (f x - ∑ y, (pi p y).toReal * f y)) ≤
      Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
  obtain ⟨x, -⟩ := (pi p).support_nonempty
  simpa only [Finset.piecewise_univ] using sum_mul_exp_piecewise_le hf p t Finset.univ x

/-- A function of independent coordinates with bounded differences `c` is sub-Gaussian about
its mean with variance proxy `∑ i, (c i / 2) ^ 2`. -/
theorem hasSubgaussianMGF_pi [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (hf : HasBoundedDifferences f c) (p : ∀ i, PMF (α i)) :
    HasSubgaussianMGF (fun x => f x - ∑ y, (pi p y).toReal * f y)
      (∑ i, (‖c i‖₊ / 2) ^ 2) (pi p).toMeasure where
  integrable_exp_mul _ := Integrable.of_finite
  mgf_le t := by
    rw [mgf, PMF.integral_eq_sum]
    refine (hf.sum_pi_mul_exp_le p t).trans_eq (congrArg Real.exp ?_)
    simp only [NNReal.coe_sum, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm,
      Real.norm_eq_abs, NNReal.coe_ofNat, div_pow, sq_abs, ← Finset.sum_div]
    ring

/-- **McDiarmid's inequality**, upper tail [McDiarmid, Lemma 1.2][McDiarmid1989]: a function of
independent coordinates with bounded differences `c` exceeds its mean by `ε` with probability at
most `exp (-2 ε² / ∑ i, c i ^ 2)`. -/
theorem pi_ge_mean_add (hf : HasBoundedDifferences f c) (p : ∀ i, PMF (α i)) {ε : ℝ}
    (hε : 0 ≤ ε) :
    ((pi p).toOuterMeasure {x | (∑ y, (pi p y).toReal * f y) + ε ≤ f x}).toReal ≤
      Real.exp (-2 * ε ^ 2 / ∑ i, c i ^ 2) := by
  let (i : ι) : MeasurableSpace (α i) := ⊤
  have h := (hf.hasSubgaussianMGF_pi p).measure_ge_le hε
  have hevent : {x : ∀ i, α i | ε ≤ f x - ∑ y, (pi p y).toReal * f y} =
      {x | (∑ y, (pi p y).toReal * f y) + ε ≤ f x} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [hevent, measureReal_def, PMF.toMeasure_apply_eq_toOuterMeasure_apply _
    ((Set.to_countable _).measurableSet)] at h
  refine h.trans_eq (congrArg Real.exp ?_)
  simp only [NNReal.coe_sum, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs,
    NNReal.coe_ofNat, div_pow, sq_abs, ← Finset.sum_div]
  ring

/-- **McDiarmid's inequality**, lower tail: a function of independent coordinates with bounded
differences `c` falls below its mean by `ε` with probability at most
`exp (-2 ε² / ∑ i, c i ^ 2)`. -/
theorem pi_le_mean_sub (hf : HasBoundedDifferences f c) (p : ∀ i, PMF (α i)) {ε : ℝ}
    (hε : 0 ≤ ε) :
    ((pi p).toOuterMeasure {x | f x ≤ (∑ y, (pi p y).toReal * f y) - ε}).toReal ≤
      Real.exp (-2 * ε ^ 2 / ∑ i, c i ^ 2) := by
  have h := hf.neg.pi_ge_mean_add p hε
  have hevent : {x : ∀ i, α i | (∑ y, (pi p y).toReal * -f y) + ε ≤ -f x} =
      {x | f x ≤ (∑ y, (pi p y).toReal * f y) - ε} := by
    ext x
    simp only [Set.mem_ofPred_eq, mul_neg, Finset.sum_neg_distrib]
    constructor <;> intro h <;> linarith
  rwa [hevent] at h

/-- **McDiarmid's inequality**, two-sided: a function of independent coordinates with bounded
differences `c` deviates from its mean by `ε` with probability at most
`2 exp (-2 ε² / ∑ i, c i ^ 2)`. -/
theorem pi_abs_sub_mean_ge (hf : HasBoundedDifferences f c) (p : ∀ i, PMF (α i)) {ε : ℝ}
    (hε : 0 ≤ ε) :
    ((pi p).toOuterMeasure {x | ε ≤ |f x - ∑ y, (pi p y).toReal * f y|}).toReal ≤
      2 * Real.exp (-2 * ε ^ 2 / ∑ i, c i ^ 2) := by
  linarith [toOuterMeasure_abs_sub_ge_toReal_le (pi p) f (∑ y, (pi p y).toReal * f y) ε,
    hf.pi_ge_mean_add p hε, hf.pi_le_mean_sub p hε]

end HasBoundedDifferences

end Cslib.Probability
