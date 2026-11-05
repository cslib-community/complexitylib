/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Bernoulli
public import Complexity.Probability.PMF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Stochastic domination after independent thinning

Fang and Wang's Theorem 1.2, STOC 2027 submission 1278, PDF page 2 [FangWang2026],
states that the independent `t`-thinning of a `q`-spread random set is stochastically dominated
by a Bernoulli product set of density `p` whenever `t q (1 - p) ≤ p (1 - t)`.

`thinning_le_bernoulli` proves this comparison for every increasing event on a finite ground
set. `pmf_thinning_le_bernoulli` specializes the parent weights to a probability mass function.
The left side is an iterated expectation: the retention mask is independent of the parent,
whose coordinates need not be independent. `thinning_le_bernoulli_explicit_density` gives
the paper's density `t q / (1 - t + t q)`, and `thinning_le_bernoulli_of_alpha` gives
Corollary 1.3 with the algebraic threshold `α² ≤ 1 - α`.

The source defines stochastic domination through a containing coupling and recalls its
equivalence to comparison on increasing events. We prove the latter formulation; this file
does not construct a coupling or formalize the general finite Strassen equivalence.

The proof follows the source's signed kernel, zero pattern, square majorant and biased Parseval
argument (Lemmas 2.1–3.2, Proposition 3.3 and Section 4, PDF pages 3–5). Centered products
are left unnormalized, avoiding square roots without changing the Fourier argument. The kernel
may be negative when `p < t`; no positivity or probabilistic interpretation of it is assumed.

## Main definitions

* `IsSpread`: upper bounds on the mass of containing each fixed set.
* `retain`: restriction of a deterministic parent to a Boolean retention mask.
* `coordinateKernel`, `kernel`, `lift`: the signed kernel and its action on real scores.

## Main results

* `indicator_retain_le_lift_sq`: pointwise square majorant for increasing events.
* `centered_parseval`: Parseval for unnormalized biased centered products.
* `pmf_thinning_le_bernoulli`: domination after independent thinning, in increasing-event form.
* `thinning_le_bernoulli_of_alpha`: the thinning-conjecture corollary.

## References

* [X. Fang and T. Wang, *A Note on a Result of Chen Li: the Thinning Problem via the
  Kernel Method*][FangWang2026], Theorem 1.2 and Corollary 1.3.
-/

public section

namespace Cslib.Probability.Thinning

open Finset
open scoped BigOperators

/-- The one-coordinate signed kernel. The four entries are those of Lemma 2.1. -/
@[expose] noncomputable def coordinateKernel (t p : ℝ) (x w : Bool) : ℝ :=
  match x, w with
  | false, false => 1 / (1 - t)
  | false, true => (p - t) / (p * (1 - t))
  | true, false => 0
  | true, true => 1 / p

/-- The kernel vanishes on an excluded selected coordinate. -/
@[simp] theorem coordinateKernel_true_false (t p : ℝ) :
    coordinateKernel t p true false = 0 := rfl

/-- Averaging in the target bit normalizes each row, including signed rows. -/
theorem coordinateKernel_average {t p : ℝ} (ht : t ≠ 1) (hp : p ≠ 0) (x : Bool) :
    (1 - p) * coordinateKernel t p x false + p * coordinateKernel t p x true = 1 := by
  have ht' : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  cases x <;> simp only [coordinateKernel] <;> field_simp <;> ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restrict the product kernel to coordinates in the deterministic parent `j`. -/
@[expose] noncomputable def kernel (t p : ℝ) (j : Finset ι) (x w : ι → Bool) : ℝ :=
  ∏ i ∈ j, coordinateKernel t p (x i) (w i)

/-- Independently retaining the coordinates selected by a mask. -/
@[expose] def retain (j : Finset ι) (x : ι → Bool) : Finset ι := j.filter fun i => x i

omit [DecidableEq ι] in
/-- A nonzero product kernel forces containment of the retained parent in the target mask. -/
theorem retain_subset_of_kernel_ne_zero {t p : ℝ} {j : Finset ι} {x w : ι → Bool}
    (h : kernel t p j x w ≠ 0) : retain j x ⊆ univ.filter (fun i => w i) := by
  intro i hi
  rcases mem_filter.mp hi with ⟨hij, hxi⟩
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  cases hwi : w i
  · have hz : kernel t p j x w = 0 := by
      apply prod_eq_zero hij
      simp [coordinateKernel, hxi, hwi]
    exact False.elim (h hz)
  · rfl

/-- The product kernel has total target average one, although it may take negative values. -/
theorem kernel_average {t p : ℝ} (ht : t ≠ 1) (hp : p ≠ 0)
    (j : Finset ι) (x : ι → Bool) :
    BitString.bernoulliAverage p (kernel t p j x) = 1 := by
  have hk (w : ι → Bool) : kernel t p j x w =
      ∏ i, if i ∈ j then coordinateKernel t p (x i) (w i) else 1 := by
    simp [kernel]
  change BitString.bernoulliAverage p (fun w => kernel t p j x w) = 1
  simp_rw [hk]
  rw [BitString.bernoulliAverage_prod p (fun i b =>
    if i ∈ j then coordinateKernel t p (x i) b else 1)]
  have hc (i : ι) :
      (1 - p) * (if i ∈ j then coordinateKernel t p (x i) false else 1) +
        p * (if i ∈ j then coordinateKernel t p (x i) true else 1) = 1 := by
    split_ifs
    · exact coordinateKernel_average ht hp _
    · ring
  simp_rw [hc]
  simp

/-- Apply the signed kernel to a real score on sets. -/
@[expose] noncomputable def lift (t p : ℝ) (j : Finset ι)
    (f : Finset ι → ℝ) (x : ι → Bool) : ℝ :=
  BitString.bernoulliAverage p fun w => kernel t p j x w * f (univ.filter fun i => w i)

/-- The lifted indicator is exactly one when the retained parent belongs to an increasing event. -/
theorem lift_indicator_eq_one {t p : ℝ} (ht : t ≠ 1) (hp : p ≠ 0)
    {U : Set (Finset ι)} (hU : IsUpperSet U) {j : Finset ι} {x : ι → Bool}
    (hx : retain j x ∈ U) : lift t p j (U.indicator 1) x = 1 := by
  have hf (w : ι → Bool) :
      kernel t p j x w * U.indicator (1 : Finset ι → ℝ) (univ.filter fun i => w i) =
        kernel t p j x w := by
    by_cases hk : kernel t p j x w = 0
    · simp [hk]
    · rw [Set.indicator_of_mem (hU (retain_subset_of_kernel_ne_zero hk) hx)]
      simp
  simp only [lift, hf]
  exact kernel_average ht hp j x

/-- **Pointwise square majorant**, Lemma 3.1 of [FangWang2026]. No positivity of the
signed kernel is required. -/
theorem indicator_retain_le_lift_sq {t p : ℝ} (ht : t ≠ 1) (hp : p ≠ 0)
    {U : Set (Finset ι)} (hU : IsUpperSet U) (j : Finset ι) (x : ι → Bool) :
    U.indicator (1 : Finset ι → ℝ) (retain j x) ≤ lift t p j (U.indicator 1) x ^ 2 := by
  by_cases hx : retain j x ∈ U
  · rw [Set.indicator_of_mem hx, lift_indicator_eq_one ht hp hU hx]
    norm_num
  · rw [Set.indicator_of_notMem hx]
    exact sq_nonneg _

/-- Averaging the square majorant in an independent retention mask. This is the first
inequality of Proposition 3.3, before its Fourier expansion. -/
theorem bernoulliAverage_indicator_retain_le {t p : ℝ} (ht : 0 ≤ t) (ht' : t < 1)
    (hp : p ≠ 0) {U : Set (Finset ι)} (hU : IsUpperSet U) (j : Finset ι) :
    BitString.bernoulliAverage t (fun x => U.indicator (1 : Finset ι → ℝ) (retain j x)) ≤
      BitString.bernoulliAverage t (fun x => lift t p j (U.indicator 1) x ^ 2) :=
  BitString.bernoulliAverage_mono ht ht'.le
    (indicator_retain_le_lift_sq ht'.ne hp hU j)


/-- The unnormalized centered product on a set of coordinates. -/
@[expose] noncomputable def centeredProduct (p : ℝ) (s : Finset ι) (x : ι → Bool) : ℝ :=
  ∏ i ∈ s, if x i then 1 - p else -p

/-- Distinct centered products are orthogonal for the biased product measure. -/
theorem centeredProduct_orthogonal (p : ℝ) (s r : Finset ι) :
    BitString.bernoulliAverage p (fun x => centeredProduct p s x * centeredProduct p r x) =
      if s = r then (p * (1 - p)) ^ s.card else 0 := by
  have hc (x : ι → Bool) : centeredProduct p s x * centeredProduct p r x =
      ∏ i, ((if i ∈ s then (if x i then 1 - p else -p) else 1) *
        (if i ∈ r then (if x i then 1 - p else -p) else 1)) := by
    rw [prod_mul_distrib]
    simp only [centeredProduct, Fintype.prod_ite_mem]
  simp_rw [hc]
  rw [BitString.bernoulliAverage_prod p (fun i b =>
    ((if i ∈ s then (if b then 1 - p else -p) else 1) *
      (if i ∈ r then (if b then 1 - p else -p) else 1)))]
  have hlocal (i : ι) :
      (1 - p) * ((if i ∈ s then -p else 1) * (if i ∈ r then -p else 1)) +
        p * ((if i ∈ s then 1 - p else 1) * (if i ∈ r then 1 - p else 1)) =
      if i ∈ s then (if i ∈ r then p * (1 - p) else 0)
        else (if i ∈ r then 0 else 1) := by
    split_ifs <;> ring
  simp only [Bool.false_eq_true, ite_false, ite_true]
  simp_rw [hlocal]
  by_cases hsr : s = r
  · subst r
    simp only [ite_true]
    calc
      _ = ∏ i, if i ∈ s then p * (1 - p) else 1 := by
        apply prod_congr rfl
        intro i _
        split_ifs <;> rfl
      _ = _ := by rw [Fintype.prod_ite_mem]; simp
  · simp only [hsr, ite_false]
    obtain ⟨i, hi⟩ : ∃ i, (i ∈ s ∧ i ∉ r) ∨ (i ∉ s ∧ i ∈ r) := by
      by_contra! h
      apply hsr
      ext i
      exact ⟨(h i).1, fun hi => by
        by_contra hn
        exact (h i).2 hn hi⟩
    apply prod_eq_zero (mem_univ i)
    rcases hi with ⟨hs, hr⟩ | ⟨hs, hr⟩ <;> simp [hs, hr]

/-- Biased, unnormalized Fourier coefficients. -/
@[expose] noncomputable def centeredCoefficient (p : ℝ) (f : Finset ι → ℝ)
    (s : Finset ι) : ℝ :=
  BitString.bernoulliAverage p fun w => f (univ.filter fun i => w i) * centeredProduct p s w

/-- The kernel as a constant plus a product of centered coordinates. -/
theorem coordinateKernel_eq_centered {t p : ℝ} (ht : t ≠ 1) (hp : p ≠ 0) (x w : Bool) :
    coordinateKernel t p x w =
      1 + (if x then 1 - t else -t) * (if w then 1 - p else -p) / (p * (1 - t)) := by
  have ht' : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  cases x <;> cases w <;> simp only [coordinateKernel, Bool.false_eq_true, ite_false, ite_true] <;>
    field_simp <;> ring

omit [Fintype ι] [DecidableEq ι] in
/-- Expansion of the restricted product kernel in centered products. -/
theorem kernel_eq_sum {t p : ℝ} (ht : t ≠ 1) (hp : p ≠ 0)
    (j : Finset ι) (x w : ι → Bool) :
    kernel t p j x w = ∑ s ∈ j.powerset,
      (1 / (p * (1 - t))) ^ s.card * centeredProduct t s x * centeredProduct p s w := by
  simp only [kernel, coordinateKernel_eq_centered ht hp]
  rw [prod_one_add]
  apply sum_congr rfl
  intro s hs
  simp only [div_eq_mul_inv, mul_comm _ ((p * (1 - t))⁻¹),
    prod_mul_distrib, prod_const, centeredProduct]
  ring

/-- The lifted function has the biased centered-product expansion. -/
theorem lift_eq_sum {t p : ℝ} (ht : t ≠ 1) (hp : p ≠ 0)
    (j : Finset ι) (f : Finset ι → ℝ) (x : ι → Bool) :
    lift t p j f x = ∑ s ∈ j.powerset,
      (1 / (p * (1 - t))) ^ s.card * centeredCoefficient p f s * centeredProduct t s x := by
  simp only [lift, kernel_eq_sum ht hp, sum_mul]
  rw [BitString.bernoulliAverage_sum]
  apply sum_congr rfl
  intro s hs
  have he (w : ι → Bool) :
      (1 / (p * (1 - t))) ^ s.card * centeredProduct t s x * centeredProduct p s w *
          f (univ.filter fun i => w i) =
      ((1 / (p * (1 - t))) ^ s.card * centeredProduct t s x) *
        (f (univ.filter fun i => w i) * centeredProduct p s w) := by ring
  simp_rw [he]
  rw [BitString.bernoulliAverage_const_mul]
  unfold centeredCoefficient
  ring


/-- Orthogonality computes the second moment of a finite centered expansion. -/
theorem bernoulliAverage_centered_sum_sq (p : ℝ) (j : Finset ι) (c : Finset ι → ℝ) :
    BitString.bernoulliAverage p (fun x =>
      (∑ s ∈ j.powerset, c s * centeredProduct p s x) ^ 2) =
      ∑ s ∈ j.powerset, c s ^ 2 * (p * (1 - p)) ^ s.card := by
  have hexpand (x : ι → Bool) :
      (∑ s ∈ j.powerset, c s * centeredProduct p s x) ^ 2 =
      ∑ s ∈ j.powerset, ∑ r ∈ j.powerset,
        (c s * c r) * (centeredProduct p s x * centeredProduct p r x) := by
    simp only [pow_two, sum_mul, mul_sum]
    apply sum_congr rfl
    intro s hs
    apply sum_congr rfl
    intro r hr
    ring
  simp_rw [hexpand, BitString.bernoulliAverage_sum,
    BitString.bernoulliAverage_const_mul, centeredProduct_orthogonal]
  apply sum_congr rfl
  intro s hs
  rw [sum_eq_single s]
  · simp [pow_two]
  · intro r hr hsr
    simp [Ne.symm hsr]
  · exact fun hn => (hn hs).elim

/-- The squared norm of the lifted score, the unnormalized form of Lemma 3.2. -/
theorem bernoulliAverage_lift_sq {t p : ℝ} (ht : t ≠ 1) (hp : p ≠ 0)
    (j : Finset ι) (f : Finset ι → ℝ) :
    BitString.bernoulliAverage t (fun x => lift t p j f x ^ 2) =
      ∑ s ∈ j.powerset,
        centeredCoefficient p f s ^ 2 * (t / (p ^ 2 * (1 - t))) ^ s.card := by
  simp_rw [lift_eq_sum ht hp]
  rw [bernoulliAverage_centered_sum_sq]
  apply sum_congr rfl
  intro s hs
  have he : (1 / (p * (1 - t))) ^ 2 * (t * (1 - t)) =
      t / (p ^ 2 * (1 - t)) := by
    have ht' : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    field_simp
  rw [mul_pow, ← pow_mul, mul_comm s.card 2, pow_mul]
  calc
    _ = centeredCoefficient p f s ^ 2 *
        (((1 / (p * (1 - t))) ^ 2) ^ s.card * (t * (1 - t)) ^ s.card) := by ring
    _ = _ := by rw [← mul_pow, he]


/-- At equal densities the full kernel reproduces the input score. -/
theorem lift_univ_self {p : ℝ} (hp : p ≠ 0) (hp' : p ≠ 1)
    (f : Finset ι → ℝ) (x : ι → Bool) :
    lift p p univ f x = f (univ.filter fun i => x i) := by
  have hp1 : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp')
  unfold lift BitString.bernoulliAverage
  rw [sum_eq_single x]
  · have hweight : BitString.bernoulliWeight p x * kernel p p univ x x = 1 := by
      simp only [BitString.bernoulliWeight, kernel]
      rw [← prod_mul_distrib]
      have he (i : ι) : (if x i then p else 1 - p) * coordinateKernel p p (x i) (x i) = 1 := by
        cases x i <;> simp [coordinateKernel, hp, hp1]
      simp_rw [he]
      simp
    rw [← mul_assoc, hweight, one_mul]
  · intro w hw hne
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ w i := by
      by_contra! h
      exact hne (funext h).symm
    have hz : kernel p p univ x w = 0 := by
      apply prod_eq_zero (mem_univ i)
      cases hx : x i <;> cases hw : w i <;> simp_all [coordinateKernel]
    simp [hz]
  · simp

/-- Biased Parseval in the unnormalized centered-product basis. -/
theorem centered_parseval {p : ℝ} (hp : p ≠ 0) (hp' : p ≠ 1) (f : Finset ι → ℝ) :
    (∑ s : Finset ι, centeredCoefficient p f s ^ 2 *
      (1 / (p * (1 - p))) ^ s.card) =
      BitString.bernoulliAverage p (fun x => f (univ.filter fun i => x i) ^ 2) := by
  have hn : p / (p ^ 2 * (1 - p)) = 1 / (p * (1 - p)) := by field_simp
  have h := bernoulliAverage_lift_sq hp' hp univ f
  simp_rw [lift_univ_self hp hp', hn] at h
  simpa only [powerset_univ] using h.symm

/-- The positive coefficient majorant of Proposition 3.3. -/
theorem bernoulliAverage_indicator_retain_le_sum {t p : ℝ} (ht : 0 ≤ t) (ht' : t < 1)
    (hp : p ≠ 0) {U : Set (Finset ι)} (hU : IsUpperSet U) (j : Finset ι) :
    BitString.bernoulliAverage t (fun x => U.indicator (1 : Finset ι → ℝ) (retain j x)) ≤
      ∑ s ∈ j.powerset, centeredCoefficient p (U.indicator 1) s ^ 2 *
        (t / (p ^ 2 * (1 - t))) ^ s.card := by
  rw [← bernoulliAverage_lift_sq ht'.ne hp]
  exact bernoulliAverage_indicator_retain_le ht ht' hp hU j


/-- A nonnegative finite mass function is `q`-spread when containment of each fixed set `s`
has mass at most `q ^ s.card`. For a probability mass function this is Definition 1.1. -/
@[expose] def IsSpread (q : ℝ) (μ : Finset ι → ℝ) : Prop :=
  ∀ s, (∑ j : Finset ι, if s ⊆ j then μ j else 0) ≤ q ^ s.card

/-- **Domination after thinning**, the upper-event formulation of Theorem 1.2 of
[FangWang2026]. The parent weights may even form a subprobability law: the spread hypothesis
on the empty set already bounds their total mass by one. The retention mask is independent
of the parent, as expressed by the iterated finite expectation. -/
theorem thinning_le_bernoulli {t p q : ℝ} (ht : 0 ≤ t) (ht' : t < 1)
    (hp : 0 < p) (hp' : p < 1) (hq : 0 ≤ q)
    (hcond : t * q * (1 - p) ≤ p * (1 - t))
    (μ : Finset ι → ℝ) (hμ : ∀ j, 0 ≤ μ j) (hspread : IsSpread q μ)
    {U : Set (Finset ι)} (hU : IsUpperSet U) :
    (∑ j : Finset ι, μ j * BitString.bernoulliAverage t
      (fun x => U.indicator (1 : Finset ι → ℝ) (retain j x))) ≤
      BitString.bernoulliAverage p (fun w =>
        U.indicator (1 : Finset ι → ℝ) (univ.filter fun i => w i)) := by
  let a := t / (p ^ 2 * (1 - t))
  let b := 1 / (p * (1 - p))
  let c (s : Finset ι) := centeredCoefficient p (U.indicator 1) s ^ 2 * a ^ s.card
  have ha : 0 ≤ a := div_nonneg ht (mul_nonneg (sq_nonneg p) (by linarith))
  have hc (s : Finset ι) : 0 ≤ c s := mul_nonneg (sq_nonneg _) (pow_nonneg ha _)
  have hab : a * q ≤ b := by
    dsimp [a, b]
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hp) (by linarith))
      (mul_pos hp (by linarith))).mpr
    nlinarith [mul_le_mul_of_nonneg_left hcond hp.le]
  have hexchange :
      (∑ j : Finset ι, μ j * ∑ s ∈ j.powerset, c s) =
      ∑ s : Finset ι, c s * ∑ j : Finset ι, if s ⊆ j then μ j else 0 := by
    have hps (j : Finset ι) : j.powerset = univ.filter (fun s => s ⊆ j) := by
      ext s
      simp
    simp_rw [hps, sum_filter, mul_sum, mul_ite, mul_zero]
    rw [sum_comm]
    apply sum_congr rfl
    intro s hs
    apply sum_congr rfl
    intro j hj
    split_ifs <;> ring
  calc
    _ ≤ ∑ j : Finset ι, μ j * ∑ s ∈ j.powerset, c s := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (bernoulliAverage_indicator_retain_le_sum ht ht' hp.ne' hU j) (hμ j)
    _ = ∑ s : Finset ι, c s * ∑ j : Finset ι, if s ⊆ j then μ j else 0 := hexchange
    _ ≤ ∑ s : Finset ι, c s * q ^ s.card := by
      exact sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hspread s) (hc s)
    _ ≤ ∑ s : Finset ι, centeredCoefficient p (U.indicator 1) s ^ 2 * b ^ s.card := by
      apply sum_le_sum
      intro s hs
      change (centeredCoefficient p (U.indicator 1) s ^ 2 * a ^ s.card) * q ^ s.card ≤ _
      rw [mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg ha hq) hab _)
        (sq_nonneg _)
    _ = BitString.bernoulliAverage p (fun w =>
        U.indicator (1 : Finset ι → ℝ) (univ.filter fun i => w i)) := by
      rw [centered_parseval hp.ne' hp'.ne]
      congr 1
      funext w
      by_cases hw : (univ.filter fun i => w i) ∈ U <;> simp [hw]


/-- The probability-law specialization of `thinning_le_bernoulli`. Both expectations use
ordinary finite PMF probabilities; no assumption about the parent coordinates being independent
is made. Only the retention mask is sampled independently. -/
theorem pmf_thinning_le_bernoulli {t p q : ℝ} (ht : 0 ≤ t) (ht' : t < 1)
    (hp : 0 < p) (hp' : p < 1) (hq : 0 ≤ q)
    (hcond : t * q * (1 - p) ≤ p * (1 - t))
    (μ : PMF (Finset ι)) (hspread : IsSpread q (fun j => (μ j).toReal))
    {U : Set (Finset ι)} (hU : IsUpperSet U) :
    (∑ j : Finset ι, (μ j).toReal * BitString.bernoulliAverage t
      (fun x => U.indicator (1 : Finset ι → ℝ) (retain j x))) ≤
      BitString.bernoulliAverage p (fun w =>
        U.indicator (1 : Finset ι → ℝ) (univ.filter fun i => w i)) :=
  thinning_le_bernoulli ht ht' hp hp' hq hcond _
    (fun _ => ENNReal.toReal_nonneg) hspread hU

/-- The explicit domination density `t q / (1 - t + t q)` of Theorem 1.2. -/
theorem thinning_le_bernoulli_explicit_density {t q : ℝ} (ht : 0 < t) (ht' : t < 1)
    (hq : 0 < q) (μ : Finset ι → ℝ) (hμ : ∀ j, 0 ≤ μ j) (hspread : IsSpread q μ)
    {U : Set (Finset ι)} (hU : IsUpperSet U) :
    (∑ j : Finset ι, μ j * BitString.bernoulliAverage t
      (fun x => U.indicator (1 : Finset ι → ℝ) (retain j x))) ≤
      BitString.bernoulliAverage (t * q / (1 - t + t * q)) (fun w =>
        U.indicator (1 : Finset ι → ℝ) (univ.filter fun i => w i)) := by
  have hd : 0 < 1 - t + t * q := by positivity
  apply thinning_le_bernoulli ht.le ht' (div_pos (mul_pos ht hq) hd)
    ((div_lt_one hd).mpr (by linarith)) hq.le _ μ hμ hspread hU
  field_simp
  nlinarith

/-- The thinning-conjecture corollary for every admissible constant `α`, including `α = 1/2`.
The condition `α² ≤ 1 - α` is the algebraic form of the paper's golden-ratio threshold. -/
theorem thinning_le_bernoulli_of_alpha {α p : ℝ} (hα : 0 ≤ α) (hα' : α < 1)
    (hαsq : α ^ 2 ≤ 1 - α) (hp : 0 < p) (hp' : p < 1)
    (μ : Finset ι → ℝ) (hμ : ∀ j, 0 ≤ μ j) (hspread : IsSpread (α * p) μ)
    {U : Set (Finset ι)} (hU : IsUpperSet U) :
    (∑ j : Finset ι, μ j * BitString.bernoulliAverage α
      (fun x => U.indicator (1 : Finset ι → ℝ) (retain j x))) ≤
      BitString.bernoulliAverage p (fun w =>
        U.indicator (1 : Finset ι → ℝ) (univ.filter fun i => w i)) := by
  apply thinning_le_bernoulli hα hα' hp hp' (mul_nonneg hα hp.le) _ μ hμ hspread hU
  have hbound : α ^ 2 * (1 - p) ≤ 1 - α := by
    nlinarith [mul_nonneg hp.le (sq_nonneg α)]
  nlinarith [mul_le_mul_of_nonneg_left hbound hp.le]

end Cslib.Probability.Thinning
