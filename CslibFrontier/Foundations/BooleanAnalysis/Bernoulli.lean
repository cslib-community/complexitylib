/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Weight
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Algebra.Order.Group.Indicator
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Order.UpperLower
import Mathlib.Data.Bool.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bernoulli coordinate sampling and transference

A Boolean mask `selected : ι → Bool` is a set of coordinates. Selecting each coordinate
independently with probability `p` gives it the weight `bernoulliWeight p selected`, and
`bernoulliAverage p f` is the expectation of `f` over the random mask, a finite sum. The coordinates
of the random mask are independent (`bernoulliAverage_prod`), the union of independent masks of
rates `p` and `q` has rate `p + q - p q` (`bernoulliAverage_union`), and increasing the rate
decreases the expectation of an antitone function
(`bernoulliAverage_le_bernoulliAverage_of_antitone`).

The union of `h` independent masks of rate `p` lies in a lower set `A` only if each of them does.
So when `h p ≤ q`, the probability of `A` at rate `q` is at most its probability at rate `p` to the
power `h` (`bernoulliAverage_lowerSet_pow_le`). This transference principle appears in Section 2 of
[Korten2026] (Lemma 3) and again in Section 4; Korten attributes it to
[Zhao, Lemma 4.3.7][Zhao2023]. Its form at small rates, with a real exponent, is
`BitString.bernoulliAverage_lowerSet_transfer`.

## Main definitions

* `Cslib.BitString.bernoulliWeight`: the probability of a mask.
* `Cslib.BitString.bernoulliAverage`: the expectation over a random mask.

## Main results

* `Cslib.BitString.bernoulliAverage_prod`: the coordinates of a random mask are independent.
* `Cslib.BitString.bernoulliAverage_reindex`, `Cslib.BitString.bernoulliAverage_sumElim`,
  `Cslib.BitString.bernoulliAverage_restrict`: reindexing, splitting over a disjoint union, and
  restricting the coordinates of a random mask.
* `Cslib.BitString.bernoulliAverage_zero`, `Cslib.BitString.bernoulliWeight_one_half`,
  `Cslib.BitString.bernoulliAverage_one_half`: sampling at rates `0` and `1 / 2`.
* `Cslib.BitString.bernoulliAverage_one_sub`: complementing the mask exchanges the rates `p` and
  `1 - p`.
* `Cslib.BitString.bernoulliAverage_coordinate`,
  `Cslib.BitString.bernoulliAverage_nonempty`, `Cslib.BitString.bernoulliAverage_hits`,
  `Cslib.BitString.bernoulliAverage_weight`: the probability that a coordinate is selected,
  that some coordinate is, that some coordinate of a given set is, and the expected number of
  selected coordinates.
* `Cslib.BitString.bernoulliWeight_eq_pow_mul_pow`, `Cslib.BitString.bernoulliAverage_comp_weight`,
  `Cslib.BitString.bernoulliAverage_lt_weight`: the weight of a random mask is binomially
  distributed, with upper tail `∑_{r < k ≤ n} C(n, k) p ^ k (1 - p) ^ (n - k)`.
* `Cslib.BitString.bernoulliAverage_bernoulliAverage_eq_sum`: the law of a coordinatewise
  image of two independent masks.
* `Cslib.BitString.bernoulliAverage_union`: unions of independent masks.
* `Cslib.BitString.bernoulliAverage_le_bernoulliAverage_of_antitone`: antitone functions have
  smaller expectations at larger rates.
* `Cslib.BitString.bernoulliAverage_lowerSet_union`,
  `Cslib.BitString.bernoulliAverage_lowerSet_pow_le`: transference for lower sets.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
* [Y. Zhao, *Probabilistic Methods in Combinatorics*][Zhao2023]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

/-- The probability of the mask `selected` when each coordinate is selected independently with
probability `p`. -/
def bernoulliWeight {ι : Type*} [Fintype ι] (p : ℝ) (selected : ι → Bool) : ℝ :=
  ∏ i, if selected i then p else 1 - p

/-- The expectation of `f` over a random mask selecting each coordinate independently with
probability `p`. It is a probability expectation when `0 ≤ p ≤ 1`. -/
def bernoulliAverage {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ)
    (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ selected, bernoulliWeight p selected * f selected

/-! ### Reindexing and splitting the coordinates -/

/-- The weight of a mask on `Fin (n + 1)` is the weight of its first coordinate times the weight
of the others. -/
theorem bernoulliWeight_cons {n : ℕ} (p : ℝ) (b : Bool) (selected : Fin n → Bool) :
    bernoulliWeight p (Fin.cons b selected) =
      (if b then p else 1 - p) * bernoulliWeight p selected := by
  simp [bernoulliWeight, Fin.prod_univ_succ]

/-- **Conditioning on the first coordinate**: the expectation over a mask on `Fin (n + 1)` is the
average, with weights `1 - p` and `p`, of the expectations with the first coordinate unselected
and selected. -/
theorem bernoulliAverage_cons {n : ℕ} (p : ℝ) (f : (Fin (n + 1) → Bool) → ℝ) :
    bernoulliAverage p f =
      (1 - p) * bernoulliAverage p (fun x => f (Fin.cons false x)) +
        p * bernoulliAverage p (fun x => f (Fin.cons true x)) := by
  unfold bernoulliAverage
  rw [Fin.sum_univ_cons_bool]
  simp_rw [bernoulliWeight_cons]
  simp only [Bool.false_eq_true, ite_false, ite_true, mul_assoc, ← mul_sum]

/-- An equivalence of coordinate types preserves the weights of masks. -/
theorem bernoulliWeight_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (p : ℝ) (s : κ → Bool) :
    bernoulliWeight p (fun i => s (e i)) = bernoulliWeight p s :=
  e.prod_comp (fun i => if s i then p else 1 - p)

/-- An equivalence of coordinate types preserves Bernoulli expectations. -/
theorem bernoulliAverage_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (p : ℝ) (f : (κ → Bool) → ℝ) :
    bernoulliAverage p (fun x => f (fun j => x (e.symm j))) = bernoulliAverage p f := by
  let E := Equiv.arrowCongr e (Equiv.refl Bool)
  unfold bernoulliAverage
  rw [← E.sum_comp (fun x => bernoulliWeight p x * f x)]
  apply sum_congr rfl
  intro x _
  change bernoulliWeight p x * f (fun j => x (e.symm j)) =
    bernoulliWeight p (fun j => x (e.symm j)) * f (fun j => x (e.symm j))
  rw [bernoulliWeight_reindex]

/-- **Random masks on a disjoint union of coordinates are pairs of independent masks**: the
expectation over a mask on `ι ⊕ κ` is the iterated expectation over a mask on `ι` and one on
`κ`. -/
theorem bernoulliAverage_sumElim {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (p : ℝ) (h : (ι ⊕ κ → Bool) → ℝ) :
    bernoulliAverage p h =
      bernoulliAverage p fun P₁ => bernoulliAverage p fun P₂ => h (Sum.elim P₁ P₂) := by
  have hw (P₁ : ι → Bool) (P₂ : κ → Bool) :
      bernoulliWeight p (Sum.elim P₁ P₂) = bernoulliWeight p P₁ * bernoulliWeight p P₂ := by
    rw [bernoulliWeight, Fintype.prod_sum_type]
    rfl
  simp only [bernoulliAverage, mul_sum, ← mul_assoc, ← hw]
  rw [← Fintype.sum_prod_type fun P : (ι → Bool) × (κ → Bool) =>
    bernoulliWeight p (Sum.elim P.1 P.2) * h (Sum.elim P.1 P.2)]
  exact Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow ι κ Bool) _ _ fun P => by
    rw [← Sum.elim_comp_inl_inr P]
    rfl

theorem bernoulliWeight_split {ι : Type*} [Fintype ι] (p : ℝ) (s x : ι → Bool) :
    bernoulliWeight p x = bernoulliWeight p (fun i : {i // s i = true} => x i) *
      bernoulliWeight p (fun i : {i // s i ≠ true} => x i) :=
  (Fintype.prod_subtype_mul_prod_subtype (fun i => s i = true)
    (fun i => if x i then p else 1 - p)).symm

/-- The probability of a mask is `p ^ |s| (1 - p) ^ (|ι| - |s|)`, where `|s|` is its weight. -/
theorem bernoulliWeight_eq_pow_mul_pow {ι : Type*} [Fintype ι] (p : ℝ) (s : ι → Bool) :
    bernoulliWeight p s = p ^ weight s * (1 - p) ^ (Fintype.card ι - weight s) := by
  classical
  rw [bernoulliWeight, ← prod_filter_mul_prod_filter_not univ (fun i => s i = true)]
  rw [prod_congr rfl (fun i hi => ite_eq_left (mem_filter.mp hi).2),
    prod_congr rfl (fun i hi => ite_eq_right (mem_filter.mp hi).2), prod_const, prod_const]
  congr 2
  rw [← card_filter_eq_false_eq_card_sub_weight]
  congr 1

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Linearity and positivity -/

/-- Bernoulli expectation preserves pointwise inequalities at probability rates. -/
theorem bernoulliAverage_mono {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {f g : (ι → Bool) → ℝ}
    (hfg : ∀ x, f x ≤ g x) : bernoulliAverage p f ≤ bernoulliAverage p g := by
  apply sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left (hfg x)
  apply prod_nonneg
  intro i _
  split_ifs
  · exact hp
  · exact sub_nonneg.mpr hp'

/-- The weights of the masks sum to one, so constants are their own expectations. This holds for
every `p`; the weights are nonnegative when `p ∈ [0, 1]`. -/
theorem bernoulliAverage_const (p c : ℝ) :
    bernoulliAverage p (fun _ : ι → Bool => c) = c := by
  unfold bernoulliAverage bernoulliWeight
  rw [← sum_mul, ← Fintype.prod_sum (fun (_ : ι) (b : Bool) => if b then p else 1 - p)]
  simp

/-- Bernoulli expectation is additive. -/
theorem bernoulliAverage_add (p : ℝ) (f g : (ι → Bool) → ℝ) :
    bernoulliAverage p (fun x => f x + g x) = bernoulliAverage p f + bernoulliAverage p g := by
  simp only [bernoulliAverage, mul_add, sum_add_distrib]

/-- Bernoulli expectation commutes with subtraction. -/
theorem bernoulliAverage_sub (p : ℝ) (f g : (ι → Bool) → ℝ) :
    bernoulliAverage p (fun x => f x - g x) = bernoulliAverage p f - bernoulliAverage p g := by
  simp only [bernoulliAverage, mul_sub, sum_sub_distrib]

/-- Bernoulli expectation commutes with multiplication by a constant. -/
theorem bernoulliAverage_const_mul (p a : ℝ) (f : (ι → Bool) → ℝ) :
    bernoulliAverage p (fun x => a * f x) = a * bernoulliAverage p f := by
  simp only [bernoulliAverage, mul_sum, mul_left_comm]

/-- Bernoulli expectation commutes with finite sums. -/
theorem bernoulliAverage_sum {α : Type*} (s : Finset α) (p : ℝ) (f : α → (ι → Bool) → ℝ) :
    bernoulliAverage p (fun x => ∑ a ∈ s, f a x) = ∑ a ∈ s, bernoulliAverage p (f a) := by
  simp only [bernoulliAverage, mul_sum]
  exact sum_comm

/-- Bernoulli expectation commutes with finite averages. -/
theorem bernoulliAverage_expect_comm {α : Type*} (A : Finset α) (p : ℝ)
    (f : (ι → Bool) → α → ℝ) :
    bernoulliAverage p (fun s => 𝔼 x ∈ A, f s x) =
      𝔼 x ∈ A, bernoulliAverage p (fun s => f s x) := by
  unfold bernoulliAverage
  simp_rw [mul_expect]
  exact (expect_sum_comm A univ _).symm

/-- The probability of a set of masks is between zero and one. -/
theorem bernoulliAverage_indicator_mem_Icc (A : Set (ι → Bool)) {p : ℝ} (hp : 0 ≤ p)
    (hp' : p ≤ 1) : bernoulliAverage p (A.indicator 1) ∈ Set.Icc 0 1 := by
  constructor
  · simpa only [bernoulliAverage_const] using bernoulliAverage_mono hp hp' (f := fun _ => 0)
      (g := A.indicator 1) fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  · simpa only [bernoulliAverage_const] using bernoulliAverage_mono hp hp' (f := A.indicator 1)
      (g := fun _ => 1) fun x => Set.indicator_le_self' (fun _ _ => zero_le_one) x

/-! ### Independence of the coordinates -/

/-- **The coordinates of a random mask are independent**: the average of a product of functions of
the separate coordinates is the product of their averages. -/
theorem bernoulliAverage_prod (p : ℝ) (g : ι → Bool → ℝ) :
    bernoulliAverage p (fun P => ∏ i, g i (P i)) = ∏ i, ((1 - p) * g i false + p * g i true) := by
  simp only [bernoulliAverage, bernoulliWeight, ← prod_mul_distrib]
  rw [← Fintype.prod_sum fun i (b : Bool) => (if b then p else 1 - p) * g i b]
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false, add_comm]

/-- Restricting a Bernoulli mask to fixed coordinates preserves its product law. -/
theorem bernoulliAverage_restrict (p : ℝ) (s : ι → Bool) (f : ({i // s i = true} → Bool) → ℝ) :
    bernoulliAverage p (fun x : ι → Bool => f (fun i => x i)) = bernoulliAverage p f := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => s i = true) (fun _ => Bool)
  unfold bernoulliAverage
  rw [← e.symm.sum_comp (fun x => bernoulliWeight p x * f (fun i => x i))]
  simp_rw [bernoulliWeight_split p s]
  have hleft (z : ({i // s i = true} → Bool) × ({i // s i ≠ true} → Bool)) :
      (fun i : {i // s i = true} => e.symm z i) = z.1 :=
    congrArg Prod.fst (e.apply_symm_apply z)
  have hright (z : ({i // s i = true} → Bool) × ({i // s i ≠ true} → Bool)) :
      (fun i : {i // s i ≠ true} => e.symm z i) = z.2 :=
    congrArg Prod.snd (e.apply_symm_apply z)
  simp_rw [hleft, hright]
  rw [Fintype.sum_prod_type]
  have htotal : (∑ y : {i // s i ≠ true} → Bool, bernoulliWeight p y) = 1 := by
    simpa [bernoulliAverage] using
      bernoulliAverage_const (ι := {i // s i ≠ true}) p 1
  simp only [mul_assoc, ← mul_sum, ← sum_mul, htotal, one_mul]

/-- Sampling at rate zero selects the empty coordinate set. -/
theorem bernoulliAverage_zero (f : (ι → Bool) → ℝ) :
    bernoulliAverage 0 f = f (fun _ => false) := by
  rw [bernoulliAverage, Fintype.sum_eq_single (fun _ => false) fun s hs => ?_]
  · simp [bernoulliWeight]
  obtain ⟨i, hi⟩ : ∃ i, s i = true := by
    by_contra h
    exact hs (funext fun i => by simpa using fun hi => h ⟨i, hi⟩)
  rw [bernoulliWeight, prod_eq_zero (mem_univ i) (by simp [hi]), zero_mul]

omit [DecidableEq ι] in
/-- At rate `1 / 2`, every mask has weight `(1 / 2) ^ |ι|`. -/
theorem bernoulliWeight_one_half (selected : ι → Bool) :
    bernoulliWeight (1 / 2) selected = (1 / 2) ^ Fintype.card ι := by
  simp only [bernoulliWeight, show (1 : ℝ) - 1 / 2 = 1 / 2 by ring, ite_self, prod_const,
    card_univ]

/-- At rate `1 / 2`, the Bernoulli expectation is the uniform expectation on the cube. -/
theorem bernoulliAverage_one_half (f : (ι → Bool) → ℝ) :
    bernoulliAverage (1 / 2) f = 𝔼 selected, f selected := by
  simp only [bernoulliAverage, bernoulliWeight_one_half, ← mul_sum,
    Fintype.expect_eq_sum_div_card, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [one_div, inv_pow, div_eq_inv_mul]

/-- **Complementing the mask** exchanges the rates `p` and `1 - p`: the expectation of `f` at
rate `1 - p` is the expectation of `f` of the complemented mask at rate `p`. -/
theorem bernoulliAverage_one_sub (p : ℝ) (f : (ι → Bool) → ℝ) :
    bernoulliAverage (1 - p) f = bernoulliAverage p (fun s => f fun i => !s i) := by
  let e : (ι → Bool) ≃ (ι → Bool) :=
    ⟨fun s i => !s i, fun s i => !s i, fun s => by simp, fun s => by simp⟩
  refine (Fintype.sum_equiv e _ _ fun s => ?_).symm
  congr 1
  refine prod_congr rfl fun i _ => ?_
  change (if s i then p else 1 - p) = if !s i then 1 - p else 1 - (1 - p)
  cases s i <;> simp

/-- A coordinate is selected with probability `p`. -/
theorem bernoulliAverage_coordinate (p : ℝ) (i : ι) :
    bernoulliAverage p (fun s : ι → Bool => if s i then (1 : ℝ) else 0) = p := by
  let e := Equiv.piSplitAt i (fun _ : ι => Bool)
  have hw (s : ι → Bool) : bernoulliWeight p s =
      (if s i then p else 1 - p) * bernoulliWeight p (fun j : {j // j ≠ i} => s j) := by
    exact Fintype.prod_eq_mul_prod_subtype_ne (fun j => if s j then p else 1 - p) i
  unfold bernoulliAverage
  rw [← e.symm.sum_comp (fun s => bernoulliWeight p s * (if s i then (1 : ℝ) else 0))]
  simp_rw [hw]
  have hleft (z : Bool × ({j // j ≠ i} → Bool)) : e.symm z i = z.1 := by
    simp [e, Equiv.piSplitAt]
  have hright (z : Bool × ({j // j ≠ i} → Bool)) :
      (fun j : {j // j ≠ i} => e.symm z j) = z.2 := by
    funext j
    simp [e, Equiv.piSplitAt, j.property]
  simp_rw [hleft, hright]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Bool.false_eq_true, ite_true, ite_false, mul_one, mul_zero,
    sum_const_zero, add_zero, ← mul_sum]
  have hs : (∑ s : {j // j ≠ i} → Bool, bernoulliWeight p s) = 1 := by
    simpa [bernoulliAverage] using bernoulliAverage_const (ι := {j // j ≠ i}) p 1
  rw [hs, mul_one]

/-- A mask is nonempty with probability `1 - (1 - p) ^ |ι|`. -/
theorem bernoulliAverage_nonempty (p : ℝ) :
    bernoulliAverage p (fun P : ι → Bool => if ∃ i, P i = true then (1 : ℝ) else 0) =
      1 - (1 - p) ^ Fintype.card ι := by
  have he (P : ι → Bool) : (if ∃ i, P i = true then (1 : ℝ) else 0) =
      1 - (if P = (fun _ => false) then 1 else 0) := by
    by_cases h : ∃ i, P i = true
    · have hn : P ≠ fun _ => false := by
        intro hn
        obtain ⟨i, hi⟩ := h
        simp [hn] at hi
      simp [h, hn]
    · have hn : P = fun _ => false := by
        funext i
        have hi : P i ≠ true := fun hi => h ⟨i, hi⟩
        simpa using hi
      simp [hn]
  simp_rw [he, bernoulliAverage_sub, bernoulliAverage_const]
  congr 1
  simp [bernoulliAverage, bernoulliWeight]

/-- A mask of rate `p` has `|ι| p` coordinates on average. -/
theorem bernoulliAverage_weight (p : ℝ) :
    bernoulliAverage p (fun P : ι → Bool => (BitString.weight P : ℝ)) = Fintype.card ι * p := by
  have he (P : ι → Bool) : (BitString.weight P : ℝ) = ∑ i, if P i then (1 : ℝ) else 0 := by
    simp [BitString.weight]
  unfold bernoulliAverage
  simp_rw [he, mul_sum]
  rw [sum_comm]
  have hc (i : ι) := bernoulliAverage_coordinate p i
  simp only [bernoulliAverage] at hc
  simp_rw [hc]
  simp

/-- The weight of a mask of rate `p` is binomially distributed: the expectation of a function of
the weight is its average against `C(n, k) p ^ k (1 - p) ^ (n - k)`, where `n = |ι|`. -/
theorem bernoulliAverage_comp_weight (p : ℝ) (g : ℕ → ℝ) :
    bernoulliAverage p (fun s : ι → Bool => g (weight s)) =
      ∑ k ∈ range (Fintype.card ι + 1),
        ((Fintype.card ι).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card ι - k) * g k := by
  rw [bernoulliAverage, ← sum_fiberwise_of_maps_to (g := weight)
    (t := range (Fintype.card ι + 1)) (fun s _ => mem_range.mpr (Nat.lt_succ_of_le (weight_le s)))]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_congr rfl fun s hs => by rw [bernoulliWeight_eq_pow_mul_pow, (mem_filter.mp hs).2],
    sum_const, card_filter_weight_eq, nsmul_eq_mul]
  ring

/-- A mask of rate `p` has more than `r` coordinates with probability
`∑_{r < k ≤ n} C(n, k) p ^ k (1 - p) ^ (n - k)`, the upper tail of the binomial distribution. -/
theorem bernoulliAverage_lt_weight (p : ℝ) (r : ℕ) :
    bernoulliAverage p (fun s : ι → Bool => if r < weight s then 1 else 0) =
      ∑ k ∈ range (Fintype.card ι + 1) with r < k,
        ((Fintype.card ι).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card ι - k) := by
  rw [sum_filter]
  exact (bernoulliAverage_comp_weight p fun k => if r < k then 1 else 0).trans
    (sum_congr rfl fun k _ => by split_ifs <;> ring)

/-- A mask of rate `p` meets the coordinates selected by `s` with probability
`1 - (1 - p) ^ |s|`. -/
theorem bernoulliAverage_hits (p : ℝ) (s : ι → Bool) :
    bernoulliAverage p (fun P : ι → Bool =>
      if ∃ i, s i = true ∧ P i = true then (1 : ℝ) else 0) =
        1 - (1 - p) ^ BitString.weight s := by
  let f (P : {i // s i = true} → Bool) : ℝ := if ∃ i, P i = true then 1 else 0
  calc
    _ = bernoulliAverage p (fun P : ι → Bool => f (fun i => P i)) := by
      congr 1 with P : 1
      simp [f]
    _ = bernoulliAverage p f := bernoulliAverage_restrict p s f
    _ = _ := by
      simpa only [f, Fintype.card_subtype, BitString.weight] using
        bernoulliAverage_nonempty (ι := {i // s i = true}) p

/-! ### Unions of independent masks -/

/-- **Coordinatewise images of two independent masks**: the expectation of `f` at the image
`i ↦ φ (P i) (Q i)` of independent masks `P` and `Q` of rates `p` and `q` is the sum of its values
against a product weight, in which each coordinate takes the value `b` with weight
`(1 - p) (1 - q) [φ false false = b] + (1 - p) q [φ false true = b] + p (1 - q) [φ true false = b]
+ p q [φ true true = b]`. -/
theorem bernoulliAverage_bernoulliAverage_eq_sum {β : Type*} [Fintype β] [DecidableEq β]
    (p q : ℝ) (φ : Bool → Bool → β) (f : (ι → β) → ℝ) :
    bernoulliAverage p (fun P => bernoulliAverage q (fun Q => f (fun i => φ (P i) (Q i)))) =
      ∑ a : ι → β, f a * ∏ i,
        ((1 - p) * ((1 - q) * (if φ false false = a i then 1 else 0) +
            q * (if φ false true = a i then 1 else 0)) +
          p * ((1 - q) * (if φ true false = a i then 1 else 0) +
            q * (if φ true true = a i then 1 else 0))) := by
  have hf (z : ι → β) : f z = ∑ a, f a * ∏ i, (if z i = a i then (1 : ℝ) else 0) := by
    simp only [prod_boole, mem_univ, forall_const, ← funext_iff, mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_ite_eq]
  have hinner (a : ι → β) (P : ι → Bool) :
      bernoulliAverage q (fun Q => ∏ i, (if φ (P i) (Q i) = a i then (1 : ℝ) else 0)) =
        ∏ i, ((1 - q) * (if φ (P i) false = a i then 1 else 0) +
          q * (if φ (P i) true = a i then 1 else 0)) :=
    bernoulliAverage_prod q (fun i b => if φ (P i) b = a i then 1 else 0)
  have houter (a : ι → β) :
      bernoulliAverage p (fun P => ∏ i, ((1 - q) * (if φ (P i) false = a i then 1 else 0) +
          q * (if φ (P i) true = a i then (1 : ℝ) else 0))) =
        ∏ i, ((1 - p) * ((1 - q) * (if φ false false = a i then 1 else 0) +
            q * (if φ false true = a i then 1 else 0)) +
          p * ((1 - q) * (if φ true false = a i then 1 else 0) +
            q * (if φ true true = a i then 1 else 0))) :=
    bernoulliAverage_prod p (fun i c => (1 - q) * (if φ c false = a i then 1 else 0) +
      q * (if φ c true = a i then 1 else 0))
  calc
    _ = bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
        ∑ a, f a * ∏ i, (if φ (P i) (Q i) = a i then (1 : ℝ) else 0))) := by
      congr 1 with P : 1
      congr 1 with Q : 1
      exact hf _
    _ = _ := by
      simp_rw [bernoulliAverage_sum, bernoulliAverage_const_mul, hinner, houter]

/-- The union of independent masks of rates `p` and `q` has rate `p + q - p * q`. -/
theorem bernoulliAverage_union (p q : ℝ) (f : (ι → Bool) → ℝ) :
    bernoulliAverage p (fun r => bernoulliAverage q (fun s =>
      f (fun i => r i || s i))) = bernoulliAverage (p + q - p * q) f := by
  have h := bernoulliAverage_bernoulliAverage_eq_sum (p + q - p * q) 0 (fun a _ => a) f
  simp only [bernoulliAverage_const] at h
  rw [bernoulliAverage_bernoulliAverage_eq_sum p q (fun a b => a || b) f, h]
  refine sum_congr rfl fun a _ => congrArg _ (prod_congr rfl fun i _ => ?_)
  cases a i <;> simp only [Bool.or_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    mul_zero, add_zero, zero_add] <;> ring

/-- Increasing the sampling rate decreases the expectation of an antitone function. -/
theorem bernoulliAverage_le_bernoulliAverage_of_antitone {f : (ι → Bool) → ℝ} (hf : Antitone f)
    {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    bernoulliAverage q f ≤ bernoulliAverage p f := by
  rcases (hpq.trans hq).eq_or_lt with rfl | hp1
  · rw [le_antisymm hq hpq]
  let s := (q - p) / (1 - p)
  have hs : 0 ≤ s := div_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hp1.le)
  have hs' : s ≤ 1 := (div_le_one (sub_pos.mpr hp1)).mpr (by linarith)
  have hq' : p + s - p * s = q := by
    have : 1 - p ≠ 0 := (sub_pos.mpr hp1).ne'
    simp only [s]
    field_simp
    ring
  rw [← hq', ← bernoulliAverage_union]
  refine bernoulliAverage_mono hp hp1.le fun P => ?_
  calc
    _ ≤ bernoulliAverage s (fun _ => f P) :=
      bernoulliAverage_mono hs hs' fun S => hf fun i => Bool.left_le_or _ _
    _ = f P := bernoulliAverage_const s _

/-! ### Transference for lower sets -/

/-- The union of independent masks of rates `p` and `q` lies in a lower set only if both masks do,
so the probability of a lower set at rate `p + q - p q` is at most the product of its
probabilities at rates `p` and `q`. -/
theorem bernoulliAverage_lowerSet_union {A : Set (ι → Bool)} (hA : IsLowerSet A)
    {p q : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : 0 ≤ q) (hq' : q ≤ 1) :
    bernoulliAverage (p + q - p * q) (A.indicator 1) ≤
      bernoulliAverage p (A.indicator 1) * bernoulliAverage q (A.indicator 1) := by
  have hpoint (r s : ι → Bool) :
      A.indicator (1 : (ι → Bool) → ℝ) (fun i => r i || s i) ≤
        A.indicator 1 r * A.indicator 1 s := by
    by_cases hu : (fun i => r i || s i) ∈ A
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hA (fun i => Bool.left_le_or _ _) hu),
        Set.indicator_of_mem (hA (fun i => Bool.right_le_or _ _) hu)]
      simp
    · rw [Set.indicator_of_notMem hu]
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) r)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) s)
  rw [← bernoulliAverage_union]
  calc
    _ ≤ bernoulliAverage p (fun r => bernoulliAverage q (fun s =>
        A.indicator (1 : (ι → Bool) → ℝ) r * A.indicator 1 s)) :=
      bernoulliAverage_mono hp hp' fun r => bernoulliAverage_mono hq hq' (hpoint r)
    _ = _ := by
      simp_rw [bernoulliAverage_const_mul]
      simp only [bernoulliAverage, ← mul_assoc, sum_mul]

/-- **Transference for lower sets**, with an integer number of repetitions: if `h` independent
masks of rate `p` have a union of rate at most `q` (`h p ≤ q`), then the probability of a lower set
at rate `q` is at most the `h`-th power of its probability at rate `p`. -/
theorem bernoulliAverage_lowerSet_pow_le {A : Set (ι → Bool)} (hA : IsLowerSet A)
    {p q : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : q ≤ 1) (h : ℕ) (hh : (h : ℝ) * p ≤ q) :
    bernoulliAverage q (A.indicator 1) ≤ bernoulliAverage p (A.indicator 1) ^ h := by
  let u (j : ℕ) : ℝ := 1 - (1 - p) ^ j
  have hu (j : ℕ) : 0 ≤ u j ∧ u j ≤ 1 := by
    constructor
    · exact sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hp') (by linarith))
    · dsimp [u]
      linarith [pow_nonneg (sub_nonneg.mpr hp') j]
  have hs (j : ℕ) : u (j + 1) = p + u j - p * u j := by
    dsimp [u]
    rw [pow_succ]
    ring
  have hb (j : ℕ) : u j ≤ (j : ℝ) * p := by
    induction j with
    | zero => simp [u]
    | succ j ih =>
      rw [hs, Nat.cast_succ]
      nlinarith [mul_nonneg hp (hu j).1]
  have hi (j : ℕ) :
      bernoulliAverage (u j) (A.indicator 1) ≤ bernoulliAverage p (A.indicator 1) ^ j := by
    induction j with
    | zero =>
      simpa only [pow_zero] using (bernoulliAverage_indicator_mem_Icc A (hu 0).1 (hu 0).2).2
    | succ j ih =>
      rw [hs, pow_succ']
      exact (bernoulliAverage_lowerSet_union hA hp hp' (hu j).1 (hu j).2).trans
        (mul_le_mul_of_nonneg_left ih (bernoulliAverage_indicator_mem_Icc A hp hp').1)
  exact (bernoulliAverage_le_bernoulliAverage_of_antitone hA.antitone_indicator_one
    (hu h).1 ((hb h).trans hh) hq).trans (hi h)

end

end Cslib.BitString
