/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ternary majority trees and counting amplification

A *majority tree* (`Cslib.majTree`) of depth `L` combines `3 ^ L` outcomes by repeated majorities
of three, `maj3 a b c = if a = b then a else c`, which is right whenever two of its arguments are.
If a single outcome errs on at most a `ρ` fraction of a finite sample space, the tree errs on at
most a `(3 * ρ) ^ (2 ^ L) / 3` fraction of the `3 ^ L`-tuples (`Cslib.card_majTree_ne_le`). For
`3 * ρ ≤ 1 / 2` this is below `2 ^ (-2 ^ L)`, so by a union bound one fixed choice of the `3 ^ L`
outcomes is right on every element of a set of at most `2 ^ (2 ^ L)` targets
(`Cslib.exists_forall_majTree_eq`). Majority trees replace a Chernoff bound by a counting argument
and need only equality tests to evaluate [Arora and Barak, Chapter 19][AroraBarak09].

The same bounds hold over weighted outcomes, where a tuple carries the product of the weights of
its entries (`Cslib.sum_majTree_ne_le`, `Cslib.exists_forall_majTree_eq_of_sum`); unit weights
give the counting forms. One level maps the missed weight `B` to at most `3 B² T - 2 B³`
(`Cslib.sum_majTree_succ_ne_le`), the weight on which two of three independent subtrees miss.
Over a probability vector this also amplifies a small advantage: if every input is missed with
probability at most `1/2 - ε`, inner trees of depth `m₁ + 1` with `(11/8)^m₁ ε ≥ 1/4` push the
error below `1/6`, and an outer tree corrects a whole set (`Cslib.exists_forall_majTree_majTree_eq`,
Valiant's amplification [Valiant1984Majority] in the form of [ChukhinKulikovMihajlinSmal2026],
Lemma 3.7).

## Main definitions

* `Cslib.maj3`, `Cslib.majTree`: majorities of three and majority trees.
* `Cslib.tripleEquiv`: the splitting of `3 ^ (L + 1)` indices into three blocks of `3 ^ L`.

## Main results

* `Cslib.card_majTree_ne_le`, `Cslib.sum_majTree_ne_le`: amplification by majority trees.
* `Cslib.sum_majTree_succ_ne_le`: one level of a majority tree over weighted outcomes.
* `Cslib.exists_forall_majTree_eq`, `Cslib.exists_forall_majTree_eq_of_sum`: one choice of
  outcomes is right across a whole set.
* `Cslib.exists_forall_majTree_majTree_eq`: Valiant's amplification from advantage `ε`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
* [L. G. Valiant, *Short monotone formulae for the majority function*][Valiant1984Majority]
* [ChukhinKulikovMihajlinSmal2026], Lemma 3.7
-/

@[expose] public section

namespace Cslib

open Finset

variable {α : Type*} [DecidableEq α]

/-- The majority of three, right whenever two of its arguments are: `a` if `a = b`, else `c`. -/
def maj3 (a b c : α) : α := if a = b then a else c

/-- If `maj3 a b c` misses `y`, then two of `a`, `b`, `c` miss `y`. -/
theorem two_ne_of_maj3_ne {a b c y : α} (h : maj3 a b c ≠ y) :
    (a ≠ y ∧ b ≠ y) ∨ (a ≠ y ∧ c ≠ y) ∨ (b ≠ y ∧ c ≠ y) := by
  unfold maj3 at h
  split_ifs at h with hab
  · subst hab
    exact Or.inl ⟨h, h⟩
  · by_cases ha : a = y
    · subst ha
      exact Or.inr (Or.inr ⟨Ne.symm hab, h⟩)
    · exact Or.inr (Or.inl ⟨ha, h⟩)

/-- The splitting of `3 ^ (L + 1)` leaves into three blocks of `3 ^ L`. -/
def tripleEquiv (L : ℕ) : Fin 3 × Fin (3 ^ L) ≃ Fin (3 ^ (L + 1)) :=
  finProdFinEquiv.trans (finCongr (pow_succ' 3 L).symm)

/-- **A majority tree** of depth `L` over `3 ^ L` values: the majority of three of the trees over
the three blocks. -/
def majTree : (L : ℕ) → (Fin (3 ^ L) → α) → α
  | 0, f => f ⟨0, by simp⟩
  | L + 1, f => maj3 (majTree L fun k => f (tripleEquiv L (0, k)))
      (majTree L fun k => f (tripleEquiv L (1, k))) (majTree L fun k => f (tripleEquiv L (2, k)))

/-! ### Majority trees over weighted outcomes

Each outcome `ω` carries a weight `w ω ≥ 0`, and a tuple `V` of outcomes the product weight
`∏ i, w (V i)`: for a probability vector `w` these are independent draws, and for `w = 1` the
weights count tuples. -/

section Weighted

variable {Ω : Type*} [Fintype Ω] {w : Ω → ℝ}

/-- Summing a product of one function of each of three coordinates over all triples. -/
private theorem sum_fin_three_mul {β : Type*} [Fintype β] (f g h : β → ℝ) :
    ∑ U : Fin 3 → β, f (U 0) * g (U 1) * h (U 2) = (∑ b, f b) * (∑ b, g b) * ∑ b, h b := by
  have := (Fintype.prod_sum (fun j : Fin 3 => ![f, g, h] j)).symm
  simpa [Fin.prod_univ_three] using this

omit [DecidableEq α] in
/-- The total product weight of the tuples of `n` outcomes. -/
theorem sum_prod_weight (w : Ω → ℝ) (n : ℕ) :
    ∑ V : Fin n → Ω, ∏ i, w (V i) = (∑ ω, w ω) ^ n := by
  rw [← Fintype.prod_sum]
  simp

/-- A majority tree of depth `0` is its single leaf. -/
theorem sum_majTree_zero_ne (w : Ω → ℝ) (val : Ω → α) (y : α) :
    ∑ V : Fin (3 ^ 0) → Ω with majTree 0 (val ∘ V) ≠ y, ∏ i, w (V i) =
      ∑ ω with val ω ≠ y, w ω := by
  have : Subsingleton (Fin (3 ^ 0)) := inferInstanceAs (Subsingleton (Fin 1))
  rw [sum_filter, sum_filter]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) Ω) _ _ fun V => ?_
  rw [Fintype.prod_subsingleton _ ⟨0, by simp⟩]
  rfl

/-- **One level of a majority tree** over weighted outcomes. If the subtrees of depth `L` miss `y`
on tuples of total weight `B`, out of the total weight `T = (∑ ω, w ω) ^ (3 ^ L)`, then the tree
of depth `L + 1` misses `y` on weight at most `3 B² T - 2 B³`, the weight on which at least two of
its three independent subtrees miss. For `T = 1` this is the error `q ↦ q² (3 - 2q)` of a
three-input majority of independent votes. -/
theorem sum_majTree_succ_ne_le (hw : ∀ ω, 0 ≤ w ω) (val : Ω → α) (y : α) (L : ℕ) :
    ∑ V : Fin (3 ^ (L + 1)) → Ω with majTree (L + 1) (val ∘ V) ≠ y, ∏ i, w (V i) ≤
      3 * (∑ V : Fin (3 ^ L) → Ω with majTree L (val ∘ V) ≠ y, ∏ i, w (V i)) ^ 2 *
          (∑ ω, w ω) ^ 3 ^ L -
        2 * (∑ V : Fin (3 ^ L) → Ω with majTree L (val ∘ V) ≠ y, ∏ i, w (V i)) ^ 3 := by
  classical
  set B := ∑ V : Fin (3 ^ L) → Ω with majTree L (val ∘ V) ≠ y, ∏ i, w (V i)
  set P : (Fin (3 ^ L) → Ω) → ℝ := fun U => ∏ k, w (U k)
  set β : (Fin (3 ^ L) → Ω) → ℝ := fun U => if majTree L (val ∘ U) ≠ y then 1 else 0
  have hβP : ∑ U, β U * P U = B := by
    simp only [β, P, ite_mul, one_mul, zero_mul, B, sum_filter]
  have hP0 (U) : 0 ≤ P U := prod_nonneg fun k _ => hw _
  -- the three blocks of a tuple
  let e : (Fin (3 ^ (L + 1)) → Ω) ≃ (Fin 3 → Fin (3 ^ L) → Ω) :=
    (Equiv.arrowCongr (tripleEquiv L).symm (Equiv.refl Ω)).trans (Equiv.curry _ _ _)
  have he (V : Fin (3 ^ (L + 1)) → Ω) (j k) : e V j k = V (tripleEquiv L (j, k)) := rfl
  have hprod (V : Fin (3 ^ (L + 1)) → Ω) : ∏ i, w (V i) = ∏ j, P (e V j) := by
    simp only [P, he, ← Fintype.prod_prod_type']
    exact (Fintype.prod_equiv (tripleEquiv L) _ _ fun _ => rfl).symm
  -- at least two of three blocks miss, as an expression in their indicators
  let two (U : Fin 3 → Fin (3 ^ L) → Ω) : ℝ :=
    β (U 0) * β (U 1) + β (U 0) * β (U 2) + β (U 1) * β (U 2) - 2 * (β (U 0) * β (U 1) * β (U 2))
  have htwo (V : Fin (3 ^ (L + 1)) → Ω) :
      (if majTree (L + 1) (val ∘ V) ≠ y then (1 : ℝ) else 0) ≤ two (e V) := by
    have hm : majTree (L + 1) (val ∘ V) = maj3 (majTree L (val ∘ e V 0))
        (majTree L (val ∘ e V 1)) (majTree L (val ∘ e V 2)) := rfl
    rw [hm]
    by_cases h : maj3 (majTree L (val ∘ e V 0)) (majTree L (val ∘ e V 1))
        (majTree L (val ∘ e V 2)) = y
    · simp only [h, ne_eq, not_true_eq_false, ↓reduceIte, two, β]
      split_ifs <;> norm_num
    · simp only [h, ne_eq, not_false_eq_true, ↓reduceIte, two, β]
      rcases two_ne_of_maj3_ne h with ⟨h₀, h₁⟩ | ⟨h₀, h₂⟩ | ⟨h₁, h₂⟩ <;> split_ifs <;> norm_num
  calc ∑ V : Fin (3 ^ (L + 1)) → Ω with majTree (L + 1) (val ∘ V) ≠ y, ∏ i, w (V i)
      = ∑ V, (if majTree (L + 1) (val ∘ V) ≠ y then (1 : ℝ) else 0) * ∏ j, P (e V j) := by
        rw [sum_filter]
        exact sum_congr rfl fun V _ => by rw [hprod, ite_mul, one_mul, zero_mul]
    _ ≤ ∑ V, two (e V) * ∏ j, P (e V j) :=
        sum_le_sum fun V _ => mul_le_mul_of_nonneg_right (htwo V)
          (prod_nonneg fun j _ => hP0 _)
    _ = ∑ U, two U * ∏ j, P (U j) := e.sum_comp fun U => two U * ∏ j, P (U j)
    _ = ∑ U : Fin 3 → Fin (3 ^ L) → Ω, ((β (U 0) * P (U 0)) * (β (U 1) * P (U 1)) * P (U 2) +
          (β (U 0) * P (U 0)) * P (U 1) * (β (U 2) * P (U 2)) +
          P (U 0) * (β (U 1) * P (U 1)) * (β (U 2) * P (U 2)) -
          2 * ((β (U 0) * P (U 0)) * (β (U 1) * P (U 1)) * (β (U 2) * P (U 2)))) := by
        refine sum_congr rfl fun U _ => ?_
        rw [Fin.prod_univ_three]
        ring
    _ = 3 * B ^ 2 * (∑ ω, w ω) ^ 3 ^ L - 2 * B ^ 3 := by
        have hT : ∑ U, P U = (∑ ω, w ω) ^ 3 ^ L := sum_prod_weight w _
        have h₁ := sum_fin_three_mul (fun u => β u * P u) (fun u => β u * P u) P
        have h₂ := sum_fin_three_mul (fun u => β u * P u) P (fun u => β u * P u)
        have h₃ := sum_fin_three_mul P (fun u => β u * P u) (fun u => β u * P u)
        have h₄ := sum_fin_three_mul (fun u => β u * P u) (fun u => β u * P u)
          (fun u => β u * P u)
        simp only [hβP, hT] at h₁ h₂ h₃ h₄
        rw [sum_sub_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum, h₁, h₂, h₃, h₄]
        ring

/-- **Amplification by majority trees** over weighted outcomes. If the outcomes `ω` with
`val ω ≠ y` have at most a `ρ` fraction of the total weight, then the tuples of `3 ^ L` outcomes
that make the majority tree miss `y` have at most a `(3 * ρ) ^ (2 ^ L) / 3` fraction. -/
theorem sum_majTree_ne_le (hw : ∀ ω, 0 ≤ w ω) (val : Ω → α) (y : α) {ρ : ℝ}
    (hρ : ∑ ω with val ω ≠ y, w ω ≤ ρ * ∑ ω, w ω) (L : ℕ) :
    ∑ V : Fin (3 ^ L) → Ω with majTree L (val ∘ V) ≠ y, ∏ i, w (V i) ≤
      (3 * ρ) ^ (2 ^ L) / 3 * (∑ ω, w ω) ^ (3 ^ L) := by
  induction L with
  | zero =>
    rw [sum_majTree_zero_ne]
    simpa using hρ
  | succ L ih =>
    set B := ∑ V : Fin (3 ^ L) → Ω with majTree L (val ∘ V) ≠ y, ∏ i, w (V i)
    set T := (∑ ω, w ω) ^ 3 ^ L
    have hB0 : 0 ≤ B := sum_nonneg fun V _ => prod_nonneg fun i _ => hw _
    have hT0 : 0 ≤ T := pow_nonneg (sum_nonneg fun ω _ => hw ω) _
    have hX : 0 ≤ (3 * ρ) ^ (2 ^ L) / 3 * T := hB0.trans ih
    calc _ ≤ 3 * B ^ 2 * T - 2 * B ^ 3 := sum_majTree_succ_ne_le hw val y L
      _ ≤ 3 * (((3 * ρ) ^ (2 ^ L) / 3 * T) * ((3 * ρ) ^ (2 ^ L) / 3 * T) * T) := by
          have := mul_le_mul ih ih hB0 hX
          nlinarith [pow_nonneg hB0 3, mul_le_mul_of_nonneg_right this hT0]
      _ = (3 * ρ) ^ (2 ^ (L + 1)) / 3 * (∑ ω, w ω) ^ (3 ^ (L + 1)) := by
          rw [pow_succ 2 L, pow_mul, pow_succ 3 L, pow_mul]
          ring

/-- **Amplification by majority trees.** If at most a `ρ` fraction of the outcomes `ω` have
`val ω ≠ y`, then at most a `(3 * ρ) ^ (2 ^ L) / 3` fraction of the tuples of `3 ^ L` outcomes
make the majority tree miss `y`. This is `sum_majTree_ne_le` with unit weights. -/
theorem card_majTree_ne_le {Ω : Type*} [Fintype Ω] (val : Ω → α) (y : α)
    {ρ : ℝ} (hρ : (#{ω | val ω ≠ y} : ℝ) ≤ ρ * Fintype.card Ω) (L : ℕ) :
    (#{V : Fin (3 ^ L) → Ω | majTree L (val ∘ V) ≠ y} : ℝ) ≤
      (3 * ρ) ^ (2 ^ L) / 3 * Fintype.card Ω ^ (3 ^ L) := by
  simpa using sum_majTree_ne_le (w := fun _ : Ω => (1 : ℝ)) (fun _ => zero_le_one) val y
    (by simpa using hρ) L

/-- **One choice of outcomes corrects a whole set**, over weighted outcomes. Let `val x`, for each
`x` in a set `S` of at most `2 ^ (2 ^ L)` inputs, miss `target x` on at most a `ρ` fraction of the
total weight, with `3 * ρ ≤ 1 / 2`. Then some tuple of `3 ^ L` outcomes makes the majority tree
right at every `x ∈ S`. -/
theorem exists_forall_majTree_eq_of_sum {X : Type*} (hw : ∀ ω, 0 ≤ w ω) (hpos : 0 < ∑ ω, w ω)
    (S : Finset X) (val : X → Ω → α) (target : X → α) {ρ : ℝ}
    (hρ : ∀ x ∈ S, ∑ ω with val x ω ≠ target x, w ω ≤ ρ * ∑ ω, w ω)
    (h3 : 3 * ρ ≤ 1 / 2) {L : ℕ} (hS : #S ≤ 2 ^ (2 ^ L)) :
    ∃ V : Fin (3 ^ L) → Ω, ∀ x ∈ S, majTree L (val x ∘ V) = target x := by
  classical
  by_contra hcon
  push Not at hcon
  have : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hpos
  obtain ⟨x₀, hx₀, -⟩ := hcon (fun _ => Classical.arbitrary Ω)
  have hρ0 : 0 ≤ ρ := by
    have := hρ x₀ hx₀
    have h0 : 0 ≤ ∑ ω with val x₀ ω ≠ target x₀, w ω := sum_nonneg fun ω _ => hw ω
    by_contra hneg
    push Not at hneg
    nlinarith
  set T := (∑ ω, w ω) ^ (3 ^ L)
  have hT : 0 < T := pow_pos hpos _
  set P : (Fin (3 ^ L) → Ω) → ℝ := fun V => ∏ i, w (V i)
  have hP0 (V) : 0 ≤ P V := prod_nonneg fun i _ => hw _
  -- every tuple is wrong somewhere, so the wrong weights cover the total weight
  have hcover : T ≤ ∑ x ∈ S, ∑ V : Fin (3 ^ L) → Ω with majTree L (val x ∘ V) ≠ target x, P V := by
    rw [show T = ∑ V : Fin (3 ^ L) → Ω, P V from (sum_prod_weight w _).symm]
    simp only [sum_filter]
    rw [sum_comm]
    refine sum_le_sum fun V _ => ?_
    obtain ⟨x, hx, hne⟩ := hcon V
    calc P V = if majTree L (val x ∘ V) ≠ target x then P V else 0 := by simp [hne]
      _ ≤ ∑ x ∈ S, if majTree L (val x ∘ V) ≠ target x then P V else 0 :=
          single_le_sum (f := fun x => if majTree L (val x ∘ V) ≠ target x then P V else 0)
            (fun x _ => by split_ifs <;> simp [hP0]) hx
  have hsum : T ≤ #S * ((3 * ρ) ^ (2 ^ L) / 3 * T) := by
    calc T ≤ _ := hcover
      _ ≤ ∑ _x ∈ S, (3 * ρ) ^ (2 ^ L) / 3 * T :=
          sum_le_sum fun x hx => sum_majTree_ne_le hw (val x) (target x) (hρ x hx) L
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hpow : (3 * ρ) ^ (2 ^ L) ≤ (1 / 2) ^ (2 ^ L) := by gcongr
  have hS' : (#S : ℝ) * (1 / 2) ^ (2 ^ L) ≤ 1 := by
    rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact_mod_cast hS
  have h1 : (#S : ℝ) * (3 * ρ) ^ (2 ^ L) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hpow (by positivity)).trans hS'
  nlinarith

/-- **One choice of randomness corrects a whole set.** Let a randomized procedure `val x`, for
each `x` in a set `S` of at most `2 ^ (2 ^ L)` inputs, miss `target x` on at most a `ρ` fraction of
its outcomes, with `3 * ρ ≤ 1 / 2`. Then some tuple of `3 ^ L` outcomes makes the majority tree
right at every `x ∈ S`. This is `exists_forall_majTree_eq_of_sum` with unit weights. -/
theorem exists_forall_majTree_eq {X Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (S : Finset X) (val : X → Ω → α) (target : X → α) {ρ : ℝ}
    (hρ : ∀ x ∈ S, (#{ω | val x ω ≠ target x} : ℝ) ≤ ρ * Fintype.card Ω)
    (h3 : 3 * ρ ≤ 1 / 2) {L : ℕ} (hS : #S ≤ 2 ^ (2 ^ L)) :
    ∃ V : Fin (3 ^ L) → Ω, ∀ x ∈ S, majTree L (val x ∘ V) = target x :=
  exists_forall_majTree_eq_of_sum (w := fun _ : Ω => (1 : ℝ)) (fun _ => zero_le_one)
    (by simpa using Fintype.card_pos) S val target (fun x hx => by simpa using hρ x hx) h3 hS

/-! ### Amplification from a small advantage -/

/-- The three-input majority error `q ↦ q² (3 - 2q)` is monotone on `[0, 1]`. -/
private theorem majErr_mono {e a : ℝ} (he : 0 ≤ e) (hea : e ≤ a) (ha : a ≤ 1) :
    3 * e ^ 2 - 2 * e ^ 3 ≤ 3 * a ^ 2 - 2 * a ^ 3 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hea) (mul_nonneg he (sub_nonneg.mpr (hea.trans ha))),
    mul_nonneg (sub_nonneg.mpr hea) (mul_nonneg (he.trans hea) (sub_nonneg.mpr ha)),
    mul_nonneg (sub_nonneg.mpr hea) (mul_nonneg he (sub_nonneg.mpr hea)),
    mul_nonneg (sub_nonneg.mpr hea) (sub_nonneg.mpr ha)]

/-- Near `1/2`, a majority level multiplies the advantage `c ≤ 1/4` by at least `11/8`. -/
private theorem majErr_half_sub_le {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1 / 4) :
    3 * (1 / 2 - c) ^ 2 - 2 * (1 / 2 - c) ^ 3 ≤ 1 / 2 - 11 / 8 * c := by
  nlinarith [mul_nonneg h0 (mul_nonneg h0 h0), mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.mpr h1)]

/-- Along the levels of a majority tree over a probability vector `w`, the advantage over `1/2`
grows by `11/8` per level until it reaches `1/4`. -/
private theorem sum_majTree_ne_le_half_sub (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    (val : Ω → α) (y : α) {ε : ℝ} (hε : 0 ≤ ε) (h : ∑ ω with val ω ≠ y, w ω ≤ 1 / 2 - ε)
    (L : ℕ) : ∑ V : Fin (3 ^ L) → Ω with majTree L (val ∘ V) ≠ y, ∏ i, w (V i) ≤
      1 / 2 - min (1 / 4) ((11 / 8) ^ L * ε) := by
  induction L with
  | zero =>
    rw [sum_majTree_zero_ne]
    have := min_le_right (1 / 4 : ℝ) ε
    simp only [pow_zero, one_mul]
    linarith
  | succ L ih =>
    set B := ∑ V : Fin (3 ^ L) → Ω with majTree L (val ∘ V) ≠ y, ∏ i, w (V i)
    set c := min (1 / 4) ((11 / 8) ^ L * ε)
    have hB0 : 0 ≤ B := sum_nonneg fun V _ => prod_nonneg fun i _ => hw _
    have hc0 : 0 ≤ c := le_min (by norm_num) (by positivity)
    have hc1 : c ≤ 1 / 4 := min_le_left _ _
    have hstep := sum_majTree_succ_ne_le hw val y L
    rw [hw1, one_pow, mul_one] at hstep
    have hmono := majErr_mono hB0 ih (by linarith)
    have hgrow := majErr_half_sub_le hc0 hc1
    have hmin : min (1 / 4) ((11 / 8) ^ (L + 1) * ε) ≤ 11 / 8 * c := by
      rcases min_choice (1 / 4 : ℝ) ((11 / 8) ^ L * ε) with h | h
      · rw [show c = 1 / 4 from h]; exact (min_le_left _ _).trans (by norm_num)
      · rw [show c = (11 / 8) ^ L * ε from h, pow_succ]
        exact (min_le_right _ _).trans (le_of_eq (by ring))
    linarith

/-- **Valiant's amplification** [Valiant1984Majority] over a probability vector `w`, in the form
of [ChukhinKulikovMihajlinSmal2026], Lemma 3.7 (printed p. 8; PDF p. 9). Let `val x` miss
`target x` on weight at most `1/2 - ε`, for each `x` in a set `S` of at most `2 ^ (2 ^ m₂)` inputs.
If `(11/8) ^ m₁ * ε ≥ 1/4`, some majority tree of depth `m₂` over majority trees of depth `m₁ + 1`
is right at every `x ∈ S`: the inner trees raise the advantage to `1/4` and then push the error
below `1/6`, and the outer tree is `exists_forall_majTree_eq_of_sum`. -/
theorem exists_forall_majTree_majTree_eq {X : Type*} (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    (S : Finset X) (val : X → Ω → α) (target : X → α) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x ∈ S, ∑ ω with val x ω ≠ target x, w ω ≤ 1 / 2 - ε)
    {m₁ m₂ : ℕ} (hm₁ : 1 / 4 ≤ (11 / 8) ^ m₁ * ε) (hS : #S ≤ 2 ^ (2 ^ m₂)) :
    ∃ V : Fin (3 ^ m₂) → Fin (3 ^ (m₁ + 1)) → Ω,
      ∀ x ∈ S, majTree m₂ (fun i => majTree (m₁ + 1) (val x ∘ V i)) = target x := by
  have hw' (U : Fin (3 ^ (m₁ + 1)) → Ω) : 0 ≤ ∏ i, w (U i) := prod_nonneg fun i _ => hw _
  have hw1' : ∑ U : Fin (3 ^ (m₁ + 1)) → Ω, ∏ i, w (U i) = 1 := by
    rw [sum_prod_weight, hw1, one_pow]
  refine exists_forall_majTree_eq_of_sum hw' (by rw [hw1']; norm_num) S
    (fun x U => majTree (m₁ + 1) (val x ∘ U)) target (ρ := 5 / 32) (fun x hx => ?_) (by norm_num)
    hS
  rw [hw1', mul_one]
  have hm := sum_majTree_ne_le_half_sub hw hw1 (val x) (target x) hε (h x hx) m₁
  rw [min_eq_left hm₁] at hm
  have hstep := sum_majTree_succ_ne_le hw (val x) (target x) m₁
  rw [hw1, one_pow, mul_one] at hstep
  have h0 : 0 ≤ ∑ V : Fin (3 ^ m₁) → Ω with majTree m₁ (val x ∘ V) ≠ target x, ∏ i, w (V i) :=
    sum_nonneg fun V _ => prod_nonneg fun i _ => hw _
  have := majErr_mono h0 (show _ ≤ (1 / 4 : ℝ) by linarith) (by norm_num)
  norm_num at this ⊢
  linarith

end Weighted

end Cslib
