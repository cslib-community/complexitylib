/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Complexity.Probability.KWiseIndependent
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Limited independence fools clause counts

A clause with `j` distinct literals and no complementary pair is falsified by a uniformly random
assignment with probability `2 ^ -j`, and this computation reads the values of only `j` variables.
So a `k`-wise independent family of assignments falsifies each clause with probability at most
`2 ^ -min k j`, and by linearity of expectation it falsifies on average at most `Σ_c 2 ^ -min k |c|`
clauses [Alon and Spencer, Section 16.2][AlonSpencer2016]. When every clause has at least `k`
distinct literals some member of the family falsifies at most `2 ^ -k` of the clauses, the bound
that a uniformly random assignment gives for MAX-E`k`-SAT. A family with polynomially many seeds
can then be searched exhaustively; `Complexity.Logics.Propositional.CNF.ParitySearch` does this for
`k = 3`.

The assignments are `h i ∘ e`, where the bits `h i x` are `k`-wise independent over the seed `i`
(`Cslib.Probability.IsKWiseIndependentHash`) and `e` maps the variables of the formula injectively
to the points `x`. Clauses may repeat literals; a clause containing a complementary pair is never
falsified.

## Main results

* `Cslib.Logic.PL.expect_indicator_eval_eq_false_le`: one clause is falsified with probability at
  most `2 ^ -min k |c|`.
* `Cslib.Logic.PL.expect_countUnsat_le`, `Cslib.Logic.PL.exists_countUnsat_le`: the average number
  of falsified clauses is at most `Σ_c 2 ^ -min k |c|`, and some seed does as well.
* `Cslib.Logic.PL.exists_two_pow_mul_countUnsat_le`: if every clause has at least `k` distinct
  literals, some seed falsifies at most `2 ^ -k` of the clauses.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Section 16.2][AlonSpencer2016]
-/

public section

namespace Cslib.Logic.PL

open Finset Cslib.Probability
open scoped BigOperators

variable {V ι X : Type*} [Fintype ι] [DecidableEq V]

/-- The indicator that `σ` falsifies `c` is at most the product, over any set of literals of
`c`, of the indicators that `σ` falsifies each of them. -/
theorem indicator_eval_eq_false_le_prod (σ : V → Bool) (c : Clause V) {S : Finset (Literal V)}
    (hS : S ⊆ c.toFinset) :
    (if c.eval σ = false then (1 : ℝ) else 0) ≤
      ∏ l ∈ S, if σ l.1 = !l.2 then (1 : ℝ) else 0 := by
  by_cases hc : c.eval σ = false
  · rw [ite_eq_left hc]
    refine le_of_eq (prod_eq_one fun l hl => ite_eq_left ?_).symm
    have hl : l ∈ c := List.mem_toFinset.1 (hS hl)
    have hne : σ l.1 ≠ l.2 := fun h => by
      rw [← Bool.not_eq_true, Clause.eval_eq_true_iff] at hc
      exact hc ⟨l, hl, h⟩
    cases h : σ l.1 <;> cases h' : l.2 <;> simp_all
  · rw [ite_eq_right hc]
    exact prod_nonneg fun _ _ => by positivity

/-- **Limited independence and one clause**: if the bits `h i x` are `k`-wise independent and `e`
is injective on the variables of `c`, then the assignment `h i ∘ e` falsifies `c` with probability
at most `2 ^ -min k |c|`, where `|c|` is the number of distinct literals of `c`. -/
theorem expect_indicator_eval_eq_false_le {k : ℕ} {h : ι → X → Bool}
    (hh : IsKWiseIndependentHash k h) {e : V → X} (c : Clause V)
    (he : ∀ l ∈ c, ∀ l' ∈ c, e l.1 = e l'.1 → l.1 = l'.1) :
    𝔼 i, (if c.eval (h i ∘ e) = false then (1 : ℝ) else 0) ≤
      (2 : ℝ)⁻¹ ^ min k c.toFinset.card := by
  classical
  by_cases hcomp : ∃ l ∈ c, ∃ l' ∈ c, l.1 = l'.1 ∧ l.2 ≠ l'.2
  · -- a clause with a complementary pair is never falsified
    obtain ⟨l, hl, l', hl', hv, hb⟩ := hcomp
    have hzero : ∀ i, (if c.eval (h i ∘ e) = false then (1 : ℝ) else 0) = 0 := fun i => by
      rw [ite_eq_right]
      rw [Bool.not_eq_false, Clause.eval_eq_true_iff]
      by_cases hσ : (h i ∘ e) l.1 = l.2
      · exact ⟨l, hl, hσ⟩
      · refine ⟨l', hl', ?_⟩
        rw [← hv]
        cases h1 : (h i ∘ e) l.1 <;> cases h2 : l.2 <;> cases h3 : l'.2 <;> simp_all
    simp only [hzero, expect_const_zero]
    positivity
  push Not at hcomp
  obtain ⟨S, hSc, hScard⟩ := exists_subset_card_eq (min_le_right k c.toFinset.card)
  -- the literals of `S` have distinct images under `e ∘ Prod.fst`
  have hinj : Set.InjOn (fun l : Literal V => e l.1) S := fun l hl l' hl' hll' => by
    have hl := List.mem_toFinset.1 (hSc hl)
    have hl' := List.mem_toFinset.1 (hSc hl')
    have hv := he l hl l' hl' hll'
    exact Prod.ext hv (hcomp l hl l' hl' hv)
  have hS : #(S.image fun l => e l.1) ≤ k := by
    rw [card_image_of_injOn hinj, hScard]
    exact min_le_left _ _
  -- the falsifying value at each point of the image of `S`
  let target : X → Bool := fun x =>
    if hx : ∃ l ∈ S, e l.1 = x then !hx.choose.2 else false
  have htarget : ∀ l ∈ S, target (e l.1) = !l.2 := fun l hl => by
    have hx : ∃ l' ∈ S, e l'.1 = e l.1 := ⟨l, hl, rfl⟩
    simp only [target, dite_eq_left hx]
    rw [hinj hx.choose_spec.1 hl hx.choose_spec.2]
  have hcoin : ∀ b : Bool, 𝔼 y : Bool, (if y = b then (1 : ℝ) else 0) = 2⁻¹ := fun b => by
    rw [Fintype.expect_eq_sum_div_card, Fintype.sum_bool]
    cases b <;> norm_num
  calc 𝔼 i, (if c.eval (h i ∘ e) = false then (1 : ℝ) else 0)
      ≤ 𝔼 i, ∏ l ∈ S, if (h i ∘ e) l.1 = !l.2 then (1 : ℝ) else 0 :=
        expect_le_expect fun i _ => indicator_eval_eq_false_le_prod _ c hSc
    _ = 𝔼 i, ∏ x ∈ S.image (fun l => e l.1), if h i x = target x then (1 : ℝ) else 0 := by
        refine expect_congr rfl fun i _ => ?_
        rw [prod_image hinj]
        exact prod_congr rfl fun l hl => by rw [Function.comp_apply, htarget l hl]
    _ = ∏ x ∈ S.image (fun l => e l.1), 𝔼 y : Bool, if y = target x then (1 : ℝ) else 0 :=
        hh.expect_prod hS fun x y => if y = target x then (1 : ℝ) else 0
    _ = (2 : ℝ)⁻¹ ^ min k c.toFinset.card := by
        simp only [hcoin, prod_const, card_image_of_injOn hinj, hScard]

/-- **Limited independence and clause counts**: if the bits `h i x` are `k`-wise independent and
`e` is injective on the variables of `φ`, then the expected number of clauses that `h i ∘ e`
falsifies is at most `Σ_c 2 ^ -min k |c|`, counting distinct literals. -/
theorem expect_countUnsat_le {k : ℕ} {h : ι → X → Bool} (hh : IsKWiseIndependentHash k h)
    {e : V → X} (φ : CNF V) (he : ∀ v ∈ φ.vars, ∀ w ∈ φ.vars, e v = e w → v = w) :
    𝔼 i, (φ.countUnsat (h i ∘ e) : ℝ) ≤
      (φ.map fun c => (2 : ℝ)⁻¹ ^ min k c.toFinset.card).sum := by
  induction φ with
  | nil => simp [CNF.countUnsat]
  | cons c φ ih =>
    have hvars : ∀ v ∈ CNF.vars φ, v ∈ CNF.vars (c :: φ) := fun v hv => by
      obtain ⟨c', hc', b, hb⟩ := CNF.mem_vars.1 hv
      exact CNF.mem_vars.2 ⟨c', List.mem_cons_of_mem _ hc', b, hb⟩
    have hc : ∀ l ∈ c, l.1 ∈ CNF.vars (c :: φ) := fun l hl =>
      CNF.mem_vars.2 ⟨c, List.mem_cons_self, l.2, hl⟩
    have ih := ih fun v hv w hw => he v (hvars v hv) w (hvars w hw)
    have h1 := expect_indicator_eval_eq_false_le hh c fun l hl l' hl' =>
      he l.1 (hc l hl) l'.1 (hc l' hl')
    have hsplit : ∀ i, (CNF.countUnsat (h i ∘ e) (c :: φ) : ℝ) =
        (if c.eval (h i ∘ e) = false then (1 : ℝ) else 0) + (CNF.countUnsat (h i ∘ e) φ : ℝ) :=
      fun i => by
        simp only [CNF.countUnsat, List.countP_cons]
        cases c.eval (h i ∘ e) <;> simp [add_comm]
    simp only [hsplit, expect_add_distrib, List.map_cons, List.sum_cons]
    exact add_le_add h1 ih

/-- Some seed attains the bound of `Cslib.Logic.PL.expect_countUnsat_le`. -/
theorem exists_countUnsat_le {k : ℕ} {h : ι → X → Bool} (hh : IsKWiseIndependentHash k h)
    {e : V → X} (φ : CNF V) (he : ∀ v ∈ φ.vars, ∀ w ∈ φ.vars, e v = e w → v = w) :
    ∃ i, (φ.countUnsat (h i ∘ e) : ℝ) ≤
      (φ.map fun c => (2 : ℝ)⁻¹ ^ min k c.toFinset.card).sum := by
  have := hh.nonempty
  obtain ⟨i, -, hi⟩ := exists_le_of_expect_le univ_nonempty (expect_countUnsat_le hh φ he)
  exact ⟨i, hi⟩

/-- **Limited independence for MAX-E`k`-SAT**: if every clause has at least `k` distinct
literals, some seed of a `k`-wise independent family falsifies at most `2 ^ -k` of the clauses. -/
theorem exists_two_pow_mul_countUnsat_le {k : ℕ} {h : ι → X → Bool}
    (hh : IsKWiseIndependentHash k h) {e : V → X} {φ : CNF V}
    (he : ∀ v ∈ φ.vars, ∀ w ∈ φ.vars, e v = e w → v = w)
    (hk : ∀ c ∈ φ, k ≤ c.toFinset.card) :
    ∃ i, 2 ^ k * φ.countUnsat (h i ∘ e) ≤ φ.length := by
  obtain ⟨i, hi⟩ := exists_countUnsat_le hh φ he
  refine ⟨i, ?_⟩
  have hsum : (φ.map fun c => (2 : ℝ)⁻¹ ^ min k c.toFinset.card).sum =
      φ.length * (2 : ℝ)⁻¹ ^ k := by
    rw [List.map_congr_left (g := fun _ => (2 : ℝ)⁻¹ ^ k) fun c hc => by
        rw [min_eq_left (hk c hc)],
      List.map_const', List.sum_replicate, nsmul_eq_mul]
  rw [hsum] at hi
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have : ((2 ^ k * φ.countUnsat (h i ∘ e) : ℕ) : ℝ) ≤ φ.length := by
    push_cast
    calc (2 : ℝ) ^ k * φ.countUnsat (h i ∘ e) ≤ 2 ^ k * (φ.length * (2 : ℝ)⁻¹ ^ k) :=
          mul_le_mul_of_nonneg_left hi h2.le
      _ = φ.length := by rw [inv_pow, mul_left_comm, mul_inv_cancel₀ h2.ne', mul_one]
  exact_mod_cast this

end Cslib.Logic.PL
