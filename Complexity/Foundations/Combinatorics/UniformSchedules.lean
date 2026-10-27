/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.BalancedSchedules
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite uniform averages and existence of balanced label schedules

This module develops the finite-average step and schedule-existence proof of Lemma 4.5,
printed pp. 30–31 of `[OpenAI2026ETH]`:

1. **Schedule marginals and expected potentials:**
   - A sampled schedule is a single function: repeated access to one variable reads the same
     coordinate (`expect_schedule_apply`, `expect_schedule_apply_apply`,
     `expect_schedule_collision`).
   - Exact finite-uniform occupancy variance `expect_potential` and expected total group potential
     `expect_group_potential` ($\mathbb{E}\Xi = Q n (1 - 1 / r) \le Q n$,
     `expect_group_potential_le`).
   - Product formula `expect_incidence_collision` for incidence-label collisions and the upper
     bound `expect_incidence_potential_le` ($\mathbb{E}\Phi \le M (b + w)$) when each variable
     belongs to at most `b` incidences and each factor contains at most `w` incidences.

2. **Finite-average selection and conditional expectation step:**
   - `exists_le_expect` and `exists_coord_expect_le` (fixing one schedule coordinate at a time
     without increasing the conditional expectation over the remaining coordinates).
   - `normalizeEmptyFactors`: setting $d_f(t) = g_0$ on factors with no incidences in `A` leaves
     all incidence labels `(a (varOf e), d (factorOf e))` unchanged
     (`incidenceLabel_normalizeEmptyFactors`).
   - `exists_balanced_schedules` and `exists_balanced_schedules_of_scopes`: full existence
     statement of Lemma 4.5 from the size hypotheses (4.13).

Finite averages are mathematical sums, not runtime certificates.

## References

* [OpenAI2026ETH]
-/

public section

namespace Cslib.BalancedSchedules

open Finset
open scoped BigOperators

variable {A L : Type*} [Fintype A] [DecidableEq A] [Fintype L] [Nonempty L]

/-- A uniform average over a product is the iterated finite average. -/
private theorem expect_prod {X Y : Type*} [Fintype X] [Fintype Y] (f : X × Y → ℚ) :
    (𝔼 p, f p) = 𝔼 x, 𝔼 y, f (x, y) := by
  simpa only [univ_product_univ] using expect_product univ univ f

/-- Accessing one coordinate of a uniformly enumerated function gives a uniform label. -/
theorem expect_schedule_apply (i : A) (f : L → ℚ) :
    (𝔼 a : A → L, f (a i)) = 𝔼 x, f x := by
  calc
    (𝔼 a : A → L, f (a i)) =
        𝔼 p : L × ({j : A // j ≠ i} → L), f p.1 :=
      Fintype.expect_equiv (Equiv.funSplitAt i L) _ _ (fun _ => rfl)
    _ = 𝔼 x : L, 𝔼 _ : ({j : A // j ≠ i} → L), f x := expect_prod _
    _ = 𝔼 x, f x := by simp only [Fintype.expect_const]

/-- Distinct coordinates of a uniformly enumerated function give two independent uniform
labels. The distinctness hypothesis is essential: a repeated coordinate is not resampled. -/
theorem expect_schedule_apply_apply (i j : A) (hji : j ≠ i) (f : L → L → ℚ) :
    (𝔼 a : A → L, f (a i) (a j)) = 𝔼 x, 𝔼 y, f x y := by
  calc
    (𝔼 a : A → L, f (a i) (a j)) =
        𝔼 p : L × ({k : A // k ≠ i} → L), f p.1 (p.2 ⟨j, hji⟩) :=
      Fintype.expect_equiv (Equiv.funSplitAt i L) _ _ (fun _ => rfl)
    _ = 𝔼 x : L, 𝔼 a : ({k : A // k ≠ i} → L), f x (a ⟨j, hji⟩) :=
      expect_prod _
    _ = 𝔼 x, 𝔼 y, f x y := by
      apply Finset.expect_congr rfl
      intro x _
      exact expect_schedule_apply (A := {k : A // k ≠ i}) (L := L) ⟨j, hji⟩ (f x)

/-- Exact collision average, retaining the diagonal case separately. -/
theorem expect_schedule_collision [DecidableEq L] (i j : A) :
    (𝔼 a : A → L, if a i = a j then (1 : ℚ) else 0) =
      if i = j then 1 else 1 / (Fintype.card L : ℚ) := by
  split_ifs with hij
  · subst j
    simp only [↓reduceIte, Fintype.expect_const]
  · rw [expect_schedule_apply_apply i j (Ne.symm hij)
      (fun x y : L => if x = y then (1 : ℚ) else 0)]
    simp [NNRat.smul_def]

/-- Exact finite-uniform occupancy variance. No independence is asserted for a repeated
source coordinate; its diagonal collision contributes one. -/
theorem expect_potential [DecidableEq L] :
    (𝔼 a : A → L, potential a) =
      (Fintype.card A : ℚ) * (1 - 1 / (Fintype.card L : ℚ)) := by
  have hL : 0 < Fintype.card L := Fintype.card_pos
  have hrow (i : A) :
      (∑ j : A, if i = j then (1 : ℚ) else 1 / (Fintype.card L : ℚ)) =
        (Fintype.card A : ℚ) / Fintype.card L + 1 - 1 / (Fintype.card L : ℚ) := by
    have hite (j : A) : (if i = j then (1 : ℚ) else 1 / (Fintype.card L : ℚ)) =
        1 / (Fintype.card L : ℚ) +
          if i = j then (1 - 1 / (Fintype.card L : ℚ)) else 0 := by
      split_ifs <;> ring
    simp_rw [hite]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    ring
  simp_rw [potential_eq_collisions_sub _ hL]
  rw [Finset.expect_sub_distrib, Fintype.expect_const]
  simp_rw [Finset.expect_sum_comm, expect_schedule_collision]
  simp only [hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The expected total group potential for a schedule family. Every variable has one whole
schedule, reused at all points; swapping the two function indices just enumerates that same data. -/
theorem expect_group_potential {T V G : Type*} [Fintype T] [DecidableEq T]
    [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Nonempty G] :
    (𝔼 a : V → T → G, ∑ t, potential (fun v => a v t)) =
      (Fintype.card T : ℚ) * Fintype.card V * (1 - 1 / (Fintype.card G : ℚ)) := by
  calc
    (𝔼 a : V → T → G, ∑ t, potential (fun v => a v t)) =
        𝔼 a : T → V → G, ∑ t, potential (a t) :=
      Fintype.expect_equiv (Equiv.piComm (fun _ : V => fun _ : T => G)) _ _ (fun _ => rfl)
    _ = ∑ t : T, 𝔼 a : T → V → G, potential (a t) :=
      Finset.expect_sum_comm _ _ _
    _ = ∑ _ : T, (Fintype.card V : ℚ) * (1 - 1 / (Fintype.card G : ℚ)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [expect_schedule_apply t potential, expect_potential]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Exact average collision probability for two incidence labels. Only variable labels and
factor labels are independently enumerated; incidences sharing either endpoint stay correlated. -/
theorem expect_incidence_collision {V F : Type*} [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] [DecidableEq L] (v v' : V) (f f' : F) :
    (𝔼 a : V → L, 𝔼 d : F → L,
      if (a v, d f) = (a v', d f') then (1 : ℚ) else 0) =
      (if v = v' then 1 else 1 / (Fintype.card L : ℚ)) *
        (if f = f' then 1 else 1 / (Fintype.card L : ℚ)) := by
  have hd (a : V → L) :
      (𝔼 d : F → L, if (a v, d f) = (a v', d f') then (1 : ℚ) else 0) =
        (if a v = a v' then (1 : ℚ) else 0) *
          (if f = f' then 1 else 1 / (Fintype.card L : ℚ)) := by
    by_cases h : a v = a v'
    · simp only [Prod.mk.injEq, h, true_and, ↓reduceIte, one_mul]
      exact expect_schedule_collision f f'
    · simp only [Prod.mk.injEq, h, false_and, ↓reduceIte, zero_mul,
        Finset.expect_const_zero]
  simp_rw [hd]
  rw [← Finset.expect_mul, expect_schedule_collision]

/-- Upper bound `𝔼 Ξ ≤ |T| * |V|` on the expected total group potential (Lemma 4.5, p. 31). -/
theorem expect_group_potential_le {T V G : Type*} [Fintype T] [DecidableEq T]
    [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Nonempty G] :
    (𝔼 a : V → T → G, ∑ t, potential (fun v => a v t)) ≤
      (Fintype.card T : ℚ) * Fintype.card V := by
  rw [expect_group_potential]
  have hG : (0 : ℚ) ≤ 1 / (Fintype.card G : ℚ) := by positivity
  have hTV : (0 : ℚ) ≤ (Fintype.card T : ℚ) * Fintype.card V := by positivity
  nlinarith

/-- The incidence label map `u_e = (a (varOf e), d (factorOf e))` assigning each incidence `e : A`
the pair of schedules of its variable `varOf e` and its factor `factorOf e` (Section 4.4, p. 30). -/
@[expose] def incidenceLabel {A V F L : Type*} (varOf : A → V) (factorOf : A → F)
    (a : V → L) (d : F → L) (e : A) : L × L :=
  (a (varOf e), d (factorOf e))

/-- Expected collision probability of `incidenceLabel varOf factorOf a d` at two incidences
`e, e' : A`. -/
theorem expect_incidenceLabel_collision {A V F L : Type*} [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] [Fintype L] [DecidableEq L] [Nonempty L]
    (varOf : A → V) (factorOf : A → F) (e e' : A) :
    (𝔼 a : V → L, 𝔼 d : F → L,
      if incidenceLabel varOf factorOf a d e = incidenceLabel varOf factorOf a d e' then
        (1 : ℚ) else 0) =
      (if varOf e = varOf e' then 1 else 1 / (Fintype.card L : ℚ)) *
        (if factorOf e = factorOf e' then 1 else 1 / (Fintype.card L : ℚ)) :=
  expect_incidence_collision (varOf e) (varOf e') (factorOf e) (factorOf e')

/-- Pointwise bound on the expected collision excess of two incidences `e, e' : A`:
independent pairs (`varOf e ≠ varOf e'` and `factorOf e ≠ factorOf e'`) contribute `0`, while
correlated pairs contribute at most `1` (p. 31). -/
private theorem incidence_pair_excess_le {A V F L : Type*} [Fintype L] [Nonempty L]
    [DecidableEq V] [DecidableEq F]
    (varOf : A → V) (factorOf : A → F) (e e' : A) :
    (if varOf e = varOf e' then 1 else 1 / (Fintype.card L : ℚ)) *
        (if factorOf e = factorOf e' then 1 else 1 / (Fintype.card L : ℚ)) -
      1 / (Fintype.card (L × L) : ℚ) ≤
      (if varOf e' = varOf e then (1 : ℚ) else 0) +
        (if factorOf e' = factorOf e then (1 : ℚ) else 0) := by
  have hcard_pos : 0 < Fintype.card L := Fintype.card_pos
  have hcard_ge_one : (1 : ℚ) ≤ Fintype.card L := by exact_mod_cast hcard_pos
  have hp_nonneg : (0 : ℚ) ≤ 1 / (Fintype.card L : ℚ) := by positivity
  have hp_le_one : 1 / (Fintype.card L : ℚ) ≤ 1 := div_le_one_of_le₀ hcard_ge_one (by positivity)
  have hprod :
      1 / (Fintype.card (L × L) : ℚ) =
        (1 / (Fintype.card L : ℚ)) * (1 / (Fintype.card L : ℚ)) := by
    rw [Fintype.card_prod, Nat.cast_mul, one_div_mul_one_div]
  rw [hprod]
  simp only [@eq_comm V (varOf e) (varOf e'), @eq_comm F (factorOf e) (factorOf e')]
  split_ifs <;> nlinarith

omit [DecidableEq A] in
/-- **Lemma 4.5 expected incidence potential bound (p. 31)**: when each variable occurs in at
most `b` incidences and each factor contains at most `w` incidences,
`𝔼 a, 𝔼 d, potential (incidenceLabel varOf factorOf a d) ≤ |A| * (b + w)`. -/
theorem expect_incidence_potential_le {V F : Type*} [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] [DecidableEq L]
    (varOf : A → V) (factorOf : A → F) {b w : ℕ}
    (hb : ∀ e : A, #{e' : A | varOf e' = varOf e} ≤ b)
    (hw : ∀ e : A, #{e' : A | factorOf e' = factorOf e} ≤ w) :
    (𝔼 a : V → L, 𝔼 d : F → L, potential (incidenceLabel varOf factorOf a d)) ≤
      (Fintype.card A : ℚ) * (b + w) := by
  have hLL : 0 < Fintype.card (L × L) := Fintype.card_pos
  simp_rw [potential_eq_collisions_sub _ hLL]
  simp only [Finset.expect_sub_distrib, Fintype.expect_const]
  simp_rw [Finset.expect_sum_comm, expect_incidenceLabel_collision]
  have hconst :
      (Fintype.card A : ℚ) ^ 2 / Fintype.card (L × L) =
        ∑ _e : A, ∑ _e' : A, (1 / (Fintype.card (L × L) : ℚ)) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hconst, ← Finset.sum_sub_distrib]
  have hrow :
      ∀ e : A,
        (∑ e' : A,
            ((if varOf e' = varOf e then (1 : ℚ) else 0) +
              (if factorOf e' = factorOf e then (1 : ℚ) else 0))) ≤
          (b : ℚ) + w := by
    intro e
    rw [Finset.sum_add_distrib]
    have hb_e :
        (∑ e' : A, if varOf e' = varOf e then (1 : ℚ) else 0) ≤ b := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hb e
    have hw_e :
        (∑ e' : A, if factorOf e' = factorOf e then (1 : ℚ) else 0) ≤ w := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hw e
    linarith
  calc
    (∑ e : A,
        ((∑ e' : A,
            (if varOf e = varOf e' then 1 else 1 / (Fintype.card L : ℚ)) *
              (if factorOf e = factorOf e' then 1 else 1 / (Fintype.card L : ℚ))) -
          ∑ _e' : A, (1 / (Fintype.card (L × L) : ℚ)))) ≤
      ∑ e : A,
        ∑ e' : A,
          ((if varOf e' = varOf e then (1 : ℚ) else 0) +
            (if factorOf e' = factorOf e then (1 : ℚ) else 0)) := by
      refine Finset.sum_le_sum fun e _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun e' _ => incidence_pair_excess_le varOf factorOf e e'
    _ ≤ ∑ _e : A, ((b : ℚ) + w) := Finset.sum_le_sum fun e _ => hrow e
    _ = (Fintype.card A : ℚ) * (b + w) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Any rational function on a nonempty finite type attains a value at most its uniform average. -/
theorem exists_le_expect {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℚ) :
    ∃ ω : Ω, f ω ≤ 𝔼 ω', f ω' := by
  obtain ⟨ω, _, hω⟩ := exists_le_of_expect_le univ_nonempty (f := f) le_rfl
  exact ⟨ω, hω⟩

/-- Fixing one coordinate `i : A` of a schedule `a : A → L` can be done without increasing the
conditional expectation over the remaining coordinates `{j : A // j ≠ i} → L` (Lemma 4.5, p. 31). -/
theorem exists_coord_expect_le (i : A) (f : (A → L) → ℚ) :
    ∃ x : L,
      (𝔼 a' : ({j : A // j ≠ i} → L), f ((Equiv.funSplitAt i L).symm (x, a'))) ≤
        𝔼 a : A → L, f a := by
  have heq :
      (𝔼 a : A → L, f a) =
        𝔼 x : L, 𝔼 a' : ({j : A // j ≠ i} → L), f ((Equiv.funSplitAt i L).symm (x, a')) := by
    calc
      (𝔼 a : A → L, f a) =
          𝔼 p : L × ({j : A // j ≠ i} → L), f ((Equiv.funSplitAt i L).symm p) :=
        Fintype.expect_equiv (Equiv.funSplitAt i L) _ _ fun a =>
          congrArg f ((Equiv.funSplitAt i L).symm_apply_apply a).symm
      _ = 𝔼 x : L, 𝔼 a' : ({j : A // j ≠ i} → L),
          f ((Equiv.funSplitAt i L).symm (x, a')) :=
        expect_prod _
  rw [heq]
  exact exists_le_expect _

omit [DecidableEq A] in
/-- Replace `d f` by the constant schedule `fun _ => g₀` on every factor `f : F` that has no
incidences in `A` (Lemma 4.5, p. 30: "with `d_f(t) = 1` for factors of empty scope"). -/
def normalizeEmptyFactors {F T G : Type*} [DecidableEq F]
    (factorOf : A → F) (g₀ : G) (d : F → T → G) (f : F) : T → G :=
  if ∃ e : A, factorOf e = f then d f else fun _ => g₀

omit [DecidableEq A] in
theorem normalizeEmptyFactors_of_not_exists {F T G : Type*} [DecidableEq F]
    (factorOf : A → F) (g₀ : G) (d : F → T → G) {f : F} (hf : ¬ ∃ e : A, factorOf e = f) :
    normalizeEmptyFactors factorOf g₀ d f = fun _ => g₀ := by
  simp only [normalizeEmptyFactors, hf, ↓reduceIte]

omit [DecidableEq A] in
@[simp]
theorem normalizeEmptyFactors_factorOf {F T G : Type*} [DecidableEq F]
    (factorOf : A → F) (g₀ : G) (d : F → T → G) (e : A) :
    normalizeEmptyFactors factorOf g₀ d (factorOf e) = d (factorOf e) := by
  have hex : ∃ e' : A, factorOf e' = factorOf e := ⟨e, rfl⟩
  simp only [normalizeEmptyFactors, hex, ↓reduceIte]

omit [DecidableEq A] in
@[simp]
theorem incidenceLabel_normalizeEmptyFactors {V F T G : Type*} [DecidableEq F]
    (varOf : A → V) (factorOf : A → F) (g₀ : G) (a : V → T → G) (d : F → T → G) :
    incidenceLabel varOf factorOf a (normalizeEmptyFactors factorOf g₀ d) =
      incidenceLabel varOf factorOf a d := by
  ext e : 1
  simp [incidenceLabel]

omit [DecidableEq A] in
/-- **Lemma 4.5 (balanced variable and factor schedules, pp. 30–31)**:
Suppose each variable in `V` occurs in at most `b` incidences of `A`, each factor in `F`
contains at most `w` incidences of `A`, `0 < b + w`, and the size hypotheses (4.13) hold:
`2 * (b + w) * Fintype.card ((T → G) × (T → G)) ^ 2 ≤ Fintype.card A` and
`2 * Fintype.card T * Fintype.card G ^ 2 ≤ Fintype.card V`.
Then for any default group `g₀ : G`, there exist schedules `a : V → T → G` and `d : F → T → G`
such that:
1. `d f = fun _ => g₀` for every factor `f : F` with no incidences in `A`;
2. Every label pair `u : (T → G) × (T → G)` has incidence occupancy satisfying
   `occupancy (incidenceLabel varOf factorOf a d) u * Fintype.card ((T → G) × (T → G)) ≤
     2 * Fintype.card A`;
3. Every step `t : T` and group `g : G` has variable group size satisfying
   `occupancy (fun v => a v t) g * Fintype.card G ≤ 2 * Fintype.card V`. -/
theorem exists_balanced_schedules {T V F G : Type*}
    [Fintype T] [DecidableEq T] [Nonempty T]
    [Fintype V] [DecidableEq V] [Nonempty V]
    [Finite F] [DecidableEq F]
    [Fintype G] [DecidableEq G] [Nonempty G]
    (varOf : A → V) (factorOf : A → F) {b w : ℕ}
    (hb : ∀ e : A, #{e' : A | varOf e' = varOf e} ≤ b)
    (hw : ∀ e : A, #{e' : A | factorOf e' = factorOf e} ≤ w)
    (hbw : 0 < b + w)
    (hincidenceSize :
      2 * (b + w) * Fintype.card ((T → G) × (T → G)) ^ 2 ≤ Fintype.card A)
    (hgroupSize : 2 * Fintype.card T * Fintype.card G ^ 2 ≤ Fintype.card V)
    (g₀ : G) :
    ∃ (a : V → T → G) (d : F → T → G),
      (∀ f : F, (¬ ∃ e : A, factorOf e = f) → d f = fun _ => g₀) ∧
      (∀ u : (T → G) × (T → G),
        occupancy (incidenceLabel varOf factorOf a d) u *
          Fintype.card ((T → G) × (T → G)) ≤ 2 * Fintype.card A) ∧
      (∀ t : T, ∀ g : G,
        occupancy (fun v => a v t) g * Fintype.card G ≤ 2 * Fintype.card V) := by
  cases nonempty_fintype F
  have hB : 0 < Fintype.card ((T → G) × (T → G)) := Fintype.card_pos
  have hT : 0 < Fintype.card T := Fintype.card_pos
  have hV : 0 < Fintype.card V := Fintype.card_pos
  have hG : 0 < Fintype.card G := Fintype.card_pos
  have hA : 0 < Fintype.card A := by
    have hpos : 0 < 2 * (b + w) * Fintype.card ((T → G) × (T → G)) ^ 2 := by positivity
    exact hpos.trans_le hincidenceSize
  have hx : (0 : ℚ) < (Fintype.card A : ℚ) * (b + w : ℕ) := by positivity
  have hy : (0 : ℚ) < (Fintype.card T : ℚ) * Fintype.card V := by positivity
  let obj (p : (V → T → G) × (F → T → G)) : ℚ :=
    potential (incidenceLabel varOf factorOf p.1 p.2) / ((Fintype.card A : ℚ) * (b + w : ℕ)) +
      (∑ t : T, potential (fun v => p.1 v t)) / ((Fintype.card T : ℚ) * Fintype.card V)
  obtain ⟨⟨a, d₀⟩, hle⟩ := exists_le_expect obj
  have hexp_le : (𝔼 p : (V → T → G) × (F → T → G), obj p) ≤ 2 := by
    rw [expect_prod]
    simp only [obj, Finset.expect_add_distrib, Fintype.expect_const]
    have h1 :
        (𝔼 a' : V → T → G,
            𝔼 d' : F → T → G,
              potential (incidenceLabel varOf factorOf a' d') /
                ((Fintype.card A : ℚ) * (b + w : ℕ))) ≤ 1 := by
      simp_rw [div_eq_mul_inv, ← Finset.expect_mul, ← div_eq_mul_inv]
      rw [div_le_one hx]
      simpa only [Nat.cast_add] using expect_incidence_potential_le varOf factorOf hb hw
    have h2 :
        (𝔼 a' : V → T → G,
            (∑ t : T, potential (fun v => a' v t)) /
              ((Fintype.card T : ℚ) * Fintype.card V)) ≤ 1 := by
      simp_rw [div_eq_mul_inv, ← Finset.expect_mul, ← div_eq_mul_inv]
      rw [div_le_one hy]
      exact expect_group_potential_le
    linarith
  have hpot : obj (a, d₀) ≤ 2 := hle.trans hexp_le
  have hbounds :=
    incidence_and_group_bounds
      (incidenceLabel varOf factorOf a d₀) (fun t v => a v t) (b + w)
      hA hB hbw hT hV hG hincidenceSize hgroupSize hpot
  refine ⟨a, normalizeEmptyFactors factorOf g₀ d₀, ?_, ?_, hbounds.2⟩
  · intro f hf
    exact normalizeEmptyFactors_of_not_exists factorOf g₀ d₀ hf
  · rw [incidenceLabel_normalizeEmptyFactors]
    exact hbounds.1

/-! ### Explicit factor-scope incidence type `A = {(f, v) : f ∈ F, v ∈ I_f}` (eq. 4.1, p. 26) -/

/-- The incidence type `A = {(f, v) : f ∈ F, v ∈ scope f}` of a family of factor scopes
`scope : F → Finset V` (eq. 4.1, p. 26). -/
abbrev ScopeIncidence {F V : Type*} (scope : F → Finset V) : Type _ :=
  (f : F) × {v : V // v ∈ scope f}

/-- Variable projection `(f, v) ↦ v` on `ScopeIncidence scope`. -/
@[expose] def scopeVarOf {F V : Type*} (scope : F → Finset V) (e : ScopeIncidence scope) : V :=
  e.2.1

/-- Factor projection `(f, v) ↦ f` on `ScopeIncidence scope`. -/
@[expose] def scopeFactorOf {F V : Type*} (scope : F → Finset V) (e : ScopeIncidence scope) : F :=
  e.1

/-- Total incidence count `M = |A| = ∑ f, #(scope f)` (eq. 4.1, p. 26). -/
theorem card_scopeIncidence {F V : Type*} [Fintype F]
    (scope : F → Finset V) :
    Fintype.card (ScopeIncidence scope) = ∑ f : F, #(scope f) := by
  simp [ScopeIncidence, Fintype.card_sigma, Fintype.card_coe]

/-- For each `e : ScopeIncidence scope`, the number of incidences sharing factor
`scopeFactorOf scope e` equals `#(scope (scopeFactorOf scope e))`. -/
theorem card_filter_scopeFactorOf_eq {F V : Type*} [Fintype F] [DecidableEq F]
    (scope : F → Finset V) (e : ScopeIncidence scope) :
    #{e' : ScopeIncidence scope | scopeFactorOf scope e' = scopeFactorOf scope e} =
      #(scope (scopeFactorOf scope e)) := by
  symm
  refine Finset.card_bij (fun v hv => ⟨scopeFactorOf scope e, ⟨v, hv⟩⟩) ?_ ?_ ?_
  · intro v hv
    rw [mem_filter]
    exact ⟨mem_univ _, rfl⟩
  · intro v₁ _ v₂ _ hEq
    cases hEq
    rfl
  · rintro ⟨f', v', hv'⟩ he'
    rw [mem_filter] at he'
    have hf' : f' = scopeFactorOf scope e := he'.2
    subst hf'
    exact ⟨v', hv', rfl⟩

/-- For each `e : ScopeIncidence scope`, the number of incidences sharing variable
`scopeVarOf scope e` equals `#{f : F | scopeVarOf scope e ∈ scope f}`. -/
theorem card_filter_scopeVarOf_eq {F V : Type*} [Fintype F] [DecidableEq V]
    (scope : F → Finset V) (e : ScopeIncidence scope) :
    #{e' : ScopeIncidence scope | scopeVarOf scope e' = scopeVarOf scope e} =
      #{f : F | scopeVarOf scope e ∈ scope f} := by
  refine Finset.card_bij (fun e' _ => e'.1) ?_ ?_ ?_
  · rintro ⟨f, v, hv⟩ he'
    rw [mem_filter] at he' ⊢
    refine ⟨mem_univ _, ?_⟩
    have hv_eq : v = scopeVarOf scope e := he'.2
    rwa [← hv_eq]
  · rintro ⟨f₁, v₁, hv₁⟩ h₁ ⟨f₂, v₂, hv₂⟩ h₂ hEq
    rw [mem_filter] at h₁ h₂
    dsimp only at hEq
    subst hEq
    have hv_eq : v₁ = v₂ := h₁.2.trans h₂.2.symm
    subst hv_eq
    rfl
  · intro f hf
    rw [mem_filter] at hf
    refine ⟨⟨f, ⟨scopeVarOf scope e, hf.2⟩⟩, ?_, rfl⟩
    rw [mem_filter]
    exact ⟨mem_univ _, rfl⟩

/-- A factor `f : F` has an incidence in `ScopeIncidence scope` iff `scope f` is nonempty. -/
theorem exists_scopeFactorOf_eq_iff {F V : Type*} (scope : F → Finset V) (f : F) :
    (∃ e : ScopeIncidence scope, scopeFactorOf scope e = f) ↔ (scope f).Nonempty := by
  constructor
  · rintro ⟨⟨f', v, hv⟩, rfl⟩
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨⟨f, ⟨v, hv⟩⟩, rfl⟩

/-- **Lemma 4.5 for explicit factor scopes `scope : F → Finset V` (pp. 30–31)**:
When `∀ f, #(scope f) ≤ w`, `∀ v, #{f | v ∈ scope f} ≤ b`, `0 < b + w`, and the size bounds
(4.13) hold for `M = Fintype.card (ScopeIncidence scope) = ∑ f, #(scope f)`, there exist
schedules `a : V → T → G` and `d : F → T → G` such that `d f = fun _ => g₀` whenever
`scope f = ∅`, every label pair `u` has incidence occupancy at most `2 * M / D`, and every
variable group has size at most `2 * |V| / |G|`. -/
theorem exists_balanced_schedules_of_scopes {T V F G : Type*}
    [Fintype T] [DecidableEq T] [Nonempty T]
    [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype F]
    [Fintype G] [DecidableEq G] [Nonempty G]
    (scope : F → Finset V) {b w : ℕ}
    (hb : ∀ v : V, #{f : F | v ∈ scope f} ≤ b)
    (hw : ∀ f : F, #(scope f) ≤ w)
    (hbw : 0 < b + w)
    (hincidenceSize :
      2 * (b + w) * Fintype.card ((T → G) × (T → G)) ^ 2 ≤
        Fintype.card (ScopeIncidence scope))
    (hgroupSize : 2 * Fintype.card T * Fintype.card G ^ 2 ≤ Fintype.card V)
    (g₀ : G) :
    ∃ (a : V → T → G) (d : F → T → G),
      (∀ f : F, scope f = ∅ → d f = fun _ => g₀) ∧
      (∀ u : (T → G) × (T → G),
        occupancy (incidenceLabel (scopeVarOf scope) (scopeFactorOf scope) a d) u *
          Fintype.card ((T → G) × (T → G)) ≤ 2 * Fintype.card (ScopeIncidence scope)) ∧
      (∀ t : T, ∀ g : G,
        occupancy (fun v => a v t) g * Fintype.card G ≤ 2 * Fintype.card V) := by
  classical
  obtain ⟨a, d, hempty, hinc, hgrp⟩ :=
    exists_balanced_schedules
      (A := ScopeIncidence scope) (scopeVarOf scope) (scopeFactorOf scope)
      (fun e => (card_filter_scopeVarOf_eq scope e).le.trans (hb (scopeVarOf scope e)))
      (fun e => (card_filter_scopeFactorOf_eq scope e).le.trans (hw (scopeFactorOf scope e)))
      hbw hincidenceSize hgroupSize g₀
  refine ⟨a, d, fun f hf => hempty f ?_, hinc, hgrp⟩
  rw [exists_scopeFactorOf_eq_iff, hf]
  exact Finset.not_nonempty_empty

end Cslib.BalancedSchedules
