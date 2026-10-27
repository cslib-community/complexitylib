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
import Mathlib.Tactic

/-!
# Finite uniform averages for label schedules

This module develops the finite-average step of Lemma 4.5, printed pp. 30–31 of
[OpenAI2026ETH]. A sampled schedule is a single function: repeated access to one variable
reads the same coordinate. Finite averages are mathematical sums, not runtime certificates.
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

end Cslib.BalancedSchedules
