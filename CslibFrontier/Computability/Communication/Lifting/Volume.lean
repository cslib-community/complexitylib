/-
Copyright (c) 2026 Samuel Schlesinger, Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Volume bounds for lifting simulations

Fixing coordinates limits the cardinality of a finite set of input vectors. Combining the
bounds for the two sides of a rectangle with an accumulated volume budget bounds the number
of fixed coordinates. These are algebraic ingredients of a simulation, not an unconditional
lifting theorem. In particular, the simulation must separately establish its volume budget.

The bound is valid even when the sets of coordinates fixed on the two sides overlap; when a
simulation charges fresh queries to disjoint fixed-coordinate sets, their combined cardinality
is the number of queries.

## Main results

* `volume_le_pow_mul_of_steps`: finite-step multiplicative retention accounting.
* `card_le_pow_of_fixed`: the cardinality bound for a set fixed on some coordinates.
* `pow_div_le_of_volume_budget`: the query exponent bound from an accumulated volume budget.
-/

public section

namespace Cslib.Communication.Lifting

open Finset

variable {n m : ℕ}

/-- Multiplicative retention bounds telescope along finitely many simulation steps. The
constant loss is charged once per step, and coordinate-dependent losses are charged by the
sum of the step costs. In a lifting application `a = 8` and `r = 2 * τ`.
The proof does not require the volumes to be normalized probabilities. -/
theorem volume_le_pow_mul_of_steps {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r)
    (volume : ℕ → ℝ) (cost : ℕ → ℕ) (c : ℕ)
    (hstep : ∀ i < c, volume i ≤ a * r ^ cost i * volume (i + 1)) :
    volume 0 ≤ a ^ c * r ^ (∑ i ∈ range c, cost i) * volume c := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hprev := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    calc
      _ ≤ a ^ c * r ^ (∑ i ∈ range c, cost i) * volume c := hprev
      _ ≤ a ^ c * r ^ (∑ i ∈ range c, cost i) *
          (a * r ^ cost c * volume (c + 1)) :=
        mul_le_mul_of_nonneg_left (hstep c (Nat.lt_succ_self c))
          (mul_nonneg (pow_nonneg ha c) (pow_nonneg hr _))
      _ = _ := by simp only [sum_range_succ, pow_succ, pow_add]; ring

/-- A set fixed on `J` has at most `m ^ #Jᶜ` pointer vectors. -/
theorem card_le_pow_of_fixed {J : Finset (Fin n)} {X : Finset (Fin n → Fin m)}
    (hX : ∀ x ∈ X, ∀ x' ∈ X, ∀ i ∈ J, x i = x' i) : #X ≤ m ^ #Jᶜ := by
  have hinj : Set.InjOn (fun x : Fin n → Fin m => fun i : (Jᶜ : Finset (Fin n)) => x i)
      (X : Set (Fin n → Fin m)) := by
    intro x hx x' hx' h
    funext i
    by_cases hi : i ∈ J
    · exact hX x hx x' hx' i hi
    · exact congrFun h ⟨i, mem_compl.mpr hi⟩
  calc #X ≤ #(univ : Finset ((Jᶜ : Finset (Fin n)) → Fin m)) :=
        card_le_card_of_injOn _ (fun _ _ => mem_univ _) hinj
    _ = m ^ #Jᶜ := by simp [card_compl]

/-- An accumulated volume budget controls the total number of coordinates fixed on the two
sides. In a lifting simulation `K = 8^c`, where `c` is the number of simulated protocol bits.
No disjointness is needed for this algebraic bound; the simulation supplies disjointness to
identify the exponent with its query count. -/
theorem pow_div_le_of_volume_budget {AX AY : Finset (Fin n)}
    {X Y : Finset (Fin n → Fin m)} {τ K : ℝ}
    (hm : 0 < m) (hτ : 0 < τ) (hK : 0 ≤ K)
    (hX : ∀ x ∈ X, ∀ x' ∈ X, ∀ i ∈ AX, x i = x' i)
    (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ i ∈ AY, y i = y' i)
    (hbudget : (m : ℝ) ^ (2 * n) ≤ K * (2 * τ) ^ (#AX + #AY) * #X * #Y) :
    ((m : ℝ) / (2 * τ)) ^ (#AX + #AY) ≤ K := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hx : (#X : ℝ) ≤ (m : ℝ) ^ #AXᶜ := by exact_mod_cast card_le_pow_of_fixed hX
  have hy : (#Y : ℝ) ≤ (m : ℝ) ^ #AYᶜ := by exact_mod_cast card_le_pow_of_fixed hY
  have hxy : (#X : ℝ) * #Y ≤ (m : ℝ) ^ #AXᶜ * (m : ℝ) ^ #AYᶜ :=
    mul_le_mul hx hy (Nat.cast_nonneg _) (pow_nonneg hm'.le _)
  have hexp : (#AX + #AY) + (#AXᶜ + #AYᶜ) = 2 * n := by
    have hAX := card_add_card_compl AX
    have hAY := card_add_card_compl AY
    rw [Fintype.card_fin] at hAX hAY
    omega
  have hvol : (m : ℝ) ^ (2 * n) ≤
      (K * (2 * τ) ^ (#AX + #AY)) * (m : ℝ) ^ (#AXᶜ + #AYᶜ) := by
    calc
      _ ≤ (K * (2 * τ) ^ (#AX + #AY)) * ((#X : ℝ) * #Y) := by
        simpa only [mul_assoc] using hbudget
      _ ≤ (K * (2 * τ) ^ (#AX + #AY)) *
          ((m : ℝ) ^ #AXᶜ * (m : ℝ) ^ #AYᶜ) :=
        mul_le_mul_of_nonneg_left hxy (mul_nonneg hK (by positivity))
      _ = _ := by simp only [pow_add]
  rw [← hexp, pow_add] at hvol
  have hquery := (mul_le_mul_iff_left₀ (pow_pos hm' (#AXᶜ + #AYᶜ))).mp hvol
  rw [div_pow, div_le_iff₀ (by positivity)]
  exact hquery

end Cslib.Communication.Lifting
