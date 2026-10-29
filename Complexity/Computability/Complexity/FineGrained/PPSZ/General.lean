/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.PPSZ.AssignSL
public import Complexity.Computability.Complexity.FineGrained.PPSZ.Frozen
public import Complexity.Computability.Complexity.FineGrained.PPSZ.GeneralK
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.MeanInequalities

/-!
# PPSZ for satisfiable formulas

This file proves that PPSZ with w-implication (`Cslib.Complexity.PPSZ.round`), unmodified, finds a
satisfying assignment of every satisfiable k-CNF formula, `k ≥ 3`, with the probability that the
analysis of [Paturi, Pudlák, Saks, Zane][PaturiPudlakSaksZane2005] gives for uniquely satisfiable
formulas: at least `2^{-(1 - qbar k h) n}` for `w ≥ ∑ i < h, (k - 1) ^ i`
(`round_success_of_satisfiable`), and at least `2^{-(1 - μ_k / (k - 1) + ε) n}` in the `ε`-form
(`round_success_limit`). The theorem behind it is Hertli's theorem in the form of
[Scheder, Steinberger, Theorem 6 (p. 9:5)][SchederSteinberger2017]: if every frozen variable of
every restriction of `φ` is guessed with probability at most `p`, and `p ≥ p* = 1 - 1 / (2 ln 2)`,
then one round succeeds with probability at least `2^{-p n}` (`round_success_ge_of_guess_le`).

## The proof

The proof is Hertli's cost-function induction [Hertli, §3][Hertli2011], adapted to the
unmodified algorithm (original adaptation). [Hertli][Hertli2011] analyses a modified PPSZ that
sets every w-implied literal before choosing the next variable, and remarks that his approach
does not work for the original algorithm; here guesses of frozen variables are charged in each
step instead.

* **The success recursion** (`succSum_eq`). Fix the first `i` positions of the order. The sum
  `succSum`, over the satisfying extensions `α` of the partial assignment `τ` built so far and over
  the orders with this prefix, of `2^{-u}` (where `u` counts the guessed steps from position `i`
  on) splits by the variable `y` at position `i` and its value `b`: the step on `y` costs a factor
  `2^{-e}`, where `e = guessBit φ w τ y` is `1` if no value is w-implied on `y` and `0` otherwise.
  At `i = 0` the sum is `n!` times the success probability (`round_apply_eq`). This replaces
  [Hertli, Observation 9][Hertli2011] and is
  [Scheder, Steinberger, Observation 1][SchederSteinberger2017] unrolled one step.
* **The cost** (`cost`, `totalCost`), after [Hertli, Definition 14 (p. 7)][Hertli2011]: an
  assigned variable costs `0`, a liquid unassigned variable costs `p`, and a frozen one costs its
  guess probability averaged over the AssignSL distribution `assignProb`.
* **The cost decrease** (`sum_guessBit_add_totalCost_le`), the generalization of
  [Hertli, Theorem 17 and Lemmas 18, 19 (pp. 7, 9–10)][Hertli2011]: summed over the satisfying
  literals `l`, `e_l + c(τ[l])` is at most `s · c(τ) + (2 - 2p)(s - m)`, where `s` counts the
  satisfying literals and `m` the unassigned variables. For a frozen variable the inequality is
  proved in multiplied form (`sum_cost_update_add_le_of_frozen`, original), from Observation 13,
  Lemma 10, Lemma 11 and Lemma 16 of [Hertli][Hertli2011] (`card_satLits_mul_assignProb`,
  `guessProb_le_of_subset`, `sum_guessProb_sub`, `assignProb_le_assignProb_update`).
* **The induction** (`factorial_mul_le_succSum`), after [Hertli, Theorem 15 (pp. 7–8)][Hertli2011]:
  `succSum ≥ m! · 2^{-c(τ)}`, by the arithmetic–geometric mean inequality over the satisfying
  literals and `(2 - 2p)(s - m) ≤ s log₂ (s / m)` (`two_sub_two_mul_mul_le_mul_logb`), which
  holds for `p ≥ p*` since `ln (s / m) ≥ 1 - m / s`.
* **The threshold**: `qbar k h ≤ qbar 3 h ≤ 2 - 2 ln 2 ≤ 1 / (2 ln 2)` for `k ≥ 3`
  (`one_sub_one_div_two_mul_log_two_le_one_sub_qbar`), so `p = 1 - qbar k h` clears `p*`; the guess
  bound for frozen variables is `guessProb_le_of_frozen`.

## Main definitions

* `Cslib.Complexity.PPSZ.cost`, `Cslib.Complexity.PPSZ.totalCost`: Hertli's cost.
* `Cslib.Complexity.PPSZ.succSum`: the success sum over the orders with a fixed prefix.

## Main results

* `Cslib.Complexity.PPSZ.sum_guessBit_add_totalCost_le`: the cost decrease.
* `Cslib.Complexity.PPSZ.factorial_mul_le_succSum`: Hertli's Theorem 15 for the unmodified
  algorithm.
* `Cslib.Complexity.PPSZ.round_success_ge_of_guess_le`: Hertli's theorem in the form of
  Scheder and Steinberger's Theorem 6.
* `Cslib.Complexity.PPSZ.round_success_of_satisfiable`: PPSZ for satisfiable k-CNF formulas,
  `k ≥ 3`, at a fixed depth.
* `Cslib.Complexity.PPSZ.round_success_of_satisfiable_three`: the depth-two bound
  `2^{-(39/70) n}` for satisfiable 3-CNF formulas.
* `Cslib.Complexity.PPSZ.round_success_limit`: the `ε`-form `2^{-(1 - μ_k / (k - 1) + ε) n}`.

## References

* [T. Hertli, *3-SAT faster and simpler*][Hertli2011]
* [D. Scheder, J. Steinberger, *PPSZ for general k-SAT*][SchederSteinberger2017]
* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
-/

@[expose] public section

namespace Cslib.Complexity.PPSZ

open Cslib.Logic.PL Function
open Finset hiding restrict
open Cslib.BitString.PartialAssignment (Agrees free mem_free free_update)
open Cslib.Complexity.PPZ (restrict prefixSet EqOnPrefix prefixSet_zero prefixSet_self
  card_prefixSet eqOnPrefix_swap_iff prefixSet_swap)

variable {n : ℕ} {φ : CNF (Fin n)} {w : ℕ} {p : ℝ}

/-- A partial assignment is the restriction of each of its extensions to its assigned
variables. -/
private theorem restrict_compl_free {τ : Fin n → Option Bool} {σ : Fin n → Bool}
    (h : Agrees τ σ) : restrict σ (free τ)ᶜ = τ := by
  funext y
  rcases hy : τ y with _ | b
  · simp [restrict, hy]
  · simp [restrict, hy, h y b hy]

/-! ### The cost -/

/-- `1` if no value is w-implied on `y` under `τ`, so that PPSZ guesses `y` at this step, and `0`
otherwise. -/
noncomputable def guessBit (φ : CNF (Fin n)) (w : ℕ) (τ : Fin n → Option Bool) (y : Fin n) : ℕ :=
  if implied φ w τ y = none then 1 else 0

open Classical in
/-- **Hertli's cost** of the variable `x` under the partial assignment `τ`, after
[Hertli, Definition 14 (p. 7)][Hertli2011]: `0` if `x` is assigned, `p` if `x` is unassigned and
not frozen, and, if `x` is frozen, its guess probability `guessProb` for the unmodified algorithm
with the assigned variables fixed, averaged over the output distribution `assignProb` of
AssignSL. Hertli uses the guess probability of his modified algorithm and takes `p = S_k`, the
guess bound of frozen variables; here `p` is a parameter. -/
noncomputable def cost (φ : CNF (Fin n)) (w : ℕ) (p : ℝ) (τ : Fin n → Option Bool) (x : Fin n) :
    ℝ :=
  if Frozen φ τ x then ∑ α, assignProb φ τ α * guessProb φ w (free τ)ᶜ α x
  else if τ x = none then p else 0

/-- **Hertli's cost** of a partial assignment [Hertli, Definition 14 (p. 7)][Hertli2011]: the sum
of the costs of the variables. -/
noncomputable def totalCost (φ : CNF (Fin n)) (w : ℕ) (p : ℝ) (τ : Fin n → Option Bool) : ℝ :=
  ∑ x, cost φ w p τ x

/-- The cost of a frozen variable. -/
theorem cost_of_frozen {τ : Fin n → Option Bool} {x : Fin n} (h : Frozen φ τ x) :
    cost φ w p τ x = ∑ α, assignProb φ τ α * guessProb φ w (free τ)ᶜ α x := by
  rw [cost, ite_eq_left h]

/-- The cost of an unassigned variable that is not frozen is `p`. -/
theorem cost_of_not_frozen {τ : Fin n → Option Bool} {x : Fin n} (h : ¬ Frozen φ τ x)
    (hx : τ x = none) : cost φ w p τ x = p := by
  rw [cost, ite_eq_right h, ite_eq_left hx]

/-- An assigned variable costs nothing. -/
theorem cost_of_ne_none {τ : Fin n → Option Bool} {x : Fin n} (hx : τ x ≠ none) :
    cost φ w p τ x = 0 := by
  rw [cost, ite_eq_right fun h => hx h.1, ite_eq_right hx]

/-- **The cost of a variable is at most `p`** if every frozen variable is guessed with probability
at most `p`: the cost of a frozen variable is an average of its guess probabilities. -/
theorem cost_le (hp : 0 ≤ p)
    (herr : ∀ (T : Finset (Fin n)) (σ : Fin n → Bool) (x : Fin n), φ.eval σ = true →
      Frozen φ (restrict σ T) x → guessProb φ w T σ x ≤ p)
    {τ : Fin n → Option Bool} (hτ : ∃ σ, IsSatExtension φ τ σ) (x : Fin n) :
    cost φ w p τ x ≤ p := by
  by_cases hfr : Frozen φ τ x
  · rw [cost_of_frozen hfr]
    calc ∑ α, assignProb φ τ α * guessProb φ w (free τ)ᶜ α x
        ≤ ∑ α, assignProb φ τ α * p := sum_le_sum fun α _ => by
          by_cases hα : IsSatExtension φ τ α
          · refine mul_le_mul_of_nonneg_left (herr _ α x hα.2 ?_) (assignProb_nonneg _ _ _)
            rwa [restrict_compl_free hα.1]
          · rw [assignProb_eq_zero hα, zero_mul, zero_mul]
      _ = p := by rw [← sum_mul, sum_assignProb hτ, one_mul]
  · by_cases hx : τ x = none
    · rw [cost_of_not_frozen hfr hx]
    · rw [cost_of_ne_none hx]
      exact hp

/-! ### The cost decrease -/

/-- **The decrease for a frozen variable**, the generalization of
[Hertli, Lemma 19 (p. 9)][Hertli2011] in multiplied form (original). Let `x` be frozen under `τ`,
let `s` be the number of satisfying literals and `f = guessBit φ w τ x`. Summed over the
satisfying literals `l`, the costs of `x` under `τ[l]` are at most `s · c(τ, x) - f`. Hertli
assumes `f = 1` and divides by the output probabilities of AssignSL; here, for each output `α`,
with `P = R(τ)(α)`, `w_y = R(τ[y ↦ α y])(α)`, `u` the guess probability and `u_y` the one with
`y` also fixed, the inequality `∑_{y ≠ x} w_y u_y + P f ≤ s P u` follows from Observation 13
(`s P = ∑_y w_y`), Lemma 11 (`∑_{y ≠ x} (u - u_y) = f - u`), Lemma 10 (`u_y ≤ u`) and Lemma 16
(`P ≤ w_y`, also for `y = x`). -/
theorem sum_cost_update_add_le_of_frozen {τ : Fin n → Option Bool} {σ : Fin n → Bool}
    (hσ : IsSatExtension φ τ σ) {x : Fin n} (hfr : Frozen φ τ x) :
    ∑ l ∈ satLits φ τ, cost φ w p (update τ l.1 (some l.2)) x + (guessBit φ w τ x : ℝ) ≤
      (satLits φ τ).card * cost φ w p τ x := by
  have hxW : x ∈ free τ := mem_free.2 hfr.1
  have hxT : x ∉ (free τ)ᶜ := fun h => mem_compl.1 h hxW
  -- The costs after one step, as a sum over the outputs `α` of AssignSL.
  have hA : ∑ l ∈ satLits φ τ, cost φ w p (update τ l.1 (some l.2)) x =
      ∑ α, ∑ y ∈ (free τ).erase x, assignProb φ (update τ y (some (α y))) α *
        guessProb φ w (insert y (free τ)ᶜ) α x := by
    have hl : ∀ l ∈ satLits φ τ, cost φ w p (update τ l.1 (some l.2)) x =
        if l.1 = x then 0 else ∑ α, assignProb φ (update τ l.1 (some l.2)) α *
          guessProb φ w (insert l.1 (free τ)ᶜ) α x := by
      intro l hl
      have hy := (mem_satLits.1 hl).1
      split_ifs with hlx
      · exact cost_of_ne_none (by rw [hlx, update_self]; exact Option.some_ne_none _)
      · rw [cost_of_frozen (hfr.update (Ne.symm hlx) hy l.2), free_update,
          compl_erase]
    rw [sum_congr rfl hl, sum_subset (s₂ := free τ ×ˢ (univ : Finset Bool))
      (fun l hl => mem_product.2 ⟨mem_free.2 (mem_satLits.1 hl).1, mem_univ _⟩)
      fun l hl hl' => ?_]
    · rw [sum_product]
      have hy : ∀ y ∈ free τ, ∑ b : Bool, (if y = x then 0 else
          ∑ α, assignProb φ (update τ y (some b)) α *
            guessProb φ w (insert y (free τ)ᶜ) α x) =
          ∑ α, if y = x then 0 else assignProb φ (update τ y (some (α y))) α *
            guessProb φ w (insert y (free τ)ᶜ) α x := by
        intro y hyW
        by_cases hyx : y = x
        · simp only [ite_eq_left hyx, sum_const_zero]
        · simp only [ite_eq_right hyx]
          rw [sum_comm]
          refine sum_congr rfl fun α _ => ?_
          refine sum_eq_single (α y) (fun b _ hb => ?_) fun h => absurd (mem_univ _) h
          rw [assignProb_eq_zero fun h =>
            hb ((isSatExtension_update_iff (mem_free.1 hyW)).1 h).2.symm, zero_mul]
      rw [sum_congr rfl hy, sum_comm]
      refine sum_congr rfl fun α _ => ?_
      rw [← add_sum_erase _ _ hxW, ite_eq_left rfl, zero_add]
      exact sum_congr rfl fun y hy => ite_eq_right (ne_of_mem_erase hy)
    · split_ifs
      · rfl
      · refine sum_eq_zero fun α _ => ?_
        rw [assignProb_eq_zero fun h => hl' (mem_satLits.2 (satLit_iff_update.2
          ⟨mem_free.1 (mem_product.1 hl).1, α, h⟩)), zero_mul]
  -- The inequality for each output `α`.
  have hB : ∀ α, ∑ y ∈ (free τ).erase x, assignProb φ (update τ y (some (α y))) α *
        guessProb φ w (insert y (free τ)ᶜ) α x +
        assignProb φ τ α * (guessBit φ w τ x : ℝ) ≤
      (satLits φ τ).card * (assignProb φ τ α * guessProb φ w (free τ)ᶜ α x) := by
    intro α
    by_cases hα : IsSatExtension φ τ α
    swap
    · have h0 : ∀ y ∈ (free τ).erase x, assignProb φ (update τ y (some (α y))) α = 0 :=
        fun y hy => assignProb_eq_zero fun h =>
          hα ((isSatExtension_update_iff (mem_free.1 (mem_of_mem_erase hy))).1 h).1
      rw [assignProb_eq_zero hα, sum_eq_zero fun y hy => by rw [h0 y hy, zero_mul]]
      simp only [zero_mul, mul_zero, zero_add, le_refl]
    have h13 := card_satLits_mul_assignProb φ τ α
    rw [← add_sum_erase _ _ hxW] at h13
    have h11 := sum_guessProb_sub (φ := φ) (w := w) (σ := α) hxT
    rw [compl_compl, restrict_compl_free hα.1] at h11
    have hf : (if WImplied φ w τ x (α x) then (0 : ℝ) else 1) = (guessBit φ w τ x : ℝ) := by
      unfold guessBit
      by_cases hI : WImplied φ w τ x (α x) <;> simp [hI, implied_eq_none_iff hα.2 hα.1]
    rw [hf] at h11
    have hu : 0 ≤ guessProb φ w (free τ)ᶜ α x := guessProb_nonneg
    have e2 : ∑ y ∈ (free τ).erase x, assignProb φ τ α *
          (guessProb φ w (free τ)ᶜ α x - guessProb φ w (insert y (free τ)ᶜ) α x) ≤
        ∑ y ∈ (free τ).erase x, assignProb φ (update τ y (some (α y))) α *
          (guessProb φ w (free τ)ᶜ α x - guessProb φ w (insert y (free τ)ᶜ) α x) :=
      sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (assignProb_le_assignProb_update φ τ α y)
        (sub_nonneg.2 (guessProb_le_of_subset (subset_insert y _)))
    rw [← mul_sum, h11, mul_sub] at e2
    have e4 : ∑ y ∈ (free τ).erase x, assignProb φ (update τ y (some (α y))) α *
          (guessProb φ w (free τ)ᶜ α x - guessProb φ w (insert y (free τ)ᶜ) α x) =
        (∑ y ∈ (free τ).erase x, assignProb φ (update τ y (some (α y))) α) *
            guessProb φ w (free τ)ᶜ α x -
          ∑ y ∈ (free τ).erase x, assignProb φ (update τ y (some (α y))) α *
            guessProb φ w (insert y (free τ)ᶜ) α x := by
      rw [sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun y _ => mul_sub _ _ _
    have e5 : assignProb φ τ α * guessProb φ w (free τ)ᶜ α x ≤
        assignProb φ (update τ x (some (α x))) α * guessProb φ w (free τ)ᶜ α x :=
      mul_le_mul_of_nonneg_right (assignProb_le_assignProb_update φ τ α x) hu
    have e1 : ((satLits φ τ).card : ℝ) * (assignProb φ τ α * guessProb φ w (free τ)ᶜ α x) =
        assignProb φ (update τ x (some (α x))) α * guessProb φ w (free τ)ᶜ α x +
          (∑ y ∈ (free τ).erase x, assignProb φ (update τ y (some (α y))) α) *
            guessProb φ w (free τ)ᶜ α x := by
      rw [← mul_assoc, h13, add_mul]
    linarith
  calc ∑ l ∈ satLits φ τ, cost φ w p (update τ l.1 (some l.2)) x + (guessBit φ w τ x : ℝ)
      = ∑ α, (∑ y ∈ (free τ).erase x, assignProb φ (update τ y (some (α y))) α *
          guessProb φ w (insert y (free τ)ᶜ) α x +
          assignProb φ τ α * (guessBit φ w τ x : ℝ)) := by
        rw [hA, sum_add_distrib, ← sum_mul, sum_assignProb ⟨σ, hσ⟩, one_mul]
    _ ≤ ∑ α, ((satLits φ τ).card : ℝ) *
          (assignProb φ τ α * guessProb φ w (free τ)ᶜ α x) := sum_le_sum fun α _ => hB α
    _ = (satLits φ τ).card * cost φ w p τ x := by rw [← mul_sum, cost_of_frozen hfr]

/-- **The cost decrease**, the generalization of [Hertli, Theorem 17 (p. 7)][Hertli2011] to the
unmodified algorithm (original). If `τ` has a satisfying extension and every frozen variable is
guessed with probability at most `p ≥ 0`, then summed over the `s` satisfying literals `l`,
`e_l + c(τ[l])` is at most `s · c(τ) + (2 - 2p)(s - m)`, where `e_l = guessBit φ w τ l.1` and `m`
is the number of unassigned variables. A liquid variable contributes `2 + (s - 2) p`
([Hertli, Lemma 18 (p. 9)][Hertli2011]), a frozen one at most `s · c(τ, x)`
(`sum_cost_update_add_le_of_frozen`), and `s - m` is the number of liquid variables. -/
theorem sum_guessBit_add_totalCost_le (hp : 0 ≤ p)
    (herr : ∀ (T : Finset (Fin n)) (σ : Fin n → Bool) (x : Fin n), φ.eval σ = true →
      Frozen φ (restrict σ T) x → guessProb φ w T σ x ≤ p)
    {τ : Fin n → Option Bool} (hτ : ∃ σ, IsSatExtension φ τ σ) :
    ∑ l ∈ satLits φ τ, ((guessBit φ w τ l.1 : ℝ) + totalCost φ w p (update τ l.1 (some l.2))) ≤
      (satLits φ τ).card * totalCost φ w p τ +
        (2 - 2 * p) * ((satLits φ τ).card - (free τ).card) := by
  obtain ⟨σ, hσ⟩ := hτ
  have hx : ∀ x, (#((satLits φ τ).filter (·.1 = x)) : ℝ) * guessBit φ w τ x +
      ∑ l ∈ satLits φ τ, cost φ w p (update τ l.1 (some l.2)) x ≤
      (satLits φ τ).card * cost φ w p τ x +
        (2 - 2 * p) * (#((satLits φ τ).filter (·.1 = x)) - if τ x = none then 1 else 0) := by
    intro x
    by_cases hxn : τ x = none
    · by_cases hfr : Frozen φ τ x
      · have hfib : (satLits φ τ).filter (·.1 = x) = {(x, σ x)} := by
          ext ⟨y, b⟩
          simp only [mem_filter, mem_satLits, mem_singleton, Prod.mk.injEq]
          constructor
          · rintro ⟨hl, rfl⟩
            exact ⟨rfl, (satLit_iff_of_frozen hσ hfr).1 hl⟩
          · rintro ⟨rfl, rfl⟩
            exact ⟨⟨hxn, σ, hσ, rfl⟩, rfl⟩
        rw [hfib, card_singleton, ite_eq_left hxn, Nat.cast_one, one_mul, sub_self, mul_zero,
          add_zero, add_comm]
        exact sum_cost_update_add_le_of_frozen hσ hfr
      · obtain ⟨σ₁, σ₂, h₁, h₂, h12⟩ := exists_ne_of_not_frozen hxn hfr
        have hall : ∀ b, SatLit φ τ x b := fun b => by
          by_cases hb : σ₁ x = b
          · exact ⟨hxn, σ₁, h₁, hb⟩
          · exact ⟨hxn, σ₂, h₂,
              (by decide : ∀ a c d : Bool, a ≠ c → a ≠ d → c = d) _ _ _ h12 hb⟩
        have hfib : (satLits φ τ).filter (·.1 = x) = {(x, true), (x, false)} := by
          ext ⟨y, b⟩
          simp only [mem_filter, mem_satLits, mem_insert, mem_singleton, Prod.mk.injEq]
          constructor
          · rintro ⟨-, rfl⟩
            cases b <;> simp
          · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact ⟨hall _, rfl⟩
        have hcard : #((satLits φ τ).filter (·.1 = x)) = 2 := by
          rw [hfib, card_pair (by simp)]
        have hgb : guessBit φ w τ x = 1 :=
          ite_eq_left ((implied_eq_none_iff h₁.2 h₁.1).2 fun hI => h12 (hI.eq h₂.2 h₂.1).symm)
        have hsum : ∑ l ∈ satLits φ τ, cost φ w p (update τ l.1 (some l.2)) x ≤
            ((satLits φ τ).card - 2) * p := by
          calc ∑ l ∈ satLits φ τ, cost φ w p (update τ l.1 (some l.2)) x
              ≤ ∑ l ∈ satLits φ τ, if l.1 = x then 0 else p := sum_le_sum fun l hl => by
                split_ifs with hlx
                · rw [cost_of_ne_none (by rw [hlx, update_self]; exact Option.some_ne_none _)]
                · exact cost_le hp herr (mem_satLits.1 hl).update_isSatExtension x
            _ = ((satLits φ τ).card - 2) * p := by
                rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
                have h := card_filter_add_card_filter_not (s := satLits φ τ)
                  fun l : Fin n × Bool => l.1 = x
                rw [hcard] at h
                rw [← h]
                push_cast
                ring
        rw [hcard, hgb, ite_eq_left hxn, cost_of_not_frozen hfr hxn]
        push_cast
        linarith
    · have hfib : (satLits φ τ).filter (·.1 = x) = ∅ :=
        filter_eq_empty_iff.2 fun l hl hlx => hxn (by rw [← hlx]; exact (mem_satLits.1 hl).1)
      have h0 : ∀ l ∈ satLits φ τ, cost φ w p (update τ l.1 (some l.2)) x = 0 := fun l hl =>
        cost_of_ne_none (by
          rw [update_of_ne fun h => hxn (by rw [h]; exact (mem_satLits.1 hl).1)]
          exact hxn)
      rw [hfib, card_empty, sum_eq_zero h0, ite_eq_right hxn, cost_of_ne_none hxn]
      simp
  have hL : ∑ l ∈ satLits φ τ,
      ((guessBit φ w τ l.1 : ℝ) + totalCost φ w p (update τ l.1 (some l.2))) =
      ∑ x, ((#((satLits φ τ).filter (·.1 = x)) : ℝ) * guessBit φ w τ x +
        ∑ l ∈ satLits φ τ, cost φ w p (update τ l.1 (some l.2)) x) := by
    rw [sum_add_distrib, sum_add_distrib]
    congr 1
    · calc ∑ l ∈ satLits φ τ, (guessBit φ w τ l.1 : ℝ)
          = ∑ x, ∑ l ∈ satLits φ τ with l.1 = x, (guessBit φ w τ x : ℝ) :=
            (sum_fiberwise' (satLits φ τ) Prod.fst fun x => (guessBit φ w τ x : ℝ)).symm
        _ = _ := sum_congr rfl fun x _ => by rw [sum_const, nsmul_eq_mul]
    · unfold totalCost
      exact sum_comm
  have h1 : ∑ x, (#((satLits φ τ).filter (·.1 = x)) : ℝ) = (satLits φ τ).card := by
    exact_mod_cast (card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ)
      fun _ _ => mem_univ _).symm
  have h2 : ∑ x, (if τ x = none then (1 : ℝ) else 0) = (free τ).card := by
    rw [sum_boole]
    rfl
  calc _ = _ := hL
    _ ≤ ∑ x, (((satLits φ τ).card : ℝ) * cost φ w p τ x +
          (2 - 2 * p) * (#((satLits φ τ).filter (·.1 = x)) - if τ x = none then 1 else 0)) :=
        sum_le_sum fun x _ => hx x
    _ = _ := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_sub_distrib, h1, h2]
        rfl

/-! ### The success recursion -/

/-- The number of steps from position `i` on at which the run in the order `π` that agrees with
`α` guesses: no value is w-implied on the variable at that position. These are the unforced steps
(`unforcedCount`, that is `Cslib.Complexity.PPZ.unforcedCountWith` with the oracle `implied φ w`)
from position `i` on (`guessCount_add_unforcedCount`). -/
noncomputable def guessCount (φ : CNF (Fin n)) (w : ℕ) (α : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  #(univ.filter fun j : Fin n =>
    i ≤ (j : ℕ) ∧ implied φ w (restrict α (prefixSet π j)) (π j) = none)

/-- The guesses from position `i` on and the unforced steps before position `i` are all the
unforced steps. -/
theorem guessCount_add_unforcedCount (α : Fin n → Bool) (π : Equiv.Perm (Fin n)) (i : ℕ) :
    guessCount φ w α π i + unforcedCount φ w α π i = unforcedCount φ w α π n := by
  unfold guessCount unforcedCount PPZ.unforcedCountWith
  rw [← card_union_of_disjoint (disjoint_filter.2 fun j _ h1 h2 => absurd h2.1 (not_lt.2 h1.1))]
  congr 1
  ext j
  have hj := j.isLt
  simp only [mem_filter, mem_univ, true_and, mem_union]
  constructor
  · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact ⟨hj, h⟩
  · rintro ⟨-, h⟩
    by_cases hij : i ≤ (j : ℕ)
    · exact Or.inl ⟨hij, h⟩
    · exact Or.inr ⟨not_le.1 hij, h⟩

/-- From position `0`, the guesses are the unforced variables. -/
private theorem guessCount_zero (α : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    guessCount φ w α π 0 = unforcedCount φ w α π n := by
  have h := guessCount_add_unforcedCount (φ := φ) (w := w) α π 0
  rwa [show unforcedCount φ w α π 0 = 0 by simp [unforcedCount, PPZ.unforcedCountWith],
    add_zero] at h

/-- No guesses remain after position `n`. -/
private theorem guessCount_self (α : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    guessCount φ w α π n = 0 := by
  have h := guessCount_add_unforcedCount (φ := φ) (w := w) α π n
  omega

/-- Splitting off the step at position `i`. -/
private theorem guessCount_eq {i : ℕ} (hi : i < n) (α : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    guessCount φ w α π i = guessCount φ w α π (i + 1) +
      if implied φ w (restrict α (prefixSet π i)) (π ⟨i, hi⟩) = none then 1 else 0 := by
  have h := guessCount_add_unforcedCount (φ := φ) (w := w) α π i
  have h' := guessCount_add_unforcedCount (φ := φ) (w := w) α π (i + 1)
  have hs := PPZ.unforcedCountWith_succ (implied φ w) α π hi
  unfold unforcedCount at h h'
  split_ifs at hs ⊢ <;> omega

/-- **The success sum** at the partial assignment `τ` after the first `i` positions of the order
`π₀`: the sum, over the satisfying extensions `α` of `τ` and over the orders `π` that agree with
`π₀` on the first `i` positions, of `2^{-u}`, where `u = guessCount φ w α π i` counts the guesses
from position `i` on. At `i = 0` it is `n!` times the probability that one round outputs a
satisfying assignment (`succSum_zero`). -/
noncomputable def succSum (φ : CNF (Fin n)) (w : ℕ) (π₀ : Equiv.Perm (Fin n)) (i : ℕ)
    (τ : Fin n → Option Bool) : ℝ :=
  ∑ α ∈ univ.filter (IsSatExtension φ τ), ∑ π ∈ univ.filter (EqOnPrefix · π₀ i),
    (1 / 2 : ℝ) ^ guessCount φ w α π i

/-- The success sum is nonnegative. -/
theorem succSum_nonneg (π₀ : Equiv.Perm (Fin n)) (i : ℕ) (τ : Fin n → Option Bool) :
    0 ≤ succSum φ w π₀ i τ :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity

/-- **The success recursion** (original), the exact form of [Hertli, Observation 9][Hertli2011]
for the unmodified algorithm and [Scheder, Steinberger, Observation 1][SchederSteinberger2017]
unrolled one step. If `τ` assigns exactly the first `i < n` variables of `π₀`, the success sum
splits by the unassigned variable `y` at position `i` and its value `b`: the step on `y` costs
the factor `2^{-guessBit φ w τ y}`. -/
theorem succSum_eq {π₀ : Equiv.Perm (Fin n)} {i : ℕ} (hi : i < n) {τ : Fin n → Option Bool}
    (hτ : free τ = (prefixSet π₀ i)ᶜ) :
    succSum φ w π₀ i τ = ∑ y ∈ free τ, (1 / 2 : ℝ) ^ guessBit φ w τ y *
      ∑ b : Bool, succSum φ w (Equiv.swap (π₀ ⟨i, hi⟩) y * π₀) (i + 1) (update τ y (some b)) := by
  have hnot : ∀ y ∈ free τ, y ∉ prefixSet π₀ i := fun y hy => by
    rw [hτ] at hy
    exact mem_compl.1 hy
  have hfib : ∀ y ∈ free τ, (univ.filter (EqOnPrefix · π₀ i)).filter (fun π => π ⟨i, hi⟩ = y) =
      univ.filter (EqOnPrefix · (Equiv.swap (π₀ ⟨i, hi⟩) y * π₀) (i + 1)) := by
    intro y hy
    ext π
    simp only [mem_filter, mem_univ, true_and]
    exact (eqOnPrefix_swap_iff hi (hnot y hy)).symm
  have hmaps : ∀ π ∈ univ.filter (EqOnPrefix · π₀ i), π ⟨i, hi⟩ ∈ free τ := fun π hπ => by
    rw [hτ]
    exact mem_compl.2 ((mem_filter.1 hπ).2.apply_notMem_prefixSet hi)
  have hinner : ∀ α ∈ univ.filter (IsSatExtension φ τ),
      ∑ π ∈ univ.filter (EqOnPrefix · π₀ i), (1 / 2 : ℝ) ^ guessCount φ w α π i =
      ∑ y ∈ free τ, (1 / 2 : ℝ) ^ guessBit φ w τ y *
        ∑ π ∈ univ.filter (EqOnPrefix · (Equiv.swap (π₀ ⟨i, hi⟩) y * π₀) (i + 1)),
          (1 / 2 : ℝ) ^ guessCount φ w α π (i + 1) := by
    intro α hα
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine sum_congr rfl fun y hy => ?_
    rw [hfib y hy, mul_sum]
    refine sum_congr rfl fun π hπ => ?_
    have hag := (eqOnPrefix_swap_iff hi (hnot y hy)).1 (mem_filter.1 hπ).2
    have hc : (free τ)ᶜ = prefixSet π₀ i := by rw [hτ, compl_compl]
    rw [guessCount_eq hi, pow_add, mul_comm, hag.1.prefixSet_eq, ← hc,
      restrict_compl_free (mem_filter.1 hα).2.1, hag.2]
    rfl
  unfold succSum
  rw [sum_congr rfl hinner, sum_comm]
  refine sum_congr rfl fun y hy => ?_
  rw [← mul_sum]
  congr 1
  rw [← sum_fiberwise (univ.filter (IsSatExtension φ τ)) (fun α => α y)]
  refine sum_congr rfl fun b _ => ?_
  rw [filter_filter]
  congr 1
  exact filter_congr fun α _ => (isSatExtension_update_iff (mem_free.1 hy)).symm

/-- **The success sum at the start** is `n!` times the probability that one round of PPSZ outputs
a satisfying assignment. -/
theorem succSum_zero (π₀ : Equiv.Perm (Fin n)) :
    succSum φ w π₀ 0 (fun _ => none) = n.factorial *
      ∑ σ ∈ univ.filter (fun σ => φ.eval σ = true), ((round φ w) fun x => some (σ x)).toReal := by
  have hN : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  unfold succSum
  rw [mul_sum]
  refine sum_congr (filter_congr fun α _ => ⟨fun h => h.2, fun h => ⟨fun _ _ h => (by cases h), h⟩⟩)
    fun α hα => ?_
  rw [round_apply_eq (mem_filter.1 hα).2, mul_sum,
    filter_true_of_mem fun π _ j hj => absurd hj (Nat.not_lt_zero _)]
  refine sum_congr rfl fun π _ => ?_
  rw [guessCount_zero, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]

/-! ### The induction -/

/-- **The weighted arithmetic–geometric mean inequality** in the form used by the induction:
`|S| · 2^{-(∑ a) / |S|} ≤ ∑ 2^{-a}`. -/
private theorem card_mul_two_rpow_neg_le_sum {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (a : ι → ℝ) :
    (S.card : ℝ) * (2 : ℝ) ^ (-((∑ l ∈ S, a l) / S.card)) ≤ ∑ l ∈ S, (2 : ℝ) ^ (-a l) := by
  have hs : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have h := Real.geom_mean_le_arith_mean_weighted S (fun _ => (S.card : ℝ)⁻¹)
    (fun l => (2 : ℝ) ^ (-a l)) (fun _ _ => by positivity)
    (by rw [sum_const, nsmul_eq_mul, mul_inv_cancel₀ hs.ne']) fun _ _ => by positivity
  have hprod : ∏ l ∈ S, ((2 : ℝ) ^ (-a l)) ^ (S.card : ℝ)⁻¹ =
      (2 : ℝ) ^ (-((∑ l ∈ S, a l) / S.card)) := by
    calc ∏ l ∈ S, ((2 : ℝ) ^ (-a l)) ^ (S.card : ℝ)⁻¹
        = ∏ l ∈ S, (2 : ℝ) ^ (-a l * (S.card : ℝ)⁻¹) :=
          prod_congr rfl fun l _ => (Real.rpow_mul zero_le_two _ _).symm
      _ = (2 : ℝ) ^ ∑ l ∈ S, (-a l * (S.card : ℝ)⁻¹) := (Real.rpow_sum_of_pos two_pos _ _).symm
      _ = _ := by rw [← sum_mul, sum_neg_distrib, div_eq_mul_inv, neg_mul]
  rw [hprod, ← mul_sum] at h
  calc (S.card : ℝ) * (2 : ℝ) ^ (-((∑ l ∈ S, a l) / S.card))
      ≤ S.card * ((S.card : ℝ)⁻¹ * ∑ l ∈ S, (2 : ℝ) ^ (-a l)) :=
        mul_le_mul_of_nonneg_left h hs.le
    _ = ∑ l ∈ S, (2 : ℝ) ^ (-a l) := mul_inv_cancel_left₀ hs.ne' _

/-- **The leftover inequality** of the induction (original form of [Hertli, p. 9][Hertli2011]):
for `p ≥ 1 - 1 / (2 ln 2)` and `0 < m ≤ s`, `(2 - 2p)(s - m) ≤ s log₂ (s / m)`. It follows from
`ln (s / m) ≥ 1 - m / s` and `2 - 2p ≤ 1 / ln 2`. -/
private theorem two_sub_two_mul_mul_le_mul_logb (hp : 1 - 1 / (2 * Real.log 2) ≤ p) {m s : ℝ}
    (hm : 0 < m) (hms : m ≤ s) : (2 - 2 * p) * (s - m) ≤ s * Real.logb 2 (s / m) := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hs : 0 < s := hm.trans_le hms
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hs hm)
  have h2 : s - m ≤ s * Real.log (s / m) := by
    have := mul_le_mul_of_nonneg_left h1 hs.le
    rwa [inv_div, mul_sub, mul_one, mul_div_cancel₀ m hs.ne'] at this
  have h3 : 2 - 2 * p ≤ 1 / Real.log 2 := by
    have : 2 * (1 / (2 * Real.log 2)) = 1 / Real.log 2 := by field_simp
    linarith
  calc (2 - 2 * p) * (s - m) ≤ 1 / Real.log 2 * (s - m) :=
        mul_le_mul_of_nonneg_right h3 (sub_nonneg.2 hms)
    _ ≤ 1 / Real.log 2 * (s * Real.log (s / m)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = s * Real.logb 2 (s / m) := by
        rw [Real.logb]
        ring

/-- Every `p ≥ 1 - 1 / (2 ln 2)` is nonnegative. -/
private theorem nonneg_of_one_sub_one_div_two_mul_log_two_le
    (hp : 1 - 1 / (2 * Real.log 2) ≤ p) : 0 ≤ p := by
  have hl := Real.one_sub_inv_le_log_of_pos two_pos
  have : 1 / (2 * Real.log 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  linarith

/-- **Hertli's Theorem 15 for the unmodified algorithm** [Hertli, Theorem 15 (p. 7)][Hertli2011]
(original adaptation): if every frozen variable of every restriction of `φ` is guessed with
probability at most `p ≥ 1 - 1 / (2 ln 2)`, then for every partial assignment `τ` with a
satisfying extension that assigns exactly the first `i` variables of `π₀`, with `m = n - i`
variables left, `succSum φ w π₀ i τ ≥ m! · 2^{-c(τ)}`. The unmodified algorithm's success
probability on the restricted formula is `succSum / m!`; Hertli's Theorem 15 bounds the success
probability of his modified algorithm. The proof is by induction on `m`, through the success
recursion (`succSum_eq`), the arithmetic–geometric mean inequality over the satisfying literals
(`card_mul_two_rpow_neg_le_sum`), the cost decrease (`sum_guessBit_add_totalCost_le`) and the
leftover inequality (`two_sub_two_mul_mul_le_mul_logb`). -/
theorem factorial_mul_le_succSum (hp : 1 - 1 / (2 * Real.log 2) ≤ p)
    (herr : ∀ (T : Finset (Fin n)) (σ : Fin n → Bool) (x : Fin n), φ.eval σ = true →
      Frozen φ (restrict σ T) x → guessProb φ w T σ x ≤ p) :
    ∀ (m i : ℕ) (π₀ : Equiv.Perm (Fin n)) (τ : Fin n → Option Bool), i + m = n →
      free τ = (prefixSet π₀ i)ᶜ → (∃ σ, IsSatExtension φ τ σ) →
      (m.factorial : ℝ) * (2 : ℝ) ^ (-totalCost φ w p τ) ≤ succSum φ w π₀ i τ := by
  have hp0 := nonneg_of_one_sub_one_div_two_mul_log_two_le hp
  intro m
  induction m with
  | zero =>
    intro i π₀ τ hi hτ hsat
    obtain ⟨σ, hσ⟩ := hsat
    have hin : i = n := by omega
    rw [hin] at hτ ⊢
    have hall : ∀ x, τ x ≠ none := fun x hx => by
      have := mem_free.2 hx
      rw [hτ, prefixSet_self, compl_univ] at this
      exact notMem_empty x this
    have hc : totalCost φ w p τ = 0 := sum_eq_zero fun x _ => cost_of_ne_none (hall x)
    rw [hc, neg_zero, Real.rpow_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
    unfold succSum
    calc (1 : ℝ) = (1 / 2 : ℝ) ^ guessCount φ w σ π₀ n := by rw [guessCount_self, pow_zero]
      _ ≤ ∑ π ∈ univ.filter (EqOnPrefix · π₀ n), (1 / 2 : ℝ) ^ guessCount φ w σ π n :=
          single_le_sum (f := fun π => (1 / 2 : ℝ) ^ guessCount φ w σ π n)
            (fun _ _ => by positivity) (mem_filter.2 ⟨mem_univ _, fun _ _ => rfl⟩)
      _ ≤ _ := single_le_sum (f := fun α => ∑ π ∈ univ.filter (EqOnPrefix · π₀ n),
            (1 / 2 : ℝ) ^ guessCount φ w α π n)
            (fun _ _ => sum_nonneg fun _ _ => by positivity) (mem_filter.2 ⟨mem_univ _, hσ⟩)
  | succ m ih =>
    intro i π₀ τ hi hτ hsat
    have hin : i < n := by omega
    have hWcard : (free τ).card = m + 1 := by
      rw [hτ, card_compl, Fintype.card_fin, card_prefixSet π₀ hin.le]
      omega
    have hsW := card_free_le_card_satLits hsat
    have hM : (0 : ℝ) < (free τ).card := by rw [hWcard]; positivity
    have hMs : ((free τ).card : ℝ) ≤ (satLits φ τ).card := by exact_mod_cast hsW
    have hs : (0 : ℝ) < (satLits φ τ).card := hM.trans_le hMs
    have hS : (satLits φ τ).Nonempty := card_pos.1 (by exact_mod_cast hs)
    -- The recursion and the induction hypothesis.
    have hstep : (m.factorial : ℝ) * ∑ l ∈ satLits φ τ, (2 : ℝ) ^ (-((guessBit φ w τ l.1 : ℝ) +
        totalCost φ w p (update τ l.1 (some l.2)))) ≤ succSum φ w π₀ i τ := by
      rw [succSum_eq hin hτ]
      calc (m.factorial : ℝ) * ∑ l ∈ satLits φ τ, (2 : ℝ) ^ (-((guessBit φ w τ l.1 : ℝ) +
            totalCost φ w p (update τ l.1 (some l.2))))
          = ∑ l ∈ satLits φ τ, (1 / 2 : ℝ) ^ guessBit φ w τ l.1 *
              ((m.factorial : ℝ) * (2 : ℝ) ^ (-totalCost φ w p (update τ l.1 (some l.2)))) := by
            rw [mul_sum]
            refine sum_congr rfl fun l _ => ?_
            rw [neg_add, Real.rpow_add two_pos, Real.rpow_neg zero_le_two (guessBit φ w τ l.1 : ℝ),
              Real.rpow_natCast, one_div, inv_pow]
            ring
        _ ≤ ∑ l ∈ satLits φ τ, (1 / 2 : ℝ) ^ guessBit φ w τ l.1 *
              succSum φ w (Equiv.swap (π₀ ⟨i, hin⟩) l.1 * π₀) (i + 1) (update τ l.1 (some l.2)) :=
            sum_le_sum fun l hl => by
              have hy := mem_free.2 (mem_satLits.1 hl).1
              refine mul_le_mul_of_nonneg_left (ih (i + 1) _ _ (by omega) ?_
                (mem_satLits.1 hl).update_isSatExtension) (by positivity)
              rw [free_update, prefixSet_swap hin (by rw [hτ] at hy; exact mem_compl.1 hy),
                compl_insert, hτ]
        _ ≤ ∑ l ∈ free τ ×ˢ (univ : Finset Bool), (1 / 2 : ℝ) ^ guessBit φ w τ l.1 *
              succSum φ w (Equiv.swap (π₀ ⟨i, hin⟩) l.1 * π₀) (i + 1) (update τ l.1 (some l.2)) :=
            sum_le_sum_of_subset_of_nonneg
              (fun l hl => mem_product.2 ⟨mem_free.2 (mem_satLits.1 hl).1, mem_univ _⟩)
              fun _ _ _ => mul_nonneg (by positivity) (succSum_nonneg _ _ _)
        _ = _ := by
            rw [sum_product]
            exact sum_congr rfl fun y _ => by rw [mul_sum]
    -- The cost decrease and the leftover inequality.
    have hcost := sum_guessBit_add_totalCost_le hp0 herr hsat
    have hlog := two_sub_two_mul_mul_le_mul_logb hp hM hMs
    have hA : (∑ l ∈ satLits φ τ, ((guessBit φ w τ l.1 : ℝ) +
        totalCost φ w p (update τ l.1 (some l.2)))) / (satLits φ τ).card ≤
        totalCost φ w p τ + Real.logb 2 ((satLits φ τ).card / (free τ).card) := by
      rw [div_le_iff₀ hs]
      linarith
    have hamgm := card_mul_two_rpow_neg_le_sum (satLits φ τ) hS fun l =>
      (guessBit φ w τ l.1 : ℝ) + totalCost φ w p (update τ l.1 (some l.2))
    calc ((m + 1).factorial : ℝ) * (2 : ℝ) ^ (-totalCost φ w p τ)
        = m.factorial * ((satLits φ τ).card *
            (2 : ℝ) ^ (-(totalCost φ w p τ +
              Real.logb 2 ((satLits φ τ).card / (free τ).card)))) := by
          rw [neg_add, Real.rpow_add two_pos, Real.rpow_neg zero_le_two (Real.logb _ _),
            Real.rpow_logb two_pos (by norm_num) (div_pos hs hM), inv_div, hWcard,
            Nat.factorial_succ, Nat.cast_mul]
          field_simp
      _ ≤ m.factorial * ((satLits φ τ).card * (2 : ℝ) ^ (-((∑ l ∈ satLits φ τ,
            ((guessBit φ w τ l.1 : ℝ) + totalCost φ w p (update τ l.1 (some l.2)))) /
              (satLits φ τ).card))) := by
          gcongr
          exact one_le_two
      _ ≤ m.factorial * ∑ l ∈ satLits φ τ, (2 : ℝ) ^ (-((guessBit φ w τ l.1 : ℝ) +
            totalCost φ w p (update τ l.1 (some l.2)))) := by
          gcongr
      _ ≤ succSum φ w π₀ i τ := hstep

/-! ### The threshold -/

/-- `2 - 2 ln 2 ≤ 1 / (2 ln 2)`, equivalently `(2 ln 2 - 1)² ≥ 0`. -/
theorem two_sub_two_mul_log_two_le : 2 - 2 * Real.log 2 ≤ 1 / (2 * Real.log 2) := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * Real.log 2 - 1)]

/-- **The threshold** (original): for `k ≥ 3` and every depth `h`, `p = 1 - qbar k h` is at least
`p* = 1 - 1 / (2 ln 2)` of [Scheder, Steinberger, Theorem 6 (p. 9:5)][SchederSteinberger2017],
since `qbar k h ≤ qbar 3 h ≤ 2 - 2 ln 2 ≤ 1 / (2 ln 2)`. The condition `k ≥ 3` is the one used
here; it is sufficient, not necessary. -/
theorem one_sub_one_div_two_mul_log_two_le_one_sub_qbar {k : ℕ} (hk : 3 ≤ k) (h : ℕ) :
    1 - 1 / (2 * Real.log 2) ≤ 1 - qbar k h := by
  have := (antitone_qbar_width h hk).trans (qbar_three_le h)
  linarith [two_sub_two_mul_log_two_le]

/-! ### PPSZ for satisfiable formulas -/

/-- **Hertli's theorem**, as stated in
[Scheder, Steinberger, Theorem 6 (p. 9:5)][SchederSteinberger2017] (attributed there to Hertli),
for PPSZ with w-implication, proved along the route of [Hertli, Theorem 15 (p. 7)][Hertli2011]:
if every frozen variable of every restriction of `φ` to a satisfying assignment is guessed with
probability at most `p`, and `p ≥ p* = 1 - 1 / (2 ln 2) = (2 - log₂ e) / 2`, then for
satisfiable `φ` one round of PPSZ outputs a satisfying assignment with probability at least
`2^{-p n}`.

The hypothesis `herr` is the condition `E_π[J_x] ≤ p` of
[Scheder, Steinberger, Definition 2 (p. 9:4)][SchederSteinberger2017], restricted to frozen `x`,
for all the restrictions `φ|σ_T` of `φ` (`restrict σ T` with `σ` satisfying `φ`); every
satisfiable restriction of `φ` is of this form. For frozen `x`, `E_π[J_x]` is `guessProb`;
Definition 2 also bounds `E_π[J_x]` for liquid `x`, which `herr` drops. So for a class closed
under restrictions [Scheder, Steinberger, Definition 8 (p. 9:6)][SchederSteinberger2017], the
setting of their Lemma 15 and of [Hertli][Hertli2011], this theorem is at least as strong as
their Theorem 6; it is not a statement about a class that is not closed under restrictions. The
algorithm is the unmodified PPSZ, as in [Scheder, Steinberger][SchederSteinberger2017];
[Hertli][Hertli2011] analyses a modified algorithm, and the adaptation of his proof is
original. -/
theorem round_success_ge_of_guess_le (hp : 1 - 1 / (2 * Real.log 2) ≤ p)
    (hsat : φ.Satisfiable)
    (herr : ∀ (T : Finset (Fin n)) (σ : Fin n → Bool) (x : Fin n), φ.eval σ = true →
      Frozen φ (restrict σ T) x → guessProb φ w T σ x ≤ p) :
    (2 : ℝ) ^ (-(p * n)) ≤
      ∑ σ ∈ univ.filter (fun σ => φ.eval σ = true), ((round φ w) fun x => some (σ x)).toReal := by
  have hp0 := nonneg_of_one_sub_one_div_two_mul_log_two_le hp
  obtain ⟨σ, hσ⟩ := hsat
  have hsat : ∃ σ, IsSatExtension φ (fun _ => none) σ := ⟨σ, fun _ _ h => (by cases h), hσ⟩
  have hτ : free (fun _ : Fin n => (none : Option Bool)) = (prefixSet 1 0)ᶜ := by
    rw [prefixSet_zero, compl_empty]
    ext x
    simp
  have h15 := factorial_mul_le_succSum hp herr n 0 1 _ (zero_add n) hτ hsat
  rw [succSum_zero] at h15
  have hcost : totalCost φ w p (fun _ => none) ≤ p * n := by
    calc totalCost φ w p (fun _ => none) ≤ ∑ _x : Fin n, p :=
          sum_le_sum fun x _ => cost_le hp0 herr hsat x
      _ = p * n := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
  calc (2 : ℝ) ^ (-(p * n)) ≤ (2 : ℝ) ^ (-totalCost φ w p (fun _ => none)) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (neg_le_neg hcost)
    _ ≤ _ := le_of_mul_le_mul_left h15 (by exact_mod_cast Nat.factorial_pos n)

/-- **PPSZ for satisfiable k-CNF formulas** at a fixed depth, the finite-depth form of
[Hertli, p. 5 and Theorem 15][Hertli2011] and
[Scheder, Steinberger, Theorem 6][SchederSteinberger2017] (original): for `k ≥ 3`,
`w ≥ ∑ i < h, (k - 1) ^ i` and every satisfiable CNF formula on `n` variables whose clauses have
at most `k` literals, one round of PPSZ with w-implication outputs a satisfying assignment with
probability at least `2^{-(1 - qbar k h) n}`, the bound of the uniquely satisfiable case
(`round_success_of_unique`). -/
theorem round_success_of_satisfiable {k h : ℕ} (hk : 3 ≤ k) (hsat : φ.Satisfiable)
    (hlen : ∀ c ∈ φ, c.length ≤ k) (hw : ∑ i ∈ range h, (k - 1) ^ i ≤ w) :
    (2 : ℝ) ^ (-((1 - qbar k h) * n)) ≤
      ∑ σ ∈ univ.filter (fun σ => φ.eval σ = true), ((round φ w) fun x => some (σ x)).toReal :=
  round_success_ge_of_guess_le (one_sub_one_div_two_mul_log_two_le_one_sub_qbar hk h) hsat
    fun _ _ _ hσ hfr => guessProb_le_of_frozen hσ hfr hlen hw

/-- **PPSZ for satisfiable 3-CNF formulas at depth two** (original): for `w ≥ 3`, one round of
PPSZ with w-implication outputs a satisfying assignment of a satisfiable 3-CNF formula with
probability at least `2^{-(39/70) n}`, as in the unique case (`round_success_of_unique_three`). -/
theorem round_success_of_satisfiable_three (hw : 3 ≤ w) (hsat : φ.Satisfiable)
    (hlen : ∀ c ∈ φ, c.length ≤ 3) :
    (2 : ℝ) ^ (-(39 / 70 * n : ℝ)) ≤
      ∑ σ ∈ univ.filter (fun σ => φ.eval σ = true), ((round φ w) fun x => some (σ x)).toReal := by
  have h := round_success_of_satisfiable (h := 2) le_rfl hsat hlen
    (by simpa [sum_range_succ] using hw)
  rwa [qbar_three_two, show (1 : ℝ) - 31 / 70 = 39 / 70 by norm_num] at h

/-- **PPSZ for satisfiable k-SAT** [Hertli, p. 5][Hertli2011],
[Scheder, Steinberger, Theorem 6 with Theorem 4][SchederSteinberger2017], for PPSZ with
w-implication. Let `k ≥ 3`. For every `ε > 0` there is a bound `w` such that, for every `n`, one
round of PPSZ with w-implication outputs a satisfying assignment of any satisfiable CNF formula on
`n` variables whose clauses have at most `k` literals with probability at least
`2^{-(1 - μ_k / (k - 1) + ε) n}`.

This is the `ε`-form of the bound `2^{-(1 - μ_k / (k - 1)) n - o(n)}` of the sources, as in
`round_success_unique_limit`; the uniform `o(n)` form with `w` growing with `n` is not formalized
here. The condition `k ≥ 3` is the one under which the threshold `p*` is cleared here. -/
theorem round_success_limit {k : ℕ} (hk : 3 ≤ k) :
    ∀ ε > 0, ∃ w : ℕ, ∀ (n : ℕ) (φ : CNF (Fin n)), φ.Satisfiable → (∀ c ∈ φ, c.length ≤ k) →
      (2 : ℝ) ^ (-((1 - mu k / ((k : ℝ) - 1) + ε) * n)) ≤
        ∑ σ ∈ univ.filter (fun σ => φ.eval σ = true), ((round φ w) fun x => some (σ x)).toReal := by
  intro ε hε
  obtain ⟨h, hh⟩ := exists_le_qbar (by omega : 2 ≤ k) hε
  refine ⟨∑ i ∈ range h, (k - 1) ^ i, fun n φ hsat hlen => ?_⟩
  refine le_trans ?_ (round_success_of_satisfiable hk hsat hlen le_rfl)
  exact Real.rpow_le_rpow_of_exponent_le one_le_two
    (neg_le_neg (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)))

end Cslib.Complexity.PPSZ
