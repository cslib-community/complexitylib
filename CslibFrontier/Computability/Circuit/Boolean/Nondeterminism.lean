/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Substitution
public import CslibFrontier.Computability.Circuit.Complexity
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Guessing inputs

Guessing the last `p` inputs of a Boolean function `f` of `n + p` variables gives the function
`x ↦ ∃ r, f (x ++ r)` of `n` variables (`existsGuess`), the function computed by a
nondeterministic circuit, and dually `x ↦ ∀ r, f (x ++ r)` (`forallGuess`). Trying all `2 ^ p`
guesses side by side and combining the answers with one big disjunction or conjunction computes
them with `2 ^ p (C + 3) + 1` gates, where `C` is the circuit complexity of `f`
(`complexity_existsGuess_le`, `complexity_forallGuess_le`).

## Main definitions

* `Cslib.Circuits.Boolean.existsGuess`, `Cslib.Circuits.Boolean.forallGuess`.

## Main results

* `Cslib.Circuits.Boolean.complexity_existsGuess_le`,
  `Cslib.Circuits.Boolean.complexity_forallGuess_le`: guessing `p` bits multiplies the circuit
  complexity by at most `2 ^ p`, up to an additive constant per guess.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {n p : ℕ}

/-- Guessing the last `p` inputs: whether some setting of them makes `f` true. -/
def existsGuess (f : BooleanFunction (n + p)) : BooleanFunction n :=
  fun x => decide (∃ r, f (Fin.append x r) = true)

/-- Guessing the last `p` inputs universally: whether every setting of them makes `f` true. -/
def forallGuess (f : BooleanFunction (n + p)) : BooleanFunction n :=
  fun x => decide (∀ r, f (Fin.append x r) = true)

/-- The settings of `p` bits, numbered. -/
private noncomputable def guesses (p : ℕ) : Fin (2 ^ p) ≃ (Fin p → Bool) :=
  (Fintype.equivFinOfCardEq (by simp)).symm

/-- Every setting of the guessed bits, side by side, costs at most `2 ^ p (C + 2)` gates. -/
private theorem complexity_guesses_le (f : BooleanFunction (n + p)) :
    complexity interpretation (fun x (i : Fin (2 ^ p)) => f (Fin.append x (guesses p i))) ≤
      2 ^ p * (complexity interpretation (single f) + 2) := by
  refine (complexity_pi_le (I := interpretation) fun i x => f (Fin.append x (guesses p i))).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (complexity interpretation (single f) + 2)
    fun i _ => ?_).trans_eq (by simp)
  simpa using complexity_substitute_le (appendInputs (n := n) (guesses p i)) f

/-- An `m`-ary disjunction or conjunction of the inputs costs at most `m + 1` gates. -/
private theorem complexity_bigOp_le {m : ℕ} (all : Bool) :
    complexity interpretation (single fun y : Fin m → Bool =>
      if all then decide (∀ i, y i = true) else decide (∃ i, y i = true)) ≤ m + 1 := by
  have hin : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      Synthesis interpretation (inputs m) {fun y : Fin m → Bool => y i} 0 :=
    fun i _ => Synthesis.of_mem ⟨i, rfl⟩
  cases all
  · obtain ⟨g, hg, hs⟩ := Synthesis.exists_exists_mem (m := m) Finset.univ _ (by simp) hin
    have : g = fun y => decide (∃ i, y i = true) :=
      funext fun y => Bool.eq_iff_iff.2 ((hg y).trans (by simp))
    simpa [this] using hs.complexity_le
  · obtain ⟨g, hg, hs⟩ := Synthesis.exists_forall_mem (m := m) Finset.univ _ (by simp) hin
    have : g = fun y => decide (∀ i, y i = true) :=
      funext fun y => Bool.eq_iff_iff.2 ((hg y).trans (by simp))
    simpa [this] using hs.complexity_le

/-- Guessing with a disjunction or conjunction of all the guesses. -/
private theorem complexity_guess_le (f : BooleanFunction (n + p)) (all : Bool) :
    complexity interpretation (single fun x =>
      if all then forallGuess f x else existsGuess f x) ≤
      2 ^ p * (complexity interpretation (single f) + 3) + 1 := by
  have h := complexity_comp_le (I := interpretation)
    (fun x (i : Fin (2 ^ p)) => f (Fin.append x (guesses p i)))
    (single fun y : Fin (2 ^ p) → Bool =>
      if all then decide (∀ i, y i = true) else decide (∃ i, y i = true))
  have heq : (single fun y : Fin (2 ^ p) → Bool =>
        if all then decide (∀ i, y i = true) else decide (∃ i, y i = true)) ∘
      (fun x (i : Fin (2 ^ p)) => f (Fin.append x (guesses p i))) =
      single fun x => if all then forallGuess f x else existsGuess f x := by
    funext x j
    cases all
    · simp only [Function.comp_apply, single, existsGuess, Bool.false_eq_true, ite_false]
      exact decide_eq_decide.2 ((guesses p).exists_congr_left.trans
        (by simp only [Equiv.apply_symm_apply]))
    · simp only [Function.comp_apply, single, forallGuess, ite_true]
      exact decide_eq_decide.2 ((guesses p).forall_congr_left.trans
        (by simp only [Equiv.apply_symm_apply]))
  rw [heq] at h
  have := complexity_guesses_le f
  have := complexity_bigOp_le (m := 2 ^ p) all
  calc _ ≤ _ := h
    _ ≤ 2 ^ p * (complexity interpretation (single f) + 2) + (2 ^ p + 1) := by omega
    _ = 2 ^ p * (complexity interpretation (single f) + 3) + 1 := by
      rw [mul_add, mul_add]
      omega

/-- **Guessing `p` bits** costs at most `2 ^ p (C + 3) + 1` gates for a function of circuit
complexity `C`. -/
theorem complexity_existsGuess_le (f : BooleanFunction (n + p)) :
    complexity interpretation (single (existsGuess f)) ≤
      2 ^ p * (complexity interpretation (single f) + 3) + 1 := by
  simpa using complexity_guess_le f false

/-- **Guessing `p` bits universally** costs at most `2 ^ p (C + 3) + 1` gates for a function of
circuit complexity `C`. -/
theorem complexity_forallGuess_le (f : BooleanFunction (n + p)) :
    complexity interpretation (single (forallGuess f)) ≤
      2 ^ p * (complexity interpretation (single f) + 3) + 1 := by
  simpa using complexity_guess_le f true

end Cslib.Circuits.Boolean
