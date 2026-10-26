/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.List
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Sparsification -- the step is polynomial-time

The list-level sparsification step (`Cslib.Logic.PL.CNF.Sparsification.next`), the test for
sparseness (`Cslib.Logic.PL.CNF.Sparsification.isSparse`) and normalization
(`Cslib.Logic.PL.CNF.Sparsification.normalize`) are polynomial-time on the framed encoding of
formulas, for any encoding of the variables. The width `k` is fixed, so a clause has a constant
number of candidate hearts; the thresholds enter only through comparisons `θ j ≤ n`, which must
themselves be polynomial-time in unary. They are for the explicit thresholds
(`Cslib.Logic.PL.ClauseSet.Sparsification.computableInPolyTime_threshold_le`).

## Main results

* `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_next`: the step.
* `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_isSparse`: the test for
  sparseness.
* `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_normalize`: normalization.
* `Cslib.Logic.PL.ClauseSet.Sparsification.computableInPolyTime_threshold_le`: comparisons
  with the explicit thresholds.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
-/

@[expose] public section

open Turing.MultiTapeTM ComputableTidilyInPolyTime

namespace Cslib.Logic.PL.ClauseSet.Sparsification

/-- Comparing the explicit thresholds with a number is polynomial-time in unary. -/
theorem computableInPolyTime_threshold_le (k α : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (threshold k α p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool := by
  have h : (fun p : ℕ × ℕ => decide (threshold k α p.1 ≤ p.2)) = fun p =>
      if p.1 = 0 then decide (1 ≤ p.2) else decide (α * base k α ^ (2 * p.1 - 1) ≤ p.2) := by
    funext p
    unfold threshold
    split_ifs <;> rfl
  rw [h]
  fun_prop

end Cslib.Logic.PL.ClauseSet.Sparsification

namespace Cslib.Logic.PL.CNF.Sparsification

variable {V : Type} [DecidableEq V] (encV : V ↪ List Bool)

/-- The framed encoding of clauses. -/
local notation "encC" => encList (encPair encV encBool)

/-- The framed encoding of formulas. -/
local notation "encF" => encList (encList (encPair encV encBool))

/-- The list-level reduction is polynomial-time. -/
private theorem computableTidilyInPolyTime_reduce :
    ComputableTidilyInPolyTime (reduce (V := V)) encF encF := by
  unfold reduce subclause
  fun_prop

private theorem computableTidilyInPolyTime_flower :
    ComputableTidilyInPolyTime (fun p : CNF V × (ℕ × Clause V) => flower p.1 p.2.1 p.2.2)
      (encPair encF (encPair encUnary encC)) encF := by
  unfold flower subclause
  fun_prop

private theorem computableTidilyInPolyTime_heavy {θ : ℕ → ℕ}
    (hθ : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => decide (θ p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool) :
    ComputableTidilyInPolyTime (fun p : CNF V × (ℕ × Clause V) => heavy θ p.1 p.2)
      (encPair encF (encPair encUnary encC)) encBool := by
  have := computableTidilyInPolyTime_flower encV
  have h₁ : ComputableTidilyInPolyTime (fun p : CNF V × (ℕ × Clause V) =>
      decide (1 ≤ p.2.2.length) && decide (p.2.2.length < p.2.1))
      (encPair encF (encPair encUnary encC)) encBool := by
    fun_prop
  have h₂ : ComputableTidilyInPolyTime (fun p : CNF V × (ℕ × Clause V) =>
      (p.2.1 - p.2.2.length, (flower p.1 p.2.1 p.2.2).length))
      (encPair encF (encPair encUnary encC)) (encPair encUnary encUnary) := by
    fun_prop
  exact bool_and.comp (h₁.prod (hθ.comp h₂))

omit [DecidableEq V] in
private theorem computableTidilyInPolyTime_candidates (k : ℕ) :
    ComputableTidilyInPolyTime (candidates (V := V) k) encF (encList (encPair encUnary encC)) := by
  have : ComputableTidilyInPolyTime (hearts (V := V) k) encC (encList encC) := by
    unfold hearts
    fun_prop
  unfold candidates
  fun_prop

/-- The computed choice is polynomial-time. -/
private theorem computableTidilyInPolyTime_choice {θ : ℕ → ℕ}
    (hθ : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => decide (θ p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool) (k : ℕ) :
    ComputableTidilyInPolyTime (choice (V := V) θ k) encF (encPair encUnary encC) := by
  have hc : ComputableTidilyInPolyTime (fun ψ : CNF V => (candidates k ψ).filter (heavy θ ψ))
      encF (encList (encPair encUnary encC)) :=
    filterWithInput (computableTidilyInPolyTime_candidates encV k)
      (computableTidilyInPolyTime_heavy encV hθ)
  have hr : ComputableTidilyInPolyTime (fun x : ℕ × Clause V => rank k x) (encPair encUnary encC)
      encUnary := by
    unfold rank
    fun_prop
  have hb : ComputableTidilyInPolyTime (fun ψ : CNF V =>
      (List.range ((k + 1) * (k + 1) + 1)).flatMap fun r =>
        ((candidates k ψ).filter (heavy θ ψ)).filter fun x => rank k x == r) encF
      (encList (encPair encUnary encC)) :=
    flatMapConst _ fun r _ => filterWithInput hc (unary_beq (hr.comp (snd _ _)) (const r))
  exact optionGetDWithInput ((head? (encPair encUnary encC)
    (encL := encList (encPair encUnary encC))).comp hb) (const (0, []))

/-- The list-level test for sparseness is polynomial-time. -/
theorem computableInPolyTime_isSparse {θ : ℕ → ℕ}
    (hθ : ComputableInPolyTime (fun p : ℕ × ℕ => decide (θ p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool) (k : ℕ) :
    ComputableInPolyTime (isSparse (V := V) θ k) encF encBool := by
  have hθ := hθ.tidy
  refine .of_tidy ?_
  unfold isSparse
  exact bool_not.comp (anyWithInput (computableTidilyInPolyTime_candidates encV k)
    (computableTidilyInPolyTime_heavy encV hθ))

/-- **The list-level step is polynomial-time.** -/
theorem computableInPolyTime_next {θ : ℕ → ℕ}
    (hθ : ComputableInPolyTime (fun p : ℕ × ℕ => decide (θ p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool) (k : ℕ) :
    ComputableInPolyTime (fun p : CNF V × Bool => next θ k p.1 p.2)
      (encPair encF encBool) encF := by
  have hθ := hθ.tidy
  refine .of_tidy ?_
  have := computableTidilyInPolyTime_choice encV hθ k
  have := computableTidilyInPolyTime_reduce encV
  have := computableTidilyInPolyTime_flower encV
  unfold next child intro petals
  fun_prop

/-- Normalization is polynomial-time. -/
theorem computableInPolyTime_normalize :
    ComputableInPolyTime (normalize (V := V)) encF encF := by
  refine .of_tidy ?_
  have := computableTidilyInPolyTime_reduce encV
  have hdedup : ComputableTidilyInPolyTime (dedup (V := V)) encC encC := by
    unfold dedup
    fun_prop
  unfold normalize dedupClauses subclause
  fun_prop

end Cslib.Logic.PL.CNF.Sparsification
