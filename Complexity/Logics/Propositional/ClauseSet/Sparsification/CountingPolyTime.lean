/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingList
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Counting sparsification -- the step is polynomial-time

The list-level counting-sparsification step (`Cslib.Logic.PL.CNF.Sparsification.countingNext`),
tautology removal (`Cslib.Logic.PL.CNF.Sparsification.removeTautologies`), nontautological
normalization (`Cslib.Logic.PL.CNF.Sparsification.countingNormalize`), and comparison with the
counting thresholds `countingThreshold M j = M ^ j`
(`Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_countingThreshold_le`) are polynomial-time
on the framed encoding of formulas, for any encoding of the variables [OpenAI2026ETH, Appendix A.1].

## Main results

* `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_countingThreshold_le`: comparisons with
  `countingThreshold M`.
* `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_removeTautologies`,
  `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_countingNormalize`: tautology removal and
  nontautological normalization.
* `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_countingNext`: the list-level counting
  step.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*, Appendix A.1][OpenAI2026ETH]
-/

@[expose] public section

open Turing.MultiTapeTM ComputableTidilyInPolyTime

namespace Cslib.Logic.PL.CNF.Sparsification

/-- Comparing the counting thresholds `countingThreshold M j = M ^ j` with a number is
polynomial-time in unary. -/
theorem computableInPolyTime_countingThreshold_le (M : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (countingThreshold M p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool := by
  unfold countingThreshold
  fun_prop

variable {V : Type} [DecidableEq V] (encV : V ↪ List Bool)

/-- The framed encoding of clauses. -/
local notation "encC" => encList (encPair encV encBool)

/-- The framed encoding of formulas. -/
local notation "encF" => encList (encList (encPair encV encBool))

/-- Tautology testing on a clause is polynomial-time. -/
theorem computableInPolyTime_isTautology :
    ComputableInPolyTime (Clause.isTautology (V := V)) encC encBool := by
  refine .of_tidy ?_
  unfold Clause.isTautology Std.Sat.Literal.negate
  fun_prop

/-- Removing tautological clauses from a formula is polynomial-time. -/
theorem computableInPolyTime_removeTautologies :
    ComputableInPolyTime (removeTautologies (V := V)) encF encF := by
  refine .of_tidy ?_
  have htaut := (computableInPolyTime_isTautology encV).tidy
  unfold removeTautologies
  fun_prop

/-- Nontautological normalization (`countingNormalize`) is polynomial-time. -/
theorem computableInPolyTime_countingNormalize :
    ComputableInPolyTime (countingNormalize (V := V)) encF encF := by
  have hrem := (computableInPolyTime_removeTautologies encV).tidy
  have hnorm := (computableInPolyTime_normalize encV).tidy
  exact .of_tidy (hnorm.comp hrem)

/-- **The list-level counting-sparsification step is polynomial-time.** -/
theorem computableInPolyTime_countingNext {θ : ℕ → ℕ}
    (hθ : ComputableInPolyTime (fun p : ℕ × ℕ => decide (θ p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool) (k : ℕ) :
    ComputableInPolyTime (fun p : CNF V × Bool => countingNext θ k p.1 p.2)
      (encPair encF encBool) encF := by
  refine .of_tidy ?_
  have := (computableInPolyTime_choice encV hθ k).tidy
  have := (computableInPolyTime_reduce encV).tidy
  have := (computableInPolyTime_dedupClauses encV).tidy
  have := (computableInPolyTime_flower encV).tidy
  unfold countingNext countingChild countingIntro petals negatedHeartUnits Std.Sat.Literal.negate
  fun_prop

end Cslib.Logic.PL.CNF.Sparsification
