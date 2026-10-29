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
* `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_countingNextWith`,
  `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_countingNext`: the list-level counting
  step, for thresholds read from a runtime parameter and for fixed thresholds.
* `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_countingThreshold_le_binary`,
  `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_isSparse_countingThreshold`,
  `Cslib.Logic.PL.CNF.Sparsification.computableInPolyTime_countingNext_countingThreshold`: the
  thresholds `countingThreshold M`, the test for sparseness and the step for a base `M` given in
  binary at runtime.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*, Appendix A.1][OpenAI2026ETH]
-/

@[expose] public section

open Turing.MultiTapeTM ComputableInPolyTime

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
  unfold Clause.isTautology Std.Sat.Literal.negate
  fun_prop

/-- Removing tautological clauses from a formula is polynomial-time. -/
theorem computableInPolyTime_removeTautologies :
    ComputableInPolyTime (removeTautologies (V := V)) encF encF := by
  have htaut := computableInPolyTime_isTautology encV
  unfold removeTautologies
  fun_prop

/-- Nontautological normalization (`countingNormalize`) is polynomial-time. -/
theorem computableInPolyTime_countingNormalize :
    ComputableInPolyTime (countingNormalize (V := V)) encF encF :=
  (computableInPolyTime_normalize encV).comp (computableInPolyTime_removeTautologies encV)

/-- A counting child of a branching node, for a supplied choice, is polynomial-time. -/
private theorem computableInPolyTime_countingChild :
    ComputableInPolyTime
      (fun x : CNF V × ((ℕ × Clause V) × Bool) => countingChild x.1 x.2.1.1 x.2.1.2 x.2.2)
      (encPair encF (encPair (encPair encUnary encC) encBool)) encF := by
  have := computableInPolyTime_reduce encV
  have := computableInPolyTime_dedupClauses encV
  have := computableInPolyTime_flower encV
  unfold countingChild countingIntro petals negatedHeartUnits Std.Sat.Literal.negate
  fun_prop

/-- **The counting step for runtime thresholds** `θ p` is polynomial-time, charging the encoding of
the parameter `p`. -/
theorem computableInPolyTime_countingNextWith {P : Type} {encP : P ↪ List Bool}
    {θ : P → ℕ → ℕ}
    (hθ : ComputableInPolyTime (fun x : P × ℕ × ℕ => decide (θ x.1 x.2.1 ≤ x.2.2))
      (encPair encP (encPair encUnary encUnary)) encBool) (k : ℕ) :
    ComputableInPolyTime (fun x : P × (CNF V × Bool) => countingNext (θ x.1) k x.2.1 x.2.2)
      (encPair encP (encPair encF encBool)) encF := by
  have hchild := computableInPolyTime_countingChild encV
  have hc0 := computableInPolyTime_choiceWith encV hθ k
  have hchoice : ComputableInPolyTime
      (fun x : P × (CNF V × Bool) => choice (θ x.1) k x.2.1)
      (encPair encP (encPair encF encBool)) (encPair encUnary encC) := by
    simpa only [Function.comp_def] using
      hc0.comp ((fst encP (encPair encF encBool)).prod (snd encP (encPair encF encBool)).fst')
  have h := hchild.comp ((snd encP (encPair encF encBool)).fst'.prod
    (hchoice.prod (snd encP (encPair encF encBool)).snd'))
  simpa only [Function.comp_def, countingNext] using h

/-- **The list-level counting-sparsification step is polynomial-time.** -/
theorem computableInPolyTime_countingNext {θ : ℕ → ℕ}
    (hθ : ComputableInPolyTime (fun p : ℕ × ℕ => decide (θ p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool) (k : ℕ) :
    ComputableInPolyTime (fun p : CNF V × Bool => countingNext θ k p.1 p.2)
      (encPair encF encBool) encF := by
  have h := computableInPolyTime_countingNextWith encV (P := ℕ) (encP := encUnary)
    (θ := fun _ => θ) (computableInPolyTime_const_threshold hθ) k
  simpa only [Function.comp_def] using h.comp ((const (encOut := encUnary) 0).prod id')

/-! ### The counting thresholds for a runtime base -/

/-- Comparing the counting thresholds `countingThreshold M j = M ^ j` with a number is
polynomial-time for a runtime base `M` in binary, with `j` and the compared number in unary. -/
theorem computableInPolyTime_countingThreshold_le_binary :
    ComputableInPolyTime (fun x : ℕ × ℕ × ℕ => decide (countingThreshold x.1 x.2.1 ≤ x.2.2))
      (encPair encNat (encPair encUnary encUnary)) encBool := by
  unfold countingThreshold
  fun_prop

/-- **Sparseness for a runtime base.** The test for sparseness against the thresholds
`countingThreshold M`, for a base `M` given in binary at runtime, is polynomial-time. -/
theorem computableInPolyTime_isSparse_countingThreshold (k : ℕ) :
    ComputableInPolyTime (fun x : ℕ × CNF V => isSparse (countingThreshold x.1) k x.2)
      (encPair encNat encF) encBool :=
  computableInPolyTime_isSparseWith encV computableInPolyTime_countingThreshold_le_binary k

/-- **The counting step for a runtime base.** The counting-sparsification step for the thresholds
`countingThreshold M`, for a base `M` given in binary at runtime, is polynomial-time. -/
theorem computableInPolyTime_countingNext_countingThreshold (k : ℕ) :
    ComputableInPolyTime
      (fun x : ℕ × (CNF V × Bool) => countingNext (countingThreshold x.1) k x.2.1 x.2.2)
      (encPair encNat (encPair encF encBool)) encF :=
  computableInPolyTime_countingNextWith encV computableInPolyTime_countingThreshold_le_binary k

end Cslib.Logic.PL.CNF.Sparsification
