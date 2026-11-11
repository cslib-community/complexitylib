/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Basic
public import CslibFrontier.Probability.PMF.ToReal

/-!
# Probability notation for Boolean experiments

`Pr[e]` is the probability, as a real number, that the Boolean experiment `e` returns `true`.
The experiment is either a program `e : ProbComp Bool`, for which `Pr[e]` is
`(ProbComp.eval e true).toReal`, or a distribution `e : PMF Bool`, for which it is
`(e true).toReal`. The notation adds no constant: `Pr[e]` elaborates to exactly these terms, so
every lemma about `ENNReal.toReal`, `PMF` and `ProbComp.eval` applies to it, and the program form
is the distribution form at `ProbComp.eval e`. The elaborator tries `ProbComp Bool` first, so a
`do` block or a chain of binds is read as a program, and falls back to `PMF Bool`.

Probabilities are real numbers so that advantages and biases are signed differences, as in
`|Pr[real] - Pr[ideal]|` or `Pr[game] - 1 / 2`. Nonnegativity is `ENNReal.toReal_nonneg`; the
upper bound `Pr[e] ≤ 1` is `Cslib.Probability.PMF.toReal_apply_le_one`, from
`CslibFrontier.Probability.PMF.ToReal`, which this module re-exports.

Events are final returns. The probability that a sample of `μ : PMF α` lies in a set `s` is
`Pr[(fun x => decide (x ∈ s)) <$> μ]`, and the probability of an outcome `a` is
`Pr[(· == a) <$> μ]`; these are `(μ.toOuterMeasure s).toReal` and `(μ a).toReal`. A Boolean game,
a set event and a single outcome therefore share one form.

The notation is scoped: `open Cslib.Probability` enables it, as does `open Probability` inside the
namespace `Cslib`. It then also prints both forms back as `Pr[e]`.

## Main definitions

* `Pr[e]`: the probability that the Boolean experiment `e` returns `true`, as a real number.
* `Cslib.Probability.elabProbabilityTrue`, `Cslib.Probability.delabProbabilityTrue`: elaborator
  and delaborator for `Pr[e]`.

## Main results

* `Cslib.ProbComp.probability_pure`: a program that returns a constant.
* `Cslib.ProbComp.probability_bind`: after a finite random choice, the probability is the
  average over the choice.
* `Cslib.Probability.PMF.probability_map_decide_mem`,
  `Cslib.ProbComp.probability_map_decide_mem`: set events.
* `Cslib.Probability.PMF.probability_map_beq`, `Cslib.ProbComp.probability_map_beq`: single
  outcomes.
-/

public section

namespace Cslib.Probability

/-- `Pr[e]` is the probability, as a real number, that the Boolean experiment `e` returns
`true`: `(ProbComp.eval e true).toReal` for a program `e : ProbComp Bool`, and `(e true).toReal`
for a distribution `e : PMF Bool`. -/
scoped syntax (name := probabilityTrue) "Pr[" term "]" : term

open Lean Elab Term in
/-- Elaborate `Pr[e]` as `(ProbComp.eval e true).toReal`, with `e` elaborated as a
`ProbComp Bool`; if that fails, as `(e true).toReal` with `e : PMF Bool`. -/
@[scoped term_elab probabilityTrue]
meta def elabProbabilityTrue : TermElab := fun stx expectedType? => do
  let `(Pr[$e]) := stx | throwUnsupportedSyntax
  let program ← Term.observing <| withoutErrToSorry <| elabTerm
    (← `(ENNReal.toReal (Cslib.ProbComp.eval ($e : Cslib.ProbComp Bool) true))) expectedType?
  let .error programError _ := program | applyResult program
  let distribution ← Term.observing <| withoutErrToSorry <| elabTerm
    (← `(ENNReal.toReal (($e : _root_.PMF Bool) true))) expectedType?
  let .error distributionError _ := distribution | applyResult distribution
  if (← programError.toMessageData.toString) == (← distributionError.toMessageData.toString) then
    return ← applyResult program
  throwError "`Pr[e]` needs a Boolean experiment `e : ProbComp Bool` or `e : PMF Bool`.\
    \nAs a `ProbComp Bool`:{indentD programError.toMessageData}\
    \nAs a `PMF Bool`:{indentD distributionError.toMessageData}"

open Lean Meta PrettyPrinter Delaborator SubExpr in
/-- Print `(ProbComp.eval e true).toReal` as `Pr[e]`, and `(μ true).toReal` for `μ : PMF Bool`
as `Pr[μ]`. Unlike an unexpander, it checks that the argument is a `PMF Bool`. -/
@[scoped delab app.ENNReal.toReal]
meta def delabProbabilityTrue : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.isAppOfArity ``ENNReal.toReal 1
  let mass := e.appArg!
  guard <| mass.isAppOfArity ``DFunLike.coe 6
  let args := mass.getAppArgs
  guard <| args[5]!.isConstOf ``Bool.true
  let law ← whnfR args[0]!
  guard <| law.isAppOfArity ``PMF 1 && law.appArg!.isConstOf ``Bool
  if args[4]!.isAppOfArity ``Cslib.ProbComp.eval 2 then
    let program ← withAppArg <| withNaryArg 4 <| withAppArg delab
    `(Pr[$program])
  else
    let distribution ← withAppArg <| withNaryArg 4 delab
    `(Pr[$distribution])

namespace PMF

variable {α : Type}

/-- The probability that a sample lies in a set is the probability that testing membership
returns `true`. -/
theorem probability_map_decide_mem (μ : _root_.PMF α) (s : Set α) [DecidablePred (· ∈ s)] :
    Pr[(fun x => decide (x ∈ s)) <$> μ] = (μ.toOuterMeasure s).toReal := by
  rw [_root_.PMF.monad_map_eq_map, ← _root_.PMF.toOuterMeasure_apply_singleton,
    _root_.PMF.toOuterMeasure_map_apply]
  congr 2
  ext x
  simp

/-- The probability of an outcome is the probability that comparing with it returns `true`. -/
theorem probability_map_beq [BEq α] [LawfulBEq α] (μ : _root_.PMF α) (a : α) :
    Pr[(· == a) <$> μ] = (μ a).toReal := by
  rw [_root_.PMF.monad_map_eq_map, ← _root_.PMF.toOuterMeasure_apply_singleton,
    _root_.PMF.toOuterMeasure_map_apply, ← _root_.PMF.toOuterMeasure_apply_singleton]
  congr 2
  ext x
  simp

end PMF

end Cslib.Probability

namespace Cslib.ProbComp

open Probability

variable {α : Type}

/-- A program that returns `b` succeeds with probability one if `b` is `true` and zero
otherwise. -/
theorem probability_pure (b : Bool) : Pr[pure b] = if b then 1 else 0 := by
  cases b <;> simp

/-- After a finite random choice, the probability of success is the average of the
probabilities of success of the continuations. -/
theorem probability_bind [Fintype α] (source : ProbComp α) (next : α → ProbComp Bool) :
    Pr[source >>= next] = ∑ a, (eval source a).toReal * Pr[next a] := by
  rw [eval_bind, PMF.bind_apply_toReal]

/-- The probability that a program's output lies in a set is the probability that testing
membership returns `true`. -/
theorem probability_map_decide_mem (program : ProbComp α) (s : Set α) [DecidablePred (· ∈ s)] :
    Pr[(fun x => decide (x ∈ s)) <$> program] = ((eval program).toOuterMeasure s).toReal := by
  rw [eval_map, ← _root_.PMF.monad_map_eq_map, PMF.probability_map_decide_mem]

/-- The probability of an output is the probability that comparing with it returns `true`. -/
theorem probability_map_beq [BEq α] [LawfulBEq α] (program : ProbComp α) (a : α) :
    Pr[(· == a) <$> program] = (eval program a).toReal := by
  rw [eval_map, ← _root_.PMF.monad_map_eq_map, PMF.probability_map_beq]

end Cslib.ProbComp
