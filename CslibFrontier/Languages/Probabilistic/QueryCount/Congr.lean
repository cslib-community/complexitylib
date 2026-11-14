/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.Run

/-!
# Oracles that agree on the calls a program makes

If every call of a program satisfies `p` (`OracleComp.QueriesSatisfy`), two handlers that agree on
the calls satisfying `p` interpret the program identically. For programs with private coins, the
predicate constrains only the external requests, and the output laws of two runs agree when the
two oracles have the same law on every request satisfying `p`.

## Main results

* `Cslib.OracleComp.QueriesSatisfy.interpret_congr`: equal interpretations.
* `Cslib.ProbOracleComp.QueriesSatisfy.eval_run_congr`: equal output laws of runs.
-/

public section

namespace Cslib

namespace OracleComp

universe u v w

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α : Type v} {m : Type v → Type w} [Monad m]
  [LawfulMonad m]

/-- Handlers that agree on every call satisfying `p` interpret a program whose calls all satisfy
`p` identically. -/
theorem QueriesSatisfy.interpret_congr {p : ι → Prop} {program : OracleComp spec α}
    (h : QueriesSatisfy p program) {handler handler' : (q : ι) → m (spec q)}
    (hagree : ∀ q, p q → handler q = handler' q) :
    interpret handler program = interpret handler' program := by
  induction program with
  | pure a => rfl
  | liftBind q cont ih =>
    obtain ⟨hq, hcont⟩ := QueriesSatisfy.liftBind_iff.mp h
    change interpret handler (OracleComp.query q >>= cont) =
      interpret handler' (OracleComp.query q >>= cont)
    rw [OracleComp.interpret_bind, OracleComp.interpret_bind, OracleComp.interpret_query,
      OracleComp.interpret_query, hagree q hq]
    exact congrArg _ (funext fun a => ih a (hcont a))

end OracleComp

namespace ProbOracleComp

variable {Query α : Type} {spec : Query → Type}

/-- Runs of a program whose external requests all satisfy `p` have the same output law under two
oracles with the same law on every request satisfying `p`. -/
theorem QueriesSatisfy.eval_run_congr {p : Query → Prop} {program : ProbOracleComp spec α}
    (h : program.QueriesSatisfy p) {oracle oracle' : (q : Query) → ProbComp (spec q)}
    (hagree : ∀ q, p q → ProbComp.eval (oracle q) = ProbComp.eval (oracle' q)) :
    ProbComp.eval (program.run oracle) = ProbComp.eval (program.run oracle') := by
  rw [eval_run, eval_run]
  refine OracleComp.QueriesSatisfy.interpret_congr h fun q hq => ?_
  cases q with
  | inl _ => rfl
  | inr q => exact hagree q hq

end ProbOracleComp

end Cslib
