/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution

/-!
# Running an oracle program against a probabilistic oracle

`A.run O` runs `A : ProbOracleComp spec α` as a closed probabilistic program: each private sample
is a fresh uniform draw, and each external query `q` runs `O q`. A deterministic oracle `f` is
`fun q => pure (f q)`, so a keyed experiment reads `A.run fun x => pure (F key x)`. Security games
write the challenger's oracle this way, instead of spelling out the sum handler that interprets
the program.

## Main definitions

* `Cslib.ProbOracleComp.run`: run an oracle program with fresh private coins against an oracle.

## Main results

* `Cslib.ProbOracleComp.run_pure`, `run_bind`, `run_map`, `run_query`, `run_sample`: `run` is the
  monad morphism answering queries with `O` and sampling with fresh coins.
* `Cslib.ProbOracleComp.run_simulate`: running a reduction built by `simulate` runs each handler
  program against the oracle.
* `Cslib.ProbOracleComp.eval_run`: the law of a run, as the program interpreted at the `PMF`
  level against the laws of the oracle's replies.
-/

public section

namespace Cslib.ProbOracleComp

open OracleComp (sumHandler)

variable {Query Query' α β : Type} {spec : Query → Type} {spec' : Query' → Type}

/-- Run `A` with fresh uniform private coins, answering each external query `q` with `O q`. -/
@[expose] def run (A : ProbOracleComp spec α) (O : (q : Query) → ProbComp (spec q)) : ProbComp α :=
  OracleComp.interpret (sumHandler ProbComp.unifFin O) A

/-- Returning a value makes no call and draws no coins. -/
@[simp] theorem run_pure (a : α) (O : (q : Query) → ProbComp (spec q)) :
    (pure a : ProbOracleComp spec α).run O = pure a := rfl

/-- A sequenced program runs its first part, then the continuation, with the same oracle. -/
@[simp] theorem run_bind (A : ProbOracleComp spec α) (next : α → ProbOracleComp spec β)
    (O : (q : Query) → ProbComp (spec q)) :
    (A >>= next).run O = A.run O >>= fun a => (next a).run O :=
  OracleComp.interpret_bind _ _ _

/-- Deterministic postprocessing commutes with running. -/
@[simp] theorem run_map (f : α → β) (A : ProbOracleComp spec α)
    (O : (q : Query) → ProbComp (spec q)) :
    (f <$> A).run O = f <$> A.run O :=
  OracleComp.interpret_map _ _ _

/-- A single external query is answered by the oracle. -/
@[simp] theorem run_query (q : Query) (O : (q : Query) → ProbComp (spec q)) :
    (query q : ProbOracleComp spec (spec q)).run O = O q :=
  interpret_query _ _ _

/-- A private sample is the sampled program itself. -/
@[simp] theorem run_sample (program : ProbComp α) (O : (q : Query) → ProbComp (spec q)) :
    (sample program : ProbOracleComp spec α).run O = program := by
  simp only [run, interpret_sample, ProbComp.interpret_unifFin]

/-- Running a substituted program runs each handler program against the oracle, with the same
fresh private coins. -/
@[simp] theorem run_simulate (handler : (q : Query) → ProbOracleComp spec' (spec q))
    (A : ProbOracleComp spec α) (O : (q : Query') → ProbComp (spec' q)) :
    (simulate handler A).run O = A.run fun q => (handler q).run O :=
  interpret_simulate _ _ _ _

/-- The law of a run: interpret the program at the `PMF` level, sampling uniformly and answering
each query with the law of the oracle's reply. -/
theorem eval_run (A : ProbOracleComp spec α) (O : (q : Query) → ProbComp (spec q)) :
    ProbComp.eval (A.run O) =
      OracleComp.interpret (sumHandler ProbComp.unifOracle fun q => ProbComp.eval (O q)) A :=
  eval_interpret O A

end Cslib.ProbOracleComp
