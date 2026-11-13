/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle

/-!
# Hard query budgets for oracle programs

`limitQueries defaultReply Q prog` runs `prog : ProbOracleComp spec α` with at most `Q` external
queries: the first `Q` queries go to the oracle, and every later query is answered with
`defaultReply` without calling it. Private samples pass through unchanged, so the capped program
makes at most `Q` external queries whatever `prog` does.

## Main definitions

* `Cslib.OracleComp.limitQueriesHandler`: the stateful handler that tracks the remaining budget.
* `Cslib.OracleComp.limitQueries`: run a program under a hard query budget.
-/

public section

namespace Cslib.OracleComp

/-- Stateful query-budget handler for `limitQueries`: maintains the remaining query budget
`rem : ℕ`, forwarding external queries `q` while `0 < rem` (decrementing `rem` to `rem - 1`) and
returning the fallback response `defaultReply q` without calling the external oracle once
`rem = 0`. -/
@[expose] def limitQueriesHandler {Query : Type} {spec : OracleSpec Query}
    (defaultReply : (q : Query) → spec q)
    (q : Query) :
    StateT ℕ (ProbOracleComp spec) (spec q) := fun rem =>
  if rem == 0 then
    pure (defaultReply q, 0)
  else
    (fun r => (r, rem - 1)) <$> ProbOracleComp.query q

/-- Enforce a hard query cap `Q : ℕ` on the external oracle `spec` in a
`ProbOracleComp spec` program, answering any external query after the first `Q` with
`defaultReply`. -/
@[expose] def limitQueries {Query : Type} {spec : OracleSpec Query} {α : Type}
    (defaultReply : (q : Query) → spec q)
    (Q : ℕ) (prog : ProbOracleComp spec α) :
    ProbOracleComp spec α :=
  Prod.fst <$> (OracleComp.interpret
    (OracleComp.sumHandler
      (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
      (limitQueriesHandler defaultReply))
    prog).run Q

end Cslib.OracleComp
