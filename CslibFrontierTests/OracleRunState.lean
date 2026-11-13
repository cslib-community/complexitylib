/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Languages.Probabilistic.Oracle.RunState

/-! Clients of `ProbOracleComp.runState`, `runLog` and `runLogWith`: a counting oracle, the log of
a two-query adversary, a one-time oracle that refuses its second query, and the query bound on
the log. -/

namespace CslibFrontierTests.OracleRunState

open Cslib

/-- Query the oracle at `0` and `1`, and return the sum of the replies. -/
def twoQueries : ProbOracleComp (fun _ : ℕ => ℕ) ℕ := do
  let a ← ProbOracleComp.query 0
  let b ← ProbOracleComp.query 1
  return a + b

/-- `twoQueries` makes two queries. -/
theorem isQueryBounded_twoQueries : twoQueries.IsQueryBounded 2 :=
  (ProbOracleComp.IsQueryBounded.query 0).bind fun _ =>
    ((ProbOracleComp.IsQueryBounded.query 1).bind fun _ => .pure _ 0)

-- A counting oracle answers with the number of earlier queries; the state counts the queries.
example : (twoQueries.runState fun _ count => pure (count, count + 1)).run 0 = pure (1, 2) :=
  rfl

-- Against the oracle `q ↦ 10 * q`, the log records both queries with their replies, oldest first.
example : twoQueries.runLog (fun q => pure (10 * q)) = pure (10, [(0, 0), (1, 10)]) :=
  rfl

-- A one-time oracle answers its first query and refuses every later one with `default`.
example : twoQueries.runLogWith (fun log q => if log.isEmpty then some (pure (10 * q)) else none) =
    pure (0, [(0, 0)]) :=
  rfl

-- `logOracle_run` steps one call of the logging oracle: a refused query keeps the log.
example (log : List (ℕ × ℕ)) (q : ℕ) :
    (ProbOracleComp.logOracle (fun _ _ => (none : Option (ProbComp ℕ))) q).run log =
      pure (0, log) := by
  simp

-- A memoryless oracle that never refuses is `runLog`.
example (O : ℕ → ProbComp ℕ) :
    twoQueries.runLogWith (fun _ q => some (O q)) = twoQueries.runLog O :=
  ProbOracleComp.runLogWith_some _ _

-- Against any oracle, the log of `twoQueries` has at most two entries.
example (O : ℕ → ProbComp ℕ) :
    ∀ z ∈ (ProbComp.eval (twoQueries.runLog O)).support, z.2.length ≤ 2 :=
  isQueryBounded_twoQueries.length_runLog_le O

-- Against a memoryless oracle, the stateful run is `run` with the state unchanged.
example (O : ℕ → ProbComp ℕ) (s : Unit) :
    (twoQueries.runState fun q => StateT.lift (O q)).run s = (·, s) <$> twoQueries.run O :=
  ProbOracleComp.runState_lift _ _ _

end CslibFrontierTests.OracleRunState
