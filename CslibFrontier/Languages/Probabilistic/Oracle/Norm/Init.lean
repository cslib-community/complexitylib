/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# The simp set `runWith_norm`

Declares the simp set `runWith_norm`, in a file of its own because an attribute cannot be used in
the file declaring it. `CslibFrontier.Languages.Probabilistic.Oracle.Norm` tags its lemmas.

## Main definitions

* `runWith_norm`: rewrites stateful `ProbOracleComp.runWith` and stateless `OracleComp.evalWith`
  executions over concrete program syntax and handler compositions without unfolding black-box
  adversary runs inside `StateT.run`.
-/

public meta section

/-- The simp set `runWith_norm` normalizes stateful `ProbOracleComp.runWith` and stateless
`OracleComp.evalWith` executions over concrete oracle-program syntax and handler compositions.
It omits `OracleComp.interpret_bind` and `StateT.run_bind` so closed runs
`ProbComp.eval ((OracleComp.interpret …).run s)` fold to `ProbOracleComp.runWith` before stepping
program syntax, preserving black-box adversary calls. -/
register_simp_attr runWith_norm

end
