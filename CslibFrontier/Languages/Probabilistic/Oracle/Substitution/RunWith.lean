/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution

/-!
# Stateful runs of substituted programs

Running `ProbOracleComp.simulate handler A` against a stateful oracle is a stateful run of `A`
itself, in which each external query `q` is answered by running `handler q` against that oracle
from the current state. This lets a reduction built with `simulate` be analysed through
`runWith`, for example with an identical-until-bad bound, without unfolding the substitution.

## Main results

* `Cslib.ProbOracleComp.runWith_simulate`: a stateful run of a substituted program.
-/

public section

namespace Cslib.ProbOracleComp

variable {Query Query' State α : Type} {spec : Query → Type} {spec' : Query' → Type}

/-- Running a substituted program against `oracle` runs the original program against the oracle
that runs each handler program against `oracle`. -/
theorem runWith_simulate (oracle : (q : Query) → StateT State PMF (spec q))
    (handler : (q : Query') → ProbOracleComp spec (spec' q)) (program : ProbOracleComp spec' α)
    (s : State) :
    runWith oracle (simulate handler program) s =
      runWith (fun q => runWith oracle (handler q)) program s :=
  runWith_interpret_sumHandler oracle handler program s

end Cslib.ProbOracleComp
