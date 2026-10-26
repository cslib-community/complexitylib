/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.Oracle.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List


import Diag1155.Measure
/-! Clean oracle phases built from plain deterministic certificates. Upstream's copy machine,
which does not clear its tapes, certifies a clean phase through the tidy normal form; plain
postprocessing, branching conditions and loop counters need no tidy deterministic certificate. -/

namespace ComplexityTests.PlainCleanPhase

open Cslib Cslib.Probability Turing Turing.MultiTapeTM

/-- The plain copy certificate of upstream's untidy copy machine is a clean phase. -/
example : IsTidyOraclePPTOn (Operation := Unit) encBits encBits (fun w : List Bool => pure w) :=
  IsTidyOraclePPTOn.of_computableInPolyTime (.of_eq fun _ => rfl)

/-- Plain postprocessing of a fair bit. -/
example : IsTidyOraclePPTOn (Operation := Unit) encBits encBool
    (fun _ : List Bool => (!·) <$> ProbOracleComp.sample (ProbComp.uniform Bool)) :=
  (IsTidyOraclePPTOn.uniform_bool encBits).map ComputableInPolyTime.bool_not

/-- A branch selected by a plain condition; only the selected branch draws a bit. -/
example : IsTidyOraclePPTOn (Operation := Unit) encBits encBool
    (fun w : List Bool => if w.headD false then
      ProbOracleComp.sample (ProbComp.uniform Bool) else pure false) :=
  IsTidyOraclePPTOn.cond (by fun_prop) (IsTidyOraclePPTOn.uniform_bool encBits)
    (IsTidyOraclePPTOn.of_computableInPolyTime (.const false))

/-- A loop of fair bits whose round counter is a plain certificate. -/
example : IsTidyOraclePPTOn (Operation := Unit) encBits encBool
    (fun w : List Bool => OracleComp.iterate w.length
      (fun _ => ProbOracleComp.sample (ProbComp.uniform Bool)) false) :=
  (IsTidyOraclePPTOn.iterate_spec (stateEncoding := encBool) (by fun_prop) (.const false)
    (IsTidyOraclePPTOn.uniform_bool encBool) (fun _ _ _ => True) (fun _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial) (size := fun _ => 1) (.const 1)
    (fun _ _ _ _ _ => by simp)).1

end ComplexityTests.PlainCleanPhase
