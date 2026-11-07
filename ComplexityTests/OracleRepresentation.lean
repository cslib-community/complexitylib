/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Languages.Probabilistic.Oracle.Simulation

/-! Reply and state transport with noninjective representations and adaptive private sampling. -/

namespace ComplexityTests.OracleRepresentation

open Cslib

private noncomputable def source (_ : Bool) : StateT (Bool × Bool) PMF (Bool × Bool) :=
  fun state => PMF.pure (state, (!state.1, !state.2))

private noncomputable def target (_ : Bool) : StateT Bool PMF Bool :=
  fun state => PMF.pure (state, !state)

private theorem run_target (q state : Bool) : (target q).run state = PMF.pure (state, !state) :=
  rfl

-- Both representations forget the second bit; injectivity is not needed for joint-law transport.
private theorem step (q : Bool) (state : Bool × Bool) :
    (source q state).map (fun (reply, next) => (reply.1, next.1)) = target q state.1 := by
  simp [source, target]

private def adaptive : OracleComp (fun _ : Bool => Bool) (Bool × Bool) := do
  let first ← OracleComp.query false
  let second ← OracleComp.query first
  return (first, second)

example :
    ((OracleComp.interpret source (OracleComp.interpret
      (fun q => Prod.fst <$> OracleComp.query q) adaptive)).run (false, true)).map
        (fun (result, state) => (result, state.1)) =
      (OracleComp.interpret target adaptive).run false :=
  OracleComp.run_interpret_map_response_state (fun _ => Prod.fst) source target Prod.fst
    step adaptive (false, true)

-- The final state remains correlated with both returned replies, rather than being discarded.
example : (OracleComp.interpret target adaptive).run false = PMF.pure ((false, true), false) := by
  simp [adaptive, OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
    run_target]

private noncomputable def randomized : ProbOracleComp (fun _ : Bool => Bool)
    (Bool × Bool × Bool) := do
  let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let first ← ProbOracleComp.query coin
  let second ← ProbOracleComp.query first
  return (coin, first, second)

-- Private sampling is forwarded identically even though external replies change type.
example :
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) source)
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => ProbOracleComp.sample (ProbComp.unifFin n))
          (fun q => Prod.fst <$> ProbOracleComp.query q)) randomized)).run (false, true)).map
        (fun (result, state) => (result, state.1)) =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) target)
          randomized).run false :=
  ProbOracleComp.run_interpret_map_response_state (fun _ => Prod.fst) source target Prod.fst
    step randomized (false, true)

end ComplexityTests.OracleRepresentation
