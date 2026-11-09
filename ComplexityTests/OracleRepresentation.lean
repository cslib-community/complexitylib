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

-- The same transport, stated with `ProbOracleComp.runWith`.
example :
    (ProbOracleComp.runWith source (OracleComp.interpret
      (OracleComp.sumHandler (fun n => ProbOracleComp.sample (ProbComp.unifFin n))
        (fun q => Prod.fst <$> ProbOracleComp.query q)) randomized) (false, true)).map
        (fun (result, state) => (result, state.1)) =
      ProbOracleComp.runWith target randomized false :=
  ProbOracleComp.runWith_map_response_state (fun _ => Prod.fst) source target Prod.fst
    step randomized (false, true)

/-- `source` answering with the first bit of its reply. -/
private noncomputable def sourceFirst (q : Bool) : StateT (Bool × Bool) PMF Bool :=
  fun state => (source q state).map (fun (reply, next) => (reply.1, next))

-- Forgetting the second bit of `sourceFirst`'s state turns it into `target`, in a randomized
-- client.
example : (ProbOracleComp.runWith sourceFirst randomized (false, true)).map
        (fun (result, state) => (result, state.1)) =
      ProbOracleComp.runWith target randomized false :=
  ProbOracleComp.runWith_map_state sourceFirst target Prod.fst
    (fun q state => by simp [sourceFirst, source, target]) randomized (false, true)

-- Every call flips both state bits, so the two bits stay different through the whole run.
example {result : Bool × Bool × Bool} {final : Bool × Bool}
    (h : (result, final) ∈ (ProbOracleComp.runWith sourceFirst randomized (false, true)).support) :
    final.1 ≠ final.2 :=
  ProbOracleComp.runWith_invariant sourceFirst (fun state => state.1 ≠ state.2)
    (fun _ state hstate _ next hnext => by
      simp only [sourceFirst, source, PMF.pure_map, PMF.mem_support_pure_iff,
        Prod.mk.injEq] at hnext
      obtain ⟨-, rfl⟩ := hnext
      simpa using hstate)
    randomized (false, true) (by decide) result final h

end ComplexityTests.OracleRepresentation
