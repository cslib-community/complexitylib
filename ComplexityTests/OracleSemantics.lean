/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Languages.Probabilistic.Oracle.Interaction
import Complexity.Languages.Probabilistic.Oracle.Support

/-! # One semantics for oracle programs -/

namespace ComplexityTests.OracleSemantics

open Cslib OracleComp

/-- Two calls to a Boolean interface. -/
private def twoCalls : OracleComp (fun _ : Unit => Bool) Bool := do
  let a ← query ()
  let b ← query ()
  return a && !b

-- A deterministic handler gives a point distribution.
example : evalWith (fun _ => PMF.pure true) twoCalls = PMF.pure false := by
  simp [twoCalls]

-- When every call must answer `true`, the only possible result is `false`.
example : supportWith (fun _ => {true}) twoCalls = {false} := by
  ext b
  simp [twoCalls, eq_comm]

-- With fair answers, `true` has positive probability: evaluation and support agree.
example : true ∈ (evalWith (fun _ => Probability.PMF.uniformOfFintype Bool) twoCalls).support := by
  rw [support_evalWith]
  simp only [twoCalls, mem_supportWith_bind_iff, supportWith_query, supportWith_pure,
    Set.mem_singleton_iff]
  exact ⟨true, by simp [PMF.mem_support_iff], false, by simp [PMF.mem_support_iff], rfl⟩

-- A stateful oracle counting its calls.
private noncomputable def counter : (q : Unit) → StateT ℕ PMF Bool :=
  fun _ s => PMF.pure (true, s + 1)

example : runWith counter twoCalls 0 = PMF.pure (false, 2) := by
  simp [twoCalls, counter]

-- Every result of the counting run is reached along a `true` reply.
example {result : Bool} {final : ℕ} (h : (result, final) ∈ (runWith counter twoCalls 0).support) :
    result ∈ supportWith (fun _ => {true}) twoCalls :=
  mem_supportWith_of_mem_support_runWith counter
    (fun _ _ _ _ h => by
      simp only [counter, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
      exact h.1) h

-- A memoryless oracle run with state keeps the state.
example (s : ℕ) :
    runWith (fun _ => StateT.lift (PMF.pure true)) twoCalls s =
      PMF.pure (false, s) := by
  rw [runWith_lift]
  simp [twoCalls]

-- Closed probabilistic programs are the instance with uniform answers.
example (program : ProbComp Bool) :
    ProbComp.eval program = evalWith ProbComp.unifOracle program :=
  ProbComp.eval_eq_evalWith program

example : (ProbComp.eval (ProbComp.unifFin 1)).support = Set.univ := by
  rw [ProbComp.support_eval]
  exact supportWith_query _ 1

/-- A program with a private coin and one external call. -/
private noncomputable def coinThenQuery : ProbOracleComp (fun _ : Unit => Bool) Bool := do
  let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let reply ← ProbOracleComp.query ()
  return coin && reply

-- Its possible results are those for any coin and any reply.
example : true ∈ support coinThenQuery := by
  simp only [coinThenQuery, mem_supportWith_bind_iff, ProbOracleComp.support_sample,
    ProbComp.eval_uniform]
  exact ⟨true, by simp [PMF.mem_support_iff], true, by simp [ProbOracleComp.query], rfl⟩

-- Its run is, by definition, the generic run of the sum handler.
example (oracle : (q : Unit) → StateT ℕ PMF Bool) (s : ℕ) :
    ProbOracleComp.runWith oracle coinThenQuery s =
      runWith (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) coinThenQuery s :=
  rfl

-- Against a reply that is always `false`, it never accepts.
example (s : ℕ) :
    ProbOracleComp.acceptProbWith (fun _ => StateT.lift (PMF.pure false)) coinThenQuery s = 0 := by
  rw [ProbOracleComp.acceptProbWith_lift]
  simp [coinThenQuery, ProbOracleComp.sample_eq_liftLeft, ProbOracleComp.query]

end ComplexityTests.OracleSemantics
