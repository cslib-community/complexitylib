/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution

/-! # Oracle substitution with private coins and shared state -/

namespace CslibFrontierTests.ProbOracleSubstitution

open Cslib

private noncomputable def adversary : ProbOracleComp (fun _ : Bool => ℕ) (Bool × ℕ) := do
  let bit ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let reply ← ProbOracleComp.query bit
  return (bit, reply)

private noncomputable def maskedQuery (bit : Bool) : ProbOracleComp (fun _ : Bool => ℕ) ℕ := do
  let mask ← ProbOracleComp.sample (ProbComp.uniform Bool)
  ProbOracleComp.query (bit ^^ mask)

private noncomputable def reduction : ProbOracleComp (fun _ : Bool => ℕ) (Bool × ℕ) :=
  ProbOracleComp.simulate maskedQuery adversary

-- Both private draws remain in the syntax, in order, before the simulated external call.
example : reduction = (do
    let bit ← ProbOracleComp.sample (ProbComp.uniform Bool)
    let mask ← ProbOracleComp.sample (ProbComp.uniform Bool)
    let reply ← ProbOracleComp.query (bit ^^ mask)
    return (bit, reply)) := by
  simp [reduction, adversary, maskedQuery]

private def countQuery (_ : ℕ) : StateT ℕ ProbComp ℕ := fun count =>
  pure (count, count + 1)

private def twice (q : ℕ) : ProbOracleComp (fun _ : ℕ => ℕ) ℕ := do
  let first ← ProbOracleComp.query q
  ProbOracleComp.query first

private noncomputable def adaptive : ProbOracleComp (fun _ : ℕ => ℕ) (Bool × ℕ) := do
  let first ← ProbOracleComp.query 0
  let bit ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let last ← ProbOracleComp.query first
  return (bit, last)

-- The runner supplies sampling once. All four target queries share the same evolving state,
-- including across the intervening private draw and the second call to the reduction handler.
example (initial : ℕ) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) countQuery)
      (ProbOracleComp.simulate twice adaptive)).run initial =
      (do
        let bit ← ProbComp.uniform Bool
        return ((bit, initial + 3), initial + 4)) := by
  rw [ProbOracleComp.interpret_simulate]
  simp only [adaptive, twice, OracleComp.interpret_bind, ProbOracleComp.interpret_query,
    StateT.run_bind, OracleComp.interpret_pure, StateT.run_pure,
    ProbOracleComp.interpret_sample, OracleComp.run_interpret_lift, ProbComp.interpret_unifFin]
  simp [countQuery, StateT.run, Nat.add_assoc]

-- External replies may depend on their query. Substitution preserves those dependent types.
private abbrev Reply : Bool → Type
  | false => Bool
  | true => ℕ

private def dependentHandler : (q : Bool) → ProbOracleComp (fun _ : ℕ => ℕ) (Reply q)
  | false => pure true
  | true => ProbOracleComp.query 7

example : ProbOracleComp.simulate dependentHandler
    (do
      let flag ← ProbOracleComp.query (spec := Reply) false
      if flag then ProbOracleComp.query true else pure 0) =
      ProbOracleComp.query (spec := fun _ : ℕ => ℕ) 7 := by
  simp [dependentHandler]

end CslibFrontierTests.ProbOracleSubstitution
