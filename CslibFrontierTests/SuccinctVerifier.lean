/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Boolean.SuccinctVerifier

/-!
# Succinct witness verification examples

The one-bit decoder repeats its input as all address and sign bits. Its two clauses force the
two assignment bits to be false and true respectively, so the zero-gate identity witness passes
and each constant witness fails on a different clause. A second decoder has no address bits
and demands both values of its single variable, so no witness can pass. The final example
checks zero clause-address bits: there is still one clause to verify.
-/

namespace CslibFrontierTests.SuccinctVerifier

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.SuccinctVerifier
open Cslib.Complexity

/-- The two clauses are `(v_false ∨ v_false ∨ v_false)` with negative signs and the
corresponding positive clause on `v_true`. -/
private def identityDecoder : Circuit signature 1 6 := Circuit.wiring signature fun _ => 0

/-- Read the sole address bit, giving the two-bit assignment `[false, true]`. -/
private def identityWitness : Circuit signature 1 1 := Circuit.wiring signature id

example : (toCNF (r := 1) identityDecoder).length = 2 := by
  rw [length_toCNF]
  decide

example : (toCNF (r := 1) identityDecoder).eval (fun y => y 0) = true := by
  rw [eval_toCNF_eq_true_iff]
  intro x
  simp [clause, identityDecoder, addressWire, signWire]

-- The two accepted assignment bits are checked without adding any clause-address bits.
example : (badClause (r := 1) identityDecoder identityWitness).size = 17 := by
  rw [size_badClause]
  decide

example : (badClause (r := 1) identityDecoder identityWitness).eval
      interpretation ![false] 0 = false ∧
    (badClause (r := 1) identityDecoder identityWitness).eval interpretation ![true] 0 = false := by
  simp only [eval_badClause]
  decide

example : ⟨1, badClause (r := 1) identityDecoder identityWitness⟩ ∉ CircuitSAT := by
  rw [not_mem_CircuitSAT_badClause_iff]
  decide

-- A false constant violates only the positive clause; a true constant violates only the
-- negative clause. These examples check that the sign bits are not discarded or reversed.
example : (badClause (r := 1) identityDecoder (Formula.const false).toCircuit).eval
      interpretation ![false] 0 = false ∧
    (badClause (r := 1) identityDecoder (Formula.const false).toCircuit).eval
      interpretation ![true] 0 = true := by
  simp only [eval_badClause]
  decide

example : (badClause (r := 1) identityDecoder (Formula.const true).toCircuit).eval
      interpretation ![false] 0 = true ∧
    (badClause (r := 1) identityDecoder (Formula.const true).toCircuit).eval
      interpretation ![true] 0 = false := by
  simp only [eval_badClause]
  decide

/-- One explicit three-literal clause, with a prescribed six-bit description. -/
private def fixedDecoder (bits : BitString 6) : Circuit signature 0 6 :=
  Circuit.pi fun j => (Formula.const (bits j)).toCircuit

-- Under the identity assignment only the last literal holds in the first clause, and only
-- the middle literal holds in the second. All three literal positions must be considered.
example : (badClause (r := 1) (fixedDecoder ![false, true, true, false, true, true])
    identityWitness).eval interpretation Fin.elim0 0 = false := by
  rw [eval_badClause]
  decide

example : (badClause (r := 1) (fixedDecoder ![false, true, false, false, true, false])
    identityWitness).eval interpretation Fin.elim0 0 = false := by
  rw [eval_badClause]
  decide

-- The existential theorem finds a witness with a genuine zero-gate budget.
example : ∃ a : BitString 1 → Bool, (toCNF (r := 1) identityDecoder).eval a = true ∧
    complexity interpretation (single a) ≤ 0 := by
  apply (exists_small_witness_iff (r := 1) identityDecoder 0).2
  refine ⟨identityWitness, by decide, ?_⟩
  rw [not_mem_CircuitSAT_badClause_iff]
  decide

/-- Both clauses address the same variable (the empty bit string), with opposite signs. -/
private def contradictoryDecoder : Circuit signature 1 3 := Circuit.wiring signature fun _ => 0

example : ¬ (toCNF (r := 0) contradictoryDecoder).Satisfiable := by
  rintro ⟨a, ha⟩
  have hconst : a = fun _ => a Fin.elim0 := by
    funext y
    exact congrArg a (Subsingleton.elim _ _)
  rw [hconst] at ha
  cases hb : a Fin.elim0 <;>
    simp [toCNF, BitString.enum, clause, Logic.PL.CNF.eval, Logic.PL.Clause.eval,
      Logic.PL.Literal.eval, contradictoryDecoder, signWire, hb] at ha

-- With no clause-address bits, exactly one clause remains. Its three literals all require
-- the sole variable to be true, and the true constant witness passes.
private def singleDecoder : Circuit signature 0 3 :=
  Circuit.pi fun _ => (Formula.const true).toCircuit

example : (toCNF (r := 0) singleDecoder).length = 1 := by
  rw [length_toCNF]
  decide

example : (badClause (r := 0) singleDecoder (Formula.const true).toCircuit).size = 23 := by
  rw [size_badClause]
  decide

example : ⟨0, badClause (r := 0) singleDecoder (Formula.const true).toCircuit⟩ ∉ CircuitSAT := by
  rw [not_mem_CircuitSAT_badClause_iff]
  decide

end CslibFrontierTests.SuccinctVerifier
