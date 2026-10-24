/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# SAT belongs to NP

The existing verifier is polynomial-time on the framed binary encoding of CNF formulas and raw
certificate bits. It looks up each variable's first occurrence, so arbitrary binary variable
labels do not inflate certificates. Repeated variables read the same certificate position.

Together with `Cslib.Complexity.SAT.isVerifier`, this proves membership in `NP`
[Arora and Barak, Section 2.3][AroraBarak09]. Combined with the tableau reduction in
`Complexity/Computability/Complexity/CookLevin/PolyTime.lean`, this gives
`Cslib.Complexity.CookLevin.SAT_npComplete` in
`Complexity/Computability/Complexity/CookLevin/Completeness.lean`.

## Main definitions

* `Cslib.Complexity.cnfDecoder`: the total decoder of formulas, along `encCNF`.
* `Cslib.Complexity.SAT.encOccurrence`: encoding of a literal occurrence for natural-number
  variables.

## Main results

* `Cslib.Complexity.SAT.computableInPolyTime_verifier`: the verifier is polynomial-time.
* `Cslib.Complexity.SAT.computableInPolyTime_distinctVars`,
  `Cslib.Complexity.SAT.computableInPolyTime_numVars`,
  `Cslib.Complexity.SAT.computableInPolyTime_occurrences`: distinct variables, their unary count,
  and literal occurrences for natural-number variables.
* `Cslib.Complexity.SAT.computableInPolyTime_clause_length`,
  `Cslib.Complexity.SAT.computableInPolyTime_length`,
  `Cslib.Complexity.SAT.computableInPolyTime_vars_length`: literal, clause and
  variable-occurrence counts for natural-number variables, in unary (`fun_prop` versions of the
  generic `Cslib.Logic.PL.CNF` lemmas).
* `Cslib.Complexity.SAT.mem_NP`: satisfiability belongs to NP.
* `Cslib.Complexity.UNSAT_mem_coNP`: unsatisfiability belongs to coNP.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Formulas in conjunctive normal form are decoded along their encoding `encCNF`. -/
def cnfDecoder : Decoder encCNF := .list (.list (.pair .nat .bool))

namespace SAT

open ComputableTidilyInPolyTime

/-- Listing the variables in order of occurrence is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_vars :
    ComputableInPolyTime (CNF.vars (V := ℕ)) encCNF (encList encNat) :=
  (CNF.computableInPolyTime_vars encNat)

/-- Listing the distinct variables in order of first occurrence is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_distinctVars :
    ComputableInPolyTime (CNF.distinctVars (V := ℕ)) encCNF (encList encNat) :=
  CNF.computableInPolyTime_distinctVars encNat

/-- The number of distinct variables of a formula, in unary, is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_numVars :
    ComputableInPolyTime (CNF.numVars (V := ℕ)) encCNF encUnary :=
  CNF.computableInPolyTime_numVars encNat

/-- Encoding of a literal occurrence: unary clause and position indices with a binary-numbered
literal. -/
abbrev encOccurrence : Occurrence ℕ ↪ List Bool :=
  Cslib.Logic.PL.encOccurrence encNat

/-- Enumerating the literal occurrences of a CNF formula is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_occurrences :
    ComputableInPolyTime (occurrences (V := ℕ)) encCNF (encList encOccurrence) :=
  Cslib.Logic.PL.computableInPolyTime_occurrences encNat

/-- The number of literals of a polynomial-time clause, in unary, is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_clause_length {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ}
    (hc : ComputableInPolyTime c input (encList (encPair encNat encBool))) :
    ComputableInPolyTime (fun a => (c a).length) input encUnary := by
  have hc := hc.tidy
  exact (Clause.computableInPolyTime_length (.of_tidy hc))

/-- The number of clauses of a polynomial-time formula, in unary, is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_length {α : Type} {input : α ↪ List Bool} {φ : α → CNF ℕ}
    (hφ : ComputableInPolyTime φ input encCNF) :
    ComputableInPolyTime (fun a => (φ a).length) input encUnary := by
  have hφ := hφ.tidy
  exact (CNF.computableInPolyTime_length (encV := encNat) (.of_tidy hφ))

/-- The number of variable occurrences of a polynomial-time formula, in unary, is
polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_vars_length {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} (hφ : ComputableInPolyTime φ input encCNF) :
    ComputableInPolyTime (fun a => (φ a).vars.length) input encUnary := by
  have hφ := hφ.tidy
  exact (CNF.computableInPolyTime_vars_length (encV := encNat) (.of_tidy hφ))

/-- Reading the certificate at the first occurrence of a variable is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_assignment :
    ComputableInPolyTime (fun p : (CNF ℕ × List Bool) × ℕ => assignment p.1.1 p.1.2 p.2)
      (encPair (encPair encCNF encBits) encNat) encBool := by
  fun_prop [assignment]

/-- Evaluating a literal with the certificate assignment is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_literal :
    ComputableInPolyTime
      (fun p : (CNF ℕ × List Bool) × Literal ℕ => Literal.eval (assignment p.1.1 p.1.2) p.2)
      (encPair (encPair encCNF encBits) (encPair encNat encBool)) encBool := by
  fun_prop [Literal.eval, assignment]

/-- Evaluating a clause with the certificate assignment is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_clause :
    ComputableInPolyTime
      (fun p : (CNF ℕ × List Bool) × Clause ℕ => Clause.eval (assignment p.1.1 p.1.2) p.2)
      (encPair (encPair encCNF encBits) (encList (encPair encNat encBool))) encBool := by
  fun_prop [Clause.eval, Literal.eval, assignment]

/-- The SAT verifier is polynomial-time, including on certificates of arbitrary length. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encCNF encBits) encBool := by
  have hclause := computableInPolyTime_clause.tidy
  refine .of_tidy ?_
  fun_prop [verifier, CNF.eval]

/-- Satisfiability is in NP, with certificates of length equal to the encoded formula length. -/
theorem mem_NP : SAT ∈ NP encCNF :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end SAT

/-- Unsatisfiability is in coNP. -/
theorem UNSAT_mem_coNP : UNSAT ∈ coNP encCNF := by
  simpa only [mem_coNP, ← compl_SAT, compl_compl] using SAT.mem_NP

end Cslib.Complexity
