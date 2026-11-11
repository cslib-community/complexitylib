/-
Copyright (c) 2026 Vincent Palma, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma, Samuel Schlesinger
-/

import CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.Resolution
import Mathlib.Data.ZMod.Basic

/-!
# Tests for the bounded resolution-to-PCR translation

Repeating a literal arbitrarily often leaves squarefree degree and translated proof size
bounded. The examples also cover characteristic two, both polarities surviving resolution
of a tautological parent, duplicated nonpivot literals, and a variable type with no elements.
-/

namespace CslibFrontierTests.ProofComplexity.ResolutionPCR

open Cslib.Logic.PL MvPolynomial

/-! ### Arbitrarily many repeated literals -/

/-- A nonempty clause consisting of `n + 1` copies of one literal. -/
private def repeatedClause (n : ℕ) (b : Bool) : Clause Unit :=
  List.replicate (n + 1) ((), b)

/-- The old encoding retains every factor; the squarefree encoding retains just one. -/
example (n : ℕ) (b : Bool) :
    (repeatedClause n b).toPCRPoly ℚ = X ((), !b) ∧
    (repeatedClause n b).toPoly ℚ = X ((), !b) ^ (n + 1) := by
  simp [repeatedClause, Clause.toPCRPoly, Clause.toPoly, Std.Sat.Literal.negate,
    List.toFinset_replicate_of_ne_zero (Nat.succ_ne_zero n)]

/-- Width, support size, and squarefree degree stay fixed while the old degree grows. -/
example (n : ℕ) (b : Bool) :
    (repeatedClause n b).width = 1 ∧
    ((repeatedClause n b).toPCRPoly ℚ).support.card = 1 ∧
    ((repeatedClause n b).toPCRPoly ℚ).totalDegree = 1 ∧
    ((repeatedClause n b).toPoly ℚ).totalDegree = n + 1 := by
  simp [repeatedClause, Clause.width, Clause.toPCRPoly, Clause.toPoly,
    List.toFinset_replicate_of_ne_zero (Nat.succ_ne_zero n), support_X,
    totalDegree_X, totalDegree_X_pow]

/-- Contradictory unit clauses represented by arbitrarily long lists. -/
private def repeatedLiteralCNF (n : ℕ) : CNF Unit :=
  [repeatedClause n true, repeatedClause n false]

private def repeatedLiteralProof (n : ℕ) : List (Clause Unit) :=
  [[], repeatedClause n false, repeatedClause n true]

private theorem repeatedLiteral_isProof (n : ℕ) :
    (repeatedLiteralCNF n).IsProof (repeatedLiteralProof n) := by
  have h : (repeatedLiteralCNF n).IsProof
      [repeatedClause n false, repeatedClause n true] :=
    (CNF.IsProof.nil.mem (by simp [repeatedLiteralCNF])).mem
      (by simp [repeatedLiteralCNF])
  simpa [repeatedLiteralProof, repeatedClause, Clause.resolvent] using
    h.resolvent (c₁ := repeatedClause n true) (c₂ := repeatedClause n false) ()
      (by simp) (by simp) (by simp [repeatedClause]) (by simp [repeatedClause])

private theorem repeatedLiteral_width (n : ℕ) :
    ∀ c ∈ repeatedLiteralProof n, c.width ≤ 1 := by
  simp [repeatedLiteralProof, repeatedClause, Clause.width,
    List.toFinset_replicate_of_ne_zero (Nat.succ_ne_zero n)]

private theorem repeatedLiteral_pcr {R : Type*} [CommRing R] (n : ℕ) :
    ∃ ms, PC.IsProof ((repeatedLiteralCNF n).toPCRPolys R) ms ∧ 1 ∈ ms ∧
      PC.size ms ≤ 54 ∧ PC.degree ms ≤ 2 := by
  simpa [repeatedLiteralProof] using
    (repeatedLiteral_isProof n).exists_pcr_refutation (R := R)
      (by simp [repeatedLiteralProof]) (repeatedLiteral_width n)

/-- The same bounds hold for every repetition count in characteristic zero. -/
example (n : ℕ) :
    ∃ ms, PC.IsProof ((repeatedLiteralCNF n).toPCRPolys ℚ) ms ∧ 1 ∈ ms ∧
      PC.size ms ≤ 54 ∧ PC.degree ms ≤ 2 :=
  repeatedLiteral_pcr n

/-- Characteristic two requires no exception to the bounded simulation. -/
example (n : ℕ) :
    ∃ ms, PC.IsProof ((repeatedLiteralCNF n).toPCRPolys (ZMod 2)) ms ∧ 1 ∈ ms ∧
      PC.size ms ≤ 54 ∧ PC.degree ms ≤ 2 :=
  repeatedLiteral_pcr n

/-- The translated refutation certifies unsatisfiability through PCR soundness. -/
example (n : ℕ) : ¬ (repeatedLiteralCNF n).Satisfiable := by
  obtain ⟨ms, hms, h1, -, -⟩ := repeatedLiteral_pcr (R := ℚ) n
  exact CNF.not_satisfiable_of_pcr hms h1

/-- The degree-only corollary applies to the same three-line, width-one source proofs. -/
example (n : ℕ) :
    PC.RefutableInDegree ((repeatedLiteralCNF n).toPCRPolys ℚ) 2 := by
  have h : (repeatedLiteralCNF n).RefutableInWidth 1 :=
    ⟨repeatedLiteralProof n, repeatedLiteral_isProof n, by simp [repeatedLiteralProof],
      repeatedLiteral_width n⟩
  exact h.pcr_refutableInDegree

/-! ### Tautological parents and surviving pivot polarities -/

/-- A tautology together with a unit clause is satisfiable. -/
private def tautologicalCNF (b : Bool) : CNF Unit :=
  [[((), true), ((), false)], [((), b)]]

private def tautologicalProof (b : Bool) : List (Clause Unit) :=
  [[((), b)], [((), b)], [((), true), ((), false)]]

/-- Either pivot polarity can survive, depending on which parent is tautological. -/
private theorem tautological_isProof (b : Bool) :
    (tautologicalCNF b).IsProof (tautologicalProof b) := by
  have h : (tautologicalCNF b).IsProof [[((), b)], [((), true), ((), false)]] :=
    (CNF.IsProof.nil.mem (by simp [tautologicalCNF])).mem (by simp [tautologicalCNF])
  cases b
  · exact h.resolvent (c₁ := [((), true), ((), false)]) (c₂ := [((), false)]) ()
      (by decide) (by decide) (by decide) (by decide)
  · exact h.resolvent (c₁ := [((), true)]) (c₂ := [((), true), ((), false)]) ()
      (by decide) (by decide) (by decide) (by decide)

/-- Translation retains the actual resolvent, including its surviving pivot. -/
example (b : Bool) :
    ∃ ms, PC.IsProof ((tautologicalCNF b).toPCRPolys ℚ) ms ∧
      Clause.toPCRPoly [((), b)] ℚ ∈ ms ∧ PC.size ms ≤ 69 ∧ PC.degree ms ≤ 3 := by
  obtain ⟨ms, hms, hlines, hs, hd⟩ := (tautological_isProof b).exists_pcr (R := ℚ) (w := 2)
    (by cases b <;> decide)
  exact ⟨ms, hms, hlines _ (by simp [tautologicalProof]),
    by simpa [tautologicalProof] using hs, hd⟩

/-- Neither surviving-pivot example has a PCR refutation. -/
example (b : Bool) :
    ¬ ∃ ms, PC.IsProof ((tautologicalCNF b).toPCRPolys ℚ) ms ∧ 1 ∈ ms := by
  rintro ⟨ms, hms, h1⟩
  exact CNF.not_satisfiable_of_pcr hms h1 ⟨fun _ => b, by cases b <;> decide⟩

/-! ### A repeated nonpivot literal in the resolvent -/

private def sharedLiteralCNF : CNF Bool :=
  [[(false, true), (true, true)], [(false, false), (true, true)]]

private def sharedLiteralProof : List (Clause Bool) :=
  [[(true, true), (true, true)], [(false, false), (true, true)],
    [(false, true), (true, true)]]

private theorem sharedLiteral_isProof : sharedLiteralCNF.IsProof sharedLiteralProof := by
  have h : sharedLiteralCNF.IsProof
      [[(false, false), (true, true)], [(false, true), (true, true)]] :=
    (CNF.IsProof.nil.mem (by decide)).mem (by decide)
  exact h.resolvent (c₁ := [(false, true), (true, true)])
    (c₂ := [(false, false), (true, true)]) false
    (by decide) (by decide) (by decide) (by decide)

/-- A literal contributed by both parents gives one factor in the translated conclusion. -/
example : ∃ ms, PC.IsProof (sharedLiteralCNF.toPCRPolys ℚ) ms ∧
    X (true, false) ∈ ms ∧ PC.size ms ≤ 69 ∧ PC.degree ms ≤ 3 := by
  obtain ⟨ms, hms, hlines, hs, hd⟩ := sharedLiteral_isProof.exists_pcr (R := ℚ) (w := 2)
    (by decide)
  refine ⟨ms, hms, ?_, by simpa [sharedLiteralProof] using hs, hd⟩
  simpa [Clause.toPCRPoly, Std.Sat.Literal.negate] using
    hlines [(true, true), (true, true)] (by decide)

/-! ### Empty variable type -/

/-- With no variables, the empty clause contributes `1` and there are no axioms to append. -/
example : CNF.toPCRPolys ([[]] : CNF (Fin 0)) ℚ = [1] := by
  simp [CNF.toPCRPolys, PCR.axioms, Algebraic.boolAxioms]

/-- Translation includes a one-line refutation of width zero on an empty variable type. -/
example : ∃ ms, PC.IsProof (CNF.toPCRPolys ([[]] : CNF (Fin 0)) ℚ) ms ∧ 1 ∈ ms ∧
    PC.size ms ≤ 13 ∧ PC.degree ms ≤ 1 := by
  have h : CNF.IsProof ([[]] : CNF (Fin 0)) [[]] := CNF.IsProof.nil.mem (by simp)
  simpa using h.exists_pcr_refutation (R := ℚ) (w := 0) (by simp) (by simp)

/-- The empty CNF remains satisfiable even when there are no variables. -/
example : ¬ ∃ ms, PC.IsProof (CNF.toPCRPolys ([] : CNF (Fin 0)) ℚ) ms ∧ 1 ∈ ms := by
  rintro ⟨ms, hms, h1⟩
  exact CNF.not_satisfiable_of_pcr hms h1 ⟨fun _ => false, rfl⟩

end CslibFrontierTests.ProofComplexity.ResolutionPCR
