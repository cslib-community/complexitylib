/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Complexity.Problems.OneInThreeSAT
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Logics.Propositional.CNF.ExactOne.ThreeEncoding
public import Complexity.Logics.Propositional.CNF.ExactThree.ThreeOccurrence
import Complexity.Computability.Complexity.Problems.OneInThreeSAT.Reduction
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# EU3SAT: exactly three distinct variables per clause

`EUThreeSAT` uses ordinary disjunction and requires three distinct variables in every clause.
Its native polynomial-time reduction from positive exact-one SAT replaces each triple by its
five-clause truth-table encoding, without new variables. Invalid source syntax is rejected.

There is no occurrence bound in this NP-completeness theorem. In particular, exact-three
formulas with distinct variables and at most three occurrences per variable are always
satisfiable, by the Hall matching argument; they are not the width-at-most-three 3SAT-3 problem.

## Main definitions

* `EUThreeSAT`: ordinary satisfiability with exact-three distinct-variable syntax.
* `toEUThreeSAT`: the reduction from positive exact-three exact-one SAT.

## Main results

* `EUThreeSAT_npComplete`: NP-completeness under the binary CNF encoding.

The reduction and its computational certificate are original. Its source hardness theorem is
`PositiveOneInExactThreeSAT_npComplete`.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Ordinary SAT with exactly three distinct variables per clause, with arbitrary signs. -/
def EUThreeSAT : Set (CNF ℕ) := {φ | φ.IsExactThreeDistinct ∧ φ.Satisfiable}

namespace EUThreeSAT

/-- Check exact-three distinct-variable syntax, allowing either literal polarity. -/
def syntaxCheck (φ : CNF ℕ) : Bool := φ.all OneSAT.exactClauseCheck

/-- The executable syntax test agrees with the shared mathematical predicate. -/
theorem syntaxCheck_iff (φ : CNF ℕ) : syntaxCheck φ = true ↔ φ.IsExactThreeDistinct := by
  simp [syntaxCheck, CNF.IsExactThreeDistinct, Clause.IsExactThreeDistinct,
    OneSAT.exactClauseCheck_iff]

/-- Exact-three distinct-variable syntax is decidable in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_syntaxCheck :
    ComputableInPolyTime syntaxCheck encCNF encBool := by
  fun_prop [syntaxCheck, encCNF]

/-- The ordinary SAT verifier guarded by exact-three distinct-variable syntax. -/
def verifier (x : CNF ℕ × List Bool) : Bool := syntaxCheck x.1 && SAT.verifier x

/-- The syntax guard preserves the usual first-occurrence certificate convention. -/
theorem isVerifier : IsVerifier encCNF Polynomial.X verifier EUThreeSAT := by
  have h : EUThreeSAT = {φ | syntaxCheck φ = true ∧ φ ∈ SAT} := by
    ext φ
    simp [EUThreeSAT, syntaxCheck_iff, SAT]
  rw [h]
  exact SAT.isVerifier.guard

/-- EU3SAT belongs to NP under the ordinary binary formula encoding. -/
theorem mem_NP : EUThreeSAT ∈ NP encCNF :=
  ⟨Polynomial.X, verifier, by fun_prop [verifier], isVerifier⟩

/-- Read a literal position, supplying a fixed value outside the clause. -/
theorem computableInPolyTime_literalAt (i : ℕ) :
    ComputableInPolyTime (fun c : Clause ℕ => c.getD i (0, false))
      (encList (encPair encNat encBool)) (encPair encNat encBool) := by
  exact ComputableInPolyTime.listGetDWithInput
    (ComputableInPolyTime.id' (encIn := encList (encPair encNat encBool)))
    (ComputableInPolyTime.const i) (0, false)

/-- Emit the five-clause truth table for the first three literal positions. -/
def clause (c : Clause ℕ) : CNF ℕ :=
  Clause.oneThreeEncoding (c.getD 0 (0, false)) (c.getD 1 (0, false))
    (c.getD 2 (0, false))

/-- The constant-size clause replacement is computed in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_clause :
    ComputableInPolyTime clause (encList (encPair encNat encBool)) encCNF := by
  have h0 := (computableInPolyTime_literalAt 0).tidy
  have h1 := (computableInPolyTime_literalAt 1).tidy
  have h2 := (computableInPolyTime_literalAt 2).tidy
  unfold clause Clause.oneThreeEncoding encCNF
  fun_prop

/-- On a triple, the replacement expresses exactly-one semantics. -/
theorem eval_clause (σ : ℕ → Bool) (c : Clause ℕ) (hc : c.length = 3) :
    (clause c).eval σ = c.evalOne σ := by
  match c, hc with
  | [a, b, c], _ => simpa [clause] using Clause.eval_oneThreeEncoding σ a b c

/-- The replacement preserves exact-three distinct-variable syntax. -/
theorem exact_clause (c : Clause ℕ) (hc : c.IsExactThreeDistinct) :
    (clause c).IsExactThreeDistinct := by
  obtain ⟨a, b, d, rfl, h⟩ := Clause.isExactThreeDistinct_iff.mp hc
  simpa [clause] using Clause.isExactThreeDistinct_oneThreeEncoding a b d
    (Clause.isExactThreeDistinct_iff.mpr ⟨a, b, d, rfl, h⟩)

end EUThreeSAT

/-- Ordinary EU3SAT with at most three literal occurrences per variable. -/
def EUThreeSATThree : Set (CNF ℕ) :=
  {φ | φ.IsExactThreeDistinct ∧ (∀ v, φ.vars.count v ≤ 3) ∧ φ.Satisfiable}

/-- In the occurrence-three exact-distinct language, the syntax alone ensures satisfiability. -/
theorem mem_EUThreeSATThree_iff (φ : CNF ℕ) :
    φ ∈ EUThreeSATThree ↔ φ.IsExactThreeDistinct ∧ ∀ v, φ.vars.count v ≤ 3 :=
  ⟨fun h => ⟨h.1, h.2.1⟩,
    fun h => ⟨h.1, h.2, CNF.satisfiable_of_exactThreeDistinct_of_count_le_three h.1 h.2⟩⟩

/-- EU3SAT-3 is decidable in native polynomial time by checking only its syntax. -/
theorem EUThreeSATThree.mem_P : EUThreeSATThree ∈ P encCNF := by
  refine ⟨fun φ => EUThreeSAT.syntaxCheck φ &&
      ThreeSATThree.syntaxCheck φ, by fun_prop, fun φ => ?_⟩
  rw [mem_EUThreeSATThree_iff, Bool.and_eq_true, EUThreeSAT.syntaxCheck_iff,
    ThreeSATThree.syntaxCheck_iff]
  exact ⟨fun h => ⟨h.1, (fun c hc => (h.1 c hc).1.le), h.2⟩,
    fun h => ⟨h.1, h.2.2⟩⟩

/-- Replace positive exact-one triples by ordinary exact-three clauses; reject invalid syntax. -/
def toEUThreeSAT (φ : CNF ℕ) : CNF ℕ :=
  if PositiveOneInExactThreeSAT.syntaxCheck φ then φ.flatMap EUThreeSAT.clause else [[]]

/-- The complete reduction is polynomial-time on binary variable labels. -/
@[fun_prop]
theorem computableInPolyTime_toEUThreeSAT :
    ComputableInPolyTime toEUThreeSAT encCNF encCNF := by
  fun_prop [toEUThreeSAT, encCNF]

/-- Total correctness includes source inputs outside the positive exact-three syntax. -/
theorem mem_EUThreeSAT_toEUThreeSAT_iff (φ : CNF ℕ) :
    toEUThreeSAT φ ∈ EUThreeSAT ↔ φ ∈ PositiveOneInExactThreeSAT := by
  unfold toEUThreeSAT
  split_ifs with hg
  · obtain ⟨hw, hp⟩ := (PositiveOneInExactThreeSAT.syntaxCheck_iff φ).mp hg
    have he : CNF.IsExactThreeDistinct (φ.flatMap EUThreeSAT.clause) := by
      intro d hd
      obtain ⟨c, hc, hd⟩ := List.mem_flatMap.mp hd
      exact EUThreeSAT.exact_clause c (hw c hc) d hd
    have hv (σ : ℕ → Bool) : CNF.eval σ (φ.flatMap EUThreeSAT.clause) = φ.evalOne σ := by
      rw [Bool.eq_iff_iff, CNF.eval_flatMap_eq_true_iff, CNF.evalOne_eq_true_iff]
      exact forall₂_congr fun c hc => by rw [EUThreeSAT.eval_clause σ c (hw c hc).1]
    change (_ ∧ _) ↔ _ ∧ _ ∧ _
    have hs : CNF.Satisfiable (φ.flatMap EUThreeSAT.clause) ↔ φ.OneSatisfiable := by
      grind [CNF.Satisfiable, CNF.OneSatisfiable]
    simp only [he, hp, true_and]
    exact ⟨fun h => ⟨hw, hs.mp h⟩, fun h => hs.mpr h.2⟩
  · have hg' : ¬((∀ c ∈ φ, c.length = 3 ∧ (c.map Prod.fst).Nodup) ∧
        OneSAT.positiveCheck φ = true) :=
      fun h => hg ((PositiveOneInExactThreeSAT.syntaxCheck_iff φ).mpr h)
    simp only [EUThreeSAT, Set.mem_ofPred_eq, CNF.IsExactThreeDistinct,
      Clause.IsExactThreeDistinct, PositiveOneInExactThreeSAT] at *
    simp_all

/-- Positive exact-three exact-one SAT reduces to ordinary EU3SAT. -/
theorem polyTimeReducible_PositiveOneInExactThreeSAT_EUThreeSAT :
    PolyTimeReducible encCNF encCNF PositiveOneInExactThreeSAT EUThreeSAT :=
  ⟨toEUThreeSAT, computableInPolyTime_toEUThreeSAT,
    fun φ => (mem_EUThreeSAT_toEUThreeSAT_iff φ).symm⟩

/-- EU3SAT is NP-hard. No bound on variable occurrences is imposed. -/
theorem EUThreeSAT_npHard : NPHard encCNF EUThreeSAT :=
  PositiveOneInExactThreeSAT_npHard.trans
    polyTimeReducible_PositiveOneInExactThreeSAT_EUThreeSAT

/-- EU3SAT is NP-complete. -/
theorem EUThreeSAT_npComplete : NPComplete encCNF EUThreeSAT :=
  ⟨EUThreeSAT.mem_NP, EUThreeSAT_npHard⟩

end Cslib.Complexity
