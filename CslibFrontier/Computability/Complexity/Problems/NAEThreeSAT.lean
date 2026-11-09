/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.EUThreeSAT
public import CslibFrontier.Computability.Complexity.Problems.ThreeSATThree
public import CslibFrontier.Logics.Propositional.CNF.NotAllEqual.ThreeOccurrence
import CslibFrontier.Computability.Complexity.Problems.OneInThreeSAT.Reduction
import CslibFrontier.Computability.Complexity.Problems.ThreeSATThree.Syntax
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# NAE 3SAT and NAE EU3SAT

`NAEThreeSAT` is NAE3SAT, with clauses of width at most three. `NAEEUThreeSAT` is NAE EU3SAT:
every clause has exactly three distinct variables. `NAEThreeSATThree` adds a bound of three
total literal occurrences per variable to `NAEThreeSAT`. The bounded-occurrence reduction uses
binary clauses; it does not prove hardness for exact-three occurrence-three NAE.

The original reduction from positive exact-one triples introduces one shared reference variable.
It replaces `(a,b,c)` by NAE triples `(a,b,c)`, `(a,b,t)`, `(a,c,t)`, `(b,c,t)`. Global
complement symmetry lets us assume `t=true`; the last three clauses then forbid two true
source literals, while the first requires at least one. The reference is fresh, and the output
has exactly three distinct variables per clause. Source hardness is
`PositiveOneInExactThreeSAT_npComplete`.

## Main definitions

* `NAESAT`: unrestricted not-all-equal satisfiability.
* `NAEThreeSAT`: NAE3SAT, with width at most three.
* `NAEEUThreeSAT`: NAE EU3SAT, with exactly three distinct variables per clause.
* `NAEThreeSATThree`: NAE3SAT-3, with width and variable occurrences at most three.
* `toNAEEUThreeSAT`: the exact-three distinct-variable reduction.

## Main results

* `NAEThreeSAT_npComplete`, `NAEEUThreeSAT_npComplete`, `NAEThreeSATThree_npComplete`.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Not-all-equal satisfiable formulas, without syntactic restrictions. -/
def NAESAT : Set (CNF ℕ) := {φ | φ.NAESatisfiable}

/-- Not-all-equal satisfiability with at most three literals per clause. -/
def NAEThreeSAT : Set (CNF ℕ) := {φ | (∀ c ∈ φ, c.length ≤ 3) ∧ φ.NAESatisfiable}

/-- NAE EU3SAT: not-all-equal satisfiability with exactly three distinct variables per clause. -/
def NAEEUThreeSAT : Set (CNF ℕ) := {φ | φ.IsExactThreeDistinct ∧ φ.NAESatisfiable}

/-- Not-all-equal width-three SAT with at most three literal occurrences per variable. -/
def NAEThreeSATThree : Set (CNF ℕ) :=
  {φ | (∀ c ∈ φ, c.length ≤ 3) ∧ (∀ v, φ.vars.count v ≤ 3) ∧ φ.NAESatisfiable}

namespace NAESAT

/-- Evaluate both polarities of every clause under the usual certificate assignment. -/
def verifier (x : CNF ℕ × List Bool) : Bool := x.1.evalNAE (SAT.assignment x.1 x.2)

/-- First-occurrence certificates also encode all NAE assignments. -/
theorem isVerifier : IsVerifier encCNF Polynomial.X verifier NAESAT := by
  refine IsVerifier.of_padding (fun φ w _ h => ⟨_, h⟩) fun φ ⟨τ, hτ⟩ => ?_
  refine ⟨φ.vars.map τ, by simpa using SAT.length_vars_le φ, fun k => ?_⟩
  refine (CNF.evalNAE_congr fun v hv => ?_).trans hτ
  have hlt : φ.vars.idxOf v < φ.vars.length := List.idxOf_lt_length_iff.mpr hv
  have hlt' : φ.vars.idxOf v < (φ.vars.map τ).length := by simpa using hlt
  rw [SAT.assignment, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt',
    List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
  rfl

/-- Evaluating the complemented certificate assignment is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_complementClause :
    ComputableInPolyTime
      (fun p : (CNF ℕ × List Bool) × Clause ℕ =>
        p.2.eval (fun v => !SAT.assignment p.1.1 p.1.2 v))
      (encPair (encPair encCNF encBits) (encList (encPair encNat encBool))) encBool := by
  fun_prop [Clause.eval, Literal.eval, SAT.assignment]

/-- NAE evaluation of an arbitrary certificate takes native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encCNF encBits) encBool := by
  fun_prop [verifier, CNF.evalNAE, CNF.eval]

/-- Unrestricted NAE satisfiability belongs to NP. -/
theorem mem_NP : NAESAT ∈ NP encCNF :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end NAESAT

/-- Width-three NAE satisfiability belongs to NP. -/
theorem NAEThreeSAT.mem_NP : NAEThreeSAT ∈ NP encCNF := by
  have h : NAEThreeSAT =
      {φ | (φ.all fun c => decide (c.length ≤ 3)) = true ∧ φ ∈ NAESAT} := by
    ext φ
    simp [NAEThreeSAT, NAESAT]
  rw [h]
  exact ⟨Polynomial.X, fun x => (x.1.all fun c => decide (c.length ≤ 3)) && NAESAT.verifier x,
    by fun_prop [encCNF], NAESAT.isVerifier.guard⟩

/-- Exact-three distinct-variable NAE satisfiability belongs to NP. -/
theorem NAEEUThreeSAT.mem_NP : NAEEUThreeSAT ∈ NP encCNF := by
  have h : NAEEUThreeSAT = {φ | EUThreeSAT.syntaxCheck φ = true ∧ φ ∈ NAESAT} := by
    ext φ
    simp [NAEEUThreeSAT, NAESAT, EUThreeSAT.syntaxCheck_iff]
  rw [h]
  exact ⟨Polynomial.X, fun x => EUThreeSAT.syntaxCheck x.1 && NAESAT.verifier x,
    by fun_prop, NAESAT.isVerifier.guard⟩

/-- Width-three occurrence-three NAE satisfiability belongs to NP. -/
theorem NAEThreeSATThree.mem_NP : NAEThreeSATThree ∈ NP encCNF := by
  have h : NAEThreeSATThree = {φ | ThreeSATThree.syntaxCheck φ = true ∧ φ ∈ NAESAT} := by
    ext φ
    simp [NAEThreeSATThree, NAESAT, ThreeSATThree.syntaxCheck_iff, and_assoc]
  rw [h]
  exact ⟨Polynomial.X, fun x => ThreeSATThree.syntaxCheck x.1 && NAESAT.verifier x,
    by fun_prop, NAESAT.isVerifier.guard⟩

namespace NAEEUThreeSAT

/-- Shift source variables away from the shared reference variable zero. -/
def liftLiteral (l : Literal ℕ) : Literal ℕ := (l.1 + 1, l.2)

/-- Shift a source triple and add its three pair constraints using reference variable zero. -/
def clause (c : Clause ℕ) : CNF ℕ :=
  Clause.oneNAEEncoding (0, true) (liftLiteral (c.getD 0 (0, false)))
    (liftLiteral (c.getD 1 (0, false))) (liftLiteral (c.getD 2 (0, false)))

/-- The four-clause replacement is native polynomial-time on binary source labels. -/
@[fun_prop]
theorem computableInPolyTime_clause :
    ComputableInPolyTime clause (encList (encPair encNat encBool)) encCNF := by
  have h0 := EUThreeSAT.computableInPolyTime_literalAt 0
  have h1 := EUThreeSAT.computableInPolyTime_literalAt 1
  have h2 := EUThreeSAT.computableInPolyTime_literalAt 2
  have hl : ComputableInPolyTime liftLiteral (encPair encNat encBool)
      (encPair encNat encBool) := by fun_prop [liftLiteral]
  fun_prop [clause, Clause.oneNAEEncoding, encCNF]

/-- A true reference makes every triple's replacement express exactly-one semantics. -/
theorem eval_clause (σ : ℕ → Bool) (hσ : σ 0 = true) (c : Clause ℕ) (hc : c.length = 3) :
    (clause c).evalNAE σ = c.evalOne (fun v => σ (v + 1)) := by
  match c, hc with
  | [a, b, c], _ =>
    have ht : Literal.eval σ (0, true) = true := by simp [Literal.eval, hσ]
    simpa [clause, liftLiteral, Clause.evalOne, List.countP_cons, Literal.eval] using
      Clause.eval_oneNAEEncoding σ (0, true) (liftLiteral a) (liftLiteral b) (liftLiteral c) ht

/-- All four target clauses have three distinct variables. The reference is fresh. -/
theorem exact_clause (c : Clause ℕ) (hc : c.IsExactThreeDistinct) :
    (clause c).IsExactThreeDistinct := by
  obtain ⟨a, b, d, rfl, hab, had, hbd⟩ := Clause.isExactThreeDistinct_iff.mp hc
  intro e he
  simp only [clause, List.getD, Clause.oneNAEEncoding, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  all_goals simp [Clause.IsExactThreeDistinct, liftLiteral, hab, had, hbd]

/-- A true reference gives the original exact-one formula under the shifted assignment. -/
theorem eval_formula (σ : ℕ → Bool) (hσ : σ 0 = true) (φ : CNF ℕ)
    (hw : φ.IsExactThreeDistinct) :
    CNF.evalNAE σ (φ.flatMap clause) = true ↔ φ.evalOne (fun v => σ (v + 1)) = true := by
  rw [CNF.evalNAE_flatMap_eq_true_iff, CNF.evalOne_eq_true_iff]
  exact forall₂_congr fun c hc => by rw [eval_clause σ hσ c (hw c hc).1]

/-- Global complement symmetry removes the need to pin the fresh reference variable. -/
theorem naeSatisfiable_formula (φ : CNF ℕ) (hw : φ.IsExactThreeDistinct) :
    CNF.NAESatisfiable (φ.flatMap clause) ↔ φ.OneSatisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    cases h0 : σ 0 with
    | false =>
      refine ⟨fun v => !σ (v + 1), ?_⟩
      exact (eval_formula (fun v => !σ v) (by simp [h0]) φ hw).mp
        (by simpa using hσ)
    | true => exact ⟨fun v => σ (v + 1), (eval_formula σ h0 φ hw).mp hσ⟩
  · rintro ⟨σ, hσ⟩
    let τ : ℕ → Bool := Nat.rec true (fun n _ => σ n)
    exact ⟨τ, (eval_formula τ rfl φ hw).mpr hσ⟩

end NAEEUThreeSAT

/-- Compile positive exact-one triples to NAE triples, rejecting malformed source syntax. -/
def toNAEEUThreeSAT (φ : CNF ℕ) : CNF ℕ :=
  if PositiveOneInExactThreeSAT.syntaxCheck φ then φ.flatMap NAEEUThreeSAT.clause else [[]]

/-- The complete NAE reduction is native polynomial-time under binary CNF encodings. -/
@[fun_prop]
theorem computableInPolyTime_toNAEEUThreeSAT :
    ComputableInPolyTime toNAEEUThreeSAT encCNF encCNF := by
  fun_prop [toNAEEUThreeSAT, encCNF]

/-- Total correctness of the exact-three distinct-variable NAE compiler. -/
theorem mem_NAEEUThreeSAT_toNAEEUThreeSAT_iff (φ : CNF ℕ) :
    toNAEEUThreeSAT φ ∈ NAEEUThreeSAT ↔ φ ∈ PositiveOneInExactThreeSAT := by
  unfold toNAEEUThreeSAT
  split_ifs with hg
  · obtain ⟨hw, hp⟩ := (PositiveOneInExactThreeSAT.syntaxCheck_iff φ).mp hg
    have he : CNF.IsExactThreeDistinct (φ.flatMap NAEEUThreeSAT.clause) := by
      intro d hd
      obtain ⟨c, hc, hd⟩ := List.mem_flatMap.mp hd
      exact NAEEUThreeSAT.exact_clause c (hw c hc) d hd
    change (_ ∧ _) ↔ _ ∧ _ ∧ _
    simp only [he, hp, true_and]
    have hs := NAEEUThreeSAT.naeSatisfiable_formula φ hw
    exact ⟨fun h => ⟨hw, hs.mp h⟩, fun h => hs.mpr h.2⟩
  · have hg' : ¬((∀ c ∈ φ, c.length = 3 ∧ (c.map Prod.fst).Nodup) ∧
        OneSAT.positiveCheck φ = true) :=
      fun h => hg ((PositiveOneInExactThreeSAT.syntaxCheck_iff φ).mpr h)
    simp only [NAEEUThreeSAT, Set.mem_ofPred_eq, CNF.IsExactThreeDistinct,
      Clause.IsExactThreeDistinct, PositiveOneInExactThreeSAT] at *
    simp_all

/-- Positive exact-three exact-one SAT reduces to exact-three distinct-variable NAE SAT. -/
theorem polyTimeReducible_PositiveOneInExactThreeSAT_NAEEUThreeSAT :
    PolyTimeReducible encCNF encCNF PositiveOneInExactThreeSAT NAEEUThreeSAT :=
  ⟨toNAEEUThreeSAT, computableInPolyTime_toNAEEUThreeSAT,
    fun φ => (mem_NAEEUThreeSAT_toNAEEUThreeSAT_iff φ).symm⟩

/-- NAE EU3SAT is NP-hard, without an occurrence bound. -/
theorem NAEEUThreeSAT_npHard : NPHard encCNF NAEEUThreeSAT :=
  PositiveOneInExactThreeSAT_npHard.trans
    polyTimeReducible_PositiveOneInExactThreeSAT_NAEEUThreeSAT

/-- NAE EU3SAT is NP-complete. -/
theorem NAEEUThreeSAT_npComplete : NPComplete encCNF NAEEUThreeSAT :=
  ⟨NAEEUThreeSAT.mem_NP, NAEEUThreeSAT_npHard⟩

/-- Forget exact-three syntax after rejecting formulas outside that source syntax. -/
theorem polyTimeReducible_NAEEUThreeSAT_NAEThreeSAT :
    PolyTimeReducible encCNF encCNF NAEEUThreeSAT NAEThreeSAT := by
  refine ⟨fun φ => if EUThreeSAT.syntaxCheck φ then φ else [[]], by fun_prop, ?_⟩
  intro φ
  dsimp only
  split_ifs with hg
  · have he := (EUThreeSAT.syntaxCheck_iff φ).mp hg
    have hw : ∀ c ∈ φ, c.length ≤ 3 := fun c hc => (he c hc).1.le
    change (_ ∧ _) ↔ _ ∧ _
    exact ⟨fun h => ⟨hw, h.2⟩, fun h => ⟨he, h.2⟩⟩
  · have he : ¬φ.IsExactThreeDistinct := fun h => hg ((EUThreeSAT.syntaxCheck_iff φ).mpr h)
    simp [NAEEUThreeSAT, NAEThreeSAT, he, CNF.NAESatisfiable, CNF.evalNAE]

/-- Width-at-most-three NAE SAT is NP-hard. -/
theorem NAEThreeSAT_npHard : NPHard encCNF NAEThreeSAT :=
  NAEEUThreeSAT_npHard.trans polyTimeReducible_NAEEUThreeSAT_NAEThreeSAT

/-- Width-at-most-three NAE SAT is NP-complete. -/
theorem NAEThreeSAT_npComplete : NPComplete encCNF NAEThreeSAT :=
  ⟨NAEThreeSAT.mem_NP, NAEThreeSAT_npHard⟩

/-- The ordinary splitter is also a total reduction between the NAE languages. -/
theorem mem_NAEThreeSATThree_toThreeSATThree_iff (φ : CNF ℕ) :
    toThreeSATThree φ ∈ NAEThreeSATThree ↔ φ ∈ NAEThreeSAT := by
  unfold toThreeSATThree
  split_ifs with hg
  · have hw : ∀ c ∈ φ, c.length ≤ 3 := by simpa using hg
    have hs := (CNF.naeSatisfiable_relabel ThreeSATThree.numberCopy_injective
      φ.toThreeOccurrence).trans (CNF.naeSatisfiable_toThreeOccurrence φ)
    have hc := count_vars_toThreeSATThree_le φ
    have ht := width_toThreeSATThree φ
    simp only [toThreeSATThree, hg, ↓reduceIte] at hc ht
    change (_ ∧ _ ∧ _) ↔ _ ∧ _
    exact ⟨fun h => ⟨hw, hs.mp h.2.2⟩, fun h => ⟨ht, hc, hs.mpr h.2⟩⟩
  · have hw : ¬∀ c ∈ φ, c.length ≤ 3 := by simpa using hg
    simp [NAEThreeSATThree, NAEThreeSAT, hw, CNF.NAESatisfiable, CNF.evalNAE]

/-- The native occurrence splitter gives the bounded-occurrence NAE reduction. -/
theorem polyTimeReducible_NAEThreeSAT_NAEThreeSATThree :
    PolyTimeReducible encCNF encCNF NAEThreeSAT NAEThreeSATThree :=
  ⟨toThreeSATThree, computableInPolyTime_toThreeSATThree,
    fun φ => (mem_NAEThreeSATThree_toThreeSATThree_iff φ).symm⟩

/-- NAE 3SAT-3 is NP-hard with binary and ternary clauses allowed. -/
theorem NAEThreeSATThree_npHard : NPHard encCNF NAEThreeSATThree :=
  NAEThreeSAT_npHard.trans polyTimeReducible_NAEThreeSAT_NAEThreeSATThree

/-- NAE 3SAT-3 is NP-complete with binary and ternary clauses allowed. -/
theorem NAEThreeSATThree_npComplete : NPComplete encCNF NAEThreeSATThree :=
  ⟨NAEThreeSATThree.mem_NP, NAEThreeSATThree_npHard⟩

end Cslib.Complexity
