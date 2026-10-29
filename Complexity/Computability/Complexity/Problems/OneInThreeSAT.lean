/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ExactOne.ModelCount
public import Complexity.Computability.Complexity.Problems.ThreeSATThree.Syntax
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Positive exact-one satisfiability

All four positive languages prohibit negated literals. `Three` bounds clause length by three;
`ExactThree` requires three distinct variables in each clause. The final `Three` bounds total
literal occurrences per variable by three, including repeated positions.

These notions reuse the signed CNF representation and the occurrence-count semantics
`CNF.evalOne`. Certificates use the same first-occurrence assignment as ordinary SAT.

## Main definitions

* `PositiveOneInThreeSAT`, `PositiveOneInExactThreeSAT`.
* `PositiveOneInThreeSATThree`, `PositiveOneInExactThreeSATThree`.
* `OneSAT`: exact-one satisfiability without syntax restrictions.

## Main results

* `OneSAT.mem_NP`: unrestricted exact-one satisfiability belongs to NP.
* Each positive language has an analogous `mem_NP` theorem.

## References

* [Hunt, Marathe, Radhakrishnan and Stearns][HuntMaratheRadhakrishnanStearns1998],
  Definition 2.9 and Theorem 3.8.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Exact-one satisfiable formulas, without a clause-size or polarity restriction. -/
def OneSAT : Set (CNF ℕ) := {φ | φ.OneSatisfiable}

namespace OneSAT

/-- Evaluate exact-one clauses under the usual first-occurrence certificate assignment. -/
def verifier (x : CNF ℕ × List Bool) : Bool := x.1.evalOne (SAT.assignment x.1 x.2)

/-- The standard SAT certificates also represent every exact-one satisfying assignment. -/
theorem isVerifier : IsVerifier encCNF Polynomial.X verifier OneSAT := by
  refine IsVerifier.of_padding (fun φ w _ h => ⟨_, h⟩) fun φ ⟨τ, hτ⟩ => ?_
  refine ⟨φ.vars.map τ, by simpa using SAT.length_vars_le φ, fun k => ?_⟩
  refine (CNF.evalOne_congr fun v hv => ?_).trans hτ
  have hlt : φ.vars.idxOf v < φ.vars.length := List.idxOf_lt_length_iff.mpr hv
  have hlt' : φ.vars.idxOf v < (φ.vars.map τ).length := by simpa using hlt
  rw [SAT.assignment, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt',
    List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
  rfl

/-- Count the true literal occurrences of a clause in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_clause_count :
    ComputableInPolyTime
      (fun p : (CNF ℕ × List Bool) × Clause ℕ =>
        p.2.countP (Literal.eval (SAT.assignment p.1.1 p.1.2)))
      (encPair (encPair encCNF encBits) (encList (encPair encNat encBool))) encUnary := by
  apply ComputableInPolyTime.countPWithInput
  · fun_prop
  · fun_prop [Literal.eval, SAT.assignment]

/-- An exact-one clause is verified in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_clause :
    ComputableInPolyTime
      (fun p : (CNF ℕ × List Bool) × Clause ℕ =>
        p.2.evalOne (SAT.assignment p.1.1 p.1.2))
      (encPair (encPair encCNF encBits) (encList (encPair encNat encBool))) encBool := by
  unfold Clause.evalOne
  exact ComputableInPolyTime.beq computableInPolyTime_clause_count (.const 1)

/-- The exact-one verifier is polynomial-time for binary formula labels. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encCNF encBits) encBool := by
  fun_prop [verifier, CNF.evalOne]

/-- Exact-one satisfiability belongs to NP. -/
theorem mem_NP : OneSAT ∈ NP encCNF :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

/-- Check that all literal polarities are positive. -/
def positiveCheck (φ : CNF ℕ) : Bool := φ.all fun c => c.all Prod.snd

/-- Positivity means that every occurring literal has polarity `true`. -/
theorem positiveCheck_iff (φ : CNF ℕ) :
    positiveCheck φ = true ↔ ∀ c ∈ φ, ∀ l ∈ c, l.2 = true := by
  simp [positiveCheck]

/-- Check for three distinct variable positions without any restriction on the input length. -/
def exactClauseCheck (c : Clause ℕ) : Bool :=
  (c.length == 3) &&
    (!((c.map Prod.fst).getD 0 0 == (c.map Prod.fst).getD 1 0)) &&
    (!((c.map Prod.fst).getD 0 0 == (c.map Prod.fst).getD 2 0)) &&
    (!((c.map Prod.fst).getD 1 0 == (c.map Prod.fst).getD 2 0))

/-- The exact-clause check requires three pairwise distinct variables. -/
theorem exactClauseCheck_iff (c : Clause ℕ) :
    exactClauseCheck c = true ↔ c.length = 3 ∧ (c.map Prod.fst).Nodup := by
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩
  all_goals simp [exactClauseCheck, List.getD, List.nodup_cons, and_assoc, and_left_comm,
    and_comm]

/-- Positivity is decidable in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_positiveCheck :
    ComputableInPolyTime positiveCheck encCNF encBool := by
  unfold positiveCheck encCNF
  fun_prop

/-- Exact length and distinctness of a clause are decidable in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_exactClauseCheck :
    ComputableInPolyTime exactClauseCheck (encList (encPair encNat encBool)) encBool := by
  have hvars : ComputableInPolyTime (fun c : Clause ℕ => c.map Prod.fst)
      (encList (encPair encNat encBool)) (encList encNat) := by fun_prop
  have hread (i : ℕ) : ComputableInPolyTime
      (fun c : Clause ℕ => (c.map Prod.fst).getD i 0)
      (encList (encPair encNat encBool)) encNat :=
    (ComputableInPolyTime.listGetD (encA := encNat) (encL := encList encNat) 0).comp
      (hvars.prod (.const i))
  have hlen : ComputableInPolyTime (fun c : Clause ℕ => c.length == 3)
      (encList (encPair encNat encBool)) encBool :=
    ComputableInPolyTime.beq
      (ComputableInPolyTime.length_list (encPair encNat encBool))
      (.const 3)
  have h01 := (hread 0).beq (hread 1)
  have h02 := (hread 0).beq (hread 2)
  have h12 := (hread 1).beq (hread 2)
  unfold exactClauseCheck
  fun_prop

end OneSAT

/-- Positive exact-one satisfiability with at most three literals per clause. -/
def PositiveOneInThreeSAT : Set (CNF ℕ) :=
  {φ | (∀ c ∈ φ, c.length ≤ 3) ∧ OneSAT.positiveCheck φ = true ∧ φ.OneSatisfiable}

/-- Positive exact-one satisfiability with exactly three distinct variables per clause. -/
def PositiveOneInExactThreeSAT : Set (CNF ℕ) :=
  {φ | (∀ c ∈ φ, c.length = 3 ∧ (c.map Prod.fst).Nodup) ∧
    OneSAT.positiveCheck φ = true ∧ φ.OneSatisfiable}

/-- Positive width-three exact-one satisfiability with at most three occurrences per variable. -/
def PositiveOneInThreeSATThree : Set (CNF ℕ) :=
  {φ | φ ∈ PositiveOneInThreeSAT ∧ ∀ v, φ.vars.count v ≤ 3}

/-- Positive exact-three exact-one satisfiability with at most three occurrences per variable. -/
def PositiveOneInExactThreeSATThree : Set (CNF ℕ) :=
  {φ | φ ∈ PositiveOneInExactThreeSAT ∧ ∀ v, φ.vars.count v ≤ 3}

namespace PositiveOneInThreeSAT

/-- The positive width-three syntax guard. -/
def syntaxCheck (φ : CNF ℕ) : Bool :=
  (φ.all fun c => decide (c.length ≤ 3)) && OneSAT.positiveCheck φ

/-- The syntax guard checks exactly the nonsemantic restrictions. -/
theorem syntaxCheck_iff (φ : CNF ℕ) :
    syntaxCheck φ = true ↔ (∀ c ∈ φ, c.length ≤ 3) ∧ OneSAT.positiveCheck φ = true := by
  simp [syntaxCheck]

/-- The positive width-three syntax guard is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_syntaxCheck :
    ComputableInPolyTime syntaxCheck encCNF encBool := by
  fun_prop [syntaxCheck, encCNF]

/-- Positive width-three exact-one satisfiability belongs to NP. -/
theorem mem_NP : PositiveOneInThreeSAT ∈ NP encCNF := by
  have h : PositiveOneInThreeSAT = {φ | syntaxCheck φ = true ∧ φ ∈ OneSAT} := by
    ext φ
    simp [PositiveOneInThreeSAT, syntaxCheck_iff, OneSAT, and_assoc]
  rw [h]
  exact ⟨Polynomial.X, fun x => syntaxCheck x.1 && OneSAT.verifier x,
    by fun_prop, OneSAT.isVerifier.guard⟩

end PositiveOneInThreeSAT

namespace PositiveOneInExactThreeSAT

/-- The positive exact-three syntax guard. -/
def syntaxCheck (φ : CNF ℕ) : Bool :=
  (φ.all OneSAT.exactClauseCheck) && OneSAT.positiveCheck φ

/-- The syntax guard checks three distinct variables and positivity. -/
theorem syntaxCheck_iff (φ : CNF ℕ) :
    syntaxCheck φ = true ↔
      (∀ c ∈ φ, c.length = 3 ∧ (c.map Prod.fst).Nodup) ∧ OneSAT.positiveCheck φ = true := by
  simp [syntaxCheck, OneSAT.exactClauseCheck_iff]

/-- The positive exact-three syntax guard is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_syntaxCheck :
    ComputableInPolyTime syntaxCheck encCNF encBool := by
  fun_prop [syntaxCheck, encCNF]

/-- Positive exact-three exact-one satisfiability belongs to NP. -/
theorem mem_NP : PositiveOneInExactThreeSAT ∈ NP encCNF := by
  have h : PositiveOneInExactThreeSAT = {φ | syntaxCheck φ = true ∧ φ ∈ OneSAT} := by
    ext φ
    simp [PositiveOneInExactThreeSAT, syntaxCheck_iff, OneSAT, and_assoc]
  rw [h]
  exact ⟨Polynomial.X, fun x => syntaxCheck x.1 && OneSAT.verifier x,
    by fun_prop, OneSAT.isVerifier.guard⟩

end PositiveOneInExactThreeSAT

namespace PositiveOneInThreeSATThree

/-- Check positivity, width three, and at most three occurrences per variable. -/
def syntaxCheck (φ : CNF ℕ) : Bool :=
  ThreeSATThree.syntaxCheck φ && OneSAT.positiveCheck φ

/-- The bounded positive syntax guard is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_syntaxCheck :
    ComputableInPolyTime syntaxCheck encCNF encBool := by
  unfold syntaxCheck
  fun_prop

/-- The bounded positive syntax guard checks exactly the syntactic restrictions. -/
theorem syntaxCheck_iff (φ : CNF ℕ) :
    syntaxCheck φ = true ↔ (∀ c ∈ φ, c.length ≤ 3) ∧
      OneSAT.positiveCheck φ = true ∧ ∀ v, φ.vars.count v ≤ 3 := by
  simp [syntaxCheck, ThreeSATThree.syntaxCheck_iff, and_assoc, and_comm]

/-- Positive width-three exact-one satisfiability with occurrence bound three belongs to NP. -/
theorem mem_NP : PositiveOneInThreeSATThree ∈ NP encCNF := by
  have h : PositiveOneInThreeSATThree = {φ | syntaxCheck φ = true ∧ φ ∈ OneSAT} := by
    ext φ
    simp [PositiveOneInThreeSATThree, PositiveOneInThreeSAT, syntaxCheck_iff, OneSAT,
      and_assoc, and_comm, and_left_comm]
  rw [h]
  exact ⟨Polynomial.X, fun x => syntaxCheck x.1 && OneSAT.verifier x,
    by fun_prop, OneSAT.isVerifier.guard⟩

end PositiveOneInThreeSATThree

namespace PositiveOneInExactThreeSATThree

/-- Check positive exact-three clauses and the occurrence bound three. -/
def syntaxCheck (φ : CNF ℕ) : Bool :=
  PositiveOneInExactThreeSAT.syntaxCheck φ && ThreeSATThree.syntaxCheck φ

/-- The bounded positive exact-three syntax guard is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_syntaxCheck :
    ComputableInPolyTime syntaxCheck encCNF encBool := by
  unfold syntaxCheck
  fun_prop

/-- The bounded exact-three guard checks exactly the syntactic restrictions. -/
theorem syntaxCheck_iff (φ : CNF ℕ) :
    syntaxCheck φ = true ↔
      (∀ c ∈ φ, c.length = 3 ∧ (c.map Prod.fst).Nodup) ∧
        OneSAT.positiveCheck φ = true ∧ ∀ v, φ.vars.count v ≤ 3 := by
  rw [syntaxCheck, Bool.and_eq_true, PositiveOneInExactThreeSAT.syntaxCheck_iff,
    ThreeSATThree.syntaxCheck_iff]
  constructor
  · rintro ⟨⟨hc, hp⟩, _, hv⟩
    exact ⟨hc, hp, hv⟩
  · rintro ⟨hc, hp, hv⟩
    exact ⟨⟨hc, hp⟩, (fun c h => (hc c h).1.le), hv⟩

/-- Positive exact-three exact-one satisfiability with occurrence bound three belongs to NP. -/
theorem mem_NP : PositiveOneInExactThreeSATThree ∈ NP encCNF := by
  have h : PositiveOneInExactThreeSATThree = {φ | syntaxCheck φ = true ∧ φ ∈ OneSAT} := by
    ext φ
    simp [PositiveOneInExactThreeSATThree, PositiveOneInExactThreeSAT, syntaxCheck_iff,
      OneSAT, and_assoc, and_comm, and_left_comm]
  rw [h]
  exact ⟨Polynomial.X, fun x => syntaxCheck x.1 && OneSAT.verifier x,
    by fun_prop, OneSAT.isVerifier.guard⟩

end PositiveOneInExactThreeSATThree

/-- Count exact-one models on the occurring variables, without a syntax restriction. -/
def SharpOneSAT (φ : CNF ℕ) : ℕ := φ.oneModelCount

/-- Count positive width-three exact-one models, returning zero on other syntax. -/
def SharpPositiveOneInThreeSAT (φ : CNF ℕ) : ℕ :=
  if PositiveOneInThreeSAT.syntaxCheck φ then SharpOneSAT φ else 0

/-- Count positive exact-three exact-one models, returning zero on other syntax. -/
def SharpPositiveOneInExactThreeSAT (φ : CNF ℕ) : ℕ :=
  if PositiveOneInExactThreeSAT.syntaxCheck φ then SharpOneSAT φ else 0

/-- Count positive width-three, occurrence-three exact-one models; reject other syntax. -/
def SharpPositiveOneInThreeSATThree (φ : CNF ℕ) : ℕ :=
  if PositiveOneInThreeSATThree.syntaxCheck φ then SharpOneSAT φ else 0

/-- Count positive exact-three, occurrence-three exact-one models; reject other syntax. -/
def SharpPositiveOneInExactThreeSATThree (φ : CNF ℕ) : ℕ :=
  if PositiveOneInExactThreeSATThree.syntaxCheck φ then SharpOneSAT φ else 0

/-- Exact-one satisfiability is equivalent to a positive exact-one model count. -/
theorem SharpOneSAT.mem_OneSAT_iff {φ : CNF ℕ} : φ ∈ OneSAT ↔ 0 < SharpOneSAT φ := by
  simp [OneSAT, SharpOneSAT, CNF.oneModelCount_pos_iff]

/-- Membership in the positive width-three language is positivity of its guarded count. -/
theorem SharpPositiveOneInThreeSAT.mem_PositiveOneInThreeSAT_iff {φ : CNF ℕ} :
    φ ∈ PositiveOneInThreeSAT ↔ 0 < SharpPositiveOneInThreeSAT φ := by
  have h : φ ∈ PositiveOneInThreeSAT ↔
      PositiveOneInThreeSAT.syntaxCheck φ = true ∧ φ.OneSatisfiable := by
    simp [PositiveOneInThreeSAT, PositiveOneInThreeSAT.syntaxCheck_iff, and_assoc]
  rw [h]
  unfold SharpPositiveOneInThreeSAT
  split <;> simp_all [SharpOneSAT, CNF.oneModelCount_pos_iff]

/-- Membership in the positive exact-three language is positivity of its guarded count. -/
theorem SharpPositiveOneInExactThreeSAT.mem_PositiveOneInExactThreeSAT_iff {φ : CNF ℕ} :
    φ ∈ PositiveOneInExactThreeSAT ↔ 0 < SharpPositiveOneInExactThreeSAT φ := by
  have h : φ ∈ PositiveOneInExactThreeSAT ↔
      PositiveOneInExactThreeSAT.syntaxCheck φ = true ∧ φ.OneSatisfiable := by
    simp [PositiveOneInExactThreeSAT, PositiveOneInExactThreeSAT.syntaxCheck_iff, and_assoc]
  rw [h]
  unfold SharpPositiveOneInExactThreeSAT
  split <;> simp_all [SharpOneSAT, CNF.oneModelCount_pos_iff]

/-- Membership in the positive width-three, occurrence-three language is a positive count. -/
theorem SharpPositiveOneInThreeSATThree.mem_PositiveOneInThreeSATThree_iff {φ : CNF ℕ} :
    φ ∈ PositiveOneInThreeSATThree ↔ 0 < SharpPositiveOneInThreeSATThree φ := by
  have h : φ ∈ PositiveOneInThreeSATThree ↔
      PositiveOneInThreeSATThree.syntaxCheck φ = true ∧ φ.OneSatisfiable := by
    simp [PositiveOneInThreeSATThree, PositiveOneInThreeSAT,
      PositiveOneInThreeSATThree.syntaxCheck_iff, and_assoc, and_comm, and_left_comm]
  rw [h]
  unfold SharpPositiveOneInThreeSATThree
  split <;> simp_all [SharpOneSAT, CNF.oneModelCount_pos_iff]

/-- Membership in the positive exact-three, occurrence-three language is a positive count. -/
theorem SharpPositiveOneInExactThreeSATThree.mem_PositiveOneInExactThreeSATThree_iff
    {φ : CNF ℕ} :
    φ ∈ PositiveOneInExactThreeSATThree ↔ 0 < SharpPositiveOneInExactThreeSATThree φ := by
  have h : φ ∈ PositiveOneInExactThreeSATThree ↔
      PositiveOneInExactThreeSATThree.syntaxCheck φ = true ∧ φ.OneSatisfiable := by
    simp [PositiveOneInExactThreeSATThree, PositiveOneInExactThreeSAT,
      PositiveOneInExactThreeSATThree.syntaxCheck_iff, and_assoc, and_comm, and_left_comm]
  rw [h]
  unfold SharpPositiveOneInExactThreeSATThree
  split <;> simp_all [SharpOneSAT, CNF.oneModelCount_pos_iff]

end Cslib.Complexity
