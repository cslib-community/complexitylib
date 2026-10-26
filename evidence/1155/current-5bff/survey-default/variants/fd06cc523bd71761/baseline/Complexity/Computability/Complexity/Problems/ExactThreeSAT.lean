/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.ThreeSAT
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# 3SAT with clauses of exactly three literals

`ExactThreeSAT` is the set of satisfiable formulas in conjunctive normal form all of whose clauses
are lists of exactly three literals. The literals of a clause need not be distinct, so a clause
`x ∨ x ∨ y` is allowed. This is weaker than 3-satisfiability as defined by Garey and Johnson
[Garey and Johnson, Problem LO2][GareyJohnson1979], whose clauses are sets of three distinct
literals; `NP`-completeness of that version, where short clauses are padded with fresh variables,
is not proved here.

`ExactThreeSAT` is `NP`-complete: `ThreeSAT` (clauses of at most three literals) reduces to it by
repeating a literal of every clause with one or two literals
(`Cslib.Complexity.ExactThreeSAT.padClause`, `Cslib.Complexity.toExactThreeSAT`). Repetition does
not change the value of a clause, and the empty clause stays empty, so a formula with an empty
clause stays unsatisfiable.

## Main definitions

* `Cslib.Complexity.ExactThreeSAT`.
* `Cslib.Complexity.ExactThreeSAT.padClause`: repeat literals to reach three.
* `Cslib.Complexity.toExactThreeSAT`: the reduction from `ThreeSAT`, padding every clause.

## Main results

* `Cslib.Complexity.ExactThreeSAT.mem_NP`: `ExactThreeSAT ∈ NP`.
* `Cslib.Complexity.polyTimeReducible_ThreeSAT_ExactThreeSAT`: `ThreeSAT` reduces to
  `ExactThreeSAT`.
* `Cslib.Complexity.ExactThreeSAT_npComplete`: `ExactThreeSAT` is `NP`-complete.

## References

* [M. R. Garey, D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The satisfiable formulas all of whose clauses have exactly three literals, not necessarily
distinct. The 3-satisfiability of [Garey and Johnson, Problem LO2][GareyJohnson1979] requires
them to be distinct. -/
def ExactThreeSAT : Set (CNF ℕ) := {φ | (∀ c ∈ φ, c.length = 3) ∧ φ.Satisfiable}

namespace ExactThreeSAT

/-- Pad a clause of one or two literals to three literals by repeating literals; other clauses are
unchanged. -/
def padClause (c : Clause ℕ) : Clause ℕ :=
  if c.length = 1 then c ++ c ++ c
  else if c.length = 2 then c ++ [c.headD (0, true)] else c

/-- Padding a clause neither adds nor removes literals. -/
private theorem mem_padClause (c : Clause ℕ) (l : Literal ℕ) : l ∈ padClause c ↔ l ∈ c := by
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, t⟩⟩⟩
  · simp [padClause]
  · simp [padClause]
  · simp only [padClause, List.length_cons, List.length_nil, Nat.reduceAdd,
      OfNat.ofNat_ne_one, ↓reduceIte, List.headD_cons, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · simp [padClause]

/-- Padding a clause does not shorten it. -/
private theorem length_le_length_padClause (c : Clause ℕ) : c.length ≤ (padClause c).length := by
  unfold padClause
  split_ifs <;> simp

/-- Padding a nonempty clause of at most three literals gives exactly three. -/
theorem length_padClause {c : Clause ℕ} (h0 : c ≠ []) (h3 : c.length ≤ 3) :
    (padClause c).length = 3 := by
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩
  · exact absurd rfl h0
  · simp [padClause]
  · simp [padClause]
  · simp [padClause]
  · simp only [List.length_cons] at h3
    omega

/-- Repeating literals does not change the value of a clause. -/
theorem eval_padClause (σ : ℕ → Bool) (c : Clause ℕ) :
    Clause.eval σ (padClause c) = Clause.eval σ c := by
  rw [Bool.eq_iff_iff, Clause.eval_eq_true_iff, Clause.eval_eq_true_iff]
  simp only [mem_padClause]

/-- Padding a clause is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_padClause :
    ComputableInPolyTime padClause (encList (encPair encNat encBool))
      (encList (encPair encNat encBool)) := by
  unfold padClause
  fun_prop

/-- The verifier for `ExactThreeSAT`: check that every clause has exactly three literals and
evaluate the formula under the certificate assignment. -/
def verifier (x : CNF ℕ × List Bool) : Bool :=
  (x.1.all fun c => c.length == 3) && SAT.verifier x

/-- `ExactThreeSAT.verifier` verifies `ExactThreeSAT` with certificates as long as the encoded
formula: it is `SAT.verifier` guarded by the clause-width test. -/
theorem isVerifier : IsVerifier encCNF Polynomial.X verifier ExactThreeSAT := by
  have h : ExactThreeSAT = {φ | (φ.all fun c => c.length == 3) = true ∧ φ ∈ SAT} := by
    ext φ
    simp only [ExactThreeSAT, Set.mem_ofPred_eq, List.all_eq_true, beq_iff_eq, mem_SAT]
  rw [h]
  exact SAT.isVerifier.guard

/-- Checking the clause widths and evaluating the formula is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encCNF encBits) encBool := by
  unfold verifier
  fun_prop

/-- `ExactThreeSAT` belongs to `NP`. -/
theorem mem_NP : ExactThreeSAT ∈ NP encCNF :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end ExactThreeSAT

open ExactThreeSAT

/-- The reduction from `ThreeSAT` to `ExactThreeSAT`: pad every clause. -/
def toExactThreeSAT (φ : CNF ℕ) : CNF ℕ := φ.map padClause

/-- Padding every clause is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toExactThreeSAT :
    ComputableInPolyTime toExactThreeSAT encCNF encCNF :=
  .of_tidy (ComputableTidilyInPolyTime.map computableInPolyTime_padClause.tidy)

/-- A formula is in `ThreeSAT` exactly when padding its clauses puts it in `ExactThreeSAT`. -/
theorem mem_ExactThreeSAT_toExactThreeSAT_iff (φ : CNF ℕ) :
    toExactThreeSAT φ ∈ ExactThreeSAT ↔ φ ∈ ThreeSAT := by
  have heval (σ : ℕ → Bool) : CNF.eval σ (toExactThreeSAT φ) = CNF.eval σ φ := by
    simp only [toExactThreeSAT, CNF.eval, List.all_map, Function.comp_def, eval_padClause]
  constructor
  · rintro ⟨hlen, σ, hσ⟩
    refine ⟨fun c hc => ?_, σ, by rw [← heval]; exact hσ⟩
    exact (length_le_length_padClause c).trans (hlen _ (List.mem_map_of_mem hc)).le
  · rintro ⟨hlen, σ, hσ⟩
    refine ⟨fun c' hc' => ?_, σ, by rw [heval]; exact hσ⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    refine length_padClause (fun h0 => ?_) (hlen c hc)
    have := (CNF.eval_eq_true_iff σ _).1 hσ c hc
    rw [h0, Clause.eval_nil] at this
    exact Bool.false_ne_true this

/-- `ThreeSAT` reduces to `ExactThreeSAT` in polynomial time via `toExactThreeSAT`. -/
theorem polyTimeReducible_ThreeSAT_ExactThreeSAT :
    PolyTimeReducible encCNF encCNF ThreeSAT ExactThreeSAT :=
  ⟨toExactThreeSAT, computableInPolyTime_toExactThreeSAT,
    fun φ => (mem_ExactThreeSAT_toExactThreeSAT_iff φ).symm⟩

/-- `ExactThreeSAT` is `NP`-hard. -/
theorem ExactThreeSAT_npHard : NPHard encCNF ExactThreeSAT :=
  ThreeSAT_npHard.trans polyTimeReducible_ThreeSAT_ExactThreeSAT

/-- **3SAT with clauses of exactly three, not necessarily distinct, literals is NP-complete.** -/
theorem ExactThreeSAT_npComplete : NPComplete encCNF ExactThreeSAT :=
  ⟨ExactThreeSAT.mem_NP, ExactThreeSAT_npHard⟩

end Cslib.Complexity
