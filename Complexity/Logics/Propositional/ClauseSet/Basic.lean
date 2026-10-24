/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Sort

/-!
# Clause sets

A *clause set* is a finite set of clauses, each a finite set of literals: the set-based form of a
formula in conjunctive normal form, in which the order and repetition of clauses and literals do
not matter. Set operations on clauses (subclauses, differences) are what the sparsification lemma
works with. A formula in conjunctive normal form and its clause set have the same solutions
(`CNF.sat_toClauseSet_iff`), and a clause set is the clause set of a formula listing its clauses
(`ClauseSet.eval_toCNF_eq_true_iff`).

## Main definitions

* `Cslib.Logic.PL.ClauseSet`: finite sets of finite sets of literals.
* `Cslib.Logic.PL.ClauseSet.Sat`, `Cslib.Logic.PL.ClauseSet.solutions`: satisfaction.
* `Cslib.Logic.PL.ClauseSet.occurrences`: the number of clauses mentioning a variable.
* `Cslib.Logic.PL.CNF.toClauseSet`, `Cslib.Logic.PL.ClauseSet.toCNF`: the translations.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- There are two literals for each variable. -/
theorem card_literal [Fintype V] : Fintype.card (Literal V) = 2 * Fintype.card V := by
  simp [Literal, Std.Sat.Literal, Fintype.card_prod, mul_comm]

/-- A *clause set*: a finite set of clauses, each a finite set of literals. A clause is satisfied
when one of its literals is true; a clause set when all of its clauses are. -/
abbrev ClauseSet (V : Type*) := Finset (Finset (Literal V))

namespace ClauseSet

/-- `x` satisfies every clause of `ψ`. -/
def Sat (ψ : ClauseSet V) (x : V → Bool) : Prop :=
  ∀ C ∈ ψ, ∃ l ∈ C, x l.1 = l.2

/-- Whether an assignment satisfies a clause set is decidable. -/
instance (ψ : ClauseSet V) (x : V → Bool) : Decidable (ψ.Sat x) :=
  inferInstanceAs (Decidable (∀ C ∈ ψ, ∃ l ∈ C, _))

/-- The solutions of a clause set. -/
def solutions [Fintype V] (ψ : ClauseSet V) : Finset (V → Bool) :=
  univ.filter ψ.Sat

/-- An assignment belongs to `ψ.solutions` if and only if it satisfies `ψ`. -/
@[simp] theorem mem_solutions [Fintype V] {ψ : ClauseSet V} {x : V → Bool} :
    x ∈ ψ.solutions ↔ ψ.Sat x := by
  simp [solutions]

/-- The number of clauses of `ψ` mentioning the variable `v`. -/
def occurrences (ψ : ClauseSet V) (v : V) : ℕ :=
  (ψ.filter fun C => ∃ l ∈ C, l.1 = v).card

end ClauseSet

/-- The clause set of a formula in conjunctive normal form. -/
def CNF.toClauseSet (φ : CNF V) : ClauseSet V :=
  (φ.map List.toFinset).toFinset

/-- A formula in conjunctive normal form and its clause set have the same solutions. -/
theorem CNF.sat_toClauseSet_iff (φ : CNF V) (x : V → Bool) :
    φ.toClauseSet.Sat x ↔ φ.eval x = true := by
  simp only [ClauseSet.Sat, CNF.toClauseSet, List.mem_toFinset, List.mem_map,
    CNF.eval_eq_true_iff, Clause.eval_eq_true_iff, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

/-- A clause of the clause set of a formula has at most as many literals as the clause it comes
from. -/
theorem CNF.exists_card_le_of_mem_toClauseSet {φ : CNF V} {C : Finset (Literal V)}
    (hC : C ∈ φ.toClauseSet) : ∃ c ∈ φ, C.card ≤ c.length := by
  simp only [CNF.toClauseSet, List.mem_toFinset, List.mem_map] at hC
  obtain ⟨c, hc, rfl⟩ := hC
  exact ⟨c, hc, List.toFinset_card_le c⟩

/-- A formula listing the clauses of a clause set. -/
noncomputable def ClauseSet.toCNF (ψ : ClauseSet V) : CNF V :=
  ψ.toList.map Finset.toList

omit [DecidableEq V] in
/-- The formula of a clause set accepts exactly its solutions. -/
theorem ClauseSet.eval_toCNF_eq_true_iff (ψ : ClauseSet V) (x : V → Bool) :
    ψ.toCNF.eval x = true ↔ ψ.Sat x := by
  simp only [ClauseSet.toCNF, CNF.eval_eq_true_iff, List.mem_map, Finset.mem_toList,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Clause.eval_eq_true_iff,
    ClauseSet.Sat]

omit [DecidableEq V] in
/-- The clauses of the formula of a clause set have at most as many literals as its clauses. -/
theorem ClauseSet.length_le_of_mem_toCNF {ψ : ClauseSet V} {k : ℕ} (hk : ∀ C ∈ ψ, C.card ≤ k)
    {c : Clause V} (hc : c ∈ ψ.toCNF) : c.length ≤ k := by
  simp only [ClauseSet.toCNF, List.mem_map, Finset.mem_toList] at hc
  obtain ⟨C, hC, rfl⟩ := hc
  rw [Finset.length_toList]
  exact hk C hC

/-- The formula of a clause set has as many clauses mentioning `v` as the clause set. -/
theorem ClauseSet.occurrences_toCNF (ψ : ClauseSet V) (v : V) :
    ψ.toCNF.occurrences v = ψ.occurrences v := by
  simp only [CNF.occurrences, ClauseSet.toCNF, List.countP_map, ClauseSet.occurrences]
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup
    ((Finset.nodup_toList ψ).filter _)]
  congr 1
  ext C
  simp [Finset.mem_toList]

end Cslib.Logic.PL
