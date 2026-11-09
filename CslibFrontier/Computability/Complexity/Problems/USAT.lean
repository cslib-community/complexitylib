/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Complexity.Problems.SAT
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime

/-!
# Unique satisfiability

A formula in conjunctive normal form is *uniquely satisfiable* when it has exactly one
satisfying assignment of its variables. Formulas here have variables numbered by `ℕ`, and an
assignment `ℕ → Bool` also gives values to the infinitely many variables that do not occur; so
`USAT` asks for a satisfying assignment with which every satisfying assignment agrees on the
variables of the formula (`Cslib.Logic.PL.CNF.vars`).

Valiant and Vazirani consider the promise problem `PromiseUSAT` whose yes-instances are the
uniquely satisfiable formulas and whose no-instances are the unsatisfiable ones
[Valiant and Vazirani][ValiantVazirani1986], [Arora and Barak, Section 17.4][AroraBarak09].
Formulas with two or more satisfying assignments are outside the promise, so a function solves
`PromiseUSAT` when the set it accepts lies between `USAT` and `SAT` (`solvedBy_PromiseUSAT_iff`);
deciding either `USAT` or `SAT` does (`solvedBy_USAT`, `solvedBy_SAT`). `PromiseUSAT` lies in
`PromiseNP`, separated by `SAT` (`PromiseUSAT_mem_PromiseNP`).

## Main definitions

* `Cslib.Complexity.USAT`: the uniquely satisfiable formulas.
* `Cslib.Complexity.PromiseUSAT`: unique satisfiability as a promise problem.

## Main results

* `Cslib.Complexity.USAT_subset_SAT`: a uniquely satisfiable formula is satisfiable.
* `Cslib.Complexity.solvedBy_PromiseUSAT_iff`: the solutions of `PromiseUSAT`.
* `Cslib.Complexity.solvedBy_USAT`, `Cslib.Complexity.solvedBy_SAT`: deciding `USAT`, or `SAT`,
  solves `PromiseUSAT`.
* `Cslib.Complexity.PromiseUSAT_mem_PromiseNP`: `PromiseUSAT` lies in `PromiseNP`.

## References

* [A. Blass, Y. Gurevich, *On the unique satisfiability problem*][BlassGurevich1982]
* [L. G. Valiant, V. V. Vazirani, *NP is as easy as detecting unique
  solutions*][ValiantVazirani1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL PromiseProblem

/-- The uniquely satisfiable formulas: some assignment satisfies the formula, and every satisfying
assignment agrees with it on every variable of the formula
[Blass and Gurevich][BlassGurevich1982]. -/
def USAT : Set (CNF ℕ) :=
  {φ | ∃ σ : ℕ → Bool, φ.eval σ = true ∧
    ∀ τ : ℕ → Bool, φ.eval τ = true → ∀ v ∈ φ.vars, τ v = σ v}

theorem mem_USAT {φ : CNF ℕ} : φ ∈ USAT ↔ ∃ σ : ℕ → Bool, φ.eval σ = true ∧
    ∀ τ : ℕ → Bool, φ.eval τ = true → ∀ v ∈ φ.vars, τ v = σ v :=
  Iff.rfl

/-- A uniquely satisfiable formula is satisfiable. -/
theorem USAT_subset_SAT : USAT ⊆ SAT := fun _ ⟨σ, hσ, _⟩ => ⟨σ, hσ⟩

/-- No uniquely satisfiable formula is unsatisfiable. -/
theorem disjoint_USAT_UNSAT : Disjoint USAT UNSAT :=
  Set.disjoint_left.2 fun _ hφ hφ' => hφ' (USAT_subset_SAT hφ)

/-- Unique satisfiability as a promise problem: the yes-instances are the uniquely satisfiable
formulas, the no-instances the unsatisfiable ones, and formulas with at least two satisfying
assignments are outside the promise. -/
def PromiseUSAT : PromiseProblem (CNF ℕ) := ⟨USAT, UNSAT, disjoint_USAT_UNSAT⟩

@[simp] theorem yes_PromiseUSAT : PromiseUSAT.yes = USAT := rfl

@[simp] theorem no_PromiseUSAT : PromiseUSAT.no = UNSAT := rfl

/-- A function solves `PromiseUSAT` exactly when the set it accepts lies between `USAT` and
`SAT`. -/
theorem solvedBy_PromiseUSAT_iff {f : CNF ℕ → Bool} :
    PromiseUSAT.SolvedBy f ↔ USAT ⊆ {φ | f φ = true} ∧ {φ | f φ = true} ⊆ SAT := by
  simp only [SolvedBy, yes_PromiseUSAT, no_PromiseUSAT, mem_UNSAT, Bool.eq_false_iff]
  exact ⟨fun h => ⟨h.1, fun φ hφ => not_not.1 fun hn => h.2 φ hn hφ⟩,
    fun h => ⟨h.1, fun φ hφ hf => hφ (h.2 hf)⟩⟩

open Classical in
/-- Deciding `USAT` solves `PromiseUSAT`. -/
theorem solvedBy_USAT : PromiseUSAT.SolvedBy fun φ => decide (φ ∈ USAT) :=
  solvedBy_PromiseUSAT_iff.2 ⟨fun _ hφ => decide_eq_true hφ,
    fun _ hφ => USAT_subset_SAT (of_decide_eq_true hφ)⟩

open Classical in
/-- Deciding `SAT` also solves `PromiseUSAT`: its answers on formulas outside the promise are
irrelevant. -/
theorem solvedBy_SAT : PromiseUSAT.SolvedBy fun φ => decide (φ ∈ SAT) :=
  solvedBy_PromiseUSAT_iff.2 ⟨fun _ hφ => decide_eq_true (USAT_subset_SAT hφ),
    fun _ hφ => of_decide_eq_true hφ⟩

/-- **`PromiseUSAT` lies in `PromiseNP`**, separated by `SAT ∈ NP`. -/
theorem PromiseUSAT_mem_PromiseNP : PromiseUSAT ∈ PromiseNP encCNF :=
  ⟨SAT, SAT.mem_NP, USAT_subset_SAT, disjoint_compl_right⟩

end Cslib.Complexity
