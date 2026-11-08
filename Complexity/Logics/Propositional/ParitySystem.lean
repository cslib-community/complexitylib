/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.BitString.Parity
public import Mathlib.Order.SymmDiff

/-!
# Parity systems and bounded-width derivations

A *parity system* `P : ParitySystem σ` is a finite list of equations `⊕_{i ∈ S} xᵢ = b` over
`𝔽₂`, each given by its set `S` of variables and its right-hand side `b`. An assignment
`a : σ → Bool` satisfies `P` (`ParitySystem.Holds`) when `parityOn S a = b` for every equation.
Variables are sets rather than lists, unlike `Cslib.Logic.PL.AffineEquation`: the algebraic
encodings over `±1` variables (`Cslib.Logic.PL.ParitySystem.toPolys`) are multilinear in the
variables of an equation.

Summing two equations gives the equation of the symmetric difference of their sets and the
exclusive or of their right-hand sides. **Width-`w` derivations** (`ParitySystem.Derives P w`)
start from `0 = 0` and the equations of `P` with at most `w` variables, and close under this rule
as long as the result has at most `w` variables. This is width-`w` resolution on XOR formulas,
[Schoenebeck, Definition 10][Schoenebeck2008], except that the equations of `P` used must also have
width at most `w`; restricting the axioms derives fewer equations, so the hypothesis "width-`w`
derivations do not reach `0 = 1`" is weaker here than in the source. Every derived equation holds
under every satisfying assignment (`ParitySystem.Holds.parityOn_eq_of_derives`), so a system from
which `0 = 1` is derivable is unsatisfiable. Tseitin parity systems are in
`Complexity.Logics.Propositional.ParitySystem.Tseitin`.

## Main definitions

* `Cslib.Logic.PL.ParitySystem`: systems of parity equations.
* `Cslib.Logic.PL.ParitySystem.Holds`: satisfaction by an assignment.
* `Cslib.Logic.PL.ParitySystem.Derives`: width-`w` derivations.

## Main results

* `Cslib.Logic.PL.ParitySystem.Holds.parityOn_eq_of_derives`: soundness of derivations.
* `Cslib.Logic.PL.ParitySystem.not_holds_of_derives_empty_true`: a system from which `0 = 1` is
  derivable is unsatisfiable.

## References

* [G. Schoenebeck, *Linear level Lasserre lower bounds for certain k-CSPs*][Schoenebeck2008]
-/

public section

namespace Cslib.Logic.PL

open Finset
open scoped symmDiff

/-- A **parity system**: a list of equations `⊕_{i ∈ S} xᵢ = b` over `𝔽₂`, each given by the set
`S` of its variables and its right-hand side `b`. -/
abbrev ParitySystem (σ : Type*) := List (Finset σ × Bool)

namespace ParitySystem

variable {σ : Type*}

/-- The assignment `a` satisfies every equation of `P`: the parity of `a` on the variables of an
equation is its right-hand side. -/
@[expose] def Holds (P : ParitySystem σ) (a : σ → Bool) : Prop :=
  ∀ e ∈ P, parityOn e.1 a = e.2

variable [DecidableEq σ]

/-- **Width-`w` derivations** from a parity system `P`: `Derives P w S b` says that the equation
`⊕_{i ∈ S} xᵢ = b` is obtained from `0 = 0` and the equations of `P` with at most `w` variables by
summing two derived equations, every derived equation having at most `w` variables. Deriving
`0 = 1` is `Derives P w ∅ true`. -/
inductive Derives (P : ParitySystem σ) (w : ℕ) : Finset σ → Bool → Prop
  /-- The trivial equation `0 = 0`. -/
  | empty : Derives P w ∅ false
  /-- An equation of `P` with at most `w` variables. -/
  | mem {S : Finset σ} {b : Bool} : (S, b) ∈ P → #S ≤ w → Derives P w S b
  /-- The sum of two derived equations, if it has at most `w` variables. -/
  | symmDiff {S T : Finset σ} {b c : Bool} : Derives P w S b → Derives P w T c →
      #(S ∆ T) ≤ w → Derives P w (S ∆ T) (b ^^ c)

variable {P : ParitySystem σ} {w : ℕ}

/-- A derived equation has at most `w` variables. -/
theorem Derives.card_le {S : Finset σ} {b : Bool} (h : P.Derives w S b) : #S ≤ w := by
  cases h with
  | empty => simp
  | mem _ h => exact h
  | symmDiff _ _ h => exact h

/-- Width-`w` derivations are width-`w'` derivations for `w ≤ w'`. -/
theorem Derives.mono {S : Finset σ} {b : Bool} (h : P.Derives w S b) {w' : ℕ} (hw : w ≤ w') :
    P.Derives w' S b := by
  induction h with
  | empty => exact .empty
  | mem hS hc => exact .mem hS (hc.trans hw)
  | symmDiff _ _ hc ih₁ ih₂ => exact .symmDiff ih₁ ih₂ (hc.trans hw)

/-- **Soundness of derivations**: every derived equation holds under every assignment satisfying
the system. -/
theorem Holds.parityOn_eq_of_derives {a : σ → Bool} (ha : P.Holds a) {S : Finset σ} {b : Bool}
    (h : P.Derives w S b) : parityOn S a = b := by
  induction h with
  | empty => exact parityOn_empty a
  | mem hS _ => exact ha _ hS
  | symmDiff _ _ _ ih₁ ih₂ => rw [parityOn_symmDiff, ih₁, ih₂]

/-- A system from which `0 = 1` is derivable is unsatisfiable. -/
theorem not_holds_of_derives_empty_true (h : P.Derives w ∅ true) (a : σ → Bool) :
    ¬ P.Holds a := fun ha => by
  have := ha.parityOn_eq_of_derives h
  rw [parityOn_empty] at this
  exact Bool.false_ne_true this

end ParitySystem

end Cslib.Logic.PL
