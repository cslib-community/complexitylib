/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Tseitin
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
which `0 = 1` is derivable is unsatisfiable.

The **Tseitin parity system** `ParitySystem.tseitin ends χ` of a multigraph `ends : E → Sym2 V`
with charges `χ` has a variable for each edge and, for each vertex `v`, the equation saying that
the parity of the edges at `v` other than self-loops is `χ v`. It is satisfied by the same
assignments as the Tseitin formula `CNF.tseitinFormula ends χ`
(`ParitySystem.holds_tseitin_iff_eval_tseitinFormula`), so it is unsatisfiable when the total
charge is odd (`ParitySystem.not_holds_tseitin`), and on a connected multigraph satisfiable
exactly when the total charge is even (`ParitySystem.exists_holds_tseitin_iff`).

## Main definitions

* `Cslib.Logic.PL.ParitySystem`: systems of parity equations.
* `Cslib.Logic.PL.ParitySystem.Holds`: satisfaction by an assignment.
* `Cslib.Logic.PL.ParitySystem.Derives`: width-`w` derivations.
* `Cslib.Logic.PL.ParitySystem.tseitin`: the Tseitin parity system of a multigraph with charges.

## Main results

* `Cslib.Logic.PL.ParitySystem.Holds.parityOn_eq_of_derives`: soundness of derivations.
* `Cslib.Logic.PL.ParitySystem.holds_tseitin_iff`,
  `Cslib.Logic.PL.ParitySystem.holds_tseitin_iff_eval_tseitinFormula`: the semantics of Tseitin
  parity systems.
* `Cslib.Logic.PL.ParitySystem.not_holds_tseitin`,
  `Cslib.Logic.PL.ParitySystem.exists_holds_tseitin_iff`: satisfiability by total charge.

## References

* [G. Schoenebeck, *Linear level Lasserre lower bounds for certain k-CSPs*][Schoenebeck2008]
* [G. S. Tseitin, *On the complexity of derivation in propositional calculus*][Tseitin1983]
* [A. Urquhart, *Hard examples for resolution*][Urquhart1987]
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

/-! ### Tseitin parity systems -/

section Tseitin

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

/-- The **Tseitin parity system** of the multigraph `ends` with charges `χ`: a variable for each
edge, and for each vertex `v` the equation saying that the parity of the edges at `v` other than
self-loops is `χ v`. -/
noncomputable def tseitin (ends : E → Sym2 V) (χ : V → Bool) : ParitySystem E :=
  univ.toList.map fun v => (Multigraph.incidence ends v, χ v)

variable {ends : E → Sym2 V} {χ : V → Bool}

/-- The equations of the Tseitin parity system are those of the vertices. -/
theorem mem_tseitin {e : Finset E × Bool} :
    e ∈ tseitin ends χ ↔ ∃ v, (Multigraph.incidence ends v, χ v) = e := by
  simp [tseitin]

/-- The Tseitin parity system has an equation for each vertex. -/
@[simp] theorem length_tseitin : (tseitin ends χ).length = Fintype.card V := by
  simp [tseitin]

/-- The equation of the vertex `v` belongs to the Tseitin parity system. -/
theorem incidence_mem_tseitin (v : V) : (Multigraph.incidence ends v, χ v) ∈ tseitin ends χ :=
  mem_tseitin.2 ⟨v, rfl⟩

/-- An assignment satisfies the Tseitin parity system when its parity at every vertex is the
charge. -/
theorem holds_tseitin_iff (a : E → Bool) :
    (tseitin ends χ).Holds a ↔ ∀ v, parityOn (Multigraph.incidence ends v) a = χ v := by
  simp [Holds, mem_tseitin]

/-- The Tseitin parity system and the Tseitin formula have the same satisfying assignments. -/
theorem holds_tseitin_iff_eval_tseitinFormula [DecidableEq E] (a : E → Bool) :
    (tseitin ends χ).Holds a ↔ (CNF.tseitinFormula ends χ).eval a = true := by
  rw [holds_tseitin_iff, CNF.eval_tseitinFormula_eq_true_iff]

/-- **Tseitin parity systems with odd total charge are unsatisfiable.** -/
theorem not_holds_tseitin (h : parityOn univ χ = true) (a : E → Bool) :
    ¬ (tseitin ends χ).Holds a := fun ha => by
  rw [Tseitin.parityOn_univ_eq_false_of_forall ((holds_tseitin_iff a).1 ha)] at h
  exact Bool.false_ne_true h

/-- On a connected multigraph, **the Tseitin parity system is satisfiable exactly when the total
charge is even**. -/
theorem exists_holds_tseitin_iff (hG : (Multigraph.toSimpleGraph ends).Connected) :
    (∃ a, (tseitin ends χ).Holds a) ↔ parityOn univ χ = false := by
  classical
  simp only [holds_tseitin_iff_eval_tseitinFormula]
  exact CNF.satisfiable_tseitinFormula_iff hG

end Tseitin

end ParitySystem

end Cslib.Logic.PL
