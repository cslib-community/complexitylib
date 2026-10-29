/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Logics.Propositional.CNF.PolynomialTests
import Mathlib.Tactic.FinCases

/-! Tests for `𝔽₂` polynomial compilation of CNF clause-violation parity checks. -/

namespace ComplexityTests.CNFPolynomialTests

open Finset Cslib.BitString Cslib.Logic.PL

/-! ### Clause-falsification monomials: empty, tautological, and repeated-literal clauses -/

/-- A tautological clause containing `(0, true)` and `(0, false)` compiles to `∅`, even when
another variable is present. -/
def tautClause : Clause (Fin 2) := [(0, true), (1, true), (0, false)]

/-- Repeated literals in `(x₀ ∨ x₀ ∨ ¬x₁)` collapse to the two monomials `{1}` and `{0, 1}`
(`x₁ + x₀ x₁`), strictly below the uncollapsed `2 ^ 3 = 8` bound. -/
def dupClause : Clause (Fin 2) := [(0, true), (0, true), (1, false)]

example (σ : Fin 2 → Bool) :
    Clause.falsifyMonomials ([] : Clause (Fin 2)) = {∅} ∧
    tautClause.falsifyMonomials = ∅ ∧
    (∑ M ∈ tautClause.falsifyMonomials, monomial (ZMod 2) M σ = 0 ∧
      bitVal (ZMod 2) (!tautClause.eval σ) = 0) ∧
    dupClause.falsifyMonomials = {{1}, {0, 1}} ∧
    (#dupClause.falsifyMonomials = 2 ∧ #dupClause.falsifyMonomials < 2 ^ dupClause.length) ∧
    (∑ M ∈ dupClause.falsifyMonomials, monomial (ZMod 2) M ![false, true] = 1 ∧
      ∑ M ∈ dupClause.falsifyMonomials, monomial (ZMod 2) M ![true, true] = 0) := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide⟩
  have h0 : tautClause.falsifyMonomials = ∅ :=
    Clause.falsifyMonomials_eq_empty_of_tautology (v := 0) (by decide) (by decide)
  rw [← Clause.sum_falsifyMonomials, h0]
  simp

/-! ### Mod-`2` monomial cancellation across clauses in a parity row -/

/-- Two-clause 2-CNF `(x₀ ∨ ¬x₁) ∧ (¬x₁)` on three declared variables (`Fin 3`, with `x₂` unused):
clause `0` has falsification monomials `{{1}, {0, 1}}` and clause `1` has `{{1}}`. -/
def cancelFormula : CNF (Fin 3) :=
  [[(0, true), (1, false)], [(1, false)]]

/-- A test list with repeated clause index `((0, true), (1, true), (0, true))` cancels clause `0`
in `testRow`, leaving weight `1 ≤ 3` and monomial set `{{1}}`. -/
def cancelTestList : Fin 3 → Fin cancelFormula.length × Bool :=
  ![(⟨0, by decide⟩, true), (⟨1, by decide⟩, true), (⟨0, by decide⟩, true)]

example :
    cancelFormula.parityRowMonomials ![true, true] = {{0, 1}} ∧
    (cancelFormula.eval ![false, true, false] = false ∧
      (∀ e, cancelFormula.violations ![false, true, false] e = true) ∧
      ∑ M ∈ cancelFormula.parityRowMonomials ![true, true],
        monomial (ZMod 2) M ![false, true, false] = 0) ∧
    (cancelFormula.parityRowMonomials (![true, false] + ![false, true]) =
      symmDiff (cancelFormula.parityRowMonomials ![true, false])
        (cancelFormula.parityRowMonomials ![false, true]) ∧
      symmDiff (cancelFormula.parityRowMonomials ![true, false])
        (cancelFormula.parityRowMonomials ![false, true]) = {{0, 1}}) ∧
    (weight (testRow cancelTestList) = 1 ∧
      cancelFormula.parityRowMonomials (testRow cancelTestList) = {{1}}) :=
  ⟨by decide, by decide, ⟨CNF.parityRowMonomials_add _ _ _, by decide⟩, by decide⟩

/-! ### Exact `N(A) = #F + D(A)` decomposition and common-zero agreement with `modelCountOn` -/

/-- `cancelFormula` (`(x₀ ∨ ¬x₁) ∧ ¬x₁` on `Fin 3`, with `x₂` free) has `4` satisfying assignments
(`x₁ = false`, any `x₀, x₂`). Under `![true, true]`, `6` assignments pass (`4` satisfying plus `2`
nonsatisfying); adding `![false, true]` eliminates the remaining bad assignments. -/
example :
    (cancelFormula.modelCountOn Finset.univ = 4 ∧
      #{σ : Fin 3 → Bool |
          ∀ r ∈ ([![true, true]] : List (Fin cancelFormula.length → Bool)),
            ∑ M ∈ cancelFormula.parityRowMonomials r, monomial (ZMod 2) M σ = 0} = 6 ∧
      #{σ : Fin 3 → Bool |
          cancelFormula.eval σ = false ∧
            PassesTests cancelFormula.violations [![true, true]] σ} = 2) ∧
    (#{σ : Fin 3 → Bool |
        ∀ r ∈ ([![true, true], ![false, true]] : List (Fin cancelFormula.length → Bool)),
          ∑ M ∈ cancelFormula.parityRowMonomials r, monomial (ZMod 2) M σ = 0} =
      cancelFormula.modelCountOn Finset.univ ∧
      cancelFormula.modelCountOn Finset.univ = 4 ∧
      cancelFormula.modelCount = 2) := by
  decide

/-- Zero-variable (`Fin 0`) boundary: the empty formula has `modelCountOn Finset.univ = 1`, while
the contradictory formula `[[]]` has `0` satisfying assignments and `1` nonsatisfying assignment
accepted by `[]` (eliminated by `[![true]]`). -/
def emptyFin0 : CNF (Fin 0) := []

def unsatFin0 : CNF (Fin 0) := [[]]

example :
    emptyFin0.modelCountOn Finset.univ = 1 ∧
      unsatFin0.modelCountOn Finset.univ = 0 ∧
      #{σ : Fin 0 → Bool |
          ∀ r ∈ ([] : List (Fin unsatFin0.length → Bool)),
            ∑ M ∈ unsatFin0.parityRowMonomials r, monomial (ZMod 2) M σ = 0} =
        unsatFin0.modelCountOn Finset.univ +
          #{σ : Fin 0 → Bool |
              unsatFin0.eval σ = false ∧
                PassesTests unsatFin0.violations [] σ} ∧
      #{σ : Fin 0 → Bool |
          ∀ r ∈ ([![true]] : List (Fin unsatFin0.length → Bool)),
            ∑ M ∈ unsatFin0.parityRowMonomials r, monomial (ZMod 2) M σ = 0} = 0 := by
  decide

/-! ### End-to-end greedy run with `CNF.card_commonZeros_greedy` and `CNF.greedy_system_bounds` -/

/-- Concrete greedy run on `x₀` over `Fin 1`: `CNF.card_commonZeros_greedy` recovers
`unitFormula.modelCountOn Finset.univ = 1`, and `CNF.greedy_system_bounds` certifies `≤ 6`
equations of degree `≤ 1` and sparsity `≤ 2`. -/
def unitFormula : CNF (Fin 1) := [[(0, true)]]

def unitList : Fin 1 → Fin unitFormula.length × Bool := fun _ => (⟨0, by decide⟩, true)

def unitRows (i : ℕ) : List (Fin unitFormula.length → Bool) :=
  List.replicate i (testRow unitList)

theorem numPassing_unitRows (i : ℕ) :
    numPassing unitFormula.violations (unitRows i ++ [testRow unitList]) = 1 := by
  have hacc : ∀ σ : Fin 1 → Bool,
      PassesTests unitFormula.violations (unitRows i ++ [testRow unitList]) σ ↔
        testRow unitList ⬝ᵥ unitFormula.violations σ = false := by
    intro σ
    simp only [PassesTests, unitRows, List.mem_append, List.mem_replicate, List.mem_singleton]
    exact ⟨fun h => h _ (Or.inr rfl), fun h _ hr => hr.elim (fun ⟨_, h'⟩ => h' ▸ h) (· ▸ h)⟩
  simp only [numPassing, hacc]
  decide

example :
    #{σ : Fin 1 → Bool |
        ∀ r ∈ unitRows (3 * Fintype.card (Fin 1)),
          ∑ M ∈ unitFormula.parityRowMonomials r, monomial (ZMod 2) M σ = 0} =
      unitFormula.modelCountOn Finset.univ ∧
    unitFormula.modelCountOn Finset.univ = 1 ∧
    (((unitRows (3 * Fintype.card (Fin 1))).map unitFormula.parityRowMonomials).length ≤
      6 * Fintype.card (Fin 1) ∧
      ∀ eq ∈ (unitRows (3 * Fintype.card (Fin 1))).map unitFormula.parityRowMonomials,
        (∀ M ∈ eq, M ⊆ unitFormula.vars.toFinset ∧ #M ≤ 1) ∧ #eq ≤ max 0 1 * 2 ^ 1) := by
  refine ⟨CNF.card_commonZeros_greedy unitFormula (P := 1) (by decide) le_rfl unitRows
      (fun σ _ h => by
        have hσ : σ = ![false] := by
          funext i
          fin_cases i
          simpa [unitFormula, CNF.eval, Clause.eval, Literal.eval] using h
        subst hσ
        decide)
      (fun _ => unitList) (fun _ => List.replicate_succ' ..)
      (fun i _ => by
        rw [numPassing_unitRows, numPassing_eq]
        exact le_add_of_le_left (by decide)),
    by decide,
    CNF.greedy_system_bounds unitFormula (k := 1) (D₀ := 0) (P := 1) (by decide) unitRows
      (by decide) (by simp [unitRows]) (fun _ => unitList) (fun _ => List.replicate_succ' ..)
      le_rfl⟩

end ComplexityTests.CNFPolynomialTests
