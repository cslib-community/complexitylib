/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.NNF.Negation.Separation

/-!
# d-DNNF negation clients

Small explicit instances for the d-DNNF negation development:

* a three-node d-DNNF for `x₀ ∧ ¬x₁` that is decomposable and deterministic, a non-decomposable
  conjunction and a non-deterministic disjunction, and the balanced-rectangle cover of
  Theorem 3.1 for the first;
* a parity read-once program and its d-DNNF in a non-standard variable order;
* `K₄` with the proper `3`-edge-colouring by its three perfect matchings: values of `f_G`, its
  balanced-cut expansion with `γ = 1`, and the separation theorem instantiated on it, so that the
  expander hypothesis of `CubicEdgeColoring.ddnnf_negation_separation` is satisfiable.
-/

namespace CslibFrontierTests.DDNNFNegation

open Cslib Cslib.Circuits Cslib.Communication.MultiPartition

/-! ### Small NNFs -/

/-- `x₀ ∧ ¬x₁`: two literals and a conjunction. -/
def andNot : NNF (Fin 2) (Fin 3) where
  gate := ![.lit 0 true, .lit 1 false, .and 0 1]
  rank := ![0, 0, 1]
  and_lt v l r h := by fin_cases v <;> cases h; decide
  or_lt v l r h := by fin_cases v <;> cases h
  root := 2

example : andNot.toFun ![true, false] = true := by decide
example : andNot.toFun ![true, true] = false := by decide
example : andNot.toFun ![false, false] = false := by decide
example : andNot.IsDecomposable := by unfold NNF.IsDecomposable; decide
example : andNot.IsDeterministic := by unfold NNF.IsDeterministic; decide
example : andNot.size = 3 := rfl

/-- `x₀ ∧ x₀` is not decomposable. -/
def andSelf : NNF (Fin 2) (Fin 2) where
  gate := ![.lit 0 true, .and 0 0]
  rank := ![0, 1]
  and_lt v l r h := by fin_cases v <;> cases h; decide
  or_lt v l r h := by fin_cases v <;> cases h
  root := 1

example : ¬andSelf.IsDecomposable := by unfold NNF.IsDecomposable; decide

/-- `x₀ ∨ x₀` is not deterministic. -/
def orSelf : NNF (Fin 2) (Fin 2) where
  gate := ![.lit 0 true, .or 0 0]
  rank := ![0, 1]
  and_lt v l r h := by fin_cases v <;> cases h
  or_lt v l r h := by fin_cases v <;> cases h; decide
  root := 1

example : ¬orSelf.IsDeterministic := by unfold NNF.IsDeterministic; decide

/-- `{0}` is balanced among three variables. -/
example : IsBalanced ({0} : Finset (Fin 3)) := by unfold IsBalanced; decide

/-- Theorem 3.1 on a three-variable d-DNNF: a cover by at most three balanced rectangles. -/
def andNot3 : NNF (Fin 3) (Fin 3) where
  gate := ![.lit 0 true, .lit 1 false, .and 0 1]
  rank := ![0, 0, 1]
  and_lt v l r h := by fin_cases v <;> cases h; decide
  or_lt v l r h := by fin_cases v <;> cases h
  root := 2

example : coverNumberFun true andNot3.toFun ≤ 3 :=
  NNF.coverNumberFun_le_size (by unfold NNF.IsDecomposable; decide) (by decide)

/-! ### A read-once program as a d-DNNF -/

/-- Parity of three bits as a read-once branching program. -/
def parity3 : BranchingPrograms.ReadOnceProgram 3 Bool Bool where
  start := false
  step _ q b := q ^^ b
  accept q := q

/-- Read in reverse order. -/
example : (parity3.toNNF Fin.rev).toFun ![true, false, false] = true := by
  rw [BranchingPrograms.ReadOnceProgram.toFun_toNNF]; decide
example : (parity3.toNNF Fin.rev).toFun ![true, true, false] = false := by
  rw [BranchingPrograms.ReadOnceProgram.toFun_toNNF]; decide
example : (parity3.toNNF Fin.rev).IsDecomposable :=
  parity3.isDecomposable_toNNF _ Fin.rev_injective
example : (parity3.toNNF Fin.rev).IsDeterministic := parity3.isDeterministic_toNNF _
example : (parity3.toNNF Fin.rev).size = 4 * 2 + 6 + 6 * 2 := by
  simp [NNF.size]

/-! ### `K₄` -/

/-- `K₄` on `Fin 4`, coloured by its three perfect matchings: colour `c` joins `v` and
`v xor (c + 1)`. -/
def k4 : CubicEdgeColoring (Fin 4) where
  mate c v := ![![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] c v
  mate_mate := by decide
  mate_ne := by decide
  mate_injective v := by fin_cases v <;> decide

/-- An edge of a single colour: `f_G` is true. -/
example : k4.someButNotAllColors ![true, true, false, false] = true := by decide
/-- All three colours: `f_G` is false. -/
example : k4.someButNotAllColors ![true, true, true, true] = false := by decide
/-- An independent set: `f_G` is false. -/
example : k4.someButNotAllColors ![true, false, false, false] = false := by decide
/-- All three colours, around a triangle. -/
example : k4.someButNotAllColors ![true, true, true, false] = false := by decide

example : k4.toSimpleGraph.IsRegularOfDegree 3 := k4.isRegularOfDegree

/-- `K₄` is a balanced-cut `1`-edge expander: a balanced cut has two vertices on each side and
four crossing edges. -/
theorem k4_isBalancedCutExpander : IsBalancedCutExpander k4.toSimpleGraph 1 := by
  intro A h1 h2
  have : 4 ≤ (k4.toSimpleGraph.interedges A Aᶜ).card := by
    rw [k4.card_interedges]
    simp only [Fintype.card_fin] at h1 h2
    revert h1 h2
    revert A
    decide
  simp only [Fintype.card_fin, one_mul]
  exact_mod_cast this

/-- Theorem 1.1's two bounds, instantiated on `K₄`: a d-DNNF for `f_{K₄}` with at most `650`
nodes, and at least `(48/47)^(4/126)` nodes for every DNNF computing its negation. -/
example := k4.ddnnf_negation_separation k4_isBalancedCutExpander (by decide)

/-- The d-DNNF of Proposition 5.1 for `K₄`. -/
example (x : Fin 4 → Bool) : k4.dDNNF.toFun x = k4.someButNotAllColors x := k4.toFun_dDNNF x
example : k4.dDNNF.size ≤ 650 := k4.size_dDNNF

end CslibFrontierTests.DDNNFNegation
