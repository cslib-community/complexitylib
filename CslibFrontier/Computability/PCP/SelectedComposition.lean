/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Composition
public import CslibFrontier.Computability.PCP.AssignmentTester.Selection

/-!
# Composition with the six-query assignment tester

The selected Hadamard tester is a second instance of the generic binary-constraint composition
interface. Its rejection coefficient is `1/140`; six queries give a composition loss of `840`.
The composed alphabet has `128` symbols, compared with `2^18` for the conjunction tester.

These are local composition parameters. They do not assert a six-query bound for the final
binary-proof verifier, which additionally encodes labels and repeats its test.

## Main definitions

* `Cslib.PCP.SelectedAlphabet`: the `128`-symbol answer alphabet `Bool × (Fin 6 → Bool)`.
* `Cslib.PCP.HadamardTester.selectedAssignmentTester`: the six-query composition contract.
* `Cslib.PCP.ConstraintGraph.composeSelected`: composition using that contract.

## Main results

* `Cslib.PCP.ConstraintGraph.le_unsatVal_composeSelected`: the value decreases by at most `840`.
* `Cslib.PCP.ConstraintGraph.satisfiable_composeSelected_iff`: satisfiability is preserved.
* `Cslib.PCP.ConstraintGraph.card_alphabet_composeSelected`: the output alphabet has size `128`.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP

/-- The fixed `128`-symbol answer alphabet `Bool × (Fin 6 → Bool)` of composition with the
selected six-query Hadamard assignment tester: one proof bit and six claimed query answers. -/
abbrev SelectedAlphabet : Type :=
  Bool × (Fin 6 → Bool)

namespace HadamardTester

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Use the same label encoding and honest auxiliary tables, selecting just one check. -/
noncomputable def selectedAssignmentTester :
    AssignmentTester α (α → Bool) (LinPos α ⊕ QuadPos α) (Fin 5 × Rand α) (Fin 6) Bool where
  test := selectedHadamardTester
  encode := BitString.longCode
  auxiliary _ σ p := honestProof σ (.inr p)

/-- Every selected check accepts an honest proof of a satisfied constraint. -/
theorem isComplete_selectedAssignmentTester :
    (selectedAssignmentTester (α := α)).IsComplete :=
  fun hσ ω ↦ passes_selected_honestProof hσ ω

/-- The selected tester rejects every violated decoded constraint with probability at least
`1/140`. The decoder is identical to the conjunction tester's decoder. -/
theorem sound_selectedAssignmentTester [Nonempty α] :
    (selectedAssignmentTester (α := α)).Sound ConstraintGraph.decodeLabel (1 / 140) := by
  intro C π h
  have hs := sound_assignmentTester C π h
  have hc := one_sub_acceptProb_le_five_mul_selected (C := C) π
  change (1 / 28 : ℝ) ≤ 1 - (hadamardTester C).acceptProb π at hs
  change (1 / 140 : ℝ) ≤ 1 - (selectedHadamardTester C).acceptProb π
  linarith

end HadamardTester

namespace ConstraintGraph

open HadamardTester

variable {V E α : Type*} [Fintype α] [DecidableEq α] (G : ConstraintGraph V E α)

/-- Compose with one randomly selected Hadamard check per local test. -/
noncomputable def composeSelected :
    ConstraintGraph (ComposePos V E α ⊕ E × (Fin 5 × Rand α))
      ((E × (Fin 5 × Rand α)) × Fin 6) SelectedAlphabet :=
  selectedAssignmentTester.compose G

/-- Quantitative perfect completeness of selected composition. -/
theorem unsatVal_composeSelected_le [Fintype E] [Nonempty α] :
    G.composeSelected.unsatVal ≤ G.unsatVal :=
  AssignmentTester.unsatVal_compose_le isComplete_selectedAssignmentTester G

/-- Six queries and rejection `1/140` give composition loss `840`. -/
theorem le_unsatVal_composeSelected [Fintype E] [Nonempty α] :
    G.unsatVal / 840 ≤ G.composeSelected.unsatVal := by
  have h := AssignmentTester.le_unsatVal_compose sound_selectedAssignmentTester (by norm_num) G
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at h
  exact h

/-- Selected composition preserves satisfiability. -/
theorem satisfiable_composeSelected_iff [Finite E] [Nonempty α] :
    G.composeSelected.Satisfiable ↔ G.Satisfiable :=
  AssignmentTester.satisfiable_compose_iff isComplete_selectedAssignmentTester
    sound_selectedAssignmentTester (by norm_num) G

/-- The selected composition alphabet stores one symbol and six claimed answers. -/
theorem card_alphabet_composeSelected : Fintype.card SelectedAlphabet = 128 := by
  norm_num

/-- The auxiliary tables are shared across the five checks; only the coin vertices are repeated. -/
theorem card_vertices_composeSelected [Fintype V] [Fintype E] :
    Fintype.card (ComposePos V E α ⊕ E × (Fin 5 × Rand α)) =
      2 ^ Fintype.card α * Fintype.card V +
        (2 ^ (2 * Fintype.card α) + 2 ^ (4 * Fintype.card α ^ 2) +
          5 * 2 ^ (20 * Fintype.card α ^ 2 + 15 * Fintype.card α + 3)) * Fintype.card E := by
  rw [Fintype.card_sum, Fintype.card_prod E, Fintype.card_prod (Fin 5), card_rand]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  ring

/-- Each original edge contributes five choices of check, the original coins, and six queries. -/
theorem card_edges_composeSelected [Fintype E] :
    Fintype.card ((E × (Fin 5 × Rand α)) × Fin 6) =
      30 * 2 ^ (20 * Fintype.card α ^ 2 + 15 * Fintype.card α + 3) * Fintype.card E := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, card_rand]
  simp only [Fintype.card_fin]
  ring

end ConstraintGraph

end Cslib.PCP
