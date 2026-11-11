/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CMMSA
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size

/-!
# Sizes of CMMSA instances

A reduction from `GapCMMSA` bounds its output, and its random bits, by the size of its input.
Since `CMMSAInstance.encoding` writes the weights and the threshold in unary, the number of
formulas, the number of variables, every weight and the threshold are each at most the length `N`
of the encoding of the instance.

The gap problem `GapCMMSA Δ g σ` only gets larger as the bound `Δ` on the literals of each formula
increases: its yes- and no-instances for `Δ` are yes- and no-instances for every `Δ' ≥ Δ`
(`GapCMMSA.yes_mono`, `GapCMMSA.no_mono`), since well-formedness is monotone
(`CMMSAInstance.WellFormed.mono`). With `PromiseProblem.NPHard.mono`, NP-hardness for `Δ` passes
to every larger bound.

## Main results

* `Cslib.Complexity.CMMSAInstance.length_formulas_le`,
  `Cslib.Complexity.CMMSAInstance.length_weights_le`,
  `Cslib.Complexity.CMMSAInstance.le_of_mem_weights`,
  `Cslib.Complexity.CMMSAInstance.threshold_le`: the parts of an instance are no larger than its
  encoding.
* `Cslib.Complexity.GapCMMSA.yes_mono`, `Cslib.Complexity.GapCMMSA.no_mono`: monotonicity of the
  gap problem in the bound `Δ`.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

namespace CMMSAInstance

variable (I : CMMSAInstance)

/-- An instance has at most as many formulas as its encoding has bits. -/
theorem length_formulas_le : I.formulas.length ≤ (encoding I).length :=
  (SizedListEncoding.length_le (encA := encDNFOver encNat) I.formulas).trans <|
    (length_le_encPair_right encUnary (encList (encDNFOver encNat)) (I.threshold, I.formulas)).trans
      (length_le_encPair_right (encList encUnary) _ (I.weights, I.threshold, I.formulas))

/-- An instance has at most as many variables as its encoding has bits. -/
theorem length_weights_le : I.weights.length ≤ (encoding I).length :=
  (SizedListEncoding.length_le (encA := encUnary) I.weights).trans
    (length_le_encPair_left (encList encUnary) _ (I.weights, I.threshold, I.formulas))

/-- Every weight, written in unary, is at most the length of the encoding. -/
theorem le_of_mem_weights {w : ℕ} (hw : w ∈ I.weights) : w ≤ (encoding I).length := by
  have h : (encUnary w).length ≤ (encoding I).length :=
    (SizedListEncoding.length_elem_le (encL := encList encUnary) I.weights w hw).trans
      (length_le_encPair_left (encList encUnary) (encPair encUnary (encList (encDNFOver encNat)))
        (I.weights, I.threshold, I.formulas))
  simpa using h

/-- The threshold, written in unary, is at most the length of the encoding. -/
theorem threshold_le : I.threshold ≤ (encoding I).length := by
  have h : (encUnary I.threshold).length ≤ (encoding I).length :=
    (length_le_encPair_left encUnary (encList (encDNFOver encNat)) (I.threshold, I.formulas)).trans
      (length_le_encPair_right (encList encUnary) _ (I.weights, I.threshold, I.formulas))
  simpa using h

end CMMSAInstance

namespace GapCMMSA

variable {Δ Δ' : ℕ} {g σ : ℝ}

/-- A yes-instance for the bound `Δ` is a yes-instance for every larger bound. -/
theorem yes_mono (hΔ : Δ ≤ Δ') : (GapCMMSA Δ g σ).yes ⊆ (GapCMMSA Δ' g σ).yes := fun _ hI => by
  rw [mem_yes_GapCMMSA] at hI ⊢
  exact ⟨hI.1.mono hΔ, hI.2⟩

/-- A no-instance for the bound `Δ` is a no-instance for every larger bound. -/
theorem no_mono (hΔ : Δ ≤ Δ') : (GapCMMSA Δ g σ).no ⊆ (GapCMMSA Δ' g σ).no := fun _ hI => by
  rw [mem_no_GapCMMSA] at hI ⊢
  exact ⟨hI.1.mono hΔ, hI.2⟩

end GapCMMSA

end Cslib.Complexity
