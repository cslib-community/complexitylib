/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.Activity
public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.TranscriptTree
public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Data.Matrix.Mul
import CslibFrontier.Computability.DecisionTree.InnerProduct

/-!
# Threshold gate activity for inner product and rectangle-free functions

For any coordinate split `Fin n ≃ L ⊕ R` and nonempty subsets `A ⊆ (L → Bool)` and
`B ⊆ (R → Bool)`, if every monochromatic subrectangle `A' × B'` of a gate readout has area at most
`M`, then `|A| |B| ≤ M A^2`, where `A` is the number of attainable input-reading transcripts
(Corollary 3.3). Bounding `A` by a Hamming ball around zero or any fixed baseline pattern `v` gives
general size-activity bounds for both input-reading gates and all gates.

Specializing to inner product modulo two gives `2 ^ m ≤ A ^ 2` and the exact size-activity
inequality `2 ^ m ≤ (∑ j ≤ e, q.choose j) ^ 2` around zero or any fixed baseline `v`. Here `q` and
`e` may count only input-reading gates and their maximum activity, or all gates and their maximum
activity. The statements include zero-dimensional inputs and arbitrary real weights.

The circuit specializations require the designated output to be a gate.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.card_mul_le_mul_card_attainableTranscripts_sq`:
  the general rectangle-density pattern bound (Corollary 3.3).
* `Cslib.Circuits.Boolean.WeightedThreshold.card_mul_le_mul_sum_choose_sq`,
  `Cslib.Circuits.Boolean.WeightedThreshold.card_mul_le_mul_sum_choose_inputActivityFrom_sq`,
  `Cslib.Circuits.Boolean.WeightedThreshold.card_mul_le_mul_sum_choose_gateActivity_sq`,
  `Cslib.Circuits.Boolean.WeightedThreshold.card_mul_le_mul_sum_choose_gateActivityFrom_sq`:
  general rectangle-density size-activity bounds around zero or a fixed baseline.
* `two_pow_le_card_attainableTranscripts_sq_of_dotProduct`: the attained-pattern lower bound.
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_sum_choose_sq_of_dotProduct`,
  `two_pow_le_sum_choose_inputActivityFrom_sq_of_dotProduct`:
  the exact binomial-sum size-activity inequalities on input-reading gates.
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_sum_choose_sq_of_circuit_dotProduct`:
  the same bound for a native single-output circuit.
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_sum_choose_gateActivity_sq_of_dotProduct`,
  `two_pow_le_sum_choose_gateActivityFrom_sq_of_dotProduct`:
  the exact bounds using total gate count and total activity.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Theorem 3.2, Corollary 3.3,
  and Section 3.1] [ThresholdCircuitRepresentations2026]
-/

public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset BitString

variable {n g : ℕ} {L R β ι : Type*} [Fintype ι]

/-- **General rectangle-density pattern bound** (Corollary 3.3): if every monochromatic
subrectangle of `A × B` under a fixed gate readout has area at most `M`, then
`|A| |B| ≤ M A^2`, where `A` is the number of attainable input-reading transcripts. -/
theorem card_mul_le_mul_card_attainableTranscripts_sq
    (p : Program signature n g) (split : Fin n ≃ L ⊕ R)
    (A : Finset (L → Bool)) (B : Finset (R → Bool)) (hA : A.Nonempty) (hB : B.Nonempty)
    (readout : (Fin g → Bool) → β) {M : ℕ}
    (hM : ∀ (A' : Finset (L → Bool)), A' ⊆ A → ∀ (B' : Finset (R → Bool)), B' ⊆ B → ∀ z,
      (∀ x ∈ A', ∀ y ∈ B',
        readout (p.eval interpretation (inputOfSplit split x y)) = z) →
      A'.card * B'.card ≤ M) :
    A.card * B.card ≤ M * (attainableTranscripts p).card ^ 2 := by
  obtain ⟨t, ht, _, hl⟩ := exists_gate_readout_tree p split readout
  have htree := t.card_mul_le_mul_leafCount_sq A B hA hB (R := M) fun A' hA' B' hB' z hz =>
    hM A' hA' B' hB' z fun x hx y hy => (ht x y).symm.trans (hz x hx y hy)
  exact htree.trans (Nat.mul_le_mul_left M (Nat.pow_le_pow_left hl 2))

/-- **General rectangle-density activity bound** (Corollary 3.3) on input-reading gates. -/
theorem card_mul_le_mul_sum_choose_sq
    (p : Program signature n g) (split : Fin n ≃ L ⊕ R)
    (A : Finset (L → Bool)) (B : Finset (R → Bool)) (hA : A.Nonempty) (hB : B.Nonempty)
    (readout : (Fin g → Bool) → β) {M : ℕ}
    (hM : ∀ (A' : Finset (L → Bool)), A' ⊆ A → ∀ (B' : Finset (R → Bool)), B' ⊆ B → ∀ z,
      (∀ x ∈ A', ∀ y ∈ B',
        readout (p.eval interpretation (inputOfSplit split x y)) = z) →
      A'.card * B'.card ≤ M) :
    A.card * B.card ≤
      M * (∑ j ∈ range (inputActivity p + 1), (inputGates p).card.choose j) ^ 2 :=
  (card_mul_le_mul_card_attainableTranscripts_sq p split A B hA hB readout hM).trans
    (Nat.mul_le_mul_left M (Nat.pow_le_pow_left (card_attainableTranscripts_le_sum_choose p) 2))

/-- **General rectangle-density activity bound** on input-reading gates relative to any fixed
baseline `v`. -/
theorem card_mul_le_mul_sum_choose_inputActivityFrom_sq
    (p : Program signature n g) (split : Fin n ≃ L ⊕ R)
    (v : inputGates p → Bool)
    (A : Finset (L → Bool)) (B : Finset (R → Bool)) (hA : A.Nonempty) (hB : B.Nonempty)
    (readout : (Fin g → Bool) → β) {M : ℕ}
    (hM : ∀ (A' : Finset (L → Bool)), A' ⊆ A → ∀ (B' : Finset (R → Bool)), B' ⊆ B → ∀ z,
      (∀ x ∈ A', ∀ y ∈ B',
        readout (p.eval interpretation (inputOfSplit split x y)) = z) →
      A'.card * B'.card ≤ M) :
    A.card * B.card ≤
      M * (∑ j ∈ range (inputActivityFrom p v + 1), (inputGates p).card.choose j) ^ 2 :=
  (card_mul_le_mul_card_attainableTranscripts_sq p split A B hA hB readout hM).trans
    (Nat.mul_le_mul_left M
      (Nat.pow_le_pow_left (card_attainableTranscripts_le_sum_choose_inputActivityFrom p v) 2))

/-- **General rectangle-density activity bound** (Corollary 3.3) across all gates. -/
theorem card_mul_le_mul_sum_choose_gateActivity_sq
    (p : Program signature n g) (split : Fin n ≃ L ⊕ R)
    (A : Finset (L → Bool)) (B : Finset (R → Bool)) (hA : A.Nonempty) (hB : B.Nonempty)
    (readout : (Fin g → Bool) → β) {M : ℕ}
    (hM : ∀ (A' : Finset (L → Bool)), A' ⊆ A → ∀ (B' : Finset (R → Bool)), B' ⊆ B → ∀ z,
      (∀ x ∈ A', ∀ y ∈ B',
        readout (p.eval interpretation (inputOfSplit split x y)) = z) →
      A'.card * B'.card ≤ M) :
    A.card * B.card ≤ M * (∑ j ∈ range (gateActivity p + 1), g.choose j) ^ 2 :=
  (card_mul_le_mul_card_attainableTranscripts_sq p split A B hA hB readout hM).trans
    (Nat.mul_le_mul_left M
      (Nat.pow_le_pow_left (card_attainableTranscripts_le_sum_choose_gateActivity p) 2))

/-- **General rectangle-density activity bound** across all gates relative to any fixed baseline
`v`. -/
theorem card_mul_le_mul_sum_choose_gateActivityFrom_sq
    (p : Program signature n g) (split : Fin n ≃ L ⊕ R)
    (v : Fin g → Bool)
    (A : Finset (L → Bool)) (B : Finset (R → Bool)) (hA : A.Nonempty) (hB : B.Nonempty)
    (readout : (Fin g → Bool) → β) {M : ℕ}
    (hM : ∀ (A' : Finset (L → Bool)), A' ⊆ A → ∀ (B' : Finset (R → Bool)), B' ⊆ B → ∀ z,
      (∀ x ∈ A', ∀ y ∈ B',
        readout (p.eval interpretation (inputOfSplit split x y)) = z) →
      A'.card * B'.card ≤ M) :
    A.card * B.card ≤ M * (∑ j ∈ range (gateActivityFrom p v + 1), g.choose j) ^ 2 :=
  (card_mul_le_mul_card_attainableTranscripts_sq p split A B hA hB readout hM).trans
    (Nat.mul_le_mul_left M
      (Nat.pow_le_pow_left (card_attainableTranscripts_le_sum_choose_gateActivityFrom p v) 2))

/-- The square of the number of attainable input-reading transcripts is at least the size of
one side's Boolean cube whenever a fixed gate readout computes inner product. -/
theorem two_pow_le_card_attainableTranscripts_sq_of_dotProduct
    (p : Program signature n g) (split : Fin n ≃ ι ⊕ ι)
    (readout : (Fin g → Bool) → Bool)
    (h : ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤ (attainableTranscripts p).card ^ 2 := by
  obtain ⟨t, ht, _, hl⟩ := exists_gate_readout_tree p split readout
  exact (t.two_pow_le_leafCount_sq_of_dotProduct fun x y => (ht x y).trans (h x y)).trans
    (Nat.pow_le_pow_left hl 2)

/-- Inner product forces the exact binomial sum at the program's input-reading activity to
have square at least `2 ^ m`, where `m` is the number of coordinates on either side. -/
theorem two_pow_le_sum_choose_sq_of_dotProduct
    (p : Program signature n g) (split : Fin n ≃ ι ⊕ ι)
    (readout : (Fin g → Bool) → Bool)
    (h : ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤
      (∑ j ∈ range (inputActivity p + 1), (inputGates p).card.choose j) ^ 2 :=
  (two_pow_le_card_attainableTranscripts_sq_of_dotProduct p split readout h).trans
    (Nat.pow_le_pow_left (card_attainableTranscripts_le_sum_choose p) 2)

/-- A native single-output circuit computing inner product obeys the size-activity inequality
provided its output selects a gate. -/
theorem two_pow_le_sum_choose_sq_of_circuit_dotProduct
    (c : Circuit signature n 1) (split : Fin n ≃ ι ⊕ ι)
    (houtput : ∃ gate, c.outputs 0 = .gate gate)
    (h : ∀ x y, c.eval interpretation (inputOfSplit split x y) 0 = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤
      (∑ j ∈ range (inputActivity c.program + 1), (inputGates c.program).card.choose j) ^ 2 := by
  obtain ⟨gate, hgate⟩ := houtput
  apply two_pow_le_sum_choose_sq_of_dotProduct c.program split (fun z => z gate)
  simpa only [Circuit.eval_of_output_eq_gate hgate] using h

/-- Inner product forces the binomial sum at total gate activity to have square at least
`2 ^ m`. All gates are counted, including unused gates and gates without direct inputs. -/
theorem two_pow_le_sum_choose_gateActivity_sq_of_dotProduct
    (p : Program signature n g) (split : Fin n ≃ ι ⊕ ι)
    (readout : (Fin g → Bool) → Bool)
    (h : ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤ (∑ j ∈ range (gateActivity p + 1), g.choose j) ^ 2 :=
  (two_pow_le_card_attainableTranscripts_sq_of_dotProduct p split readout h).trans
    (Nat.pow_le_pow_left (card_attainableTranscripts_le_sum_choose_gateActivity p) 2)

/-- A native single-output inner-product circuit also obeys the bound using all gates,
provided its output selects a gate. -/
theorem two_pow_le_sum_choose_gateActivity_sq_of_circuit_dotProduct
    (c : Circuit signature n 1) (split : Fin n ≃ ι ⊕ ι)
    (houtput : ∃ gate, c.outputs 0 = .gate gate)
    (h : ∀ x y, c.eval interpretation (inputOfSplit split x y) 0 = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤
      (∑ j ∈ range (gateActivity c.program + 1), c.size.choose j) ^ 2 := by
  obtain ⟨gate, hgate⟩ := houtput
  apply two_pow_le_sum_choose_gateActivity_sq_of_dotProduct c.program split (fun z => z gate)
  simpa only [Circuit.eval_of_output_eq_gate hgate] using h

/-- Inner product forces the binomial sum at the program's shifted-baseline input-reading activity
around any fixed baseline `v` to have square at least `2 ^ m`. -/
theorem two_pow_le_sum_choose_inputActivityFrom_sq_of_dotProduct
    (p : Program signature n g) (split : Fin n ≃ ι ⊕ ι)
    (v : inputGates p → Bool) (readout : (Fin g → Bool) → Bool)
    (h : ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤
      (∑ j ∈ range (inputActivityFrom p v + 1), (inputGates p).card.choose j) ^ 2 :=
  (two_pow_le_card_attainableTranscripts_sq_of_dotProduct p split readout h).trans
    (Nat.pow_le_pow_left (card_attainableTranscripts_le_sum_choose_inputActivityFrom p v) 2)

/-- Inner product forces the binomial sum at the program's shifted-baseline total gate activity
around any fixed baseline `v` to have square at least `2 ^ m`. -/
theorem two_pow_le_sum_choose_gateActivityFrom_sq_of_dotProduct
    (p : Program signature n g) (split : Fin n ≃ ι ⊕ ι)
    (v : Fin g → Bool) (readout : (Fin g → Bool) → Bool)
    (h : ∀ x y, readout (p.eval interpretation (inputOfSplit split x y)) = x ⬝ᵥ y) :
    2 ^ Fintype.card ι ≤
      (∑ j ∈ range (gateActivityFrom p v + 1), g.choose j) ^ 2 :=
  (two_pow_le_card_attainableTranscripts_sq_of_dotProduct p split readout h).trans
    (Nat.pow_le_pow_left (card_attainableTranscripts_le_sum_choose_gateActivityFrom p v) 2)

end Cslib.Circuits.Boolean.WeightedThreshold
