/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyWeightedPreparation

/-!
# Canonical input range and stage-rate alignment

The actual input and pilot input are positive aggregates `C + Eᵢ C`, rather than
residuals. Their canonical targets satisfy the reference range needed by weighted
PREP when the base entries are bounded by the request's terminal rate. The constant
is the fixed hierarchy iteration count, independent of fields and requests.

Admissibility of channel roles alone does not give that alignment: the canonical
input always dominates its base. In particular a base entry larger than `d*f`
precludes the reference range, at every iteration, even for a nonnegative
substochastic base. This is a target-range obstruction, not estimator failure.
The results are original consequences of the existing correction-sequence API.
With a base cap `a`, the quantitative alternative is `(k+1)*a`, so using the
weighted PREP theorem requires `d=(k+1)*a/f`. This is uniform only if the
stage-cap/terminal-rate ratio is bounded. Otherwise the exact numerator-weighted
clipped mean from `HierarchyWeightedPreparation` must be paid directly, retaining
the numerator and polynomial saturation instead of this global range reduction;
no such alternative payment is proved here. Relative RAW accuracy remains an
additional induction obligation.

## Main results

* `BudgetData.canonicalPreparationInput_range`: aligned pilot and actual range.
* `BudgetData.base_le_canonicalPreparationInput`: the positive base persists.
* `BudgetData.canonicalPreparationInput_range_requires_base`: necessary alignment.
-/

public section
noncomputable section
open Finset Cslib Cslib.Probability
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
variable {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ} [Fact P.Prime]
  (B : BudgetData HP P)

private theorem pilot_sequence
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hf : 0 < r.terminal.rate) (hC : ∀ x y, 0 ≤ B.base x y) :
    IsCorrectionSeq B.base (pilotCorrection (HP.toHierarchyParams.cutoff r.terminal.rate)
      HP.γ (columnDetector (canonicalChannel id r.terminal.rate)
        (canonicalChannel id r.terminal.rate) HP.ϕ HP.ρ HP.J HP.K r.terminal.rate) B.base) :=
  isCorrectionSeq_pilotCorrection hC (HP.toHierarchyParams.cutoff_nonneg hf)
    (fun t ht => (HP.toHierarchyParams.cutoff_le hf t).trans (max_le (by
      have := mul_nonneg HP.θ_pos.le hf.le
      linarith) ht)) HP.γ_nonneg HP.γ_le_one

/-- Keep the base cap separate from the request's terminal rate. A mismatched
stage and terminal rate retains their ratio in a relative reference range. -/
theorem canonicalPreparationInput_range_of_base_cap (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hf : 0 < r.terminal.rate) (hC : ∀ x y, 0 ≤ B.base x y)
    (hC1 : B.base *ᵥ 1 ≤ 1) {a : ℝ} (ha : 0 ≤ a)
    (hCf : ∀ x y, B.base x y ≤ a)
    (x y : ZMod P) :
    B.canonicalPreparationInput pilot i r x y ∈ Set.Icc 0
      (((HP.k : ℝ) + 1) * a) := by
  have hi : (i.val : ℝ) + 1 ≤ (HP.k : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right i.isLt.le 1
  cases pilot
  · have hs := HP.toHierarchyParams.isCorrectionSeq_correctionIter
      (X := canonicalChannel id r.terminal.rate) (Y := canonicalChannel id r.terminal.rate)
      hf hC
    exact ⟨hs.input_nonneg hC i.val x y,
      (hs.input_le_mul hCf ha hC1 i.val x y).trans (mul_le_mul_of_nonneg_right hi ha)⟩
  · have hs := B.pilot_sequence r hf hC
    exact ⟨hs.input_nonneg hC i.val x y,
      (hs.input_le_mul hCf ha hC1 i.val x y).trans (mul_le_mul_of_nonneg_right hi ha)⟩

/-- Rate alignment discharges both reference ranges with an HP-only constant.
Substochasticity alone does not give the entrywise alignment premise. -/
theorem canonicalPreparationInput_range (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hf : 0 < r.terminal.rate) (hC : ∀ x y, 0 ≤ B.base x y)
    (hC1 : B.base *ᵥ 1 ≤ 1) (hCf : ∀ x y, B.base x y ≤ r.terminal.rate)
    (x y : ZMod P) :
    B.canonicalPreparationInput pilot i r x y ∈ Set.Icc 0
      (((HP.k : ℝ) + 1) * r.terminal.rate) :=
  B.canonicalPreparationInput_range_of_base_cap pilot i r hf hC hC1 hf.le hCf x y

/-- Neither pilot nor actual input can discard a positive base entry. No
substochasticity or base entry cap is needed for this direction. -/
theorem base_le_canonicalPreparationInput (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hf : 0 < r.terminal.rate) (hC : ∀ x y, 0 ≤ B.base x y) (x y : ZMod P) :
    B.base x y ≤ B.canonicalPreparationInput pilot i r x y := by
  cases pilot
  · change B.base x y ≤ B.base x y + _
    apply le_add_of_nonneg_right
    exact sum_nonneg fun z _ => mul_nonneg
      ((HP.toHierarchyParams.isCorrectionSeq_correctionIter
        (X := canonicalChannel id r.terminal.rate) (Y := canonicalChannel id r.terminal.rate)
        hf hC).nonneg i.val x z) (hC z y)
  · change B.base x y ≤ B.base x y + _
    exact le_add_of_nonneg_right (sum_nonneg fun z _ =>
      mul_nonneg ((B.pilot_sequence r hf hC).nonneg i.val x z) (hC z y))

/-- A proposed uniform reference range must at least control the actual base at
that rate. Source resets, suffixes and role admissibility cannot repair this. -/
theorem canonicalPreparationInput_range_requires_base (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hf : 0 < r.terminal.rate) (hC : ∀ x y, 0 ≤ B.base x y) {d : ℝ}
    (hG : ∀ x y, B.canonicalPreparationInput pilot i r x y ≤ d * r.terminal.rate)
    (x y : ZMod P) : B.base x y ≤ d * r.terminal.rate :=
  (B.base_le_canonicalPreparationInput pilot i r hf hC x y).trans (hG x y)

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
