/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.LogSpaceDerandomization.HierarchyParams
public import Complexity.Computability.LogSpaceDerandomization.FineOmission

/-!
# Concrete inputs of hierarchy correction tasks

The actual correction uses the final pilot multiplier at every iteration. Its raw input is
`C + Eᵢ C`, not the final residual `C - E + E C`. This module gives these inputs names and
connects them to the existing correction-sequence API. In particular, the entry and row-mass
bounds needed for fine omission are derived for products of actual correction iterates with
nonnegative bins of the stage matrix.

This implements the deterministic input/product part of [OpenAI2026LogSpace, Sections 7.1–7.3,
(7.2), Lemma 7.4, printed pp. 33–37], revision `7ef5c0cc`. Bin shape bounds remain explicit;
correction row mass is proved from the hierarchy construction. Fourth moments replace the
source's eighth moments. This does not assemble the stochastic detector/pilot tasks, the full
mean-prefix estimate, compression or the recursive estimator.

## Main definitions

* `Matrix.HierarchyParams.correctionIter`: actual correction at any iteration.
* `Matrix.HierarchyParams.correctionInput`: its next raw input.

## Main results

* `Matrix.HierarchyParams.isCorrectionSeq_correctionIter`: the concrete sequence contract.
* `Matrix.HierarchyParams.correctionIter_mul_bin_bounds`: true product entry and row mass.
* `Matrix.HierarchyParams.correctionIter_mul_bin_omission_le`: actual product omission.
* `Matrix.HierarchyParams.sum_correctionIter_mul_bin_omission_norm_le`: scheduled omission sum.
-/

public section

open Finset
open scoped BigOperators

namespace Matrix.HierarchyParams

variable {q cπ Cπ Cpair Cvar : ℝ} (P : Matrix.HierarchyParams q cπ Cπ Cpair Cvar)
  {V ι κ : Type*} [Fintype V] [Fintype ι] [Fintype κ]
  (X : ι → V → Prop) (Y : κ → V → Prop)
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
  (f : ℝ) (C : Matrix V V ℝ)

/-- Actual correction tasks use the final pilot multiplier, also at intermediate iterations. -/
@[expose] noncomputable def correctionIter (i : ℕ) : Matrix V V ℝ :=
  cutoffCorrectionIter (fun y t => P.cutoff f t * P.γ (P.pilot X Y f C y)) C i

/-- The raw input of the next actual correction, before applying the ramp and multiplier. -/
@[expose] noncomputable def correctionInput (i : ℕ) : Matrix V V ℝ :=
  C + P.correctionIter X Y f C i * C

/-- The final task agrees with the hierarchy's correction, with no alternative interface. -/
theorem correctionIter_last : P.correctionIter X Y f C P.k = P.correction X Y f C := by
  rw [P.correction_eq]
  rfl

/-- Actual correction recurrence, in original matrix units. -/
theorem correctionIter_succ_apply (i : ℕ) (x y : V) :
    P.correctionIter X Y f C (i + 1) x y =
      f * P.Q (P.correctionInput X Y f C i x y / f) * P.γ (P.pilot X Y f C y) := by
  rw [correctionIter, cutoffCorrectionIter_succ]
  simp only [cutoffCorrection, of_apply, P.cutoff_apply, correctionInput, correctionIter]

variable {X Y f C}

/-- Derive the sequence contract from the actual ramp and final detector multiplier. -/
theorem isCorrectionSeq_correctionIter (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y) :
    IsCorrectionSeq C (P.correctionIter X Y f C) := by
  apply isCorrectionSeq_cutoffCorrectionIter hC
    (fun y t => mul_nonneg (P.cutoff_nonneg hf t) (P.γ_nonneg _))
    (fun y t => (mul_le_of_le_one_right (P.cutoff_nonneg hf t)
      (P.γ_le_one _)).trans (P.cutoff_le hf t))
  exact mul_nonneg P.θ_pos.le hf.le

/-- The actual raw input is nonnegative, has bounded row mass and has the expected entry cap. -/
theorem correctionInput_bounds (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) (hCf : ∀ x y, C x y ≤ f) (i : ℕ) :
    (∀ x y, 0 ≤ P.correctionInput X Y f C i x y) ∧
      (∀ x, ∑ y, P.correctionInput X Y f C i x y ≤ (i : ℝ) + 1) ∧
      ∀ x y, P.correctionInput X Y f C i x y ≤ ((i : ℝ) + 1) * f := by
  have hseq := P.isCorrectionSeq_correctionIter (X := X) (Y := Y) hf hC
  exact ⟨hseq.input_nonneg hC i, fun x => (hseq.sum_input_le hC1 i x).1,
    hseq.input_le_mul hCf hf.le hC1 i⟩

/-- A bin of the stage matrix is substochastic. Multiplication by the actual correction gives
entry cap `i * Cb * b` and row mass `i`. These are consequences, not omission certificates. -/
theorem correctionIter_mul_bin_bounds (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) (i : ℕ) {B : Matrix V V ℝ} {b Cb : ℝ}
    (hB : ∀ x y, 0 ≤ B x y) (hBC : ∀ x y, B x y ≤ C x y)
    (hcap : ∀ x y, B x y ≤ Cb * b) (hCb : 0 ≤ Cb) (hb : 0 ≤ b) :
    (∀ x y, 0 ≤ (P.correctionIter X Y f C i * B) x y) ∧
      (∀ x y, (P.correctionIter X Y f C i * B) x y ≤ ((i : ℝ) * Cb) * b) ∧
      ∀ x, ∑ y, (P.correctionIter X Y f C i * B) x y ≤ i := by
  have hseq := P.isCorrectionSeq_correctionIter (X := X) (Y := Y) hf hC
  have hrow (x : V) : ∑ y, B x y ≤ 1 :=
    (sum_le_sum fun y _ => hBC x y).trans (by simpa [mulVec, dotProduct] using hC1 x)
  refine ⟨fun x y => sum_nonneg fun z _ => mul_nonneg (hseq.nonneg i x z) (hB z y),
    fun x y => ?_, fun x => ?_⟩
  · calc
      _ ≤ ∑ z, P.correctionIter X Y f C i x z * (Cb * b) :=
        sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hcap z y) (hseq.nonneg i x z)
      _ = (∑ z, P.correctionIter X Y f C i x z) * (Cb * b) := (sum_mul _ _ _).symm
      _ ≤ (i : ℝ) * (Cb * b) :=
        mul_le_mul_of_nonneg_right (hseq.sum_le hC1 i x) (mul_nonneg hCb hb)
      _ = _ := by ring
  · calc
      _ = ∑ z, P.correctionIter X Y f C i x z * ∑ y, B z y := by
        simp only [Matrix.mul_apply, mul_sum]
        rw [sum_comm]
      _ ≤ ∑ z, P.correctionIter X Y f C i x z * 1 :=
        sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hrow z) (hseq.nonneg i x z)
      _ ≤ i := by simpa only [mul_one] using hseq.sum_le hC1 i x

/-- Fine omission for a product built from an actual hierarchy correction iterate.
The only mass hypotheses concern the bin itself; the correction bounds are discharged here. -/
theorem correctionIter_mul_bin_omission_le {Γ Υ : Type*} [Fintype Γ] [Fintype Υ]
    (Xs : Γ → V → Prop) (Yt : Υ → V → Prop)
    [∀ γ x, Decidable (Xs γ x)] [∀ τ y, Decidable (Yt τ y)]
    (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1) (i : ℕ)
    {N u a b Cu Ca Cb : ℝ} (hN : 0 < N) (hu : 0 < u) (ha : 0 < a)
    (hb : 0 ≤ b) (hCu : 0 ≤ Cu) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (hcard : (Fintype.card V : ℝ) ≤ N)
    (hXs : ∀ x, (dens {γ | Xs γ x} : ℝ) ≤ Cu * u)
    (hYt : ∀ y, (dens {τ | Yt τ y} : ℝ) ≤ Ca * a)
    (B : Matrix V V ℝ) (hB : ∀ x y, 0 ≤ B x y) (hBC : ∀ x y, B x y ≤ C x y)
    (hcap : ∀ x y, B x y ≤ Cb * b) :
    Cslib.rowNormPow 4 N u (fun (σ : Γ × Υ) x => Xs σ.1 x) (fun σ y => Yt σ.2 y)
      (fun _ x y => (P.correctionIter X Y f C i * B) x y / a) ≤
        Cu * Ca * ((i : ℝ) * Cb) ^ 3 * i * (b / a) ^ 3 := by
  have hmass := P.correctionIter_mul_bin_bounds (X := X) (Y := Y) hf hC hC1 i
    hB hBC hcap hCb hb
  exact Cslib.rowNormPow_fine_omission_le Xs Yt hN hu ha hb hCu hCa
    (mul_nonneg (Nat.cast_nonneg i) hCb) (Nat.cast_nonneg i) hcard hXs hYt
    _ hmass.1 hmass.2.1 hmass.2.2

/-- Assemble the actual omitted-product family on the integer slack schedule. Its total
fourth-root norm is uniformly summable, with every per-bin product mass bound discharged. -/
theorem sum_correctionIter_mul_bin_omission_norm_le {Γ Υ : Type*}
    [Fintype Γ] [Fintype Υ] (Xs : Γ → V → Prop) (Yt : Υ → V → Prop)
    [∀ γ x, Decidable (Xs γ x)] [∀ τ y, Decidable (Yt τ y)]
    (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1) (i : ℕ)
    {N u a Cu Ca Cb Ksum : ℝ} (hN : 0 < N) (hu : 0 < u) (ha : 0 < a)
    (hCu : 0 ≤ Cu) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hKsum : 0 ≤ Ksum)
    (hconstant : Cu * Ca * ((i : ℝ) * Cb) ^ 3 * i ≤ Ksum ^ 4)
    (hcard : (Fintype.card V : ℝ) ≤ N)
    (hXs : ∀ x, (dens {γ | Xs γ x} : ℝ) ≤ Cu * u)
    (hYt : ∀ y, (dens {τ | Yt τ y} : ℝ) ≤ Ca * a)
    (M c : ℕ) (hc : 0 < c) (T : Finset ℤ) (b : ℤ → ℝ) (B : ℤ → Matrix V V ℝ)
    (hb : ∀ h ∈ T, 0 < b h) (hfine : ∀ h ∈ T, h < 0)
    (homit : ∀ h ∈ T, M ≤ Cslib.LogSpaceEstimation.scaleCutoff c h)
    (hscale : ∀ h ∈ T, Real.logb 2 (b h / a) = (h : ℝ))
    (hB : ∀ h ∈ T, ∀ x y, 0 ≤ B h x y) (hBC : ∀ h ∈ T, ∀ x y, B h x y ≤ C x y)
    (hcap : ∀ h ∈ T, ∀ x y, B h x y ≤ Cb * b h) :
    ∑ h ∈ T, (Cslib.rowNormPow 4 N u (fun (σ : Γ × Υ) x => Xs σ.1 x)
      (fun σ y => Yt σ.2 y)
      (fun _ x y => (P.correctionIter X Y f C i * B h) x y / a)) ^ (4⁻¹ : ℝ) ≤
        Ksum * ((2 : ℝ) ^ (1 / 2 - (M : ℝ) / (2 * c)) *
          (2 / (1 - (2 : ℝ) ^ (-(1 : ℝ) / 8)) - 1)) := by
  have hmass (h : ℤ) (hh : h ∈ T) := P.correctionIter_mul_bin_bounds
    (X := X) (Y := Y) hf hC hC1 i (hB h hh) (hBC h hh) (hcap h hh) hCb (hb h hh).le
  exact Cslib.LogSpaceEstimation.sum_fine_omission_norm_le Xs Yt hN hu ha hCu hCa
    (mul_nonneg (Nat.cast_nonneg i) hCb) (Nat.cast_nonneg i) hKsum hconstant hcard hXs hYt
    M c hc T b (fun h => P.correctionIter X Y f C i * B h) hb hfine homit hscale
    (fun h hh => (hmass h hh).1) (fun h hh => (hmass h hh).2.1)
    (fun h hh => (hmass h hh).2.2)

end Matrix.HierarchyParams
