/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `Borell.lean`)

public import CslibFrontier.Foundations.Probability.Gaussian.Quadrant
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate

/-!
# Reductions for Borell's Isoperimetric Theorem

The Mossel–Neeman proof of Borell's Isoperimetric Theorem
[O'Donnell, Exercises 11.26–11.29][ODonnell2014] passes through the *Two-Function Borell
Isoperimetric Theorem*: for `ρ ∈ (0, 1)`, measurable `f, g : ℝ^n → [0, 1]` and `ρ`-correlated
`n`-dimensional Gaussians `(z, z')`, `E[Λ_ρ(f z, g z')] ≤ Λ_ρ(E f, E g)`, where `Λ_ρ` is the
Gaussian quadrant function. This file formalizes the structural part of that proof: everything
except the one-dimensional case.

We state the two-function inequality and the *Two-Set* inequality
`P[z ∈ A, z' ∈ B] ≤ Λ_ρ(vol_γ A, vol_γ B)` as predicates on the index type `ι` of the
coordinates (`TwoFunctionBorellInequality`, `TwoSetBorellInequality`), and prove:

* Exercise 11.27, tensorization: the two-function inequality in the coordinates `ι` and `κ` gives
  it in `ι ⊕ κ`, so the case `n = 1` gives every finite dimension;
* Exercise 11.26 (a): the two-function inequality gives the two-set inequality and, for
  `ρ ∈ [0, 1]`, Borell's Isoperimetric Theorem `Stab_ρ[f] ≤ Λ_ρ(E f)` for `[0, 1]`-valued `f`;
* Exercise 11.26 (b): the two-set inequality in dimension `n + 1` gives the two-function
  inequality in dimension `n`;
* Exercise 11.26 (c), the equality cases: indicators of parallel halfspaces, and `Φ` composed
  with parallel affine functions.

The one-dimensional two-function inequality (Exercises 11.28 and 11.29, the heat-flow argument of
Mossel and Neeman) is **not** proved here: it appears only as the hypothesis
`TwoFunctionBorellInequality ρ (Fin 1)`, so Borell's Isoperimetric Theorem itself remains open.
As non-vacuity checks, the predicate holds at `ρ = 0` and at `ρ = 1`, and the parallel halfspaces
attain equality.

The tensorization uses only that correlated Gaussians are a product over the coordinates
(`correlatedGaussianPi_sum`), as the book asks, together with two properties of `Λ_ρ` that the
Bochner integral needs: it is jointly measurable for `|ρ| ≤ 1`, and its values lie in `[0, 1]`,
so the integrands are integrable and the partial means stay in `[0, 1]`.

## Main definitions

* `ProbabilityTheory.TwoFunctionBorellInequality`: the Two-Function Borell inequality in the
  coordinates `ι`.
* `ProbabilityTheory.TwoSetBorellInequality`: the Two-Set Borell inequality in the coordinates
  `ι`.

## Main results

* `ProbabilityTheory.pi_gaussianReal_sum`, `ProbabilityTheory.correlatedGaussianPi_sum`,
  `ProbabilityTheory.measurePreserving_pi_gaussianReal_comp_symm`,
  `ProbabilityTheory.correlatedGaussianPi_map_comp_symm`: splitting and relabelling coordinates.
* `ProbabilityTheory.twoFunctionBorellInequality_iff`,
  `ProbabilityTheory.twoSetBorellInequality_iff`: unfolding the predicates.
* `ProbabilityTheory.TwoFunctionBorellInequality.sum`,
  `ProbabilityTheory.TwoFunctionBorellInequality.of_equiv`,
  `ProbabilityTheory.twoFunctionBorellInequality_of_isEmpty`,
  `ProbabilityTheory.TwoFunctionBorellInequality.of_fin_one`: Exercise 11.27.
* `ProbabilityTheory.TwoFunctionBorellInequality.twoSetBorellInequality`,
  `ProbabilityTheory.TwoFunctionBorellInequality.gaussianNoiseStability_le`,
  `ProbabilityTheory.TwoFunctionBorellInequality.gaussianNoiseStability_le_of_ae`,
  `ProbabilityTheory.TwoFunctionBorellInequality.gaussianNoiseStability_le_of_integral_eq_half`,
  `ProbabilityTheory.integral_gaussianQuadrant_indicator`: Exercise 11.26 (a).
* `ProbabilityTheory.TwoSetBorellInequality.twoFunctionBorellInequality`: Exercise 11.26 (b).
* `ProbabilityTheory.measureReal_correlatedGaussianPi_setOf_dotProduct_le_prod`,
  `ProbabilityTheory.integral_gaussianQuadrant_indicator_setOf_dotProduct_le`,
  `ProbabilityTheory.integral_gaussianQuadrant_cdf_dotProduct_add`: Exercise 11.26 (c).
* `ProbabilityTheory.twoFunctionBorellInequality_zero`,
  `ProbabilityTheory.twoFunctionBorellInequality_one`: the cases `ρ = 0` and `ρ = 1`.
* `ProbabilityTheory.TwoFunctionBorellInequality.twoSetBorellInequality_of_fin_one`,
  `ProbabilityTheory.TwoFunctionBorellInequality.gaussianNoiseStability_le_of_fin_one`: the full
  reduction of Borell's Isoperimetric Theorem to the one-dimensional two-function inequality.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory Real Set

namespace ProbabilityTheory

local notation "Φ" => cdf (gaussianReal 0 1)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Splitting the coordinates of correlated Gaussians -/

omit [Fintype ι] [Fintype κ] in
private theorem measurable_sumElim :
    Measurable fun q : (ι → ℝ) × (κ → ℝ) => Sum.elim q.1 q.2 :=
  (MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ κ => ℝ).symm.measurable

omit [Fintype ι] [Fintype κ] in
private theorem measurable_sumElim_pair :
    Measurable fun q : ((ι → ℝ) × (ι → ℝ)) × ((κ → ℝ) × (κ → ℝ)) =>
      (Sum.elim q.1.1 q.2.1, Sum.elim q.1.2 q.2.2) :=
  (measurable_sumElim.comp (measurable_fst.fst.prodMk measurable_snd.fst)).prodMk
    (measurable_sumElim.comp (measurable_fst.snd.prodMk measurable_snd.snd))

/-- A standard Gaussian vector indexed by `ι ⊕ κ` is a pair of independent standard Gaussian
vectors indexed by `ι` and by `κ`. -/
theorem pi_gaussianReal_sum :
    (Measure.pi fun _ : ι ⊕ κ => gaussianReal 0 1) =
      ((Measure.pi fun _ : ι => gaussianReal 0 1).prod
        (Measure.pi fun _ : κ => gaussianReal 0 1)).map fun q => Sum.elim q.1 q.2 :=
  (measurePreserving_sumPiEquivProdPi_symm fun _ : ι ⊕ κ => gaussianReal 0 1).map_eq.symm

/-- `ρ`-correlated vectors indexed by `ι ⊕ κ` are a pair of independent `ρ`-correlated vectors
indexed by `ι` and by `κ`: correlated Gaussians are a product over the coordinates. -/
theorem correlatedGaussianPi_sum (ρ : ℝ) :
    correlatedGaussianPi (ι ⊕ κ) ρ =
      ((correlatedGaussianPi ι ρ).prod (correlatedGaussianPi κ ρ)).map
        fun ((z₁, z₁'), (z₂, z₂')) => (Sum.elim z₁ z₂, Sum.elim z₁' z₂') := by
  have hS := measurable_sumElim_pair (ι := ι) (κ := κ)
  rw [correlatedGaussianPi_eq_map_pi, ← (measurePreserving_sumPiEquivProdPi_symm
      fun _ : ι ⊕ κ => correlatedGaussian ρ).map_eq,
    Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _), correlatedGaussianPi_eq_map_pi,
    correlatedGaussianPi_eq_map_pi, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map hS (by fun_prop)]
  congr 1
  funext q
  refine Prod.ext ?_ ?_ <;> funext i <;> rcases i with i | i <;> rfl

/-- Reindexing a standard Gaussian vector along `e : ι ≃ κ` gives a standard Gaussian vector. -/
theorem measurePreserving_pi_gaussianReal_comp_symm (e : ι ≃ κ) :
    MeasurePreserving (fun z : ι → ℝ => fun j => z (e.symm j))
      (Measure.pi fun _ : ι => gaussianReal 0 1) (Measure.pi fun _ : κ => gaussianReal 0 1) :=
  measurePreserving_arrowCongr' (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1) e
    (MeasurableEquiv.refl ℝ) fun _ => MeasurePreserving.id _

/-- Reindexing `ρ`-correlated vectors along `e : ι ≃ κ` gives `ρ`-correlated vectors. -/
theorem correlatedGaussianPi_map_comp_symm (ρ : ℝ) (e : ι ≃ κ) :
    (correlatedGaussianPi ι ρ).map (fun p => (fun j => p.1 (e.symm j), fun j => p.2 (e.symm j))) =
      correlatedGaussianPi κ ρ := by
  have hφ : MeasurePreserving (fun z : ι → ℝ × ℝ => fun j => z (e.symm j))
      (Measure.pi fun _ : ι => correlatedGaussian ρ)
      (Measure.pi fun _ : κ => correlatedGaussian ρ) :=
    measurePreserving_arrowCongr' (fun _ => correlatedGaussian ρ) (fun _ => correlatedGaussian ρ) e
      (MeasurableEquiv.refl _) fun _ => MeasurePreserving.id _
  rw [correlatedGaussianPi_eq_map_pi, correlatedGaussianPi_eq_map_pi, ← hφ.map_eq,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) hφ.measurable]
  rfl

/-! ### Integrals over split coordinates -/

private theorem integral_mem_Icc {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {h : α → ℝ} (h01 : ∀ x, h x ∈ Icc 0 1) : ∫ x, h x ∂μ ∈ Icc 0 1 :=
  ⟨integral_nonneg fun x => (h01 x).1, (integral_mono_of_nonneg (ae_of_all _ fun x => (h01 x).1)
    (integrable_const 1) (ae_of_all _ fun x => (h01 x).2)).trans_eq (by simp)⟩

private theorem integrable_of_mem_Icc {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {h : α → ℝ} (hh : Measurable h) (h01 : ∀ x, h x ∈ Icc 0 1) :
    Integrable h μ :=
  Integrable.of_mem_Icc 0 1 hh.aemeasurable (ae_of_all _ h01)

/-- Fubini for a standard Gaussian vector indexed by `ι ⊕ κ`. -/
private theorem integral_pi_gaussianReal_sum {h : (ι ⊕ κ → ℝ) → ℝ} (hh : Measurable h)
    (h01 : ∀ z, h z ∈ Icc 0 1) :
    ∫ z, h z ∂(Measure.pi fun _ : ι ⊕ κ => gaussianReal 0 1) =
      ∫ u, ∫ v, h (Sum.elim u v) ∂(Measure.pi fun _ : κ => gaussianReal 0 1)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  rw [pi_gaussianReal_sum, integral_map measurable_sumElim.aemeasurable
    hh.aestronglyMeasurable]
  exact integral_prod _ (integrable_of_mem_Icc (hh.comp measurable_sumElim) fun q => h01 _)

/-- Fubini for `ρ`-correlated vectors indexed by `ι ⊕ κ`. -/
private theorem integral_correlatedGaussianPi_sum (ρ : ℝ)
    {h : (ι ⊕ κ → ℝ) × (ι ⊕ κ → ℝ) → ℝ} (hh : Measurable h) (h01 : ∀ p, h p ∈ Icc 0 1) :
    ∫ p, h p ∂correlatedGaussianPi (ι ⊕ κ) ρ =
      ∫ p, ∫ r, h (Sum.elim p.1 r.1, Sum.elim p.2 r.2) ∂correlatedGaussianPi κ ρ
        ∂correlatedGaussianPi ι ρ := by
  have hS := measurable_sumElim_pair (ι := ι) (κ := κ)
  rw [correlatedGaussianPi_sum, integral_map hS.aemeasurable hh.aestronglyMeasurable]
  exact integral_prod _ (integrable_of_mem_Icc (hh.comp hS) fun q => h01 _)

/-! ### The two-function and two-set inequalities -/

/-- The **Two-Function Borell Isoperimetric inequality** in the coordinates `ι`
[O'Donnell, Exercise 11.26][ODonnell2014]: for measurable `f, g : ℝ^ι → [0, 1]` and
`ρ`-correlated `ι`-dimensional Gaussians `(z, z')`, `E[Λ_ρ(f z, g z')] ≤ Λ_ρ(E f, E g)`.

This is the statement, not a proof: it is a hypothesis of the reductions below. It is meant for
`ρ ∈ [0, 1]` (the book asserts it for `ρ ∈ (0, 1)`; it holds at `ρ = 0` and `ρ = 1`). It is false
for `ρ ∈ [-1, 0)`: it implies `TwoSetBorellInequality`, which fails there, for instance at
`ρ = -1 / 2` in one dimension for `A = {z ≤ 0}`, `B = {z ≥ 0}`, where
`P[z ∈ A, z' ∈ B] = 1 / 3 > 1 / 6 = Λ_ρ(1 / 2, 1 / 2)`. -/
def TwoFunctionBorellInequality (ρ : ℝ) (ι : Type*) [Fintype ι] : Prop :=
  ∀ f g : (ι → ℝ) → ℝ, Measurable f → Measurable g → (∀ z, f z ∈ Icc 0 1) →
    (∀ z, g z ∈ Icc 0 1) →
    ∫ p, gaussianQuadrant ρ (f p.1) (g p.2) ∂correlatedGaussianPi ι ρ ≤
      gaussianQuadrant ρ (∫ z, f z ∂Measure.pi fun _ : ι => gaussianReal 0 1)
        (∫ z, g z ∂Measure.pi fun _ : ι => gaussianReal 0 1)

/-- Unfolding `TwoFunctionBorellInequality`. -/
theorem twoFunctionBorellInequality_iff {ρ : ℝ} :
    TwoFunctionBorellInequality ρ ι ↔ ∀ f g : (ι → ℝ) → ℝ, Measurable f → Measurable g →
      (∀ z, f z ∈ Icc 0 1) → (∀ z, g z ∈ Icc 0 1) →
      ∫ p, gaussianQuadrant ρ (f p.1) (g p.2) ∂correlatedGaussianPi ι ρ ≤
        gaussianQuadrant ρ (∫ z, f z ∂Measure.pi fun _ : ι => gaussianReal 0 1)
          (∫ z, g z ∂Measure.pi fun _ : ι => gaussianReal 0 1) := by
  rw [TwoFunctionBorellInequality]

/-- The **Two-Set Borell Isoperimetric inequality** in the coordinates `ι`
[O'Donnell, Exercise 11.26, (11.47)][ODonnell2014]: for measurable `A, B ⊆ ℝ^ι` and
`ρ`-correlated `ι`-dimensional Gaussians `(z, z')`,
`P[z ∈ A, z' ∈ B] ≤ Λ_ρ(vol_γ A, vol_γ B)`.

This is the statement, not a proof. It is meant for `ρ ∈ [0, 1]` (the book: `ρ ∈ (0, 1)`). It is
false for `ρ ∈ [-1, 0)`: in one dimension, `A = {z ≤ 0}` and `B = {z ≥ 0}` have
`P[z ∈ A, z' ∈ B] = arccos ρ / (2π) > 1 / 2 - arccos ρ / (2π) = Λ_ρ(1 / 2, 1 / 2)`, which at
`ρ = -1 / 2` reads `1 / 3 > 1 / 6`. -/
def TwoSetBorellInequality (ρ : ℝ) (ι : Type*) [Fintype ι] : Prop :=
  ∀ A B : Set (ι → ℝ), MeasurableSet A → MeasurableSet B →
    (correlatedGaussianPi ι ρ).real (A ×ˢ B) ≤
      gaussianQuadrant ρ ((Measure.pi fun _ : ι => gaussianReal 0 1).real A)
        ((Measure.pi fun _ : ι => gaussianReal 0 1).real B)

/-- Unfolding `TwoSetBorellInequality`. -/
theorem twoSetBorellInequality_iff {ρ : ℝ} :
    TwoSetBorellInequality ρ ι ↔ ∀ A B : Set (ι → ℝ), MeasurableSet A → MeasurableSet B →
      (correlatedGaussianPi ι ρ).real (A ×ˢ B) ≤
        gaussianQuadrant ρ ((Measure.pi fun _ : ι => gaussianReal 0 1).real A)
          ((Measure.pi fun _ : ι => gaussianReal 0 1).real B) := by
  rw [TwoSetBorellInequality]

/-! ### Exercise 11.27: tensorization -/

/-- The Two-Function Borell inequality holds in dimension zero, where both sides are
`Λ_ρ(f 0, g 0)`. -/
theorem twoFunctionBorellInequality_of_isEmpty [IsEmpty ι] (ρ : ℝ) :
    TwoFunctionBorellInequality ρ ι := by
  intro f g _ _ _ _
  have hf : f = fun _ => f default := funext fun z => congrArg f (Subsingleton.elim _ _)
  have hg : g = fun _ => g default := funext fun z => congrArg g (Subsingleton.elim _ _)
  rw [hf, hg]
  simp only [integral_const, probReal_univ, one_smul, le_rfl]

/-- The Two-Function Borell inequality is invariant under relabelling the coordinates. -/
theorem TwoFunctionBorellInequality.of_equiv {ρ : ℝ} (h : TwoFunctionBorellInequality ρ ι)
    (e : ι ≃ κ) : TwoFunctionBorellInequality ρ κ := by
  intro f g hf hg hf01 hg01
  set φ := MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl ℝ)
  have hφ : MeasurePreserving φ (Measure.pi fun _ : ι => gaussianReal 0 1)
      (Measure.pi fun _ : κ => gaussianReal 0 1) := measurePreserving_pi_gaussianReal_comp_symm e
  have hC : MeasurePreserving (φ.prodCongr φ) (correlatedGaussianPi ι ρ)
      (correlatedGaussianPi κ ρ) :=
    ⟨(φ.prodCongr φ).measurable, correlatedGaussianPi_map_comp_symm ρ e⟩
  rw [← hC.integral_comp', ← hφ.integral_comp', ← hφ.integral_comp']
  exact h _ _ (hf.comp φ.measurable) (hg.comp φ.measurable) (fun z => hf01 _) fun z => hg01 _

/-- **Tensorization** [O'Donnell, Exercise 11.27][ODonnell2014]: the Two-Function Borell
inequality in the coordinates `ι` and in the coordinates `κ` gives it in the coordinates `ι ⊕ κ`.
For fixed `ι`-coordinates the `κ`-inequality bounds the inner integral by `Λ_ρ` of the partial
means, and the `ι`-inequality bounds the outer one. -/
theorem TwoFunctionBorellInequality.sum {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (hι : TwoFunctionBorellInequality ρ ι) (hκ : TwoFunctionBorellInequality ρ κ) :
    TwoFunctionBorellInequality ρ (ι ⊕ κ) := by
  intro f g hf hg hf01 hg01
  have hΛ01 : ∀ a b, gaussianQuadrant ρ a b ∈ Icc 0 1 := fun a b =>
    ⟨gaussianQuadrant_nonneg ρ a b, gaussianQuadrant_le_one ρ a b⟩
  -- The means over the `κ`-coordinates, as functions of the `ι`-coordinates.
  let F : (ι → ℝ) → ℝ := fun u => ∫ v, f (Sum.elim u v) ∂Measure.pi fun _ : κ => gaussianReal 0 1
  let G : (ι → ℝ) → ℝ := fun u => ∫ v, g (Sum.elim u v) ∂Measure.pi fun _ : κ => gaussianReal 0 1
  have hF : Measurable F :=
    (hf.comp measurable_sumElim).stronglyMeasurable.integral_prod_right'.measurable
  have hG : Measurable G :=
    (hg.comp measurable_sumElim).stronglyMeasurable.integral_prod_right'.measurable
  rw [integral_correlatedGaussianPi_sum ρ (Measurable.gaussianQuadrant hρ
    (a := fun p => f p.1) (b := fun p => g p.2) (by fun_prop) (by fun_prop)) fun p => hΛ01 _ _,
    integral_pi_gaussianReal_sum hf hf01, integral_pi_gaussianReal_sum hg hg01]
  refine (integral_mono_of_nonneg (ae_of_all _ fun p => integral_nonneg fun r => (hΛ01 _ _).1)
    (integrable_of_mem_Icc (Measurable.gaussianQuadrant hρ (a := fun p => F p.1)
      (b := fun p => G p.2) (by fun_prop) (by fun_prop))
      fun p => hΛ01 (F p.1) (G p.2)) (ae_of_all _ fun p => ?_)).trans
    (hι F G hF hG (fun u => integral_mem_Icc fun v => hf01 _)
      fun u => integral_mem_Icc fun v => hg01 _)
  exact hκ (fun v => f (Sum.elim p.1 v)) (fun v => g (Sum.elim p.2 v))
    ((hf.comp measurable_sumElim).comp measurable_prodMk_left)
    ((hg.comp measurable_sumElim).comp measurable_prodMk_left) (fun v => hf01 _) fun v => hg01 _

/-- **Tensorization** [O'Donnell, Exercise 11.27][ODonnell2014]: the Two-Function Borell
inequality on the line (`Fin 1`) gives it in every finite dimension. -/
theorem TwoFunctionBorellInequality.of_fin_one {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (h : TwoFunctionBorellInequality ρ (Fin 1)) (ι : Type*) [Fintype ι] :
    TwoFunctionBorellInequality ρ ι := by
  have hfin : ∀ n, TwoFunctionBorellInequality ρ (Fin n) := by
    intro n
    induction n with
    | zero => exact twoFunctionBorellInequality_of_isEmpty ρ
    | succ n ih => exact (ih.sum hρ h).of_equiv finSumFinEquiv
  exact (hfin _).of_equiv (Fintype.equivFin ι).symm

/-! ### Exercise 11.26: sets and functions -/

private theorem indicator_one_mem_Icc {α : Type*} (C : Set α) (z : α) :
    C.indicator (1 : α → ℝ) z ∈ Icc 0 1 := by
  by_cases hz : z ∈ C <;> simp [hz]

/-- For indicators, `E[Λ_ρ(1_A z, 1_B z')] = P[z ∈ A, z' ∈ B]`, since
`Λ_ρ(1_A z, 1_B z') = 1_A z 1_B z'` by the values of `Λ_ρ` at `0` and `1`. -/
theorem integral_gaussianQuadrant_indicator {ρ : ℝ} (hρ : |ρ| ≤ 1) {A B : Set (ι → ℝ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫ p, gaussianQuadrant ρ (A.indicator 1 p.1) (B.indicator 1 p.2) ∂correlatedGaussianPi ι ρ =
      (correlatedGaussianPi ι ρ).real (A ×ˢ B) := by
  have hΛ : (fun p : (ι → ℝ) × (ι → ℝ) =>
      gaussianQuadrant ρ (A.indicator 1 p.1) (B.indicator 1 p.2)) = (A ×ˢ B).indicator 1 := by
    funext p
    by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ B <;>
      simp [h1, h2, gaussianQuadrant_one_left hρ zero_le_one le_rfl, gaussianQuadrant_zero_left,
        gaussianQuadrant_zero_right]
  rw [hΛ, integral_indicator_one (hA.prod hB)]

/-- **Two functions give two sets** [O'Donnell, Exercise 11.26 (a)][ODonnell2014]: the
Two-Function Borell inequality for the indicators `1_A`, `1_B` is the Two-Set Borell inequality
(`integral_gaussianQuadrant_indicator`). -/
theorem TwoFunctionBorellInequality.twoSetBorellInequality {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (h : TwoFunctionBorellInequality ρ ι) : TwoSetBorellInequality ρ ι := by
  intro A B hA hB
  have := h _ _ (measurable_one.indicator hA) (measurable_one.indicator hB)
    (indicator_one_mem_Icc A) (indicator_one_mem_Icc B)
  rwa [integral_gaussianQuadrant_indicator hρ hA hB, integral_indicator_one hA,
    integral_indicator_one hB] at this

/-- **Two functions give Borell's Isoperimetric Theorem**
[O'Donnell, Exercise 11.26 (a)][ODonnell2014]: for `ρ ∈ [0, 1]` and measurable
`f : ℝ^ι → [0, 1]`, the Two-Function Borell inequality gives `Stab_ρ[f] ≤ Λ_ρ(E f)`, since
`f z f z' ≤ Λ_ρ(f z, f z')` (Exercise 11.19 (c)). -/
theorem TwoFunctionBorellInequality.gaussianNoiseStability_le {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (h : TwoFunctionBorellInequality ρ ι) {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (hf01 : ∀ z, f z ∈ Icc 0 1) :
    gaussianNoiseStability ρ f ≤
      gaussianQuadrant ρ (∫ z, f z ∂Measure.pi fun _ : ι => gaussianReal 0 1)
        (∫ z, f z ∂Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hρ : |ρ| ≤ 1 := abs_le.2 ⟨by linarith, hρ1⟩
  refine le_trans (integral_mono (integrable_of_mem_Icc (by fun_prop) fun p =>
    ⟨mul_nonneg (hf01 _).1 (hf01 _).1,
      (mul_le_of_le_one_left (hf01 _).1 (hf01 _).2).trans (hf01 _).2⟩)
    (integrable_of_mem_Icc (Measurable.gaussianQuadrant hρ (a := fun p => f p.1)
      (b := fun p => f p.2) (by fun_prop) (by fun_prop)) fun p =>
        ⟨gaussianQuadrant_nonneg _ _ _, gaussianQuadrant_le_one _ _ _⟩) fun p => ?_)
    (h f f hf hf hf01 hf01)
  exact mul_le_gaussianQuadrant hρ0 hρ1 (hf01 _).1 (hf01 _).2 (hf01 _).1 (hf01 _).2

/-- **Two functions give Borell's Isoperimetric Theorem, almost everywhere**: the form of
`TwoFunctionBorellInequality.gaussianNoiseStability_le` for `f` that is only a.e. strongly
measurable with values a.e. in `[0, 1]`. Clamping a measurable version of `f` to `[0, 1]` changes
neither side. -/
theorem TwoFunctionBorellInequality.gaussianNoiseStability_le_of_ae {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (h : TwoFunctionBorellInequality ρ ι) {f : (ι → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hf01 : ∀ᵐ z ∂(Measure.pi fun _ : ι => gaussianReal 0 1), f z ∈ Icc 0 1) :
    gaussianNoiseStability ρ f ≤
      gaussianQuadrant ρ (∫ z, f z ∂Measure.pi fun _ : ι => gaussianReal 0 1)
        (∫ z, f z ∂Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let g : (ι → ℝ) → ℝ := fun z => max 0 (min 1 (hf.mk f z))
  have hg : Measurable g := by
    have := hf.stronglyMeasurable_mk.measurable
    fun_prop
  have hfg : f =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] g := by
    filter_upwards [hf.ae_eq_mk, hf01] with z hz h01
    change f z = max 0 (min 1 (hf.mk f z))
    rw [← hz, min_eq_right h01.2, max_eq_right h01.1]
  have h1 := (measurePreserving_fst_correlatedGaussianPi ι ρ).quasiMeasurePreserving.ae_eq_comp hfg
  have h2 := (measurePreserving_snd_correlatedGaussianPi ι (abs_le.2 ⟨by linarith, hρ1⟩)
    ).quasiMeasurePreserving.ae_eq_comp hfg
  have hstab : gaussianNoiseStability ρ f = gaussianNoiseStability ρ g := by
    rw [gaussianNoiseStability, gaussianNoiseStability]
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with p hp1 hp2
    change f p.1 = g p.1 at hp1
    change f p.2 = g p.2 at hp2
    rw [hp1, hp2]
  rw [hstab, integral_congr_ae hfg]
  exact h.gaussianNoiseStability_le hρ0 hρ1 hg
    fun z => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- **Borell's Isoperimetric Theorem at volume `1 / 2`** from the Two-Function Borell inequality:
for `ρ ∈ [0, 1]` and measurable `f : ℝ^ι → [0, 1]` with `E f = 1 / 2`,
`Stab_ρ[f] ≤ 1 / 2 - arccos ρ / (2π)`. -/
theorem TwoFunctionBorellInequality.gaussianNoiseStability_le_of_integral_eq_half {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (h : TwoFunctionBorellInequality ρ ι) {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (hf01 : ∀ z, f z ∈ Icc 0 1)
    (hmean : ∫ z, f z ∂(Measure.pi fun _ : ι => gaussianReal 0 1) = 1 / 2) :
    gaussianNoiseStability ρ f ≤ 1 / 2 - arccos ρ / (2 * π) := by
  have := h.gaussianNoiseStability_le hρ0 hρ1 hf hf01
  rwa [hmean, gaussianQuadrant_half_half (abs_le.2 ⟨by linarith, hρ1⟩)] at this

omit [Fintype ι] in
private theorem measurableSet_setOf_cdf_le {h : (ι → ℝ) → ℝ} (hh : Measurable h) :
    MeasurableSet {w : ι ⊕ Unit → ℝ | Φ (w (.inr ())) ≤ h fun i => w (.inl i)} :=
  measurableSet_le ((measurable_cdf _).comp (measurable_pi_apply _)) (hh.comp (by fun_prop))

/-- The Gaussian volume of `{(z, t) | Φ t ≤ h z}` in `ℝ^ι × ℝ` is `E h`, for `h` with values in
`[0, 1]`. -/
private theorem measureReal_pi_gaussianReal_setOf_cdf_le {h : (ι → ℝ) → ℝ} (hh : Measurable h)
    (h01 : ∀ z, h z ∈ Icc 0 1) :
    (Measure.pi fun _ : ι ⊕ Unit => gaussianReal 0 1).real
        {w | Φ (w (.inr ())) ≤ h fun i => w (.inl i)} =
      ∫ z, h z ∂Measure.pi fun _ : ι => gaussianReal 0 1 := by
  have hS := measurableSet_setOf_cdf_le hh
  rw [← integral_indicator_one hS, integral_pi_gaussianReal_sum (measurable_one.indicator hS)
    (indicator_one_mem_Icc _)]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  have hT : MeasurableSet {x | Φ x ≤ h u} := measurable_cdf _ measurableSet_Iic
  change ∫ v, ((fun v : Unit → ℝ => v ()) ⁻¹' {x | Φ x ≤ h u}).indicator 1 v ∂_ = _
  have he : Measurable fun v : Unit → ℝ => v () := by fun_prop
  rw [integral_indicator_one (hT.preimage he), ← map_measureReal_apply he hT,
    (measurePreserving_eval _ ()).map_eq,
    measureReal_setOf_cdf_gaussianReal_le 0 one_ne_zero (h01 u).1 (h01 u).2]

/-- `E[Λ_ρ(f z, g z')]` is the probability that `ρ`-correlated `(ι ⊕ Unit)`-dimensional
Gaussians `((z, t), (z', t'))` have `Φ t ≤ f z` and `Φ t' ≤ g z'`. -/
private theorem integral_gaussianQuadrant_eq_measureReal_sum (ρ : ℝ) {f g : (ι → ℝ) → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    ∫ p, gaussianQuadrant ρ (f p.1) (g p.2) ∂correlatedGaussianPi ι ρ =
      (correlatedGaussianPi (ι ⊕ Unit) ρ).real
        ({w | Φ (w (.inr ())) ≤ f fun i => w (.inl i)} ×ˢ
          {w | Φ (w (.inr ())) ≤ g fun i => w (.inl i)}) := by
  have hS := (measurableSet_setOf_cdf_le hf).prod (measurableSet_setOf_cdf_le hg)
  rw [← integral_indicator_one hS, integral_correlatedGaussianPi_sum ρ
    (measurable_one.indicator hS) (indicator_one_mem_Icc _)]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  have hQ : MeasurableSet {q : ℝ × ℝ | Φ q.1 ≤ f p.1 ∧ Φ q.2 ≤ g p.2} :=
    ((measurable_cdf _ measurableSet_Iic).preimage measurable_fst).inter
      ((measurable_cdf _ measurableSet_Iic).preimage measurable_snd)
  change _ = ∫ r, ((fun r : (Unit → ℝ) × (Unit → ℝ) => (r.1 (), r.2 ())) ⁻¹'
    {q : ℝ × ℝ | Φ q.1 ≤ f p.1 ∧ Φ q.2 ≤ g p.2}).indicator 1 r ∂_
  rw [integral_indicator_one (hQ.preimage (by fun_prop)), ← map_measureReal_apply (by fun_prop) hQ,
    correlatedGaussianPi_map_eval]
  exact gaussianQuadrant_def ρ _ _

/-- **Two sets give two functions** [O'Donnell, Exercise 11.26 (b)][ODonnell2014]: the Two-Set
Borell inequality in the coordinates `ι ⊕ Unit` (dimension `n + 1`) gives the Two-Function Borell
inequality in the coordinates `ι` (dimension `n`). Apply it to the sets `{(z, t) | Φ t ≤ f z}`
and `{(z, t) | Φ t ≤ g z}`, of volumes `E f` and `E g`. -/
theorem TwoSetBorellInequality.twoFunctionBorellInequality {ρ : ℝ}
    (h : TwoSetBorellInequality ρ (ι ⊕ Unit)) : TwoFunctionBorellInequality ρ ι := by
  intro f g hf hg hf01 hg01
  rw [integral_gaussianQuadrant_eq_measureReal_sum ρ hf hg,
    ← measureReal_pi_gaussianReal_setOf_cdf_le hf hf01,
    ← measureReal_pi_gaussianReal_setOf_cdf_le hg hg01]
  exact h _ _ (measurableSet_setOf_cdf_le hf) (measurableSet_setOf_cdf_le hg)

/-- **Parallel halfspaces attain the Two-Set Borell bound**
[O'Donnell, Exercise 11.26][ODonnell2014]: for `a ≠ 0`, the parallel halfspaces
`H₁ = {z | a ⬝ᵥ z ≤ b₁}` and `H₂ = {z | a ⬝ᵥ z ≤ b₂}` have
`P[z ∈ H₁, z' ∈ H₂] = Λ_ρ(vol_γ H₁, vol_γ H₂)`. The book allows any `a`; for `a = 0` each set
is empty or everything, and equality is immediate. -/
theorem measureReal_correlatedGaussianPi_setOf_dotProduct_le_prod (ρ : ℝ) {a : ι → ℝ}
    (ha : a ≠ 0) (b₁ b₂ : ℝ) :
    (correlatedGaussianPi ι ρ).real ({z | a ⬝ᵥ z ≤ b₁} ×ˢ {z | a ⬝ᵥ z ≤ b₂}) =
      gaussianQuadrant ρ ((Measure.pi fun _ : ι => gaussianReal 0 1).real {z | a ⬝ᵥ z ≤ b₁})
        ((Measure.pi fun _ : ι => gaussianReal 0 1).real {z | a ⬝ᵥ z ≤ b₂}) := by
  have hc := sqrt_dotProduct_self_pos ha
  have hI : MeasurableSet (Iic b₁ ×ˢ Iic b₂) := measurableSet_Iic.prod measurableSet_Iic
  have hpre : {z | a ⬝ᵥ z ≤ b₁} ×ˢ {z | a ⬝ᵥ z ≤ b₂} =
      (fun p : (ι → ℝ) × (ι → ℝ) => (a ⬝ᵥ p.1, a ⬝ᵥ p.2)) ⁻¹' (Iic b₁ ×ˢ Iic b₂) := rfl
  rw [measureReal_pi_gaussianReal_setOf_dotProduct_le ha,
    measureReal_pi_gaussianReal_setOf_dotProduct_le ha, gaussianQuadrant_cdf_cdf, hpre,
    ← map_measureReal_apply (by fun_prop) hI, correlatedGaussianPi_map_dotProduct,
    map_measureReal_apply (by fun_prop) hI]
  congr 1
  ext p
  simp only [mem_preimage, mem_prod, mem_Iic, mem_ofPred_eq, le_div_iff₀ hc, mul_comm]

/-- **Equality for parallel halfspaces** [O'Donnell, Exercise 11.26 (c)][ODonnell2014]: the
indicators `f = 1_{H₁}`, `g = 1_{H₂}` of parallel halfspaces `H₁ = {z | a ⬝ᵥ z ≤ b₁}` and
`H₂ = {z | a ⬝ᵥ z ≤ b₂}`, for `a ≠ 0`, attain equality in the Two-Function Borell inequality:
`E[Λ_ρ(f z, g z')] = Λ_ρ(E f, E g)`. The book allows any `a`; for `a = 0` both indicators are
constant and equality is immediate. -/
theorem integral_gaussianQuadrant_indicator_setOf_dotProduct_le {ρ : ℝ} (hρ : |ρ| ≤ 1)
    {a : ι → ℝ} (ha : a ≠ 0) (b₁ b₂ : ℝ) :
    ∫ p, gaussianQuadrant ρ ({z | a ⬝ᵥ z ≤ b₁}.indicator 1 p.1)
        ({z | a ⬝ᵥ z ≤ b₂}.indicator 1 p.2) ∂correlatedGaussianPi ι ρ =
      gaussianQuadrant ρ
        (∫ z, {z | a ⬝ᵥ z ≤ b₁}.indicator 1 z ∂Measure.pi fun _ : ι => gaussianReal 0 1)
        (∫ z, {z | a ⬝ᵥ z ≤ b₂}.indicator 1 z ∂Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hH : ∀ b : ℝ, MeasurableSet {z : ι → ℝ | a ⬝ᵥ z ≤ b} := fun b =>
    measurableSet_le (by fun_prop) measurable_const
  rw [integral_gaussianQuadrant_indicator hρ (hH b₁) (hH b₂), integral_indicator_one (hH b₁),
    integral_indicator_one (hH b₂), measureReal_correlatedGaussianPi_setOf_dotProduct_le_prod ρ ha]

/-- **Equality for Gaussian cdfs of parallel affine functions**
[O'Donnell, Exercise 11.26 (c)][ODonnell2014]: `f z = Φ(a ⬝ᵥ z + b₁)` and
`g z = Φ(a ⬝ᵥ z + b₂)` attain equality in the Two-Function Borell inequality:
`E[Λ_ρ(f z, g z')] = Λ_ρ(E f, E g)`. In one more dimension the sets `{(z, t) | Φ t ≤ f z}` and
`{(z, t) | Φ t ≤ g z}` are parallel halfspaces. -/
theorem integral_gaussianQuadrant_cdf_dotProduct_add (ρ : ℝ) (a : ι → ℝ) (b₁ b₂ : ℝ) :
    ∫ p, gaussianQuadrant ρ (Φ (a ⬝ᵥ p.1 + b₁)) (Φ (a ⬝ᵥ p.2 + b₂)) ∂correlatedGaussianPi ι ρ =
      gaussianQuadrant ρ (∫ z, Φ (a ⬝ᵥ z + b₁) ∂Measure.pi fun _ : ι => gaussianReal 0 1)
        (∫ z, Φ (a ⬝ᵥ z + b₂) ∂Measure.pi fun _ : ι => gaussianReal 0 1) := by
  set c : ι ⊕ Unit → ℝ := Sum.elim (-a) 1
  have hc : c ≠ 0 := fun h => by simpa [c] using congrFun h (.inr ())
  have hm : ∀ b : ℝ, Measurable fun z : ι → ℝ => Φ (a ⬝ᵥ z + b) := fun b =>
    (measurable_cdf _).comp (by fun_prop)
  have h01 : ∀ (b : ℝ) (z : ι → ℝ), Φ (a ⬝ᵥ z + b) ∈ Icc 0 1 := fun b z =>
    ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
  have hset : ∀ b : ℝ, {w : ι ⊕ Unit → ℝ | Φ (w (.inr ())) ≤ Φ (a ⬝ᵥ (fun i => w (.inl i)) + b)} =
      {w | c ⬝ᵥ w ≤ b} := fun b => by
    ext w
    simp only [mem_ofPred_eq, (strictMono_cdf_gaussianReal 0 one_ne_zero).le_iff_le, dotProduct,
      Fintype.sum_sum_type, c, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, Pi.one_apply, neg_mul,
      Finset.sum_neg_distrib, Finset.univ_unique, Finset.sum_singleton, one_mul]
    constructor <;> intro h <;> linarith
  rw [integral_gaussianQuadrant_eq_measureReal_sum ρ (hm b₁) (hm b₂), hset, hset,
    measureReal_correlatedGaussianPi_setOf_dotProduct_le_prod ρ hc, ← hset, ← hset,
    measureReal_pi_gaussianReal_setOf_cdf_le (hm b₁) (h01 b₁),
    measureReal_pi_gaussianReal_setOf_cdf_le (hm b₂) (h01 b₂)]

/-! ### The cases `ρ = 0` and `ρ = 1` -/

/-- The Two-Function Borell inequality holds, with equality, at `ρ = 0`: then `z` and `z'` are
independent and `Λ_0(α, β) = αβ`. -/
theorem twoFunctionBorellInequality_zero (ι : Type*) [Fintype ι] :
    TwoFunctionBorellInequality 0 ι := by
  intro f g hf hg hf01 hg01
  have hC : correlatedGaussianPi ι 0 = (Measure.pi fun _ : ι => gaussianReal 0 1).prod
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    rw [correlatedGaussianPi_eq_map]
    simp only [zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_zero, sqrt_one, one_mul, Prod.mk.eta, Measure.map_id']
  have hEf := integral_mem_Icc (μ := Measure.pi fun _ : ι => gaussianReal 0 1) hf01
  have hEg := integral_mem_Icc (μ := Measure.pi fun _ : ι => gaussianReal 0 1) hg01
  rw [hC, gaussianQuadrant_zero hEf.1 hEf.2 hEg.1 hEg.2, ← integral_prod_mul]
  exact integral_mono_of_nonneg (ae_of_all _ fun p => gaussianQuadrant_nonneg _ _ _)
    (integrable_of_mem_Icc (by fun_prop) fun p =>
      ⟨mul_nonneg (hf01 _).1 (hg01 _).1, (mul_le_of_le_one_left (hg01 _).1 (hf01 _).2).trans
        (hg01 _).2⟩)
    (ae_of_all _ fun p => (gaussianQuadrant_zero (hf01 _).1 (hf01 _).2 (hg01 _).1
      (hg01 _).2).le)

/-- The Two-Function Borell inequality holds at `ρ = 1`: then `z' = z` and
`Λ_1(α, β) = min α β`, and `E[min (f z) (g z)] ≤ min (E f) (E g)`. -/
theorem twoFunctionBorellInequality_one (ι : Type*) [Fintype ι] :
    TwoFunctionBorellInequality 1 ι := by
  intro f g hf hg hf01 hg01
  have hEf := integral_mem_Icc (μ := Measure.pi fun _ : ι => gaussianReal 0 1) hf01
  have hEg := integral_mem_Icc (μ := Measure.pi fun _ : ι => gaussianReal 0 1) hg01
  have hint : ∀ {h : (ι → ℝ) → ℝ}, Measurable h → (∀ z, h z ∈ Icc 0 1) →
      Integrable h (Measure.pi fun _ : ι => gaussianReal 0 1) := fun hh h01 =>
    integrable_of_mem_Icc hh h01
  have hmin : ∀ z, min (f z) (g z) ∈ Icc 0 1 := fun z =>
    ⟨le_min (hf01 z).1 (hg01 z).1, (min_le_left _ _).trans (hf01 z).2⟩
  rw [correlatedGaussianPi_one, integral_map (by fun_prop)
    (Measurable.gaussianQuadrant (le_of_eq abs_one) (a := fun p : (ι → ℝ) × (ι → ℝ) => f p.1)
      (b := fun p => g p.2) (by fun_prop) (by fun_prop)).aestronglyMeasurable,
    gaussianQuadrant_one hEf.1 hEf.2 hEg.1]
  simp only [gaussianQuadrant_one (hf01 _).1 (hf01 _).2 (hg01 _).1]
  exact le_min (integral_mono (hint (by fun_prop) hmin) (hint hf hf01) fun z => min_le_left _ _)
    (integral_mono (hint (by fun_prop) hmin) (hint hg hg01) fun z => min_le_right _ _)

/-! ### The full reduction -/

/-- **The Two-Set Borell Isoperimetric Theorem from the line**
[O'Donnell, Exercises 11.26 (a) and 11.27][ODonnell2014]: the Two-Function Borell inequality on
the line gives the Two-Set Borell inequality in every finite dimension. -/
theorem TwoFunctionBorellInequality.twoSetBorellInequality_of_fin_one {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (h : TwoFunctionBorellInequality ρ (Fin 1)) (ι : Type*) [Fintype ι] :
    TwoSetBorellInequality ρ ι :=
  (h.of_fin_one hρ ι).twoSetBorellInequality hρ

/-- **Borell's Isoperimetric Theorem from the line**
[O'Donnell, Exercises 11.26 (a) and 11.27][ODonnell2014]: for `ρ ∈ [0, 1]`, the Two-Function
Borell inequality on the line gives `Stab_ρ[f] ≤ Λ_ρ(E f)` for every measurable
`f : ℝ^ι → [0, 1]` in every finite dimension. -/
theorem TwoFunctionBorellInequality.gaussianNoiseStability_le_of_fin_one {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (h : TwoFunctionBorellInequality ρ (Fin 1)) {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (hf01 : ∀ z, f z ∈ Icc 0 1) :
    gaussianNoiseStability ρ f ≤
      gaussianQuadrant ρ (∫ z, f z ∂Measure.pi fun _ : ι => gaussianReal 0 1)
        (∫ z, f z ∂Measure.pi fun _ : ι => gaussianReal 0 1) :=
  (h.of_fin_one (abs_le.2 ⟨by linarith, hρ1⟩) ι).gaussianNoiseStability_le hρ0 hρ1 hf hf01

end ProbabilityTheory
