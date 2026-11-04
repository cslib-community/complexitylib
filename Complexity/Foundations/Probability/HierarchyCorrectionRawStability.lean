/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyCorrectionStability
public import Complexity.Foundations.Probability.CorrectionRowRecipeStability
public import Complexity.Foundations.Probability.RootMetric.AbsoluteError
public import Complexity.Foundations.Probability.NormalizedAtomRows.MeanBias

/-!
# Changing raw and preparatory correction children

The actual hierarchy gates act on signed, unbounded raw tables. Constants are selected
at fixed hierarchy parameters, before finite domains, rates or child tables. Preparation
is averaged on its original joint source/usage slice. The integrated contract pays RAW
absolute row moments with explicit width squared and inverse-rate fourth powers, PREP
source/usage row moments through conditional Jensen, and the ordinary maximum error.

This is an original local accuracy contract. Pilot recipe moments are supplied separately
in `PilotRowStability`. A well-founded approximate evaluator, allocated recursive fragments
and closure, parameter/workspace growth and native RL=L remain open.

## Main results

* `Matrix.FourthRootHierarchyParams.correction_preparation_stability_constants`:
  changing completed RAW children in actual incoming preparation.
* `Matrix.FourthRootHierarchyParams.correction_preparation_row_moment`:
  pre-walk preparation payment from the actual RAW moment.
* `Matrix.FourthRootHierarchyParams.normalized_raw_normalizer_root_stability`:
  decoder stability charged directly to its joint normalizer.
* `Matrix.HierarchyParams.H4RankEnvironment.correctionRequest_children_root_stability`:
  pointwise changes to RAW, PREP and maximum children.
* `Matrix.HierarchyParams.H4RankEnvironment.correctionRequest_children_root_moment`:
  integrated payment by the original masked child row errors.
-/
public section
noncomputable section
namespace Matrix.FourthRootHierarchyParams
open Finset Cslib
open scoped BigOperators

/-- Ordinary auxiliary-score regularity follows from its bounded root regularity.
The bound is global in both signed raw arguments. -/
theorem auxiliary_stability_constants (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ LI : ℝ, 0 ≤ LI ∧ ∀ v q v' q',
      |polynomialAuxCutoff4 HP.θ v q - polynomialAuxCutoff4 HP.θ v' q'| ≤
        LI * (|v - v'| + |q - q'|) := by
  obtain ⟨L, hL, hroot⟩ := exists_abs_polynomialAuxCutoff4_root_sub_le HP.θ
  refine ⟨4 * L, by positivity, ?_⟩
  intro v q v' q'
  have h := abs_sub_le_mul_abs_rpow_inv_sub (s := 4) (by decide)
    (polynomialAuxCutoff4_nonneg HP.θ v q) (polynomialAuxCutoff4_nonneg HP.θ v' q')
    (polynomialAuxCutoff4_le_one HP.θ v q) (polynomialAuxCutoff4_le_one HP.θ v' q')
  norm_num only [Nat.cast_ofNat, Real.one_rpow, mul_one] at h
  calc
    _ ≤ 4 * |polynomialAuxCutoff4 HP.θ v q ^ (4⁻¹ : ℝ) -
        polynomialAuxCutoff4 HP.θ v' q' ^ (4⁻¹ : ℝ)| := by simpa only [one_div] using h
    _ ≤ 4 * (L * (|v - v'| + |q - q'|)) :=
      mul_le_mul_of_nonneg_left (hroot v q v' q') (by norm_num)
    _ = _ := by ring

/-- Root regularity of the actual incoming gate composed with both unchanged rank sets. -/
theorem incoming_root_stability_constants (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ LI Lτ : ℝ, 0 ≤ LI ∧ 0 ≤ Lτ ∧
    ∀ (V : Type*) (Kc : ℕ), 0 < Kc → ∀ (f : ℝ), 0 < f →
    ∀ (A B : Matrix V V ℝ) (S T : Finset V) (y : V) (Ec Er : ℝ),
    0 ≤ Ec → 0 ≤ Er →
    (∀ x ∈ S, |A x y - B x y| ≤ Ec) →
    (∀ x ∈ S, kthLargest 1 T (fun w => |A x w - B x w|) ≤ Er) →
    |incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f A S T y ^
        (4⁻¹ : ℝ) -
      incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f B S T y ^
        (4⁻¹ : ℝ)| ≤ Lτ * (LI * (Ec + Er) / f) := by
  obtain ⟨LI, hLI, hI⟩ := HP.auxiliary_stability_constants
  obtain ⟨Lτ, hτ⟩ := HP.incomingCutoff_root
  refine ⟨LI, Lτ, hLI, Lτ.coe_nonneg, ?_⟩
  intro V Kc hKc f hf A B S T y Ec Er hEc hEr hc hr
  exact incomingGate_stability hLI Lτ.coe_nonneg hI
    (fun a b => by simpa only [Real.dist_eq] using hτ.dist_le_mul a b)
    (NormalizedRow.rank_pos HP) hKc hf A B S T y hEc hEr hc hr

/-- The selected actual correction preparation responds to changing signed raw children.
Both ranks retain the original source and terminal sets. The same estimate is usable
by actual correction and pilot preparation clients. -/
theorem correction_preparation_stability_constants
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Lh Lρ LI Lτ : ℝ, 0 ≤ Lh ∧ 0 ≤ Lρ ∧ 0 ≤ LI ∧ 0 ≤ Lτ ∧
    ∀ (V : Type*) (Kc : ℕ), 0 < Kc → ∀ (f : ℝ), 0 < f →
    ∀ (A B : Matrix V V ℝ) (S T : Finset V) (x y : V) (Ec Er : ℝ),
    0 ≤ Ec → 0 ≤ Er →
    (∀ z ∈ S, |A z y - B z y| ≤ Ec) →
    (∀ z ∈ S, kthLargest 1 T (fun w => |A z w - B z w|) ≤ Er) →
    |correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f A
        (polynomialPrepCutoff4 HP.θ) HP.ρ S T x y -
      correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f B
        (polynomialPrepCutoff4 HP.θ) HP.ρ S T x y| ≤
      (Lh * |A x y - B x y| + Lρ * kthLargest 1 T (fun w => |A x w - B x w|)) / f +
        Lτ * (LI * (Ec + Er) / f) := by
  obtain ⟨Lh, Lρ, hLh, hLρ, hh, hρ⟩ :=
    HierarchyParams.H4RankEnvironment.NormalizedMoments.preparation_stability_constants HP
  obtain ⟨LI, hLI, hI⟩ := HP.auxiliary_stability_constants
  obtain ⟨Lτ, hτ⟩ := HP.incomingCutoff_root
  refine ⟨Lh, Lρ, LI, 4 * Lτ, hLh, hLρ, hLI, by positivity, ?_⟩
  intro V Kc hKc f hf A B S T x y Ec Er hEc hEr hc hr
  exact correctionPrep_stability hLI (by positivity) hLρ
    (fun z => ⟨polynomialPrepCutoff4_nonneg _ _, polynomialPrepCutoff4_le_one _ _⟩)
    (fun z => ⟨HP.ρ_nonneg z, HP.ρ_le_one z⟩)
    (fun z => ⟨HP.incomingCutoff_nonneg z, HP.incomingCutoff_le_one z⟩) hI
    (abs_sub_le_four_mul_root_lipschitz
      (fun z => ⟨HP.incomingCutoff_nonneg z, HP.incomingCutoff_le_one z⟩) hτ)
    hh hρ (NormalizedRow.rank_pos HP) hKc hf A B S T x y hEc hEr hc hr

/-- The pre-walk incoming preparation is paid entirely by actual RAW error.
A full source by terminal maximum incurs the explicit width squared and inverse-rate
fourth power. No environment atom or pointwise convergence of walked PREP is used. -/
theorem correction_preparation_row_moment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧
    ∀ (Ω V : Type*) [Fintype Ω] [Fintype V]
      (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
      (Kc : ℕ), 0 < Kc → ∀ f : ℝ, 0 < f →
    ∀ (A B : Ω → Matrix V V ℝ) (N u : ℝ), 0 ≤ N * u →
    rowNormPow 4 N u X Y (fun σ x y =>
      correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f (A σ)
        (polynomialPrepCutoff4 HP.θ) HP.ρ {z | X σ z} {w | Y σ w} x y -
      correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f (B σ)
        (polynomialPrepCutoff4 HP.θ) HP.ρ {z | X σ z} {w | Y σ w} x y) ≤
      (L / f) ^ 4 * (Fintype.card V : ℝ) ^ 2 *
        rowNormPow 4 N u X Y (fun σ x y => A σ x y - B σ x y) := by
  obtain ⟨Lh, Lρ, LI, Lτ, hh, hρ, hi, ht, h⟩ :=
    HP.correction_preparation_stability_constants
  let L := Lh + Lρ + 2 * Lτ * LI
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro Ω V instΩ instV X Y instX instY Kc hKc f hf A B N u hNu
  classical
  let E := fun σ => kthLargest 1 {z | X σ z} (fun z =>
    kthLargest 1 {w | Y σ w} (fun w => |A σ z w - B σ z w|))
  have hE (σ : Ω) : 0 ≤ E σ := kthLargest_nonneg
  have he (σ : Ω) (z : V) (hz : X σ z) :
      kthLargest 1 {w | Y σ w} (fun w => |A σ z w - B σ z w|) ≤ E σ := by
    have hh := abs_le_kthLargest_one {z | X σ z}
      (fun z => kthLargest 1 {w | Y σ w} (fun w => |A σ z w - B σ z w|)) z
      (mem_filter.mpr ⟨mem_univ _, hz⟩)
    simpa only [abs_of_nonneg (kthLargest_nonneg (k := 1))] using hh
  have hb (σ : Ω) (x y : V) (hx : X σ x) (hy : Y σ y) :
      |correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f (A σ)
          (polynomialPrepCutoff4 HP.θ) HP.ρ {z | X σ z} {w | Y σ w} x y -
        correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f (B σ)
          (polynomialPrepCutoff4 HP.θ) HP.ρ {z | X σ z} {w | Y σ w} x y| ≤
        (L / f) * E σ := by
    have hc (z : V) (hz : X σ z) : |A σ z y - B σ z y| ≤ E σ :=
      (abs_le_kthLargest_one {w | Y σ w} (fun w => A σ z w - B σ z w) y
        (mem_filter.mpr ⟨mem_univ _, hy⟩)).trans (he σ z hz)
    have hp := h V Kc hKc f hf (A σ) (B σ) {z | X σ z} {w | Y σ w}
      x y (E σ) (E σ) (hE σ) (hE σ)
      (fun z hz => hc z (mem_filter.mp hz).2)
      (fun z hz => he σ z (mem_filter.mp hz).2)
    apply hp.trans
    calc
      _ ≤ (Lh * E σ + Lρ * E σ) / f + Lτ * (LI * (E σ + E σ) / f) := by
        gcongr
        · exact hc x hx
        · exact he σ x hx
      _ = _ := by dsimp only [L]; ring
  have hp := rowNormPow_le_mul (X := X) (Y := Y) (s := 4) hNu
    (c := (L / f) ^ 4) (Z' := fun σ _ _ => E σ) (fun σ x y hx hy => by
      have hh := pow_le_pow_left₀ (abs_nonneg _) (hb σ x y hx hy) 4
      simpa only [mul_pow, abs_of_nonneg (hE σ)] using hh)
  exact hp.trans ((mul_le_mul_of_nonneg_left
    (rowNormPow_rectangle_max_le (X := X) (Y := Y) hNu
      (fun σ x y => A σ x y - B σ x y)) (pow_nonneg (div_nonneg hL hf.le) 4)).trans_eq
        (by ring))

private lemma root_product_dist {a a' b b' c B : ℝ}
    (ha' : a' ∈ Set.Icc 0 B) (hb : b ∈ Set.Icc 0 1)
    (hc : c ∈ Set.Icc 0 1) :
    |a * b * c - a' * b' * c| ≤ |a - a'| + B * |b - b'| := by
  have he : a * b * c - a' * b' * c = ((a-a')*b + a'*(b-b'))*c := by ring
  rw [he, abs_mul, abs_of_nonneg hc.1]
  apply (mul_le_of_le_one_right (abs_nonneg _) hc.2).trans
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg hb.1, abs_of_nonneg ha'.1]
  exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hb.2)
    (mul_le_mul_of_nonneg_right ha'.2 (abs_nonneg _))

/-- Changing RAW and the literal joint normalizer in a normalized correction.
Only the difference of conditional means is charged; no pointwise PREP approximation
is needed. The original incoming ranks and clipped denominator are preserved. -/
theorem normalized_raw_normalizer_root_stability
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ C LI Lτ : ℝ, 0 ≤ C ∧ 0 ≤ LI ∧ 0 ≤ Lτ ∧
    ∀ (V Γ Ζ : Type*) [Fintype V] [Fintype Γ] [Fintype Ζ]
      (Xs : Γ → V → Prop) (Z Zt : Ζ → V → Prop)
      [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Z t v)]
      [∀ t v, Decidable (Zt t v)]
      (Kc : ℕ), 0 < Kc → ∀ (f : ℝ), 0 < f →
    ∀ (A B : Matrix V V ℝ) (prep prep' : Γ × Ζ → Matrix V V ℝ)
      (maximum : V → ℝ) (σ : Γ × Ζ) (x y : V) (Ec Er : ℝ),
    0 ≤ Ec → 0 ≤ Er →
    (∀ z ∈ ({w | Xs σ.1 w} : Finset V), |A z y - B z y| ≤ Ec) →
    (∀ z ∈ ({w | Xs σ.1 w} : Finset V),
      kthLargest 1 {w | Z σ.2 w} (fun w => |A z w - B z w|) ≤ Er) →
    |CorrectionRowRecipe.normalized (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc f Xs Z Zt A prep maximum σ x y ^
        (4⁻¹ : ℝ) -
      CorrectionRowRecipe.normalized (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc f Xs Z Zt B prep' maximum σ x y ^
        (4⁻¹ : ℝ)| ≤
    C * (|A x y - B x y| / f +
      |CorrectionRowRecipe.normalizer Xs Zt prep x y -
        CorrectionRowRecipe.normalizer Xs Zt prep' x y| +
      kthLargest 1 {w | Z σ.2 w} (fun w => |A x w - B x w|) / f) +
    (2 * HP.Q HP.toHierarchyParams.atomCap) ^ (4⁻¹ : ℝ) *
      (Lτ * (LI * (Ec + Er) / f)) := by
  obtain ⟨C, hC, hdist⟩ := NormalizedRow.root_dist HP (by norm_num : (0:ℝ) < 1)
  obtain ⟨LI, Lτ, hLI, hLτ, hi⟩ := HP.incoming_root_stability_constants
  refine ⟨C, LI, Lτ, hC, hLI, hLτ, ?_⟩
  intro V Γ Ζ instV instΓ instΖ Xs Z Zt instXs instZ instZt Kc hKc f hf
    A B prep prep' maximum σ x y Ec Er hEc hEr hc hr
  classical
  by_cases hy : Zt σ.2 y
  · let S : Finset V := {w | Xs σ.1 w}
    let T : Finset V := {w | Z σ.2 w}
    let qA := kthLargest HP.K T (fun w => A x w / f)
    let qB := kthLargest HP.K T (fun w => B x w / f)
    let mA := CorrectionRowRecipe.normalizer Xs Zt prep x y
    let mB := CorrectionRowRecipe.normalizer Xs Zt prep' x y
    let OA := NormalizedRow.output HP 1 (A x y / f) mA qA
    let OB := NormalizedRow.output HP 1 (B x y / f) mB qB
    let IA := incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f A S T y
    let IB := incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f B S T y
    have hoA : 0 ≤ OA := NormalizedRow.output_nonneg HP _ _ _ _
    have hoB : 0 ≤ OB := NormalizedRow.output_nonneg HP _ _ _ _
    have hiA : 0 ≤ IA := HP.incomingCutoff_nonneg _
    have hiB : 0 ≤ IB := HP.incomingCutoff_nonneg _
    have hg : 0 ≤ HP.γ (maximum y) := HP.γ_nonneg _
    have hq : |qA - qB| ≤ kthLargest 1 T (fun w => |A x w - B x w|) / f :=
      abs_kthLargest_div_sub_div_le (NormalizedRow.rank_pos HP) hf T (A x) (B x)
    have hd := hdist (A x y / f) mA qA (B x y / f) mB qB
    rw [← sub_div, abs_div, abs_of_pos hf] at hd
    have hd' := hd.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl hq) hC)
    rw [CorrectionRowRecipe.normalized_factorization HP _ _ _ _ _ _ _ _ _ _ _ _ _ hy,
      CorrectionRowRecipe.normalized_factorization HP _ _ _ _ _ _ _ _ _ _ _ _ _ hy]
    change |(OA * IA * HP.γ (maximum y)) ^ (4⁻¹ : ℝ) -
      (OB * IB * HP.γ (maximum y)) ^ (4⁻¹ : ℝ)| ≤ _
    rw [Real.mul_rpow (mul_nonneg hoA hiA) hg, Real.mul_rpow hoA hiA,
      Real.mul_rpow (mul_nonneg hoB hiB) hg, Real.mul_rpow hoB hiB]
    apply (root_product_dist
      ⟨Real.rpow_nonneg hoB _, Real.rpow_le_rpow hoB
        (NormalizedRow.output_le HP _ _ _ _) (by norm_num)⟩
      ⟨Real.rpow_nonneg hiA _, Real.rpow_le_one hiA (HP.incomingCutoff_le_one _)
        (by norm_num)⟩
      ⟨Real.rpow_nonneg hg _, Real.rpow_le_one hg (HP.γ_le_one _) (by norm_num)⟩).trans
    exact add_le_add hd' (mul_le_mul_of_nonneg_left
      (hi V Kc hKc f hf A B S T y Ec Er hEc hEr hc hr)
      (Real.rpow_nonneg (mul_nonneg (by norm_num) (HP.Q_nonneg _)) _))
  · simp only [CorrectionRowRecipe.normalized, hy, ↓reduceIte, sub_self, abs_zero]
    have hq : 0 ≤ kthLargest 1 {w | Z σ.2 w} (fun w => |A x w - B x w|) :=
      kthLargest_nonneg
    have hB := HP.Q_nonneg HP.toHierarchyParams.atomCap
    positivity

/-- Optional coarse corollary charging mean pointwise preparation differences.
Use `normalized_raw_normalizer_root_stability` when only the joint mean matters;
walked preparation need not approach its true input pointwise. -/
theorem normalized_raw_prep_root_stability
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ C LI Lτ : ℝ, 0 ≤ C ∧ 0 ≤ LI ∧ 0 ≤ Lτ ∧
    ∀ (V Γ Ζ : Type*) [Fintype V] [Fintype Γ] [Fintype Ζ]
      (Xs : Γ → V → Prop) (Z Zt : Ζ → V → Prop)
      [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Z t v)]
      [∀ t v, Decidable (Zt t v)]
      (Kc : ℕ), 0 < Kc → ∀ (f : ℝ), 0 < f →
    ∀ (A B : Matrix V V ℝ) (prep prep' : Γ × Ζ → Matrix V V ℝ)
      (maximum : V → ℝ) (σ : Γ × Ζ) (x y : V) (Ec Er : ℝ),
    0 ≤ Ec → 0 ≤ Er →
    (∀ z ∈ ({w | Xs σ.1 w} : Finset V), |A z y - B z y| ≤ Ec) →
    (∀ z ∈ ({w | Xs σ.1 w} : Finset V),
      kthLargest 1 {w | Z σ.2 w} (fun w => |A z w - B z w|) ≤ Er) →
    |CorrectionRowRecipe.normalized (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc f Xs Z Zt A prep maximum σ x y ^
        (4⁻¹ : ℝ) -
      CorrectionRowRecipe.normalized (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc f Xs Z Zt B prep' maximum σ x y ^
        (4⁻¹ : ℝ)| ≤
    C * (|A x y - B x y| / f +
      (𝔼 p ∈ ({s | Xs s x} : Finset Γ) ×ˢ ({t | Zt t y} : Finset Ζ),
        |prep p x y - prep' p x y|) +
      kthLargest 1 {w | Z σ.2 w} (fun w => |A x w - B x w|) / f) +
    (2 * HP.Q HP.toHierarchyParams.atomCap) ^ (4⁻¹ : ℝ) *
      (Lτ * (LI * (Ec + Er) / f)) := by
  obtain ⟨C, LI, Lτ, hC, hLI, hLτ, h⟩ := HP.normalized_raw_normalizer_root_stability
  refine ⟨C, LI, Lτ, hC, hLI, hLτ, ?_⟩
  intro V Γ Ζ instV instΓ instΖ Xs Z Zt instXs instZ instZt Kc hKc f hf
    A B prep prep' maximum σ x y Ec Er hEc hEr hc hr
  have hb := h V Γ Ζ Xs Z Zt Kc hKc f hf A B prep prep' maximum σ x y
    Ec Er hEc hEr hc hr
  have hm := CorrectionRowRecipe.normalizer_stability Xs Zt prep prep' x y
  exact hb.trans (add_le_add (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl hm) le_rfl) hC) le_rfl)

end Matrix.FourthRootHierarchyParams

namespace Matrix.HierarchyParams.H4RankEnvironment
open Finset Cslib Cslib.Probability
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime] {V : Type*} [Fintype V]

/-- All changing children of the actual request are controlled on the original shared
rank environment. The displayed preparation mean is its literal joint normalizer,
including all spectator roles and inherited suffixes. Constants precede every request. -/
theorem correctionRequest_children_root_stability_of_bounds
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ C LI Lτ Lγ : ℝ, 0 ≤ C ∧ 0 ≤ LI ∧ 0 ≤ Lτ ∧ 0 ≤ Lγ ∧
    ∀ (P J : ℕ) [Fact P.Prime] (V : Type*) [Fintype V] (k : ℕ)
      (D : ZMod P) (ident : V → ZMod P)
      (r : HierarchyTask.Request k (Fin J) (ZMod P)) (hr : Admissible r),
    0 < r.terminal.rate → ∀ (Kc : ℕ), 0 < Kc →
    ∀ (raw raw' prep prep' : Environment P J → Matrix V V ℝ)
      (maximum maximum' : Environment P J → V → ℝ)
      (σ : Environment P J) (x y : V) (Ec Er : ℝ),
    let split := Equiv.piSplitAt r.terminal.role (fun _ : Fin J => FrameChannel P 4 1)
    let S : Finset V := {z | coordinate D r.source
      ((split σ).2 ⟨r.source.role, hr.1⟩) (ident z)}
    let T : Finset V := {z | coordinate D r.terminal (split σ).1 (ident z)}
    0 ≤ Ec → 0 ≤ Er →
    (∀ z ∈ S, |raw σ z y - raw' σ z y| ≤ Ec) →
    (∀ z ∈ S, kthLargest 1 T (fun w => |raw σ z w - raw' σ z w|) ≤ Er) →
    |correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum σ x y ^ (4⁻¹ : ℝ) -
      correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw' prep' maximum' σ x y ^ (4⁻¹ : ℝ)| ≤
    C * (|raw σ x y - raw' σ x y| / r.terminal.rate +
      rowSliceMean (fun τ z => r.source.retains (channels D) τ (ident z))
        (fun τ z => r.usage.retains (channels D) τ (ident z))
        (fun τ a b => |prep τ a b - prep' τ a b|) x y +
      kthLargest 1 T (fun w => |raw σ x w - raw' σ x w|) / r.terminal.rate) +
    (2 * HP.Q HP.toHierarchyParams.atomCap) ^ (4⁻¹ : ℝ) *
      (Lτ * (LI * (Ec + Er) / r.terminal.rate)) +
    (2 * HP.Q HP.toHierarchyParams.atomCap) ^ (4⁻¹ : ℝ) * Lγ *
      |maximum σ y - maximum' σ y| := by
  obtain ⟨C, LI, Lτ, hC, hLI, hLτ, hraw⟩ := HP.normalized_raw_prep_root_stability
  obtain ⟨Lγ, hLγ, hmax⟩ := correctionRequest_maximum_root_stability HP
  refine ⟨C, LI, Lτ, Lγ, hC, hLI, hLτ, hLγ, ?_⟩
  intro P J instP V instV k D ident r hr hf Kc hKc raw raw' prep prep'
    maximum maximum' σ x y Ec Er
  dsimp only
  intro hEc hEr hc hrank
  have hd := hraw V _ _
    (fun rest z => coordinate D r.source (rest ⟨r.source.role, hr.1⟩) (ident z))
    (fun A z => coordinate D r.terminal A (ident z))
    (fun A z => coordinate D r.usage A (ident z)) Kc hKc r.terminal.rate hf
    (raw σ) (raw' σ)
    (fun p => prep ((Equiv.piSplitAt r.terminal.role
      (fun _ : Fin J => FrameChannel P 4 1)).symm (p.2, p.1)))
    (fun p => prep' ((Equiv.piSplitAt r.terminal.role
      (fun _ : Fin J => FrameChannel P 4 1)).symm (p.2, p.1)))
    (maximum σ) (((Equiv.piSplitAt r.terminal.role
      (fun _ : Fin J => FrameChannel P 4 1)) σ).2,
      ((Equiv.piSplitAt r.terminal.role (fun _ : Fin J => FrameChannel P 4 1)) σ).1)
    x y Ec Er hEc hEr hc hrank
  have he := normalizer_full D ident r hr (fun τ a b => |prep τ a b - prep' τ a b|) x y
  dsimp only [CorrectionRowRecipe.normalizer] at he
  rw [he] at hd
  have hm := hmax P J V k D ident r Kc raw' prep' maximum maximum' σ x y
  simp only [correctionRequest, dite_eq_left hr] at hm ⊢
  exact (abs_sub_le _ _ _).trans (add_le_add hd hm)

/-- Explicit entry, row, column and full source by terminal maximum bound for all
three changing child classes, with no supplied raw-error envelope. -/
theorem correctionRequest_children_root_stability
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ C LI Lτ Lγ : ℝ, 0 ≤ C ∧ 0 ≤ LI ∧ 0 ≤ Lτ ∧ 0 ≤ Lγ ∧
    ∀ (P J : ℕ) [Fact P.Prime] (V : Type*) [Fintype V] (k : ℕ)
      (D : ZMod P) (ident : V → ZMod P)
      (r : HierarchyTask.Request k (Fin J) (ZMod P)) (hr : Admissible r),
    0 < r.terminal.rate → ∀ (Kc : ℕ), 0 < Kc →
    ∀ (raw raw' prep prep' : Environment P J → Matrix V V ℝ)
      (maximum maximum' : Environment P J → V → ℝ)
      (σ : Environment P J) (x y : V),
    let split := Equiv.piSplitAt r.terminal.role (fun _ : Fin J => FrameChannel P 4 1)
    let S : Finset V := {z | coordinate D r.source
      ((split σ).2 ⟨r.source.role, hr.1⟩) (ident z)}
    let T : Finset V := {z | coordinate D r.terminal (split σ).1 (ident z)}
    let Ec := kthLargest 1 S (fun z => |raw σ z y - raw' σ z y|)
    let Er := kthLargest 1 S (fun z =>
      kthLargest 1 T (fun w => |raw σ z w - raw' σ z w|))
    |correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum σ x y ^ (4⁻¹ : ℝ) -
      correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw' prep' maximum' σ x y ^ (4⁻¹ : ℝ)| ≤
    C * (|raw σ x y - raw' σ x y| / r.terminal.rate +
      rowSliceMean (fun τ z => r.source.retains (channels D) τ (ident z))
        (fun τ z => r.usage.retains (channels D) τ (ident z))
        (fun τ a b => |prep τ a b - prep' τ a b|) x y +
      kthLargest 1 T (fun w => |raw σ x w - raw' σ x w|) / r.terminal.rate) +
    (2 * HP.Q HP.toHierarchyParams.atomCap) ^ (4⁻¹ : ℝ) *
      (Lτ * (LI * (Ec + Er) / r.terminal.rate)) +
    (2 * HP.Q HP.toHierarchyParams.atomCap) ^ (4⁻¹ : ℝ) * Lγ *
      |maximum σ y - maximum' σ y| := by
  obtain ⟨C, LI, Lτ, Lγ, hC, hLI, hLτ, hLγ, hd⟩ :=
    correctionRequest_children_root_stability_of_bounds HP
  refine ⟨C, LI, Lτ, Lγ, hC, hLI, hLτ, hLγ, ?_⟩
  intro P J instP V instV k D ident r hr hf Kc hKc raw raw' prep prep'
    maximum maximum' σ x y
  dsimp only
  apply hd P J V k D ident r hr hf Kc hKc raw raw' prep prep' maximum maximum' σ x y
    _ _ kthLargest_nonneg kthLargest_nonneg
  · intro z hz
    exact abs_le_kthLargest_one _ (fun z => raw σ z y - raw' σ z y) z hz
  · intro z hz
    let T : Finset V := {w | coordinate D r.terminal
      ((Equiv.piSplitAt r.terminal.role (fun _ : Fin J => FrameChannel P 4 1)) σ).1 (ident w)}
    have h := abs_le_kthLargest_one _
      (fun z => kthLargest 1 T (fun w => |raw σ z w - raw' σ z w|)) z hz
    simpa only [abs_of_nonneg (kthLargest_nonneg (k := 1))] using h

private lemma error_sum_bound {C B LI Lτ Lγ f d q e m z : ℝ}
    (hC : 0 ≤ C) (hf : 0 < f) (hd : d ≤ e) (hq : q ≤ e) :
    C * (d / f + m + q / f) + B * (Lτ * (LI * (e + e) / f)) + B * Lγ * z ≤
      (2 * (C + B * Lτ * LI) / f) * e + C * m + (B * Lγ) * z := by
  calc
    _ ≤ C * (e / f + m + e / f) + B * (Lτ * (LI * (e + e) / f)) + B * Lγ * z :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (div_le_div_of_nonneg_right hd hf.le) le_rfl)
          (div_le_div_of_nonneg_right hq hf.le)) hC) le_rfl) le_rfl
    _ = _ := by ring

private lemma source_rank_set {k : ℕ} (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (hr : Admissible r)
    (σ : Environment P J) :
    ({z | coordinate D r.source
      (((Equiv.piSplitAt r.terminal.role (fun _ : Fin J => FrameChannel P 4 1)) σ).2
        ⟨r.source.role, hr.1⟩) (ident z)} : Finset V) =
      ({z | r.source.retains (channels D) σ (ident z)} : Finset V) := by
  ext z
  simp [Equiv.piSplitAt_apply, coordinate, CorrectionRowTask.Channel.retains,
    channels]

private lemma terminal_rank_set {k : ℕ} (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (σ : Environment P J) :
    ({z | coordinate D r.terminal
      ((Equiv.piSplitAt r.terminal.role (fun _ : Fin J => FrameChannel P 4 1)) σ).1
      (ident z)} : Finset V) =
      ({z | r.terminal.retains (channels D) σ (ident z)} : Finset V) := by
  ext z
  simp [Equiv.piSplitAt_apply, coordinate, CorrectionRowTask.Channel.retains,
    channels]

private lemma children_root_zero {k : ℕ}
    (D : ZMod P) (ident : V → ZMod P) (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (I : ℝ → ℝ → ℝ) (τ ρ Q γ : ℝ → ℝ) (K Kc : ℕ)
    (raw raw' prep prep' : Environment P J → Matrix V V ℝ)
    (maximum maximum' : Environment P J → V → ℝ) (σ : Environment P J) (x y : V)
    (hy : ¬ r.usage.retains (channels D) σ (ident y)) :
    |correctionRequest D ident r I τ ρ Q γ K Kc raw prep maximum σ x y ^ (4⁻¹ : ℝ) -
      correctionRequest D ident r I τ ρ Q γ K Kc raw' prep' maximum' σ x y ^ (4⁻¹ : ℝ)| = 0 := by
  unfold correctionRequest
  split_ifs with hr
  · have ht : ¬ coordinate D r.usage (σ r.terminal.role) (ident y) := by
      simpa only [coordinate, CorrectionRowTask.Channel.retains, channels, hr.2.1] using hy
    simp only [Equiv.piSplitAt_apply, CorrectionRowRecipe.normalized, ht, ↓reduceIte,
      sub_self, abs_zero]
  · simp only [sub_self, abs_zero]


set_option backward.isDefEq.respectTransparency false in
/-- A coarser pointwise envelope for integration, on the original full rank rectangle.
The sharper entry/row/column terms remain in `correctionRequest_children_root_stability`. -/
theorem correctionRequest_children_root_envelope
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Cr Cp Cm : ℝ, 0 ≤ Cr ∧ 0 ≤ Cp ∧ 0 ≤ Cm ∧
    ∀ (P J : ℕ) [Fact P.Prime] (V : Type*) [Fintype V] (k : ℕ)
      (D : ZMod P) (ident : V → ZMod P)
      (r : HierarchyTask.Request k (Fin J) (ZMod P)) (_hr : Admissible r),
    0 < r.terminal.rate → ∀ (Kc : ℕ), 0 < Kc →
    ∀ (raw raw' prep prep' : Environment P J → Matrix V V ℝ)
      (maximum maximum' : Environment P J → V → ℝ) (σ : Environment P J) (x y : V),
    let X := fun τ a => r.source.retains (channels D) τ (ident a)
    let Y := fun τ b => r.terminal.retains (channels D) τ (ident b)
    let U := fun τ b => r.usage.retains (channels D) τ (ident b)
    X σ x → Y σ y →
    |correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum σ x y ^ (4⁻¹ : ℝ) -
      correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw' prep' maximum' σ x y ^ (4⁻¹ : ℝ)| ≤
    (Cr / r.terminal.rate) * kthLargest 1 {z | X σ z} (fun z =>
      kthLargest 1 {w | Y σ w} (fun w => |raw σ z w - raw' σ z w|)) +
    Cp * (if U σ y then rowSliceMean X U
      (fun τ a b => |prep τ a b - prep' τ a b|) x y else 0) +
    Cm * |maximum σ y - maximum' σ y| := by
  obtain ⟨C, LI, Lτ, Lγ, hC, hLI, hLτ, hLγ, hd⟩ :=
    correctionRequest_children_root_stability_of_bounds HP
  let B := (2 * HP.Q HP.toHierarchyParams.atomCap) ^ (4⁻¹ : ℝ)
  have hB : 0 ≤ B := Real.rpow_nonneg (mul_nonneg (by norm_num) (HP.Q_nonneg _)) _
  let Cr := 2 * (C + B * Lτ * LI)
  let Cm := B * Lγ
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hCm : 0 ≤ Cm := mul_nonneg hB hLγ
  refine ⟨Cr, C, Cm, hCr, hC, hCm, ?_⟩
  intro P J instP V instV k D ident r hr hf Kc hKc raw raw' prep prep'
    maximum maximum' σ x y
  dsimp only
  intro hx hy
  specialize hd P J V k D ident r hr hf Kc hKc raw raw' prep prep' maximum maximum'
  change r.source.role ≠ r.terminal.role ∧ r.usage.role = r.terminal.role ∧
    r.usage.suffix = r.terminal.suffix at hr
  let X := fun σ x => r.source.retains (channels D) σ (ident x)
  let Y := fun σ y => r.terminal.retains (channels D) σ (ident y)
  let U := fun σ y => r.usage.retains (channels D) σ (ident y)
  let E := fun σ => kthLargest 1 {z | X σ z} (fun z =>
    kthLargest 1 {w | Y σ w} (fun w => |raw σ z w - raw' σ z w|))
  let M := fun x y => rowSliceMean X U (fun σ a b => |prep σ a b - prep' σ a b|) x y
  let A := fun σ (_x _y : V) => (Cr / r.terminal.rate) * E σ
  let F := fun σ x y => C * (if U σ y then M x y else 0)
  let G := fun σ (_x : V) y => Cm * |maximum σ y - maximum' σ y|
  let Z := fun σ x y =>
    correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum σ x y ^ (4⁻¹ : ℝ) -
    correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw' prep' maximum' σ x y ^ (4⁻¹ : ℝ)
  have hE (σ : Environment P J) : 0 ≤ E σ := kthLargest_nonneg
  have hM (x y : V) : 0 ≤ M x y := expect_nonneg (fun _ _ => abs_nonneg _)
  have hA (σ : Environment P J) (x y : V) : 0 ≤ A σ x y :=
    mul_nonneg (div_nonneg hCr hf.le) (hE σ)
  have hF (σ : Environment P J) (x y : V) : 0 ≤ F σ x y := by
    dsimp [F]; split_ifs <;> exact mul_nonneg hC (by first | exact hM x y | rfl)
  have hG (σ : Environment P J) (x y : V) : 0 ≤ G σ x y := mul_nonneg hCm (abs_nonneg _)
  have hz (σ : Environment P J) (x y : V) (hx : X σ x) (hy : Y σ y) :
      |Z σ x y| ≤ A σ x y + F σ x y + G σ x y := by
    by_cases hu : U σ y
    · have hrow (z : V) (hz : z ∈ ({z | X σ z} : Finset V)) :
          kthLargest 1 {w | Y σ w} (fun w => |raw σ z w - raw' σ z w|) ≤ E σ := by
        have he := abs_le_kthLargest_one {z | X σ z}
          (fun z => kthLargest 1 {w | Y σ w} (fun w => |raw σ z w - raw' σ z w|)) z hz
        simpa only [abs_of_nonneg (kthLargest_nonneg (k := 1))] using he
      have hentry (z : V) (hz : z ∈ ({z | X σ z} : Finset V)) :
          |raw σ z y - raw' σ z y| ≤ E σ :=
        (abs_le_kthLargest_one {w | Y σ w} (fun w => raw σ z w - raw' σ z w) y
          (mem_filter.mpr ⟨mem_univ _, hy⟩)).trans (hrow z hz)
      have hp := hd σ x y (E σ) (E σ)
      dsimp only at hp
      rw [source_rank_set D ident r hr σ, terminal_rank_set D ident r σ] at hp
      have hp' := hp (hE σ) (hE σ) hentry hrow
      have he := hentry x (mem_filter.mpr ⟨mem_univ _, hx⟩)
      have hq := hrow x (mem_filter.mpr ⟨mem_univ _, hx⟩)
      change |Z σ x y| ≤ _ at hp'
      apply hp'.trans
      simpa only [A, F, G, hu, ↓reduceIte, Cr, Cm] using
        (error_sum_bound (B := B) (LI := LI) (Lτ := Lτ) (Lγ := Lγ)
          (m := M x y) (z := |maximum σ y - maximum' σ y|) hC hf he hq)
    · have h0 := children_root_zero D ident r (polynomialAuxCutoff4 HP.θ)
        HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc
        raw raw' prep prep' maximum maximum' σ x y hu
      change |Z σ x y| = 0 at h0
      rw [h0]
      exact add_nonneg (add_nonneg (hA σ x y) (hF σ x y)) (hG σ x y)
  exact hz σ x y hx hy

set_option backward.isDefEq.respectTransparency false in
/-- Integrated original-source/full-terminal root error for all three changing child
classes. RAW error pays its original row moment with explicit width squared and inverse
rate to the fourth power. PREP pays its source/usage conditional-row error by Jensen;
there is no full-environment atom payment or independence premise. -/
theorem correctionRequest_children_root_moment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Cr Cp Cm : ℝ, 0 ≤ Cr ∧ 0 ≤ Cp ∧ 0 ≤ Cm ∧
    ∀ (P J : ℕ) [Fact P.Prime] (V : Type*) [Fintype V] (k : ℕ)
      (D : ZMod P) (ident : V → ZMod P)
      (r : HierarchyTask.Request k (Fin J) (ZMod P)) (_hr : Admissible r),
    0 < r.terminal.rate → ∀ (Kc : ℕ), 0 < Kc →
    ∀ (raw raw' prep prep' : Environment P J → Matrix V V ℝ)
      (maximum maximum' : Environment P J → V → ℝ) (N u : ℝ),
    0 ≤ N * u →
    (∀ σ y, r.usage.retains (channels D) σ (ident y) →
      r.terminal.retains (channels D) σ (ident y)) →
    let X := fun σ x => r.source.retains (channels D) σ (ident x)
    let Y := fun σ y => r.terminal.retains (channels D) σ (ident y)
    let U := fun σ y => r.usage.retains (channels D) σ (ident y)
    rootDistPow 4 N u X Y
      (correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum)
      (correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw' prep' maximum') ≤
    64 * ((Cr / r.terminal.rate) ^ 4 * (Fintype.card V : ℝ) ^ 2 *
        rowNormPow 4 N u X Y (fun σ x y => raw σ x y - raw' σ x y) +
      Cp ^ 4 * rowNormPow 4 N u X U (fun σ x y => prep σ x y - prep' σ x y) +
      Cm ^ 4 * rowNormPow 4 N u X Y (fun σ _ y => maximum σ y - maximum' σ y)) := by
  obtain ⟨Cr, Cp, Cm, hCr, hCp, hCm, henv⟩ := correctionRequest_children_root_envelope HP
  refine ⟨Cr, Cp, Cm, hCr, hCp, hCm, ?_⟩
  intro P J instP V instV k D ident r hr hf Kc hKc raw raw' prep prep'
    maximum maximum' N u hNu hUY
  let X := fun σ x => r.source.retains (channels D) σ (ident x)
  let Y := fun σ y => r.terminal.retains (channels D) σ (ident y)
  let U := fun σ y => r.usage.retains (channels D) σ (ident y)
  let E := fun σ => kthLargest 1 {z | X σ z} (fun z =>
    kthLargest 1 {w | Y σ w} (fun w => |raw σ z w - raw' σ z w|))
  let M := fun x y => rowSliceMean X U (fun σ a b => |prep σ a b - prep' σ a b|) x y
  let A := fun σ (_x _y : V) => (Cr / r.terminal.rate) * E σ
  let F := fun σ x y => Cp * (if U σ y then M x y else 0)
  let G := fun σ (_x : V) y => Cm * |maximum σ y - maximum' σ y|
  let Z := fun σ x y =>
    correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum σ x y ^ (4⁻¹ : ℝ) -
    correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw' prep' maximum' σ x y ^ (4⁻¹ : ℝ)
  have hE (σ : Environment P J) : 0 ≤ E σ := kthLargest_nonneg
  have hM (x y : V) : 0 ≤ M x y := expect_nonneg (fun _ _ => abs_nonneg _)
  have hA (σ : Environment P J) (x y : V) : 0 ≤ A σ x y :=
    mul_nonneg (div_nonneg hCr hf.le) (hE σ)
  have hF (σ : Environment P J) (x y : V) : 0 ≤ F σ x y := by
    dsimp [F]; split_ifs <;> exact mul_nonneg hCp (by first | exact hM x y | rfl)
  have hG (σ : Environment P J) (x y : V) : 0 ≤ G σ x y := mul_nonneg hCm (abs_nonneg _)
  have hz (σ : Environment P J) (x y : V) (hx : X σ x) (hy : Y σ y) :
      |Z σ x y| ≤ A σ x y + F σ x y + G σ x y := by
    exact henv P J V k D ident r hr hf Kc hKc raw raw' prep prep' maximum maximum' σ x y hx hy
  have ha : rowNormPow 4 N u X Y A ≤
      (Cr / r.terminal.rate) ^ 4 * (Fintype.card V : ℝ) ^ 2 *
        rowNormPow 4 N u X Y (fun σ x y => raw σ x y - raw' σ x y) := by
    rw [show A = (fun σ x y => (Cr / r.terminal.rate) * (fun σ _ _ => E σ) σ x y)
      from rfl, rowNormPow_mul (div_nonneg hCr hf.le)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (rowNormPow_rectangle_max_le (X := X) (Y := Y) hNu
        (fun σ x y => raw σ x y - raw' σ x y)) (pow_nonneg (div_nonneg hCr hf.le) 4)
  have hb : rowNormPow 4 N u X Y F ≤
      Cp ^ 4 * rowNormPow 4 N u X U (fun σ x y => prep σ x y - prep' σ x y) := by
    rw [show F = (fun σ x y => Cp * (if U σ y then M x y else 0)) from rfl,
      rowNormPow_mul hCp]
    exact mul_le_mul_of_nonneg_left (rowNormPow_usage_conditional_abs_le hNu hUY
      (fun σ x y => prep σ x y - prep' σ x y)) (pow_nonneg hCp 4)
  have hg : rowNormPow 4 N u X Y G =
      Cm ^ 4 * rowNormPow 4 N u X Y (fun σ _ y => maximum σ y - maximum' σ y) := by
    rw [show G = (fun σ x y => Cm * |maximum σ y - maximum' σ y|) from rfl,
      rowNormPow_mul hCm]
    simp only [rowNormPow, abs_abs]
  exact (rowNormPow_le_three hNu Z A F G hA hF hG hz).trans
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha hb) hg.le) (by norm_num))

end Matrix.HierarchyParams.H4RankEnvironment
