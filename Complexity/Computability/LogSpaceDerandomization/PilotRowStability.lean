/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Computability.LogSpaceDerandomization.PilotRowTasks
public import Complexity.Computability.LogSpaceDerandomization.DenseRowRecipes.Stability
public import Complexity.Computability.LogSpaceDerandomization.RootMetric.AbsoluteError
public import Complexity.Computability.LogSpaceDerandomization.HierarchyCutoffs

/-!
# Accuracy of the actual pilot score, detector and maximum recipes

These original local contracts apply to the recipes used by `hierarchyTaskRecipe`.
Raw tables and score children may be signed and unbounded. Rank sets, normalization
rates and source/terminal conditioning are identical in both versions. No independent
seed, error certificate for the final pilot, or bound on raw rank inputs is assumed.

Score error pays the entry and full terminal-rank errors at the actual inverse rate.
Detector error contracts through its two literal finite means, then pays the finite
source maximum by a sum of fourth powers. Maximum error pays its two actual children.
The constants for the selected fourth-root hierarchy are chosen before all domains,
rates and child tables. These ordinary fourth moments feed the maximum-error input
of correction stability; they do not construct approximate recursive child calls.

## Main definitions

* `Matrix.HierarchyParams.PilotRowRecipe.sourceDetector`:
  retains integrated source dependencies.

## Main results

* `Matrix.HierarchyParams.PilotRowRecipe.score_row_moment`: explicit width/rate payment.
* `Matrix.HierarchyParams.PilotRowRecipe.sourceDetector_moment`:
  conditional Jensen and finite maxima.
* `Matrix.HierarchyParams.PilotRowRecipe.maximum_row_moment`: both actual child payments.
* `Matrix.FourthRootHierarchyParams.pilot_score_stability_constants`: fixed-HP constants.
-/
public section
noncomputable section
open Finset Cslib
open scoped BigOperators

namespace Matrix.HierarchyParams.PilotRowRecipe
variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
  {V ι κ : Type*} [Fintype V] [Fintype ι] [Fintype κ]
  (X : ι → V → Prop) (Y : κ → V → Prop)
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]

omit [Fintype κ] in
/-- The actual unnormalized pilot score propagates signed entry and full row-rank errors.
There is no preparatory denominator or incoming gate in this constructor. -/
theorem score_stability {Lϕ Lρ f : ℝ}
    (hρ : ∀ z, 0 ≤ P.ρ z) (hLρ : 0 ≤ Lρ)
    (hϕ : ∀ a b, |P.ϕ a - P.ϕ b| ≤ Lϕ * |a - b|)
    (hlρ : ∀ a b, |P.ρ a - P.ρ b| ≤ Lρ * |a - b|)
    (hK : 0 < P.K) (hf : 0 < f) (A B : Matrix V V ℝ) (t : κ) (x y : V) :
    |score P Y f A t x y - score P Y f B t x y| ≤
      (Lϕ * |A x y - B x y| +
        Lρ * kthLargest 1 {w | Y t w} (fun w => |A x w - B x w|)) / f :=
  DenseRowRecipe.atomPrep_stability
    (fun z => ⟨P.ϕ_nonneg z, P.ϕ_le_one z⟩)
    (fun z => ⟨hρ z, P.ρ_le_one z⟩) hϕ hlρ hLρ hK hf A B _ x y

/-- Evaluate a completed score on its literal source and terminal integration variables.
The source argument includes every spectator required by the child. -/
@[expose] def sourceDetector (A : ι → κ → Matrix V V ℝ) (y : V) : ℝ :=
  min 1 (max 0 (𝔼 s, 𝔼 t ∈ {t | Y t y},
    kthLargest P.J {x | X s x} (fun x => A s t x y)))

/-- Ignoring the integrated source recovers the original true detector exactly. -/
theorem sourceDetector_eq_detector (A : κ → Matrix V V ℝ) :
    sourceDetector P X Y (fun _ => A) = detector P X Y A := rfl

/-- The clipped detector contracts the literal two conditional means of the source-rank
maximum error. Both score children can depend on every other environment coordinate. -/
theorem sourceDetector_stability (A B : ι → κ → Matrix V V ℝ) (y : V) :
    |sourceDetector P X Y A y - sourceDetector P X Y B y| ≤
      𝔼 s, 𝔼 t ∈ {t | Y t y},
        kthLargest 1 {x | X s x} (fun x => |A s t x y - B s t x y|) := by
  have hclip (a b : ℝ) : |min 1 (max 0 a) - min 1 (max 0 b)| ≤ |a - b| := by
    apply (abs_min_sub_min_le_max _ _ _ _).trans
    apply max_le
    · simp
    · exact (abs_max_sub_max_le_max _ _ _ _).trans (by simp)
  apply (hclip _ _).trans
  rw [← expect_sub_distrib]
  apply (abs_expect_le _ _).trans
  apply expect_le_expect
  intro s _
  rw [← expect_sub_distrib]
  apply (abs_expect_le _ _).trans
  apply expect_le_expect
  intro t _
  exact abs_kthLargest_sub_le_kthLargest_one P.J_pos _ (fun x => A s t x y) (fun x => B s t x y)

/-- Conditional Jensen and finite maximum payment for the actual detector, including
empty source types, empty terminal conditioning and padded source ranks. -/
theorem sourceDetector_moment (A B : ι → κ → Matrix V V ℝ) (y : V) :
    |sourceDetector P X Y A y - sourceDetector P X Y B y| ^ 4 ≤
      𝔼 s, 𝔼 t ∈ {t | Y t y}, ∑ x ∈ ({x | X s x} : Finset V),
        |A s t x y - B s t x y| ^ 4 := by
  let E := fun s t => kthLargest 1 {x | X s x} (fun x => |A s t x y - B s t x y|)
  have he (s : ι) (t : κ) : 0 ≤ E s t := kthLargest_nonneg
  have hm (s : ι) : 0 ≤ 𝔼 t ∈ {t | Y t y}, E s t := expect_nonneg fun t _ => he s t
  calc
    _ ≤ (𝔼 s, 𝔼 t ∈ {t | Y t y}, E s t) ^ 4 :=
      pow_le_pow_left₀ (abs_nonneg _) (sourceDetector_stability P X Y A B y) 4
    _ ≤ 𝔼 s, |𝔼 t ∈ {t | Y t y}, E s t| ^ 4 := by
      simpa only [abs_of_nonneg (expect_nonneg fun s _ => hm s)] using
        (abs_expect_pow_le (univ : Finset ι) (by decide : 4 ≠ 0)
          (fun s => 𝔼 t ∈ {t | Y t y}, E s t))
    _ ≤ 𝔼 s, 𝔼 t ∈ {t | Y t y}, |E s t| ^ 4 :=
      expect_le_expect fun s _ => abs_expect_pow_le _ (by decide : 4 ≠ 0) _
    _ ≤ _ := expect_le_expect fun s _ => expect_le_expect fun t _ =>
      abs_kthLargest_pow_le_sum _ (fun x => A s t x y - B s t x y) (by decide)

/-- The clipped detector contracts the literal two conditional means of the source-rank
maximum error. Both score children can depend on every other environment coordinate. -/
theorem detector_stability (A B : κ → Matrix V V ℝ) (y : V) :
    |detector P X Y A y - detector P X Y B y| ≤
      𝔼 s, 𝔼 t ∈ {t | Y t y},
        kthLargest 1 {x | X s x} (fun x => |A t x y - B t x y|) :=
  sourceDetector_stability P X Y (fun _ => A) (fun _ => B) y

/-- Conditional Jensen and finite maximum payment for the actual detector, including
empty source types, empty terminal conditioning and padded source ranks. -/
theorem detector_moment (A B : κ → Matrix V V ℝ) (y : V) :
    |detector P X Y A y - detector P X Y B y| ^ 4 ≤
      𝔼 s, 𝔼 t ∈ {t | Y t y}, ∑ x ∈ ({x | X s x} : Finset V),
        |A t x y - B t x y| ^ 4 :=
  sourceDetector_moment P X Y (fun _ => A) (fun _ => B) y

omit [Fintype V] in
/-- Clipped running maxima are nonexpansive in the maximum of their two actual child errors. -/
theorem maximum_stability (a b a' b' : V → ℝ) (y : V) :
    |maximum a b y - maximum a' b' y| ≤ max (|a y - a' y|) (|b y - b' y|) := by
  have h0 : 0 ≤ max (|a y - a' y|) (|b y - b' y|) := (abs_nonneg _).trans (le_max_left _ _)
  apply (abs_min_sub_min_le_max _ _ _ _).trans
  apply max_le
  · simpa only [sub_self, abs_zero] using h0
  · apply (abs_max_sub_max_le_max _ _ _ _).trans
    exact max_le (by simpa only [sub_self, abs_zero] using h0)
      (abs_max_sub_max_le_max _ _ _ _)

omit [Fintype V] in
/-- No final-maximum certificate is needed: the fourth moment pays the two supplied children. -/
theorem maximum_moment (a b a' b' : V → ℝ) (y : V) :
    |maximum a b y - maximum a' b' y| ^ 4 ≤ |a y - a' y| ^ 4 + |b y - b' y| ^ 4 := by
  apply (pow_le_pow_left₀ (abs_nonneg _) (maximum_stability a b a' b' y) 4).trans
  rcases le_total (|a y - a' y|) (|b y - b' y|) with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (by positivity)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (by positivity)

/-- Integrated maximum error on any original pair masks. This is directly the ordinary
maximum-error payment consumed by `correctionRequest_children_root_moment`. -/
theorem maximum_row_moment {Ω : Type*} [Fintype Ω]
    (Xs Z : Ω → V → Prop) [∀ σ x, Decidable (Xs σ x)] [∀ σ y, Decidable (Z σ y)]
    (a b a' b' : Ω → V → ℝ) {N u : ℝ} (hNu : 0 ≤ N * u) :
    rowNormPow 4 N u Xs Z (fun σ _ y => maximum (a σ) (b σ) y -
      maximum (a' σ) (b' σ) y) ≤
    rowNormPow 4 N u Xs Z (fun σ _ y => a σ y - a' σ y) +
      rowNormPow 4 N u Xs Z (fun σ _ y => b σ y - b' σ y) := by
  unfold rowNormPow
  rw [← mul_add, ← expect_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNu)
  apply expect_le_expect
  intro σ _
  simp only [← sum_add_distrib]
  exact sum_le_sum fun x _ => sum_le_sum fun y _ => maximum_moment _ _ _ _ y

/-- Integrated score error on the original source and terminal masks. The full terminal
maximum costs one ambient width, with the actual inverse-rate fourth power displayed. -/
theorem score_row_moment {Ω : Type*} [Fintype Ω]
    (Xs Z : Ω → V → Prop) [∀ σ x, Decidable (Xs σ x)] [∀ σ y, Decidable (Z σ y)]
    {Lϕ Lρ f N u : ℝ} (hρ : ∀ z, 0 ≤ P.ρ z) (hLϕ : 0 ≤ Lϕ) (hLρ : 0 ≤ Lρ)
    (hϕ : ∀ a b, |P.ϕ a - P.ϕ b| ≤ Lϕ * |a - b|)
    (hlρ : ∀ a b, |P.ρ a - P.ρ b| ≤ Lρ * |a - b|)
    (hK : 0 < P.K) (hf : 0 < f) (hNu : 0 ≤ N * u) (A B : Ω → Matrix V V ℝ) :
    rowNormPow 4 N u Xs Z (fun σ x y => score P Z f (A σ) σ x y -
      score P Z f (B σ) σ x y) ≤
    Fintype.card V * ((Lϕ + Lρ) / f) ^ 4 *
      rowNormPow 4 N u Xs Z (fun σ x y => A σ x y - B σ x y) := by
  apply rowNormPow_le_fullRank_max hNu (fun σ x y => A σ x y - B σ x y) _
    (div_nonneg (add_nonneg hLϕ hLρ) hf.le)
  intro σ x y _ hy
  apply (score_stability P Z hρ hLρ hϕ hlρ hK hf (A σ) (B σ) σ x y).trans
  have he := abs_le_kthLargest_one {w | Z σ w} (fun w => A σ x w - B σ x w) y
    (mem_filter.mpr ⟨mem_univ _, hy⟩)
  calc
    _ ≤ (Lϕ * kthLargest 1 {w | Z σ w} (fun w => |A σ x w - B σ x w|) +
        Lρ * kthLargest 1 {w | Z σ w} (fun w => |A σ x w - B σ x w|)) / f :=
      div_le_div_of_nonneg_right
        (add_le_add (mul_le_mul_of_nonneg_left he hLϕ) le_rfl) hf.le
    _ = _ := by ring

/-- Integrated detector error, retaining both literal means and their actual finite
source-maximum payment. Outer masks and all children may share the same environment.
There is no inverse atom probability or full-environment cardinality cost. -/
theorem detector_row_moment {Ω : Type*} [Fintype Ω]
    (Xs Z : Ω → V → Prop) [∀ σ x, Decidable (Xs σ x)] [∀ σ y, Decidable (Z σ y)]
    (rankSource : Ω → ι → V → Prop) (rankTerminal : Ω → κ → V → Prop)
    [∀ σ s x, Decidable (rankSource σ s x)] [∀ σ t y, Decidable (rankTerminal σ t y)]
    (A B : Ω → κ → Matrix V V ℝ) {N u : ℝ} (hNu : 0 ≤ N * u) :
    rowNormPow 4 N u Xs Z (fun σ _ y => detector P (rankSource σ) (rankTerminal σ) (A σ) y -
      detector P (rankSource σ) (rankTerminal σ) (B σ) y) ≤
    (N * u)⁻¹ * 𝔼 σ, ∑ _a ∈ ({a | Xs σ a} : Finset V),
      ∑ y ∈ ({y | Z σ y} : Finset V),
        𝔼 s, 𝔼 t ∈ {t | rankTerminal σ t y}, ∑ x ∈ ({x | rankSource σ s x} : Finset V),
          |A σ t x y - B σ t x y| ^ 4 := by
  unfold rowNormPow
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNu)
  exact expect_le_expect fun σ _ => sum_le_sum fun _a _ => sum_le_sum fun y _ =>
    detector_moment P (rankSource σ) (rankTerminal σ) (A σ) (B σ) y

end Matrix.HierarchyParams.PilotRowRecipe

namespace Matrix.FourthRootHierarchyParams
/-- Score constants are selected at fixed hierarchy parameters, before rates, widths,
rank masks or signed raw children. The original ϕ and ρ are retained. -/
theorem pilot_score_stability_constants (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Lϕ Lρ : ℝ, 0 ≤ Lϕ ∧ 0 ≤ Lρ ∧
      (∀ a b, |HP.ϕ a - HP.ϕ b| ≤ Lϕ * |a - b|) ∧
      (∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) := by
  obtain ⟨⟨Lϕ, hϕ⟩, _⟩ := HP.cutoff_roots HP.ϕ (by simp)
  obtain ⟨⟨Lρ, hρ⟩, _⟩ := HP.cutoff_roots HP.ρ (by simp)
  refine ⟨4 * Lϕ, 4 * Lρ, by positivity, by positivity, ?_, ?_⟩
  · exact abs_sub_le_four_mul_root_lipschitz (fun z => ⟨HP.ϕ_nonneg z, HP.ϕ_le_one z⟩) hϕ
  · exact abs_sub_le_four_mul_root_lipschitz (fun z => ⟨HP.ρ_nonneg z, HP.ρ_le_one z⟩) hρ
end Matrix.FourthRootHierarchyParams
