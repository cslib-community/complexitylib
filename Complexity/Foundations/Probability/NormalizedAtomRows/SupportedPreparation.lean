/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.NormalizedAtomRows.MeanBias
import Complexity.Foundations.Probability.RootMetric.ClippedMean
import Complexity.Foundations.Analysis.RowCompression.BoundedCap
import Complexity.Foundations.Data.Finset.KthLargest.Truncation

/-!
# Supported relative stability of actual preparation

The hierarchy's own rank gate and polynomial preparation are unchanged. Saturation turns
clipped relative raw error into a uniform scalar error, including unbounded nonnegative
truth and signed approximate rows. Only the union of the two actual preparation supports
is charged. This avoids repeating a full-rank maximum at every usage endpoint.

## Main results

* `atomPrep_relative_le`: scalar stability for the actual hierarchy rank gate.
* `selectedPreparation_relative_moment`: a supported, dimension-free fourth moment.
* `selectedPreparation_relative_mean_moment`: actual usage mean from full-rank first statistics.

These are original finite stability estimates; they do not assert the recursive accuracy
or availability induction, or native RL=L.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

private lemma prep_entry_cap (HP : FourthRootHierarchyParams 16 1 16 32 8) (v : ℝ) :
    polynomialPrepCutoff4 HP.θ v = polynomialPrepCutoff4 HP.θ (min HP.θ v) := by
  by_cases hv : v ≤ HP.θ
  · rw [min_eq_right hv]
  · rw [min_eq_left (not_le.mp hv).le,
      polynomialPrepCutoff4_eq_one HP.θ_pos (by linarith [not_le.mp hv, HP.θ_pos]),
      polynomialPrepCutoff4_eq_one HP.θ_pos (by linarith [HP.θ_pos])]

private lemma prep_gate_cap (HP : FourthRootHierarchyParams 16 1 16 32 8) (v : ℝ) :
    HP.ρ v = HP.ρ (min HP.θ v) := by
  have ht : HP.η₂ ≤ HP.θ := by
    linarith [HP.η₂_lt, HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_pos]
  by_cases hv : v ≤ HP.θ
  · rw [min_eq_right hv]
  · rw [min_eq_left (not_le.mp hv).le, HP.ρ_zero v (ht.trans (not_le.mp hv).le),
      HP.ρ_zero HP.θ ht]

/-- The actual preparation is stable in the full-rank clipped relative error. The
approximate row may be signed; only the true row is nonnegative. -/
theorem atomPrep_relative_le {V : Type*}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    {a : ℝ} (ha : 0 < a) (A G : Matrix V V ℝ) (S : Finset V)
    (x : V) (hG : ∀ y ∈ S, 0 ≤ G x y) {e : ℝ} (he : 0 ≤ e)
    (herr : ∀ y ∈ S, min 1 (|A x y - G x y| / (a + G x y)) ≤ e)
    (y : V) (hy : y ∈ S) :
    |atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K a A S x y -
      atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K a G S x y| ≤
      (2 + (Lh + Lρ) * (4 * HP.θ + 5)) * e := by
  classical
  have hθ := HP.θ_pos
  have hrange (B : Matrix V V ℝ) :
      atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K a B S x y ∈ Set.Icc 0 1 :=
    ⟨mul_nonneg (polynomialPrepCutoff4_nonneg _ _) (HP.ρ_nonneg _),
      (mul_le_of_le_one_right (polynomialPrepCutoff4_nonneg _ _) (HP.ρ_le_one _)).trans
        (polynomialPrepCutoff4_le_one _ _)⟩
  by_cases hes : e ≤ 1 / 2
  · have hcap (w : V) (hw : w ∈ S) :
        |min HP.θ (A x w / a) - min HP.θ (G x w / a)| ≤ (4 * HP.θ + 5) * e := by
      have hden : 0 < a + G x w := add_pos_of_pos_of_nonneg ha (hG w hw)
      have hraw : |A x w - G x w| / (a + G x w) ≤ e :=
        (min_le_iff.mp (herr w hw)).resolve_left (by linarith)
      have hs : |A x w / a - G x w / a| ≤ (1 + G x w / a) * e := by
        rw [← sub_div, abs_div, abs_of_pos ha]
        apply (div_le_iff₀ ha).mpr
        have hb := (div_le_iff₀ hden).mp hraw
        have hid : (1 + G x w / a) * e * a = (a + G x w) * e := by field_simp
        rw [hid]
        simpa only [mul_comm] using hb
      simpa only [add_zero] using abs_min_add_sub_min_add_le HP.θ_pos he hes hs
        (show |(0 : ℝ)| ≤ HP.θ by simpa using HP.θ_pos.le)
    have hq : |min HP.θ (kthLargest HP.K S (fun w => A x w / a)) -
        min HP.θ (kthLargest HP.K S (fun w => G x w / a))| ≤ (4 * HP.θ + 5) * e := by
      rw [← kthLargest_min hK HP.θ_pos.le, ← kthLargest_min hK HP.θ_pos.le]
      exact abs_kthLargest_sub_kthLargest_le hK (by positivity) hcap
    simp only [atomPrep, rowGate]
    rw [prep_entry_cap HP (A x y / a), prep_entry_cap HP (G x y / a),
      prep_gate_cap HP (kthLargest HP.K S (fun w => A x w / a)),
      prep_gate_cap HP (kthLargest HP.K S (fun w => G x w / a))]
    have hp : ∀ u u' v v',
        |polynomialPrepCutoff4 HP.θ u * HP.ρ v - polynomialPrepCutoff4 HP.θ u' * HP.ρ v'| ≤
        Lh * |u - u'| + Lρ * |v - v'| := by
      intro u u' v v'
      calc
        _ = |(polynomialPrepCutoff4 HP.θ u - polynomialPrepCutoff4 HP.θ u') * HP.ρ v +
          polynomialPrepCutoff4 HP.θ u' * (HP.ρ v - HP.ρ v')| := by congr 1; ring
        _ ≤ _ := (abs_add_le _ _).trans (by
          rw [abs_mul, abs_mul, abs_of_nonneg (HP.ρ_nonneg _),
            abs_of_nonneg (polynomialPrepCutoff4_nonneg _ _)]
          exact add_le_add
            ((mul_le_of_le_one_right (abs_nonneg _) (HP.ρ_le_one _)).trans (hh u u'))
            ((mul_le_of_le_one_left (abs_nonneg _) (polynomialPrepCutoff4_le_one _ _)).trans
              (hρ v v')))
    apply (hp _ _ _ _).trans
    have hb := add_le_add (mul_le_mul_of_nonneg_left (hcap y hy) hLh)
      (mul_le_mul_of_nonneg_left hq hLρ)
    nlinarith
  · have h1 := hrange A
    have h2 := hrange G
    have hab : |atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K a A S x y -
        atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K a G S x y| ≤ 1 :=
      abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
    apply hab.trans
    have hc : 0 ≤ (Lh + Lρ) * (4 * HP.θ + 5) * e := by positivity
    linarith [not_le.mp hes]

/-- A coefficient depending only on the hierarchy and its two scalar regularity constants. -/
@[expose] def preparationRelativeConstant (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (Lh Lρ : ℝ) : ℝ := 2 + (Lh + Lρ) * (4 * HP.θ + 5)

/-- Only the union of the actual preparation supports pays the full-rank error maximum.
Usage is contained in rank; no independence of errors and the masks is used. -/
theorem selectedPreparation_relative_moment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (ks k ku : ℕ) (husage : k ≤ ku)
    (ss st : List (ZMod P)) {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    {N u : ℝ} (hNu : 0 ≤ N * u) :
    rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P ku) D st)
      (fun σ x y => selectedPreparation HP D R st k A σ x y -
        selectedPreparation HP D R st k (fun _ => G) σ x y) ≤
      (2 * HP.K) * (preparationRelativeConstant HP Lh Lρ) ^ 4 *
        rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
          (retainedMask R.terminal (side P k) D st)
          (fun σ x y => min 1 (|A σ x y - G x y| / (rate k + G x y))) := by
  have hθ := HP.θ_pos
  let c := preparationRelativeConstant HP Lh Lρ
  have hc : 0 ≤ c := by dsimp only [c, preparationRelativeConstant]; positivity
  let E := fun σ x y => min 1 (|A σ x y - G x y| / (rate k + G x y))
  let Z := fun σ x y => selectedPreparation HP D R st k A σ x y -
    selectedPreparation HP D R st k (fun _ => G) σ x y
  have hside : side P ku ≤ side P k := by
    rw [side_eq_ceil, side_eq_ceil]
    exact Nat.ceil_mono (mul_le_mul_of_nonneg_left
      (inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) husage)) (by positivity))
  have hsub (σ : Environment P J) (y : ZMod P)
      (hy : retainedMask R.terminal (side P ku) D st σ y) :
      retainedMask R.terminal (side P k) D st σ y :=
    mem_retentionBox.mpr (fun a => (mem_retentionBox.mp hy a).trans_le hside)
  have hp (σ : Environment P J) (x : ZMod P) :
      (∑ y ∈ ({y | retainedMask R.terminal (side P ku) D st σ y} : Finset (ZMod P)),
        |Z σ x y| ^ 4) ≤ (2 * HP.K : ℝ) * c ^ 4 *
          ∑ y ∈ ({y | retainedMask R.terminal (side P k) D st σ y} : Finset (ZMod P)),
            |E σ x y| ^ 4 := by
    let S : Finset (ZMod P) := {y | retainedMask R.terminal (side P k) D st σ y}
    let U : Finset (ZMod P) := {y | retainedMask R.terminal (side P ku) D st σ y}
    let T := U.filter (fun y => Z σ x y ≠ 0)
    let SA := S.filter (fun y => selectedPreparation HP D R st k A σ x y ≠ 0)
    let SG := S.filter (fun y => selectedPreparation HP D R st k (fun _ => G) σ x y ≠ 0)
    have hT : T ⊆ SA ∪ SG := by
      intro y hy
      rcases mem_filter.mp hy with ⟨hyu, hyz⟩
      have hys : y ∈ S := mem_filter.mpr ⟨mem_univ _, hsub σ y (mem_filter.mp hyu).2⟩
      by_cases ha : selectedPreparation HP D R st k A σ x y = 0
      · apply mem_union_right
        refine mem_filter.mpr ⟨hys, ?_⟩
        intro hg
        exact hyz (by simp only [Z, ha, hg, sub_self])
      · exact mem_union_left _ (mem_filter.mpr ⟨hys, ha⟩)
    have hcard : (#T : ℝ) ≤ 2 * HP.K := by
      have hca : #SA < HP.K := selectedPreparation_support HP hK D R st k A σ x
      have hcg : #SG < HP.K := selectedPreparation_support HP hK D R st k (fun _ => G) σ x
      have ht := (card_le_card hT).trans (card_union_le SA SG)
      exact_mod_cast (show #T ≤ 2 * HP.K by omega)
    let e := kthLargest 1 S (fun y => |E σ x y|)
    have hmax : |e| ^ 4 ≤ ∑ y ∈ S, |E σ x y| ^ 4 :=
      abs_kthLargest_pow_le_sum S (E σ x) (by decide : 4 ≠ 0)
    have he : 0 ≤ e := kthLargest_nonneg
    have hz (y : ZMod P) (hy : y ∈ T) :
        |Z σ x y| ^ 4 ≤ c ^ 4 * ∑ w ∈ S, |E σ x w| ^ 4 := by
      have hys : y ∈ S := mem_filter.mpr ⟨mem_univ _,
        hsub σ y (mem_filter.mp (mem_filter.mp hy).1).2⟩
      have hb := atomPrep_relative_le HP hK hLh hLρ hh hρ (rate_pos k) (A σ) G S x
        (fun w _ => hG x w) he (fun w hw =>
          (le_abs_self (E σ x w)).trans (abs_le_kthLargest_one S (E σ x) w hw)) y hys
      change |Z σ x y| ≤ c * e at hb
      calc
        _ ≤ (c * e) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hb 4
        _ ≤ _ := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left (by simpa only [abs_of_nonneg he] using hmax)
            (pow_nonneg hc 4)
    have hsum : (∑ y ∈ U, |Z σ x y| ^ 4) = ∑ y ∈ T, |Z σ x y| ^ 4 := by
      symm
      rw [sum_filter]
      apply sum_congr rfl
      intro y _
      split_ifs with hy
      · rfl
      · simp only [not_ne_iff.mp hy, abs_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow]
    change (∑ y ∈ U, |Z σ x y| ^ 4) ≤ (2 * HP.K : ℝ) * c ^ 4 * ∑ y ∈ S, |E σ x y| ^ 4
    rw [hsum]
    calc
      _ ≤ ∑ _y ∈ T, c ^ 4 * ∑ w ∈ S, |E σ x w| ^ 4 := sum_le_sum hz
      _ = (#T : ℝ) * (c ^ 4 * ∑ w ∈ S, |E σ x w| ^ 4) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ (2 * HP.K : ℝ) * (c ^ 4 * ∑ w ∈ S, |E σ x w| ^ 4) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  unfold rowNormPow
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | retainedMask R.source (side P ks) D ss σ x} :
        Finset (ZMod P)), (2 * HP.K : ℝ) * c ^ 4 *
          ∑ y ∈ ({y | retainedMask R.terminal (side P k) D st σ y} : Finset (ZMod P)),
            |E σ x y| ^ 4 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNu)
      exact expect_le_expect fun σ _ => sum_le_sum fun x _ => hp σ x
    _ = _ := by
      simp only [← mul_sum, ← mul_expect, c, E]
      ring

/-- The actual preparation mean consumes the first clipped mean and normalized centered
noise on the full rank mask. Conditional Jensen is applied on the narrower usage mask.
No bound on the approximate input, reseeding or support independence is required. -/
theorem selectedPreparation_relative_mean_moment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (ks k ku : ℕ) (husage : k ≤ ku)
    (ss st : List (ZMod P)) {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (A : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    {N u α β : ℝ} (hNu : 0 ≤ N * u) (ζ : ℝ)
    (hmean : rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st) (fun _ x y => min 1
        (|rowSliceMean (retainedMask R.source (side P ks) D ss)
          (retainedMask R.terminal (side P k) D st) A x y - G x y| / (rate k + G x y))) ≤ α)
    (hnoise : rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st) (fun σ x y =>
        |A σ x y - rowSliceMean (retainedMask R.source (side P ks) D ss)
          (retainedMask R.terminal (side P k) D st) A x y| / (rate k + G x y)) ≤ β) :
    rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P ku) D st) (fun _ x y => min 1 (|ζ| *
        |rowSliceMean (retainedMask R.source (side P ks) D ss)
          (retainedMask R.terminal (side P ku) D st)
          (fun σ x y => selectedPreparation HP D R st k A σ x y -
            selectedPreparation HP D R st k (fun _ => G) σ x y) x y|)) ≤
      8 * (2 * HP.K) * (|ζ| * preparationRelativeConstant HP Lh Lρ) ^ 4 * (α + β) := by
  let Xs := retainedMask R.source (side P ks) D ss
  let Ya := retainedMask R.terminal (side P k) D st
  let Yu := retainedMask R.terminal (side P ku) D st
  let μ := rowSliceMean Xs Ya A
  let E := fun σ x y => min 1 (|A σ x y - G x y| / (rate k + G x y))
  let Em := fun (_ : Environment P J) x y => min 1 (|μ x y - G x y| / (rate k + G x y))
  let En := fun σ x y => |A σ x y - μ x y| / (rate k + G x y)
  have hraw : rowNormPow 4 N u Xs Ya E ≤ 8 * (α + β) := by
    have hb : rowNormPow 4 N u Xs Ya E ≤ rowNormPow 4 N u Xs Ya (fun σ x y =>
        Em σ x y + En σ x y) := by
      apply (rowNormPow_le_mul hNu (c := 1) ?_).trans_eq (one_mul _)
      intro σ x y _ _
      have hd : 0 < rate k + G x y := add_pos_of_pos_of_nonneg (rate_pos k) (hG x y)
      have he : 0 ≤ E σ x y := by dsimp only [E]; positivity
      have hm : 0 ≤ Em σ x y := by dsimp only [Em]; positivity
      have hn : 0 ≤ En σ x y := by dsimp only [En]; positivity
      rw [one_mul, abs_of_nonneg he, abs_of_nonneg (add_nonneg hm hn)]
      apply pow_le_pow_left₀ he
      have ht := min_abs_add_div_le hd (μ x y - G x y) (A σ x y - μ x y)
      have hid : μ x y - G x y + (A σ x y - μ x y) = A σ x y - G x y := by ring
      rw [hid] at ht
      exact ht.trans (add_le_add le_rfl (min_le_right _ _))
    apply hb.trans
    apply (rowNormPow_add_le hNu Em En).trans
    exact mul_le_mul_of_nonneg_left (add_le_add hmean hnoise) (by norm_num)
  let Z := fun σ x y => selectedPreparation HP D R st k A σ x y -
    selectedPreparation HP D R st k (fun _ => G) σ x y
  have hprep := selectedPreparation_relative_moment HP hK D R ks k ku husage ss st
    hLh hLρ hh hρ A G hG hNu
  have hj := rowNormPow_sliceMean_fourth_le hNu Xs Yu Z
  have hclip : rowNormPow 4 N u Xs Yu (fun _ x y => min 1
      (|ζ| * |rowSliceMean Xs Yu Z x y|)) ≤
      |ζ| ^ 4 * rowNormPow 4 N u Xs Yu (fun _ => rowSliceMean Xs Yu Z) := by
    apply rowNormPow_le_mul hNu
    intro σ x y _ _
    have hn : 0 ≤ min 1 (|ζ| * |rowSliceMean Xs Yu Z x y|) := by positivity
    rw [abs_of_nonneg hn, ← mul_pow]
    exact pow_le_pow_left₀ hn (min_le_right _ _) 4
  apply hclip.trans
  apply (mul_le_mul_of_nonneg_left hj (by positivity)).trans
  apply (mul_le_mul_of_nonneg_left hprep (by positivity)).trans
  have hb := mul_le_mul_of_nonneg_left hraw
    (show 0 ≤ |ζ| ^ 4 * ((2 * HP.K) * preparationRelativeConstant HP Lh Lρ ^ 4) by positivity)
  dsimp only [E] at hb
  convert hb using 1 <;> ring

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
