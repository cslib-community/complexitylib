/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.DenseRowRecipes
public import Complexity.Foundations.Probability.FourthRootHierarchyParams
public import Complexity.Foundations.Probability.HierarchyAtomCutoff
public import Complexity.Foundations.Analysis.RowCompression.Reference
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual uncentered normalized atom outputs

The scalar output accepts the selected numerator and rank gate, divided by
`clip (second / ζ)`. Range, support and fourth-root regularity laws expose their precise
function hypotheses. The hierarchy's atom-cutoff clients specialize those shared laws.
The recipe identity retains the actual usage mask and full terminal
rank domain. No state, default or raw increment is translated or capped. Fourth-root
regularity is the fourth-moment adaptation of the normalization in §8.1 (printed p. 43)
of [OpenAI2026LogSpace], revision 7ef5c0cc. These deterministic scalar and support laws
do not establish recursive input moments or the integrated compression theorem.

The scalar normalization is Christian Reitwiessner's; the support/rank proof pattern
is adapted from Samuel Schlesinger's polynomial atom rows.
-/

public section
namespace Matrix.FourthRootHierarchyParams.NormalizedRow
open Finset Cslib Matrix Cslib.RowCompression
open scoped BigOperators
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)

/-- Clip the uncentered denominator to the interval [1/2, 1]. -/
@[expose] noncomputable def clip (v : ℝ) : ℝ := max (1/2) (min 1 v)
/-- The clipped denominator stays in its required positive range. -/
lemma clip_bounds (v : ℝ) : (1/2 : ℝ) ≤ clip v ∧ clip v ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
private lemma clip_dist (v w : ℝ) : |clip v - clip w| ≤ |v-w| := by
  apply (abs_max_sub_max_le_max _ _ _ _).trans
  apply max_le
  · simp only [sub_self, abs_zero]; exact abs_nonneg _
  · exact (abs_min_sub_min_le_max _ _ _ _).trans (by simp)

private noncomputable def denominatorRoot (v : ℝ) : ℝ := (clip v) ^ (-(4⁻¹ : ℝ))
private lemma denominatorRoot_pow (v : ℝ) : denominatorRoot v ^ 4 = (clip v)⁻¹ := by
  rw [denominatorRoot, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith [clip_bounds v] : 0 ≤
    clip v)]
  norm_num [Real.rpow_neg_one]
private lemma denominatorRoot_bounds (v : ℝ) : 1 ≤ denominatorRoot v ∧ denominatorRoot v ≤ 2 := by
  have hc := clip_bounds v
  have hpos : 0 < clip v := by linarith
  have hr0 : 0 ≤ denominatorRoot v := Real.rpow_nonneg hpos.le _
  have hp := denominatorRoot_pow v
  have hi1 : 1 ≤ (clip v)⁻¹ := (one_le_inv₀ hpos).mpr hc.2
  have hi2 : (clip v)⁻¹ ≤ 2 := (inv_le_comm₀ hpos (by norm_num : (0:ℝ)<2)).mpr (by simpa using hc.1)
  constructor
  · by_contra h
    have hlt : denominatorRoot v ^ 4 < (1:ℝ)^4 := pow_lt_pow_left₀ (not_le.mp h) hr0 (by decide)
    nlinarith
  · by_contra h
    have hlt : (2:ℝ)^4 < denominatorRoot v ^ 4 := pow_lt_pow_left₀ (not_le.mp h) (by norm_num)
      (by decide)
    nlinarith
private lemma denominatorRoot_dist (v w : ℝ) :
    |denominatorRoot v - denominatorRoot w| ≤ 4 * |v-w| := by
  have hv := denominatorRoot_bounds v
  have hw := denominatorRoot_bounds w
  have hpoly : |denominatorRoot v - denominatorRoot w| ≤
      |denominatorRoot v ^ 4 - denominatorRoot w ^ 4| := by
    have hfac : denominatorRoot v ^ 4 - denominatorRoot w ^ 4 =
        (denominatorRoot v-denominatorRoot w)*
          ((denominatorRoot v+denominatorRoot w)*
            (denominatorRoot v^2+denominatorRoot w^2)) := by ring
    have hf : 1 ≤ (denominatorRoot v+denominatorRoot w)*
        (denominatorRoot v^2+denominatorRoot w^2) := by
      nlinarith [sq_nonneg (denominatorRoot v-1), sq_nonneg (denominatorRoot w-1)]
    rw [hfac, abs_mul, abs_of_nonneg (by linarith :
      0 ≤ (denominatorRoot v+denominatorRoot w)*(denominatorRoot v^2+denominatorRoot w^2))]
    exact le_mul_of_one_le_right (abs_nonneg _) hf
  rw [denominatorRoot_pow, denominatorRoot_pow] at hpoly
  have hcv := clip_bounds v
  have hcw := clip_bounds w
  have hc0 : 0 < clip v * clip w := mul_pos (by linarith) (by linarith)
  have hid : |(clip v)⁻¹-(clip w)⁻¹| = |clip w-clip v|/(clip v*clip w) := by
    rw [← abs_of_pos hc0, ← abs_div]
    congr 1
    field_simp [ne_of_gt (show 0 < clip v by linarith), ne_of_gt (show 0 < clip w by linarith)]
  apply hpoly.trans
  rw [hid, abs_sub_comm]
  apply (div_le_iff₀ hc0).mpr
  have hprod : 1/4 ≤ clip v*clip w := by nlinarith
  nlinarith [clip_dist v w, abs_nonneg (v-w)]

/-- Uncentered decoder with the supplied numerator, rank gate and clipped second signal. -/
@[expose] noncomputable def output (cutoff gate : ℝ → ℝ) (scale x v q : ℝ) : ℝ :=
  cutoff x * gate q / clip (v / scale)

/-- The numerator and gate bounds give the clipped decoder's range for arbitrary signals. -/
lemma output_mem_Icc (cutoff gate : ℝ → ℝ) {cap : ℝ} (hcap : 0 ≤ cap)
    (hc : ∀ x, cutoff x ∈ Set.Icc 0 cap) (hg : ∀ q, gate q ∈ Set.Icc 0 1)
    (ζ d v r : ℝ) : output cutoff gate ζ d v r ∈ Set.Icc 0 (2 * cap) := by
  have hclip := clip_bounds (v / ζ)
  have hnum := mul_nonneg (hc d).1 (hg r).1
  refine ⟨div_nonneg hnum (by linarith), ?_⟩
  rw [output, div_le_iff₀ (by linarith : 0 < clip (v / ζ))]
  have hn := (mul_le_of_le_one_right (hc d).1 (hg r).2).trans (hc d).2
  nlinarith

/-- The atom output vanishes below the entry threshold. -/
lemma entry_zero {scale x v q : ℝ} (hx : x ≤ HP.θ) : output HP.toHierarchyParams.atomCutoff HP.ρ
    scale x v q = 0 := by
  have hQ : HP.Q x = 0 := le_antisymm
    (by simpa only [max_eq_right (sub_nonpos.mpr hx)] using HP.Q_le x) (HP.Q_nonneg x)
  simp only [output, HP.toHierarchyParams.atomCutoff_eq_zero_of_Q_eq_zero hQ, zero_mul, zero_div]
/-- The actual closed rank gate annihilates the output. -/
lemma gate_zero {scale x v q : ℝ} (hq : HP.η₂ ≤ q) : output HP.toHierarchyParams.atomCutoff HP.ρ
    scale x v q = 0 := by
  simp only [output, HP.ρ_zero _ hq, mul_zero, zero_div]
/-- Ranks in the full-gate region give the same scalar output. -/
lemma gate_flat {scale x v q q' : ℝ} (hq : q ≤ HP.η) (hq' : q' ≤ HP.η) :
    output HP.toHierarchyParams.atomCutoff HP.ρ scale x v q = output
      HP.toHierarchyParams.atomCutoff HP.ρ scale x v q' := by
  simp only [output, HP.ρ_one _ hq, HP.ρ_one _ hq']

private lemma cutoff_root_dist : ∃ L : ℝ, 0 ≤ L ∧ ∀ x x',
    |HP.toHierarchyParams.atomCutoff x ^ (4⁻¹ : ℝ) -
      HP.toHierarchyParams.atomCutoff x' ^ (4⁻¹ : ℝ)| ≤ L * |x-x'| := by
  obtain ⟨L,hL⟩ := HP.Q_root
  refine ⟨L, L.coe_nonneg, ?_⟩
  intro x x'
  have h := hL.dist_le_mul (min HP.toHierarchyParams.atomCap (max 0 x))
    (min HP.toHierarchyParams.atomCap (max 0 x'))
  simp only [Real.dist_eq] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
  apply (abs_min_sub_min_le_max _ _ _ _).trans
  apply max_le (by simp)
  exact (abs_max_sub_max_le_max _ _ _ _).trans (by simp)

private lemma output_root (cutoff gate : ℝ → ℝ)
    (hc : ∀ x, 0 ≤ cutoff x) (hg : ∀ q, 0 ≤ gate q) (scale x v q : ℝ) :
    output cutoff gate scale x v q ^ (4⁻¹ : ℝ) =
      cutoff x ^ (4⁻¹ : ℝ) * gate q ^ (4⁻¹ : ℝ) * denominatorRoot (v / scale) := by
  rw [output, Real.div_rpow (mul_nonneg (hc _) (hg _))
    (by linarith [clip_bounds (v / scale)] : 0 ≤ clip (v / scale)),
    Real.mul_rpow (hc _) (hg _)]
  rw [denominatorRoot, Real.rpow_neg (by
    linarith [clip_bounds (v / scale)] : 0 ≤ clip (v / scale))]
  rfl

/-- Fourth-root regularity of the clipped decoder for the actual numerator and gate.
The numerator bound is in fourth-root units. No preparation identity is assumed. -/
lemma root_dist_le_of_bounds (cutoff gate : ℝ → ℝ) {scale cap Lq Lr : ℝ}
    (hs : 0 < scale) (hcap : 0 ≤ cap) (hLq : 0 ≤ Lq) (hLr : 0 ≤ Lr)
    (hcut0 : ∀ x, 0 ≤ cutoff x) (hgate0 : ∀ q, 0 ≤ gate q)
    (hgate1 : ∀ q, gate q ≤ 1)
    (hbound : ∀ x, |cutoff x ^ (4⁻¹ : ℝ)| ≤ cap)
    (hq : ∀ x x', |cutoff x ^ (4⁻¹ : ℝ) - cutoff x' ^ (4⁻¹ : ℝ)| ≤ Lq * |x - x'|)
    (hgate : ∀ q q', |gate q ^ (4⁻¹ : ℝ) - gate q' ^ (4⁻¹ : ℝ)| ≤ Lr * |q - q'|) :
    ∀ x v q x' v' q',
      |output cutoff gate scale x v q ^ (4⁻¹ : ℝ) -
        output cutoff gate scale x' v' q' ^ (4⁻¹ : ℝ)| ≤
        (2 * Lq + 4 * cap / scale + 2 * cap * Lr) *
          (|x - x'| + |v - v'| + |q - q'|) := by
  let B := cap
  have hB : 0 ≤ B := hcap
  have hrbound (q : ℝ) : |gate q ^ (4⁻¹ : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (Real.rpow_nonneg (hgate0 _) _)]
    exact Real.rpow_le_one (hgate0 _) (hgate1 _) (by norm_num)
  have hc (v : ℝ) : |denominatorRoot (v/scale)| ≤ 2 :=
    (abs_of_nonneg (by linarith [denominatorRoot_bounds (v/scale)])).trans_le
      (denominatorRoot_bounds _).2
  intro x v q x' v' q'
  rw [output_root cutoff gate hcut0 hgate0, output_root cutoff gate hcut0 hgate0]
  let a := cutoff x ^ (4⁻¹ : ℝ)
  let a' := cutoff x' ^ (4⁻¹ : ℝ)
  let b := gate q ^ (4⁻¹ : ℝ)
  let b' := gate q' ^ (4⁻¹ : ℝ)
  let c := denominatorRoot (v/scale)
  let c' := denominatorRoot (v'/scale)
  have hsplit : a*b*c-a'*b'*c' = (a-a')*b*c + a'*(b-b')*c + a'*b'*(c-c') := by ring
  change |a*b*c-a'*b'*c'| ≤ _
  rw [hsplit]
  have h1 : |(a-a')*b*c| ≤ 2*Lq*|x-x'| := by
    rw [abs_mul, abs_mul]
    calc _ ≤ (Lq*|x-x'|)*1*2 := mul_le_mul (mul_le_mul (hq x x') (hrbound q) (abs_nonneg _) (by
      positivity)) (hc v) (abs_nonneg _) (by positivity)
         _ = _ := by ring
  have h2 : |a'*(b-b')*c| ≤ 2*B*Lr*|q-q'| := by
    rw [abs_mul, abs_mul]
    have hh := hgate q q'
    calc _ ≤ B*(Lr*|q-q'|)*2 :=
           mul_le_mul (mul_le_mul (hbound x') hh (abs_nonneg _) hB) (hc v)
             (abs_nonneg _) (by positivity)
         _ = _ := by ring
  have h3 : |a'*b'*(c-c')| ≤ (4*B/scale)*|v-v'| := by
    rw [abs_mul, abs_mul]
    have hh := denominatorRoot_dist (v/scale) (v'/scale)
    have he : |v/scale-(v'/scale)| = |v-v'|/scale := by
      rw [← sub_div, abs_div, abs_of_pos hs]
    rw [he] at hh
    calc _ ≤ B*1*(4*(|v-v'|/scale)) := mul_le_mul (mul_le_mul (hbound x') (hrbound q')
      (abs_nonneg _) hB) hh (abs_nonneg _) (by positivity)
         _ = _ := by ring
  have htri : |(a-a')*b*c+a'*(b-b')*c+a'*b'*(c-c')| ≤
      |(a-a')*b*c|+|a'*(b-b')*c|+|a'*b'*(c-c')| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  apply htri.trans
  have hn1 : 0 ≤ 2*Lq := by positivity
  have hn2 : 0 ≤ 2*B*(Lr:ℝ) := by positivity
  have hn3 : 0 ≤ 4*B/scale := by positivity
  nlinarith [abs_nonneg (x-x'), abs_nonneg (v-v'), abs_nonneg (q-q')]

/-- Fourth-root regularity of the clipped decoder for the actual numerator and gate.
The numerator bound is in fourth-root units. No preparation identity is assumed. -/
lemma root_dist_of_bounds (cutoff gate : ℝ → ℝ) {scale cap Lq Lr : ℝ}
    (hs : 0 < scale) (hcap : 0 ≤ cap) (hLq : 0 ≤ Lq) (hLr : 0 ≤ Lr)
    (hcut0 : ∀ x, 0 ≤ cutoff x) (hgate0 : ∀ q, 0 ≤ gate q)
    (hgate1 : ∀ q, gate q ≤ 1)
    (hbound : ∀ x, |cutoff x ^ (4⁻¹ : ℝ)| ≤ cap)
    (hq : ∀ x x', |cutoff x ^ (4⁻¹ : ℝ) - cutoff x' ^ (4⁻¹ : ℝ)| ≤ Lq * |x - x'|)
    (hgate : ∀ q q', |gate q ^ (4⁻¹ : ℝ) - gate q' ^ (4⁻¹ : ℝ)| ≤ Lr * |q - q'|) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x v q x' v' q',
      |output cutoff gate scale x v q ^ (4⁻¹ : ℝ) -
        output cutoff gate scale x' v' q' ^ (4⁻¹ : ℝ)| ≤
        L * (|x - x'| + |v - v'| + |q - q'|) := by
  refine ⟨2 * Lq + 4 * cap / scale + 2 * cap * Lr, by positivity, ?_⟩
  exact root_dist_le_of_bounds cutoff gate hs hcap hLq hLr hcut0 hgate0 hgate1 hbound hq hgate

/-- Global fourth-root regularity for the hierarchy's atom numerator and core gate. -/
lemma root_dist {scale : ℝ} (hs : 0 < scale) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x v q x' v' q',
      |output HP.toHierarchyParams.atomCutoff HP.ρ scale x v q ^ (4⁻¹ : ℝ) -
        output HP.toHierarchyParams.atomCutoff HP.ρ scale x' v' q' ^ (4⁻¹ : ℝ)| ≤
        L * (|x - x'| + |v - v'| + |q - q'|) := by
  obtain ⟨Lq, hLq, hq⟩ := cutoff_root_dist HP
  obtain ⟨⟨Lr, hr⟩, _⟩ := HP.cutoff_roots HP.ρ (by simp)
  refine root_dist_of_bounds _ _ (cap := HP.Q HP.toHierarchyParams.atomCap ^ (4⁻¹ : ℝ))
    hs (Real.rpow_nonneg (HP.Q_nonneg _) _) hLq Lr.coe_nonneg
    HP.toHierarchyParams.atomCutoff_nonneg HP.ρ_nonneg HP.ρ_le_one ?_ hq ?_
  · intro x
    rw [abs_of_nonneg (Real.rpow_nonneg (HP.toHierarchyParams.atomCutoff_nonneg _) _)]
    exact Real.rpow_le_rpow (HP.toHierarchyParams.atomCutoff_nonneg _)
      (HP.toHierarchyParams.atomCutoff_le _) (by norm_num)
  · intro q q'
    simpa only [Real.dist_eq] using hr.dist_le_mul q q'

/-- The actual hierarchy rank is positive. -/
lemma rank_pos : 0 < HP.K := by
  have hg := HP.gate
  have hh : 0 ≤ 32 * (HP.k : ℝ) / HP.η := div_nonneg (by positivity) HP.η_pos.le
  have h : (0 : ℝ) < HP.K := by linarith
  exact_mod_cast h

/-- The fourth root has a uniform range independent of input magnitudes. -/
lemma root_range (scale x v q : ℝ) :
    0 ≤ output HP.toHierarchyParams.atomCutoff HP.ρ scale x v q ^ (4⁻¹ : ℝ) ∧
    output HP.toHierarchyParams.atomCutoff HP.ρ scale x v q ^ (4⁻¹ : ℝ) ≤
      2 * HP.Q HP.toHierarchyParams.atomCap ^ (4⁻¹ : ℝ) := by
  rw [output_root _ _ HP.toHierarchyParams.atomCutoff_nonneg HP.ρ_nonneg]
  have ha := Real.rpow_nonneg (HP.toHierarchyParams.atomCutoff_nonneg x) (4⁻¹ : ℝ)
  have hb := Real.rpow_nonneg (HP.ρ_nonneg q) (4⁻¹ : ℝ)
  have hc := denominatorRoot_bounds (v/scale)
  have ha' := Real.rpow_le_rpow (HP.toHierarchyParams.atomCutoff_nonneg x)
    (HP.toHierarchyParams.atomCutoff_le x) (by norm_num : (0:ℝ) ≤ 4⁻¹)
  have hb' := Real.rpow_le_one (HP.ρ_nonneg q) (HP.ρ_le_one q) (by norm_num : (0:ℝ) ≤ 4⁻¹)
  constructor
  · exact mul_nonneg (mul_nonneg ha hb) (by linarith)
  · calc
      _ ≤ HP.Q HP.toHierarchyParams.atomCap ^ (4⁻¹ : ℝ) * 1 * 2 :=
        mul_le_mul (mul_le_mul ha' hb' hb (Real.rpow_nonneg (HP.Q_nonneg _) _))
          hc.2 (by linarith) (mul_nonneg (Real.rpow_nonneg (HP.Q_nonneg _) _) zero_le_one)
      _ = _ := by ring

/-- The actual entry threshold is separated from the closed rank gate. -/
lemma threshold_margin : 3*HP.η₂ < HP.θ := by
  have h1 := HP.η₂_lt
  have h2 := HP.δ₁_lt
  have h3 := HP.δ₀_lt_δ₁
  linarith [HP.θ_pos]


/-- The actual hierarchy rank exceeds the singleton domain. -/
lemma rank_gt_one : 1 < HP.K := by
  have hg := HP.gate
  have hh : 0 ≤ 32 * (HP.k : ℝ) / HP.η := div_nonneg (by positivity) HP.η_pos.le
  have h : (1 : ℝ) < HP.K := by linarith
  exact_mod_cast h

/-- A numerator threshold separated from the closed gate controls support after
compression, for any state, default and second coordinate. -/
lemma support_of_cutoff (cutoff gate : ℝ → ℝ) {K : ℕ} (hK : 0 < K)
    {e g : ℝ} (he : 0 ≤ e) (hge : g ≤ e)
    (hc : ∀ x, x ≤ e → cutoff x = 0) (hg : ∀ q, g ≤ q → gate q = 0)
    {ι : Type*} (s : Finset ι) (a : State ι) (scale : ℝ) :
    #{y ∈ s | output cutoff gate scale (a.row y 0) (a.row y 1)
      (firstRank s K a.defaultValue a.row) ≠ 0} < K := by
  classical
  by_contra h
  have hsub : ({y ∈ s | output cutoff gate scale (a.row y 0) (a.row y 1)
      (firstRank s K a.defaultValue a.row) ≠ 0} : Finset ι) ⊆
      {y ∈ s | e < a.row y 0} := by
    intro y hy
    refine mem_filter.mpr ⟨(mem_filter.mp hy).1, ?_⟩
    by_contra hx
    exact (mem_filter.mp hy).2 (by simp only [output, hc _ (not_lt.mp hx), zero_mul, zero_div])
  have hq : e < kthLargest K s (fun y => a.row y 0) :=
    (lt_kthLargest_iff hK he).mpr ((not_lt.mp h).trans (card_le_card hsub))
  obtain ⟨y, hy⟩ := card_pos.mp (hK.trans_le (not_lt.mp h))
  exact (mem_filter.mp hy).2 (by
    simp only [output, hg _ (hge.trans (hq.le.trans kthLargest_le_firstRank)),
      mul_zero, zero_div])

/-- All actual normalized compressed states have fewer than K nonzero retained endpoints,
including arbitrary defaults and arbitrary second signals. -/
lemma support {ι : Type*} (s : Finset ι) (a : State ι) (scale : ℝ) :
    #{y ∈ s | output HP.toHierarchyParams.atomCutoff HP.ρ scale (a.row y 0) (a.row y 1)
      (firstRank s HP.K a.defaultValue a.row) ≠ 0} < HP.K := by
  apply support_of_cutoff _ _ (rank_pos HP) HP.θ_pos.le
    (show HP.η₂ ≤ HP.θ by linarith [threshold_margin HP, HP.η_pos, HP.η_lt_η₂])
    _ HP.ρ_zero
  intro x hx
  have hQ : HP.Q x = 0 := le_antisymm
    (by simpa only [max_eq_right (sub_nonpos.mpr hx)] using HP.Q_le x) (HP.Q_nonneg x)
  exact HP.toHierarchyParams.atomCutoff_eq_zero_of_Q_eq_zero hQ

/-- Only the denominator signal is masked; the raw first signal and its rank are intact. -/
lemma recipe_identity (cutoff gate : ℝ → ℝ) (K : ℕ) {V Γ Ω : Type*} [Fintype V] [Fintype Γ]
    [Fintype Ω]
    (X : Γ → V → Prop) (Y Yt : Ω → V → Prop)
    [∀ σ x, Decidable (X σ x)] [∀ σ x, Decidable (Y σ x)] [∀ σ x, Decidable (Yt σ x)]
    (raw : Matrix V V ℝ) (prep : Γ × Ω → Matrix V V ℝ)
    {ζ : ℝ} (hζ : 0 < ζ) (b : ℝ) (σ : Γ × Ω) (x y : V) :
    DenseRowRecipe.normalized cutoff gate K b X Y Yt raw prep σ x y =
      if Yt σ.2 y then output cutoff gate ζ (raw x y/b)
        (CorrectionRowRecipe.secondChannel X Yt ζ prep σ x y)
        (firstRank {z | Y σ.2 z} K 0 (fun z ν => if ν=0 then raw x z/b else 0)) else 0 := by
  by_cases hy : Yt σ.2 y
  · simp only [DenseRowRecipe.normalized, CorrectionRowRecipe.secondChannel, hy, ↓reduceIte,
    output, clip,
      mul_div_cancel_left₀ _ hζ.ne', firstRank, max_eq_right kthLargest_nonneg, rowGate]
  · simp only [DenseRowRecipe.normalized, hy, ↓reduceIte]


/-- Core scalar reduction, valid also where the preparatory mean is zero. -/
lemma entrySize_eq_first {d ζ q hstart : ℝ} {mask : Prop} [Decidable mask]
    (hd : 0 ≤ d) (hζ : 0 ≤ ζ) (hζh : ζ ≤ hstart)
    (hq : q ∈ Set.Icc 0 1) (hzero : d ≤ hstart → q = 0) :
    entrySize (fun ν : Fin 2 => if ν=0 then d else ζ*(if mask then q else 0)) = d := by
  simp only [entrySize, Fin.isValue, ↓reduceIte, one_ne_zero, abs_of_nonneg hd]
  apply max_eq_left
  by_cases hs : d ≤ hstart
  · simp only [hzero hs, ite_self, mul_zero, abs_zero]; exact hd
  · have hqd : 0 ≤ (if mask then q else 0 : ℝ) := by split_ifs <;> linarith [hq.1]
    have hq1 : (if mask then q else 0 : ℝ) ≤ 1 := by split_ifs <;> linarith [hq.2]
    rw [abs_of_nonneg (mul_nonneg hζ hqd)]
    exact (mul_le_of_le_one_right hζ hq1).trans (hζh.trans (not_le.mp hs).le)

/-- Dummy default entries contribute zero, for every sign and size of the default. -/
lemma default_zero {ι : Type*} (s : Finset ι) (a : State ι) (scale : ℝ) :
    output HP.toHierarchyParams.atomCutoff HP.ρ scale a.defaultValue 0 (firstRank s HP.K
      a.defaultValue a.row) = 0 := by
  by_cases hz : a.defaultValue ≤ HP.θ
  · exact entry_zero HP hz
  · apply gate_zero HP
    have hsep := threshold_margin HP
    have hp := HP.η_pos.trans HP.η_lt_η₂
    have hdefault := default_le_firstRank (s := s) (K := HP.K) (z := a.defaultValue) (w := a.row)
    linarith [not_le.mp hz]



end Matrix.FourthRootHierarchyParams.NormalizedRow
