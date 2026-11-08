/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.Simple
public import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

/-!
# Self-centred geometry of fractional optima

The optimizer conclusions of [XuGaoHu2027], Proposition 5.3, PDF p. 11.
Observations and weights are arbitrary real numbers. Feasibility requires a
positive regressor scatter; the optimizer is global over all feasible box weights.
Attainment and sparsification are separate from these geometric conclusions.
-/

public section

namespace Cslib.LeastSquares.Simple

open scoped BigOperators Topology
open Set Filter

variable {ι : Type*} [Fintype ι]

/-- Scalar feasibility for a simple-regression sign audit. Both denominators
are positive; the cross numerator is mass times the centered cross-scatter. -/
@[expose] def SignFeasible (x y w : ι → ℝ) : Prop :=
  (∀ i, w i ∈ Icc (0 : ℝ) 1) ∧ 0 < mass w ∧
    0 < xNumerator x w ∧ crossNumerator x y w ≤ 0

/-- A genuinely global maximum of retained mass among nonsingular sign reversals. -/
@[expose] def MassOptimal (x y w : ι → ℝ) : Prop :=
  SignFeasible x y w ∧ ∀ u, SignFeasible x y u → mass u ≤ mass w

/-- The hyperbolic score centred at the weights' own centroid. -/
@[expose] noncomputable def centeredScore (x y w : ι → ℝ) (i : ι) : ℝ :=
  (x i - (∑ j, w j * x j) / mass w) *
    (y i - (∑ j, w j * y j) / mass w)

private theorem continuous_mass : Continuous (mass (ι := ι) (𝕜 := ℝ)) := by
  unfold mass
  fun_prop

private theorem continuous_cross (x y : ι → ℝ) :
    Continuous (crossNumerator x y) := by
  unfold crossNumerator mass
  fun_prop

private theorem continuous_variance (x : ι → ℝ) : Continuous (xNumerator x) :=
  continuous_cross x x

/-- Every global optimum is on the zero-scatter boundary, provided the full data
have positive scatter. No sparsity or rational-coordinate premise is used. -/
theorem MassOptimal.cross_eq_zero (x y w : ι → ℝ) (hw : MassOptimal x y w)
    (hfull : 0 < crossNumerator x y (fun _ => 1)) : crossNumerator x y w = 0 := by
  by_contra hn
  have hneg : crossNumerator x y w < 0 := lt_of_le_of_ne hw.1.2.2.2 hn
  let path (t : ℝ) (i : ι) := w i + t * (1 - w i)
  have hpath : Continuous path := by fun_prop
  have h0 : path 0 = w := by ext i; simp [path]
  have he : ∀ᶠ t in 𝓝 (0 : ℝ),
      0 < mass (path t) ∧ 0 < xNumerator x (path t) ∧ crossNumerator x y (path t) < 0 := by
    have hm := ((continuous_mass.comp hpath).continuousAt (x := 0)).eventually
      (lt_mem_nhds (show 0 < mass (path 0) by simpa only [h0] using hw.1.2.1))
    have hv := (((continuous_variance x).comp hpath).continuousAt (x := 0)).eventually
      (lt_mem_nhds (show 0 < xNumerator x (path 0) by simpa only [h0] using hw.1.2.2.1))
    have hc := (((continuous_cross x y).comp hpath).continuousAt (x := 0)).eventually
      (gt_mem_nhds (show crossNumerator x y (path 0) < 0 by simpa only [h0] using hneg))
    exact hm.and (hv.and hc)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp he
  let t := min (δ / 2) (1 / 2 : ℝ)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨hm, hv, hc⟩ := hball (show dist t 0 < δ by simpa [Real.dist_eq, abs_of_pos ht] using htδ)
  have hb : ∀ i, path t i ∈ Icc (0 : ℝ) 1 := by
    intro i
    obtain ⟨hl, hu⟩ := hw.1.1 i
    dsimp only [path]
    constructor <;> nlinarith
  have hmax := hw.2 (path t) ⟨hb, hm, hv, hc.le⟩
  have hex : ∃ i, w i < 1 := by
    by_contra h
    have hw1 : w = fun _ => 1 := by
      funext i
      exact le_antisymm (hw.1.1 i).2 (by simpa using not_exists.mp h i)
    rw [hw1] at hneg
    linarith
  obtain ⟨i, hi⟩ := hex
  have hmass : mass w < mass (path t) := by
    apply Finset.sum_lt_sum
    · intro j _
      dsimp only [path]
      nlinarith [(hw.1.1 j).2]
    · exact ⟨i, Finset.mem_univ i, by dsimp only [path]; nlinarith⟩
  linarith

variable [DecidableEq ι]

/-- Transfer weight from `j` to `i` while keeping mass fixed. -/
@[expose] noncomputable def transfer (w : ι → ℝ) (i j : ι) (t : ℝ) : ι → ℝ :=
  fun k => w k + (if k = i then t else 0) - (if k = j then t else 0)

/-- A transfer preserves total retained mass. -/
theorem mass_transfer (w : ι → ℝ) (i j : ι) (t : ℝ) :
    mass (transfer w i j t) = mass w := by
  simp [mass, transfer, Finset.sum_sub_distrib, Finset.sum_add_distrib]

private theorem moment_transfer (z w : ι → ℝ) (i j : ι) (t : ℝ) :
    (∑ k, transfer w i j t k * z k) = (∑ k, w k * z k) + t * (z i - z j) := by
  simp only [transfer, sub_mul, add_mul, ite_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Exact second-order change along any equal-mass swap direction. -/
theorem cross_transfer (x y w : ι → ℝ) (i j : ι)
    (hm : mass w ≠ 0) (t : ℝ) :
    crossNumerator x y (transfer w i j t) = crossNumerator x y w +
      t * mass w * (centeredScore x y w i - centeredScore x y w j) -
      t ^ 2 * ((x i - x j) * (y i - y j)) := by
  unfold crossNumerator
  rw [mass_transfer w i j t, moment_transfer x, moment_transfer y]
  have hxy := moment_transfer (fun k => x k * y k) w i j t
  simp only [mul_assoc]
  rw [hxy]
  dsimp only [centeredScore]
  field_simp
  ring

private theorem small_transfer (x w : ι → ℝ) (i j : ι) (hij : i ≠ j)
    (hb : ∀ k, w k ∈ Icc (0 : ℝ) 1) (hv : 0 < xNumerator x w)
    (hi : w i < 1) (hj : 0 < w j) (ε : ℝ) (hε : 0 < ε) :
    ∃ t, 0 < t ∧ t < ε ∧ (∀ k, transfer w i j t k ∈ Icc (0 : ℝ) 1) ∧
      0 < xNumerator x (transfer w i j t) := by
  have hcont : Continuous (fun t : ℝ => transfer w i j t) := by
    apply continuous_pi
    intro k
    unfold transfer
    split_ifs <;> fun_prop
  have hz : transfer w i j 0 = w := by
    funext k
    dsimp only [transfer]
    split_ifs <;> ring
  have he := ((continuous_variance x).comp hcont).continuousAt.eventually
    (lt_mem_nhds (show 0 < xNumerator x (transfer w i j 0) by rwa [hz]))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp he
  let t := min (min (δ / 2) (ε / 2)) (min ((1 - w i) / 2) (w j / 2))
  have ht : 0 < t := by dsimp only [t]; positivity
  have hd : t < δ := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have heps : t < ε := ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  have hti : t ≤ (1 - w i) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have htj : t ≤ w j / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨t, ht, heps, ?_, hball (by simpa [Real.dist_eq, abs_of_pos ht] using hd)⟩
  intro k
  by_cases hki : k = i
  · subst k
    simp only [transfer, ite_true, ite_eq_right hij, sub_zero, mem_Icc]
    obtain ⟨hl, hu⟩ := hb i
    constructor <;> linarith
  · by_cases hkj : k = j
    · subst k
      simp only [transfer, ite_true, ite_eq_right hij.symm, add_zero, mem_Icc]
      obtain ⟨hl, hu⟩ := hb j
      constructor <;> linarith
    · simpa only [transfer, ite_eq_right hkj, ite_eq_right hki, add_zero, sub_zero] using hb k

omit [DecidableEq ι] in
private theorem competitor_nonneg (x y w u : ι → ℝ) (hw : MassOptimal x y w)
    (hfull : 0 < crossNumerator x y (fun _ => 1))
    (hb : ∀ i, u i ∈ Icc (0 : ℝ) 1) (hm : mass u = mass w)
    (hv : 0 < xNumerator x u) : 0 ≤ crossNumerator x y u := by
  by_contra hn
  have hu : SignFeasible x y u := ⟨hb, hm ▸ hw.1.2.1, hv, (not_le.mp hn).le⟩
  have ho : MassOptimal x y u := ⟨hu, fun v hv => hm ▸ hw.2 v hv⟩
  have hz := ho.cross_eq_zero x y u hfull
  linarith

omit [DecidableEq ι] in
/-- At a global fractional optimum no admissible exchange can improve the
centred score. These inequalities are derived, not supplied as KKT hypotheses. -/
theorem MassOptimal.score_order (x y w : ι → ℝ) (hw : MassOptimal x y w)
    (hfull : 0 < crossNumerator x y (fun _ => 1)) (i j : ι)
    (hi : w i < 1) (hj : 0 < w j) : centeredScore x y w j ≤ centeredScore x y w i := by
  classical
  by_cases hij : i = j
  · subst j; exact le_rfl
  by_contra hn
  have hd : 0 < mass w * (centeredScore x y w j - centeredScore x y w i) :=
    mul_pos hw.1.2.1 (sub_pos.mpr (not_le.mp hn))
  let A := mass w * (centeredScore x y w j - centeredScore x y w i)
  let B := (x i - x j) * (y i - y j)
  obtain ⟨t, ht, he, hb, hv⟩ := small_transfer x w i j hij hw.1.1 hw.1.2.2.1 hi hj
    (A / (|B| + 1)) (div_pos hd (by positivity))
  have hsmall : t * |B| < A := by
    have := (lt_div_iff₀ (show 0 < |B| + 1 by positivity)).mp he
    nlinarith
  have hprod : 0 < t * (A + t * B) :=
    mul_pos ht (by nlinarith [mul_le_mul_of_nonneg_left (neg_abs_le B) ht.le])
  have hN := competitor_nonneg x y w (transfer w i j t) hw hfull hb
    (mass_transfer w i j t) hv
  rw [cross_transfer x y w i j (ne_of_gt hw.1.2.1) t, hw.cross_eq_zero x y w hfull] at hN
  dsimp only [A, B] at hprod
  nlinarith

omit [DecidableEq ι] in
/-- Any two fractional observations in a global optimum form a weakly
anti-monotone pair. This holds over all real observations. -/
theorem MassOptimal.fractional_pair (x y w : ι → ℝ) (hw : MassOptimal x y w)
    (hfull : 0 < crossNumerator x y (fun _ => 1)) (i j : ι) (hij : i ≠ j)
    (hi : 0 < w i ∧ w i < 1) (hj : 0 < w j ∧ w j < 1) :
    (x i - x j) * (y i - y j) ≤ 0 := by
  classical
  have hs := le_antisymm (hw.score_order x y w hfull i j hi.2 hj.1)
    (hw.score_order x y w hfull j i hj.2 hi.1)
  obtain ⟨t, ht, _, hb, hv⟩ := small_transfer x w i j hij hw.1.1 hw.1.2.2.1 hi.2 hj.1 1
    (by norm_num)
  have hN := competitor_nonneg x y w (transfer w i j t) hw hfull hb (mass_transfer w i j t) hv
  rw [cross_transfer x y w i j (ne_of_gt hw.1.2.1) t, hw.cross_eq_zero x y w hfull, hs] at hN
  have ht2 := sq_pos_of_pos ht
  nlinarith

omit [DecidableEq ι] in
/-- Weighted centred scores sum to the centred cross-scatter. -/
theorem sum_centeredScore (x y w : ι → ℝ) (hm : mass w ≠ 0) :
    (∑ i, w i * centeredScore x y w i) = crossNumerator x y w / mass w := by
  have he (i : ι) : w i * centeredScore x y w i =
      w i * x i * y i - ((∑ j, w j * y j) / mass w) * (w i * x i) -
      ((∑ j, w j * x j) / mass w) * (w i * y i) +
      (((∑ j, w j * x j) * (∑ j, w j * y j)) / mass w ^ 2) * w i := by
    dsimp only [centeredScore]
    field_simp
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  change _ = _
  dsimp only [crossNumerator]
  change _ - _ - _ + _ * mass w = _
  field_simp
  ring

omit [DecidableEq ι] in
/-- Proposition 5.3's self-centred range conclusion for every global optimum.
A maximum supported score is a threshold; fractional coordinates lie on it.
Either that threshold is positive or every supported score vanishes. -/
theorem MassOptimal.self_centered (x y w : ι → ℝ) (hw : MassOptimal x y w)
    (hfull : 0 < crossNumerator x y (fun _ => 1)) :
    crossNumerator x y w = 0 ∧ ∃ τ : ℝ,
      (∀ i, 0 < w i → centeredScore x y w i ≤ τ) ∧
      (∀ i, w i < 1 → τ ≤ centeredScore x y w i) ∧
      (∀ i, 0 < w i ∧ w i < 1 → centeredScore x y w i = τ) ∧
      (0 < τ ∨ ∀ i, 0 < w i → centeredScore x y w i = 0) := by
  classical
  have hn : (Finset.univ.filter fun i => 0 < w i).Nonempty := by
    by_contra h
    have hz : ∀ i, w i = 0 := by
      intro i
      have hi : ¬ 0 < w i := by
        intro hi
        exact h ⟨i, by simp [hi]⟩
      linarith [(hw.1.1 i).1]
    have hm := hw.1.2.1
    simp [mass, hz] at hm
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image _ (centeredScore x y w) hn
  have hjp : 0 < w j := (Finset.mem_filter.mp hj).2
  have hupper : ∀ i, 0 < w i → centeredScore x y w i ≤ centeredScore x y w j :=
    fun i hi => hmax i (by simp [hi])
  have hlower : ∀ i, w i < 1 → centeredScore x y w j ≤ centeredScore x y w i :=
    fun i hi => hw.score_order x y w hfull i j hi hjp
  refine ⟨hw.cross_eq_zero x y w hfull, centeredScore x y w j, hupper, hlower,
    fun i hi => le_antisymm (hupper i hi.1) (hlower i hi.2), ?_⟩
  by_cases ht : 0 < centeredScore x y w j
  · exact Or.inl ht
  · right
    have hsum : (∑ i, w i * centeredScore x y w i) = 0 := by
      rw [sum_centeredScore x y w (ne_of_gt hw.1.2.1), hw.cross_eq_zero x y w hfull, zero_div]
    have hterm : ∀ i, w i * centeredScore x y w i ≤ 0 := by
      intro i
      by_cases hi : 0 < w i
      · exact mul_nonpos_of_nonneg_of_nonpos (hw.1.1 i).1 ((hupper i hi).trans (not_lt.mp ht))
      · have hz : w i = 0 := le_antisymm (not_lt.mp hi) (hw.1.1 i).1
        simp [hz]
    intro i hi
    have hz : w i * centeredScore x y w i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos (fun k _ => hterm k)).mp hsum i (Finset.mem_univ i)
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hi)

end Cslib.LeastSquares.Simple
