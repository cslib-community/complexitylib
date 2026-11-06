/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.Hypersimplex
public import Complexity.Statistics.LeastSquares.FractionalGeometry
public import Complexity.Statistics.LeastSquares.RadonGeometry
import Mathlib.Tactic

/-!
# The fixed-size saddle relaxation

The exact convex-hull model and fixed-mass optimization in [XuGaoHu2027],
Sections 5.1–5.2, PDF pp. 10–11. Unlike sign-audit feasibility, this relaxation
includes singular weights and has no sign assumption on the observations.
-/

noncomputable section

public section

namespace Cslib.LeastSquares.Geometry

open Set Matrix Submodule
open scoped BigOperators Topology

variable {ι : Type*} [Fintype ι]

/-- The three-dimensional saddle lift in the paper's `(Z,P,Q)` order. -/
@[expose] def saddle (p : ι → ℝ × ℝ) (i : ι) : Fin 3 → ℝ :=
  ![(p i).1 * (p i).2, (p i).1, (p i).2]

/-- Sum of weighted lifted observations. -/
@[expose] def liftedSum (p : ι → ℝ × ℝ) : (ι → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  { toFun := fun w => ∑ i, w i • saddle p i
    map_add' := by intro u v; simp [add_smul, Finset.sum_add_distrib]
    map_smul' := by intro a w; simp [mul_smul, Finset.smul_sum] }

/-- The actual convex hull of all lifted sums of `m` original observations. -/
@[expose] def setPolytope (p : ι → ℝ × ℝ) (m : ℕ) : Set (Fin 3 → ℝ) :=
  convexHull ℝ ((liftedSum p) '' subsetIndicators m)

/-- The indefinite objective on the saddle-sum polytope. -/
@[expose] def saddleObjective (m : ℕ) (v : Fin 3 → ℝ) : ℝ :=
  v 0 - v 1 * v 2 / m

/-- The full box relaxation maps onto the actual `m`-set polytope. This is an
exact representation theorem, not a premise restricting minimizers. -/
theorem setPolytope_eq_image (p : ι → ℝ × ℝ) (m : ℕ) :
    setPolytope p m = (liftedSum p) '' hypersimplex m := by
  rw [hypersimplex_eq_convexHull, LinearMap.image_convexHull]
  rfl

/-- The polytope objective is precisely centered cross-scatter at fixed mass. -/
theorem saddleObjective_liftedSum (p : ι → ℝ × ℝ) (m : ℕ) (hm : m ≠ 0)
    (w : ι → ℝ) (hw : w ∈ hypersimplex m) :
    saddleObjective m (liftedSum p w) =
      Simple.crossNumerator (fun i => (p i).1) (fun i => (p i).2) w / m := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  simp only [saddleObjective, liftedSum, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, saddle, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Simple.crossNumerator, Simple.mass, hw.2]
  field_simp

/-- Global minimizers of the fixed-mass relaxation; singular designs are allowed. -/
@[expose] def FixedMassOptimal (p : ι → ℝ × ℝ) (m : ℕ) (w : ι → ℝ) : Prop :=
  w ∈ hypersimplex m ∧ ∀ u ∈ hypersimplex m,
    Simple.crossNumerator (fun i => (p i).1) (fun i => (p i).2) w ≤
      Simple.crossNumerator (fun i => (p i).1) (fun i => (p i).2) u

/-- Compactness derives an optimizer over all box weights of the given mass. -/
theorem exists_fixedMassOptimal (p : ι → ℝ × ℝ) (m : ℕ)
    (hm : m ≤ Fintype.card ι) : ∃ w, FixedMassOptimal p m w := by
  classical
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq
    (show m ≤ (Finset.univ : Finset ι).card by simpa using hm)
  have hn : (hypersimplex (ι := ι) m).Nonempty := by
    refine ⟨fun i => if i ∈ s then 1 else 0, ?_⟩
    exact ⟨fun i => by dsimp only; split_ifs <;> norm_num, by simp [hs]⟩
  obtain ⟨w, hw, hmin⟩ := (isCompact_hypersimplex m).exists_isMinOn hn
    (show ContinuousOn (Simple.crossNumerator (fun i => (p i).1) (fun i => (p i).2))
      (hypersimplex m) by unfold Simple.crossNumerator Simple.mass; fun_prop)
  exact ⟨w, hw, hmin⟩

omit [Fintype ι] in
open Classical in
private theorem transfer_box (w : ι → ℝ) (i j : ι) (hij : i ≠ j)
    (hw : ∀ k, w k ∈ Icc (0 : ℝ) 1) (t : ℝ)
    (ht : 0 ≤ t) (hti : t ≤ 1 - w i) (htj : t ≤ w j) :
    ∀ k, Simple.transfer w i j t k ∈ Icc (0 : ℝ) 1 := by
  classical
  intro k
  by_cases hki : k = i
  · subst k
    simp only [Simple.transfer, ite_true, ite_eq_right hij, sub_zero, mem_Icc]
    constructor <;> linarith [(hw i).1]
  · by_cases hkj : k = j
    · subst k
      simp only [Simple.transfer, ite_true, ite_eq_right hij.symm, add_zero, mem_Icc]
      constructor <;> linarith [(hw j).2]
    · simpa only [Simple.transfer, ite_eq_right hki, ite_eq_right hkj, add_zero,
        sub_zero] using hw k

/-- First-order score inequalities follow from the actual global relaxation
minimum, with no KKT or stationarity hypothesis. -/
theorem FixedMassOptimal.score_order (p : ι → ℝ × ℝ) (m : ℕ) (w : ι → ℝ)
    (hw : FixedMassOptimal p m w) (hm : 0 < m) (i j : ι)
    (hi : w i < 1) (hj : 0 < w j) :
    Simple.centeredScore (fun k => (p k).1) (fun k => (p k).2) w j ≤
      Simple.centeredScore (fun k => (p k).1) (fun k => (p k).2) w i := by
  classical
  by_cases hij : i = j
  · subst j; exact le_rfl
  by_contra hn
  let x := fun k => (p k).1
  let y := fun k => (p k).2
  let A := Simple.mass w * (Simple.centeredScore x y w j - Simple.centeredScore x y w i)
  let B := (x i - x j) * (y i - y j)
  have hmR : 0 < Simple.mass w := by change 0 < ∑ k, w k; rw [hw.1.2]; positivity
  have hA : 0 < A := mul_pos hmR (sub_pos.mpr (not_le.mp hn))
  let t := min (min ((1 - w i) / 2) (w j / 2)) (A / (2 * (|B| + 1)))
  have ht : 0 < t := by dsimp only [t]; positivity
  have hti : t ≤ 1 - w i := ((min_le_left _ _).trans (min_le_left _ _)).trans (by linarith)
  have htj : t ≤ w j := ((min_le_left _ _).trans (min_le_right _ _)).trans (by linarith)
  have htA : t * |B| < A := by
    have hbound : t ≤ A / (2 * (|B| + 1)) := min_le_right _ _
    have h := (le_div_iff₀ (show 0 < 2 * (|B| + 1) by positivity)).mp hbound
    change t * (2 * (|B| + 1)) ≤ A at h
    nlinarith [abs_nonneg B]
  have hc := hw.2 (Simple.transfer w i j t)
    ⟨transfer_box w i j hij hw.1.1 t ht.le hti htj,
      (Simple.mass_transfer w i j t).trans hw.1.2⟩
  rw [Simple.cross_transfer x y w i j (ne_of_gt hmR) t] at hc
  have hp : 0 < t * (A + t * B) :=
    mul_pos ht (by nlinarith [mul_le_mul_of_nonneg_left (neg_abs_le B) ht.le])
  dsimp only [A, B] at hp
  nlinarith

omit [Fintype ι] in
private theorem box_direction [Finite ι] (w v : ι → ℝ) (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1)
    (hv : ∀ i, v i ≠ 0 → 0 < w i ∧ w i < 1) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ i, w i + t * v i ∈ Icc (0 : ℝ) 1 := by
  apply Filter.eventually_all.mpr
  intro i
  by_cases hi : v i = 0
  · exact Filter.Eventually.of_forall fun t => by simpa [hi] using hw i
  · have hc : Continuous (fun t : ℝ => w i + t * v i) := by fun_prop
    have he : ∀ᶠ t : ℝ in 𝓝 0, w i + t * v i ∈ Ioo (0 : ℝ) 1 :=
      hc.continuousAt (x := 0) (isOpen_Ioo.mem_nhds
      (show w i + 0 * v i ∈ Ioo (0 : ℝ) 1 by simpa using hv i hi))
    exact he.mono fun _ h => ⟨h.1.le, h.2.le⟩

/-- A supported two-sided perturbation at a minimum cannot have positively
correlated regressor/response moments. This is the indefinite-Hessian step. -/
theorem FixedMassOptimal.direction_product_nonpos (p : ι → ℝ × ℝ) (m : ℕ)
    (w v : ι → ℝ) (hw : FixedMassOptimal p m w)
    (hv : ∀ i, v i ≠ 0 → 0 < w i ∧ w i < 1) (hs : ∑ i, v i = 0) :
    (∑ i, v i * (p i).1) * (∑ i, v i * (p i).2) ≤ 0 := by
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp (box_direction w v hw.1.1 hv)
  let t := δ / 2
  have ht : 0 < t := half_pos hδ
  have hbp := hb (y := t) (by simpa [Real.dist_eq, t, abs_of_pos hδ] using (half_lt_self hδ))
  have hbn := hb (y := -t) (by simpa [Real.dist_eq, t, abs_of_pos hδ] using (half_lt_self hδ))
  have hmass (r : ℝ) : (∑ i, (w i + r * v i)) = m := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs, mul_zero, add_zero, hw.1.2]
  have hp := hw.2 _ ⟨hbp, hmass t⟩
  have hn := hw.2 _ ⟨hbn, hmass (-t)⟩
  have he (r : ℝ) : Simple.crossNumerator (fun i => (p i).1) (fun i => (p i).2)
      (fun i => w i + r * v i) =
      (m : ℝ) * ((∑ i, w i * (p i).1 * (p i).2) +
        r * (∑ i, v i * (p i).1 * (p i).2)) -
      ((∑ i, w i * (p i).1) + r * (∑ i, v i * (p i).1)) *
      ((∑ i, w i * (p i).2) + r * (∑ i, v i * (p i).2)) := by
    simp only [Simple.crossNumerator, Simple.mass, hmass, add_mul,
      Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [he] at hp hn
  have hwc : Simple.crossNumerator (fun i => (p i).1) (fun i => (p i).2) w =
      (m : ℝ) * (∑ i, w i * (p i).1 * (p i).2) -
      (∑ i, w i * (p i).1) * (∑ i, w i * (p i).2) := by
    rw [Simple.crossNumerator, Simple.mass, hw.1.2]
  rw [hwc] at hp hn
  nlinarith [sq_pos_of_pos ht]

omit [Fintype ι] in
private theorem planar_independent_plane (p : ι → ℝ × ℝ)
    (hgp : LiftedGeneralPosition p) (s : Finset ι) (hs : s.card ≤ 4)
    (c : Fin 4 → ℝ) (hc : c 0 = 1) (ht : ∀ i ∈ s, lift p i ⬝ᵥ c = 0) :
    LinearIndependent ℝ (fun i : s => (![(p i).1, (p i).2, 1] : Fin 3 → ℝ)) := by
  let T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
    { toFun := fun v => ![-c 1 * v 0 - c 2 * v 1 - c 3 * v 2, v 0, v 1, v 2]
      map_add' := by intro a b; ext j; fin_cases j <;> simp; ring
      map_smul' := by intro a v; ext j; fin_cases j <;> simp; ring }
  have he : T ∘ (fun i : s => (![(p i).1, (p i).2, 1] : Fin 3 → ℝ)) =
      (fun i : s => lift p i) := by
    funext i
    have hi := ht i i.property
    simp only [dotProduct, Fin.sum_univ_four] at hi
    change (p i).1 * (p i).2 * c 0 + (p i).1 * c 1 + (p i).2 * c 2 + 1 * c 3 = 0 at hi
    rw [hc, mul_one, one_mul] at hi
    ext j
    fin_cases j <;> simp [T, lift]; nlinarith [hi]
  apply LinearIndependent.of_comp T
  rw [he]
  exact hgp s hs

private theorem planar_independent (p : ι → ℝ × ℝ) (w : ι → ℝ)
    (hgp : LiftedGeneralPosition p) (s : Finset ι) (hs : s.card ≤ 4)
    (τ : ℝ) (ht : ∀ i ∈ s,
      Simple.centeredScore (fun k => (p k).1) (fun k => (p k).2) w i = τ) :
    LinearIndependent ℝ (fun i : s => (![(p i).1, (p i).2, 1] : Fin 3 → ℝ)) := by
  let μ := (∑ i, w i * (p i).1) / Simple.mass w
  let ν := (∑ i, w i * (p i).2) / Simple.mass w
  apply planar_independent_plane p hgp s hs ![1, -ν, -μ, μ * ν - τ] rfl
  intro i hi
  have hh := ht i hi
  change ((p i).1 - μ) * ((p i).2 - ν) = τ at hh
  simp [lift, dotProduct, Fin.sum_univ_four]
  nlinarith [hh]

open Classical in
/-- Every minimizer has at most two fractional coordinates under lifted general
position. This is proved for every representation in the entire fixed-mass box,
not for a selected sparse or stationary candidate. -/
theorem FixedMassOptimal.fractional_card_le_two (p : ι → ℝ × ℝ) (m : ℕ)
    (w : ι → ℝ) (hw : FixedMassOptimal p m w) (hm : 0 < m)
    (hgp : LiftedGeneralPosition p) :
    (Finset.univ.filter fun i => 0 < w i ∧ w i < 1).card ≤ 2 := by
  classical
  by_contra hn
  obtain ⟨s, hsub, hs⟩ := Finset.exists_subset_card_eq
    (show 3 ≤ (Finset.univ.filter fun i => 0 < w i ∧ w i < 1).card by omega)
  have hfrac (i : s) : 0 < w i ∧ w i < 1 := (Finset.mem_filter.mp (hsub i.property)).2
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
  let τ := Simple.centeredScore (fun k => (p k).1) (fun k => (p k).2) w j
  have ht : ∀ i ∈ s,
      Simple.centeredScore (fun k => (p k).1) (fun k => (p k).2) w i = τ := by
    intro i hi
    exact le_antisymm (hw.score_order p m w hm j i (hfrac ⟨j, hj⟩).2 (hfrac ⟨i, hi⟩).1)
      (hw.score_order p m w hm i j (hfrac ⟨i, hi⟩).2 (hfrac ⟨j, hj⟩).1)
  let a := fun i : s => (![(p i).1, (p i).2, 1] : Fin 3 → ℝ)
  have hind : LinearIndependent ℝ a := planar_independent p w hgp s (by omega) τ ht
  have hspan : span ℝ (range a) = ⊤ :=
    hind.span_eq_top_of_card_eq_finrank' (by simp [hs])
  have hmem : (![1, 1, 0] : Fin 3 → ℝ) ∈ span ℝ (range a) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  let v : ι → ℝ := fun i => if hi : i ∈ s then c ⟨i, hi⟩ else 0
  have he (f : ι → ℝ) : (∑ i, v i * f i) = ∑ i : s, c i * f i := by
    calc
      _ = ∑ i ∈ s, v i * f i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro i _ hi
        simp [v, hi]
      _ = _ := by
        rw [Finset.sum_subtype s (fun _ => Iff.rfl) (fun i => v i * f i)]
        apply Finset.sum_congr rfl
        intro i _
        simp [v, i.property]
  have hx : (∑ i, v i * (p i).1) = 1 := by
    rw [he]
    simpa [a, Finset.sum_apply] using congrFun hc 0
  have hy : (∑ i, v i * (p i).2) = 1 := by
    rw [he]
    simpa [a, Finset.sum_apply] using congrFun hc 1
  have hz : (∑ i, v i) = 0 := by
    have hh := he (fun _ => 1)
    simp only [mul_one] at hh
    rw [hh]
    simpa [a, Finset.sum_apply] using congrFun hc 2
  have hv : ∀ i, v i ≠ 0 → 0 < w i ∧ w i < 1 := by
    intro i hi
    have his : i ∈ s := by by_contra hn; exact hi (by simp [v, hn])
    exact hfrac ⟨i, his⟩
  have hp := hw.direction_product_nonpos p m w v hv hz
  rw [hx, hy] at hp
  norm_num at hp

private theorem interpolate_planar {J : Type*}
    (a : J → Fin 3 → ℝ) (hi : LinearIndependent ℝ a) (z : J → ℝ) :
    ∃ c : Fin 3 → ℝ, ∀ i, a i ⬝ᵥ c = z i := by
  classical
  let V := span ℝ (range a)
  obtain ⟨Q, hQ⟩ := V.exists_isCompl
  let L : (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
    (Finsupp.linearCombination ℝ z).comp (hi.repr.comp (V.projectionOnto Q hQ))
  have hL (i : J) : L (a i) = z i := by
    have hr : hi.repr ⟨a i, subset_span ⟨i, rfl⟩⟩ = Finsupp.single i 1 :=
      hi.repr_eq (by simp)
    change (Finsupp.linearCombination ℝ z)
      (hi.repr (V.projectionOnto Q hQ (a i))) = z i
    rw [show V.projectionOnto Q hQ (a i) = ⟨a i, subset_span ⟨i, rfl⟩⟩ from
      Submodule.projectionOnto_apply_left hQ ⟨a i, subset_span ⟨i, rfl⟩⟩, hr]
    simp
  refine ⟨fun j => L (Pi.single j 1), fun i => ?_⟩
  rw [← hL i, LinearMap.pi_apply_eq_sum_univ L (a i)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_eq_mul]
  congr 2
  ext k
  simp [Pi.single_apply, eq_comm]

omit [Fintype ι] in
private theorem plane_card_le_three (p : ι → ℝ × ℝ) (hgp : LiftedGeneralPosition p)
    (c : Fin 4 → ℝ) (hc : c 0 = 1) (s : Finset ι)
    (hs : ∀ i ∈ s, lift p i ⬝ᵥ c = 0) : s.card ≤ 3 := by
  by_contra hn
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq (show 4 ≤ s.card by omega)
  have hi := planar_independent_plane p hgp t (by omega) c hc (fun i hi => hs i (hts hi))
  have hb := hi.fintype_card_le_finrank
  simp only [Fintype.card_coe, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, ht] at hb
  omega

omit [Fintype ι] in
private theorem refine_plane [Finite ι] (p : ι → ℝ × ℝ) (hgp : LiftedGeneralPosition p)
    (c : Fin 4 → ℝ) (hc : c 0 = 1) (z : ι → ℝ)
    (hn : ∀ i, lift p i ⬝ᵥ c < 0 → z i < 0)
    (hp : ∀ i, 0 < lift p i ⬝ᵥ c → 0 < z i) :
    ∃ d : Fin 4 → ℝ, d 0 = 1 ∧ ∀ i,
      (z i < 0 → lift p i ⬝ᵥ d < 0) ∧
      (z i = 0 → lift p i ⬝ᵥ d = 0) ∧
      (0 < z i → 0 < lift p i ⬝ᵥ d) := by
  classical
  let := Fintype.ofFinite ι
  let E := Finset.univ.filter fun i => lift p i ⬝ᵥ c = 0
  have hE : ∀ i ∈ E, lift p i ⬝ᵥ c = 0 := fun i hi => (Finset.mem_filter.mp hi).2
  have hind := planar_independent_plane p hgp E
    ((plane_card_le_three p hgp c hc E hE).trans (by norm_num)) c hc hE
  obtain ⟨q, hq⟩ := interpolate_planar
    (fun i : E => (![(p i).1, (p i).2, 1] : Fin 3 → ℝ)) hind (fun i => z i)
  let d (t : ℝ) : Fin 4 → ℝ := c + t • ![0, q 0, q 1, q 2]
  have hd (t : ℝ) (i : ι) : lift p i ⬝ᵥ d t = lift p i ⬝ᵥ c +
      t * ((![(p i).1, (p i).2, 1] : Fin 3 → ℝ) ⬝ᵥ q) := by
    simp [d, dotProduct, lift, Fin.sum_univ_four, Fin.sum_univ_three,
      Matrix.vecHead, Matrix.vecTail]
    ring
  have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, i ∉ E →
      (z i < 0 → lift p i ⬝ᵥ d t < 0) ∧
      (z i = 0 → lift p i ⬝ᵥ d t = 0) ∧
      (0 < z i → 0 < lift p i ⬝ᵥ d t) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i ∈ E
    · exact Filter.Eventually.of_forall fun t h => (h hi).elim
    have hne : lift p i ⬝ᵥ c ≠ 0 := by simpa [E] using hi
    have hcont : Continuous (fun t : ℝ => lift p i ⬝ᵥ d t) := by simp_rw [hd]; fun_prop
    have hz : lift p i ⬝ᵥ d 0 = lift p i ⬝ᵥ c := by rw [hd]; ring
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have ht := hcont.continuousAt.eventually (gt_mem_nhds (hz ▸ hneg))
      exact ht.mono fun t ht _ => ⟨fun _ => ht, fun h => by linarith [hn i hneg],
        fun h => by linarith [hn i hneg]⟩
    · have ht := hcont.continuousAt.eventually (lt_mem_nhds (hz ▸ hpos))
      exact ht.mono fun t ht _ => ⟨fun h => by linarith [hp i hpos],
        fun h => by linarith [hp i hpos], fun _ => ht⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp he
  let t := δ / 2
  have ht : 0 < t := half_pos hδ
  have hsmall := hball (y := t) (by simpa [Real.dist_eq, t, abs_of_pos hδ] using half_lt_self hδ)
  refine ⟨d t, by simpa only [d, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, mul_zero, add_zero] using hc, fun i => ?_⟩
  by_cases hi : i ∈ E
  · have hval : lift p i ⬝ᵥ d t = t * z i := by rw [hd, hE i hi, hq ⟨i, hi⟩]; ring
    rw [hval]
    exact ⟨fun h => mul_neg_of_pos_of_neg ht h, fun h => by simp [h], fun h => mul_pos ht h⟩
  · exact hsmall i hi

/-- A strict lower supporting plane at an optimum: integral coordinates lie
strictly on their appropriate sides, and only fractional coordinates remain on
the plane. Its leading saddle coefficient is one. -/
theorem FixedMassOptimal.lower_certificate (p : ι → ℝ × ℝ) (m : ℕ)
    (w : ι → ℝ) (hw : FixedMassOptimal p m w) (hm : 0 < m)
    (hgp : LiftedGeneralPosition p) :
    ∃ c : Fin 4 → ℝ, c 0 = 1 ∧ ∀ i,
      (w i = 1 → lift p i ⬝ᵥ c < 0) ∧
      (w i = 0 → 0 < lift p i ⬝ᵥ c) ∧
      (0 < w i ∧ w i < 1 → lift p i ⬝ᵥ c = 0) := by
  classical
  let h := Simple.centeredScore (fun i => (p i).1) (fun i => (p i).2) w
  let S := Finset.univ.filter fun i => 0 < w i
  have hS : S.Nonempty := by
    by_contra hn
    have hz : ∀ i, w i = 0 := by
      intro i
      have hi : ¬ 0 < w i := by intro hi; exact hn ⟨i, by simp [S, hi]⟩
      exact le_antisymm (not_lt.mp hi) (hw.1.1 i).1
    have he := hw.1.2
    simp only [hz, Finset.sum_const_zero] at he
    have hh : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    linarith
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image S h hS
  have hjp : 0 < w j := (Finset.mem_filter.mp hj).2
  let μ := (∑ i, w i * (p i).1) / Simple.mass w
  let ν := (∑ i, w i * (p i).2) / Simple.mass w
  let c : Fin 4 → ℝ := ![1, -ν, -μ, μ * ν - h j]
  have hc (i : ι) : lift p i ⬝ᵥ c = h i - h j := by
    simp [lift, c, h, Simple.centeredScore, dotProduct, Fin.sum_univ_four, μ, ν]
    ring
  let z := fun i => if w i = 1 then (-1 : ℝ) else if w i = 0 then 1 else 0
  have hn : ∀ i, lift p i ⬝ᵥ c < 0 → z i < 0 := by
    intro i hi
    have he : w i = 1 := by
      by_contra hne
      have hl : w i < 1 := lt_of_le_of_ne (hw.1.1 i).2 hne
      have hh := hw.score_order p m w hm i j hl hjp
      rw [hc] at hi
      change h j ≤ h i at hh
      linarith
    simp [z, he]
  have hp : ∀ i, 0 < lift p i ⬝ᵥ c → 0 < z i := by
    intro i hi
    have he : w i = 0 := by
      by_contra hne
      have hl : 0 < w i := lt_of_le_of_ne (hw.1.1 i).1 (Ne.symm hne)
      have hh := hmax i (by simp [S, hl])
      rw [hc] at hi
      linarith
    simp [z, he]
  obtain ⟨d, hd, hsign⟩ := refine_plane p hgp c rfl z hn hp
  refine ⟨d, hd, fun i => ⟨?_, ?_, ?_⟩⟩
  · intro hi
    exact (hsign i).1 (by simp [z, hi])
  · intro hi
    exact (hsign i).2.2 (by simp [z, hi])
  · intro hi
    exact (hsign i).2.1 (by simp [z, ne_of_gt hi.1, ne_of_lt hi.2])

/-- A lower vertex certificate in original observations. It is a strict
hyperbolic range, with positive coefficient on the saddle coordinate. -/
@[expose] def IsLowerRange (p : ι → ℝ × ℝ) (S : Finset ι) : Prop :=
  ∃ c : Fin 4 → ℝ, c 0 = 1 ∧ (∀ i ∈ S, lift p i ⬝ᵥ c < 0) ∧
    ∀ i ∉ S, 0 < lift p i ⬝ᵥ c

omit [Fintype ι] in
/-- The lower-vertex certificate is exactly a strict axis-parallel hyperbolic
sublevel set, as in the paper. -/
theorem isLowerRange_iff (p : ι → ℝ × ℝ) (S : Finset ι) :
    IsLowerRange p S ↔ ∃ μ ν τ : ℝ,
      (∀ i ∈ S, ((p i).1 - μ) * ((p i).2 - ν) < τ) ∧
      ∀ i ∉ S, τ < ((p i).1 - μ) * ((p i).2 - ν) := by
  constructor
  · rintro ⟨c, hc, hn, hp⟩
    have he (i : ι) : lift p i ⬝ᵥ c =
        ((p i).1 + c 2) * ((p i).2 + c 1) - (c 1 * c 2 - c 3) := by
      simp [lift, dotProduct, Fin.sum_univ_four, hc]
      ring
    refine ⟨-c 2, -c 1, c 1 * c 2 - c 3, ?_, ?_⟩
    · intro i hi; have hh := hn i hi; rw [he] at hh; simpa using hh
    · intro i hi; have hh := hp i hi; rw [he] at hh; simpa using hh
  · rintro ⟨μ, ν, τ, hn, hp⟩
    have he (i : ι) : lift p i ⬝ᵥ ![1, -ν, -μ, μ * ν - τ] =
        ((p i).1 - μ) * ((p i).2 - ν) - τ := by
      simp [lift, dotProduct, Fin.sum_univ_four]
      ring
    refine ⟨![1, -ν, -μ, μ * ν - τ], rfl, ?_, ?_⟩
    · intro i hi; rw [he]; linarith [hn i hi]
    · intro i hi; rw [he]; linarith [hp i hi]

/-- A lower swap edge: precisely the common retained set is strictly below a
supporting plane, the two exchanged observations lie on it, and all remaining
observations lie strictly above it. -/
@[expose] def IsLowerSwap (p : ι → ℝ × ℝ) (R : Finset ι) (i j : ι) : Prop :=
  ∃ c : Fin 4 → ℝ, c 0 = 1 ∧ lift p i ⬝ᵥ c = 0 ∧ lift p j ⬝ᵥ c = 0 ∧
    (∀ k ∈ R, lift p k ⬝ᵥ c < 0) ∧
    ∀ k, k ∉ R → k ≠ i → k ≠ j → 0 < lift p k ⬝ᵥ c

open Classical in
/-- The fixed-size relaxation dichotomy, in original-observation coordinates.
Either a lower hyperbolic range attains the global relaxation minimum, or every
minimizer is an interior point of a lower swap edge with a strictly
anti-monotone exchanged pair. This quantifies over the full box relaxation. -/
theorem fixedMass_dichotomy (p : ι → ℝ × ℝ) (m : ℕ) (hm : 0 < m)
    (hgp : LiftedGeneralPosition p) :
    (∃ S : Finset ι, S.card = m ∧ IsLowerRange p S ∧
      FixedMassOptimal p m (fun i => if i ∈ S then 1 else 0)) ∨
    (∀ w, FixedMassOptimal p m w →
      ∃ (R : Finset ι) (i j : ι) (t : ℝ), i ≠ j ∧ i ∉ R ∧ j ∉ R ∧
        R.card + 1 = m ∧ 0 < t ∧ t < 1 ∧
        IsLowerSwap p R i j ∧ ((p i).1 - (p j).1) * ((p i).2 - (p j).2) < 0 ∧
        ∀ k, w k = if k ∈ R then 1 else if k = i then 1 - t else if k = j then t else 0) := by
  classical
  by_cases hint : ∃ w, FixedMassOptimal p m w ∧ ∀ i, w i = 0 ∨ w i = 1
  · left
    obtain ⟨w, hw, hwi⟩ := hint
    let S := Finset.univ.filter fun i => w i = 1
    have he : w = fun i => if i ∈ S then 1 else 0 := by
      funext i
      rcases hwi i with hi | hi <;> simp [S, hi]
    have hcard : S.card = m := by
      have hh := hw.1.2
      rw [he] at hh
      exact_mod_cast (by simpa using hh : (S.card : ℝ) = m)
    obtain ⟨c, hc, hs⟩ := hw.lower_certificate p m w hm hgp
    refine ⟨S, hcard, ⟨c, hc, ?_, ?_⟩, he ▸ hw⟩
    · intro i hi
      exact (hs i).1 ((Finset.mem_filter.mp hi).2)
    · intro i hi
      have hzero : w i = 0 := by rw [he]; simp [hi]
      exact (hs i).2.1 hzero
  · right
    intro w hw
    obtain hwi | ⟨R, i, j, t, hij, hiR, hjR, hcard, ht, ht1, hform⟩ :=
      hypersimplex_indicator_or_swap m w hw.1 (hw.fractional_card_le_two p m w hm hgp)
    · exact (hint ⟨w, hw, hwi⟩).elim
    have hiw : w i = 1 - t := by simpa [hiR] using hform i
    have hjw : w j = t := by simpa [hjR, hij.symm] using hform j
    have hfi : 0 < w i ∧ w i < 1 := by rw [hiw]; constructor <;> linarith
    have hfj : 0 < w j ∧ w j < 1 := by rw [hjw]; exact ⟨ht, ht1⟩
    obtain ⟨c, hc, hsign⟩ := hw.lower_certificate p m w hm hgp
    have hlow : IsLowerSwap p R i j := by
      refine ⟨c, hc, (hsign i).2.2 hfi, (hsign j).2.2 hfj, ?_, ?_⟩
      · intro k hk
        exact (hsign k).1 (by simpa [hk] using hform k)
      · intro k hk hki hkj
        exact (hsign k).2.1 (by simpa [hk, hki, hkj] using hform k)
    let v := fun k => (if k = i then (1 : ℝ) else 0) - if k = j then 1 else 0
    have hv : ∀ k, v k ≠ 0 → 0 < w k ∧ w k < 1 := by
      intro k hk
      by_cases hki : k = i
      · simpa [hki] using hfi
      by_cases hkj : k = j
      · simpa [hkj] using hfj
      exact (hk (by simp [v, hki, hkj])).elim
    have hp := hw.direction_product_nonpos p m w v hv (by simp [v])
    have hpair : ((p i).1 - (p j).1) * ((p i).2 - (p j).2) ≤ 0 := by
      simpa [v, sub_mul, ite_mul, Finset.sum_sub_distrib] using hp
    have hstrict : ((p i).1 - (p j).1) * ((p i).2 - (p j).2) < 0 := by
      by_contra hn
      have hz : ((p i).1 - (p j).1) * ((p i).2 - (p j).2) = 0 :=
        le_antisymm hpair (not_lt.mp hn)
      let u := Simple.transfer w i j t
      have hue : ∀ k, u k = if k ∈ insert i R then 1 else 0 := by
        intro k
        by_cases hki : k = i
        · subst k; simp [u, Simple.transfer, hiw, hij]
        by_cases hkj : k = j
        · subst k; simp [u, Simple.transfer, hjw, hij.symm, hjR]
        simp only [u, Simple.transfer, ite_eq_right hki, ite_eq_right hkj, add_zero, sub_zero]
        rw [hform]
        simp [hki, hkj]
      have hmu : Simple.mass u = Simple.mass w := Simple.mass_transfer w i j t
      have hscore : Simple.centeredScore (fun k => (p k).1) (fun k => (p k).2) w i =
          Simple.centeredScore (fun k => (p k).1) (fun k => (p k).2) w j :=
        le_antisymm (hw.score_order p m w hm j i hfj.2 hfi.1)
          (hw.score_order p m w hm i j hfi.2 hfj.1)
      have hmR : Simple.mass w ≠ 0 := by
        change (∑ k, w k) ≠ 0
        rw [hw.1.2]
        exact Nat.cast_ne_zero.mpr (ne_of_gt hm)
      have hecross := Simple.cross_transfer (fun k => (p k).1) (fun k => (p k).2)
        w i j hmR t
      rw [hscore, hz] at hecross
      have hcu : Simple.crossNumerator (fun k => (p k).1) (fun k => (p k).2) u =
          Simple.crossNumerator (fun k => (p k).1) (fun k => (p k).2) w := by
        simpa [u] using hecross
      have hfu : FixedMassOptimal p m u := by
        refine ⟨⟨fun k => ?_, hmu.trans hw.1.2⟩, fun z hz => ?_⟩
        · rw [hue]; split_ifs <;> norm_num
        · rw [hcu]; exact hw.2 z hz
      apply hint
      refine ⟨u, hfu, fun k => ?_⟩
      rw [hue]
      split_ifs <;> simp
    exact ⟨R, i, j, t, hij, hiR, hjR, hcard, ht, ht1, hlow, hstrict, hform⟩

omit [Fintype ι] in
open Classical in
private theorem lowerSwap_endpoint [Finite ι] (p : ι → ℝ × ℝ)
    (hgp : LiftedGeneralPosition p) (R : Finset ι) (i j : ι)
    (h : IsLowerSwap p R i j) : IsLowerRange p (insert i R) := by
  classical
  obtain ⟨c, hc, hi, hj, hR, hO⟩ := h
  let z := fun k => if k ∈ insert i R then (-1 : ℝ) else 1
  have hn : ∀ k, lift p k ⬝ᵥ c < 0 → z k < 0 := by
    intro k hk
    have hmem : k ∈ insert i R := by
      by_contra hm
      have hki : k ≠ i := by intro he; subst k; simp at hm
      have hkR : k ∉ R := fun h => hm (Finset.mem_insert_of_mem h)
      by_cases hkj : k = j
      · subst k; linarith
      · linarith [hO k hkR hki hkj]
    simp only [z, ite_eq_left hmem]
    norm_num
  have hp : ∀ k, 0 < lift p k ⬝ᵥ c → 0 < z k := by
    intro k hk
    have hmem : k ∉ insert i R := by
      intro hm
      rcases Finset.mem_insert.mp hm with he | hmem
      · subst k; linarith
      · linarith [hR k hmem]
    simp only [z, ite_eq_right hmem]
    norm_num
  obtain ⟨d, hd, hsign⟩ := refine_plane p hgp c hc z hn hp
  refine ⟨d, hd, fun k hk => (hsign k).1 (by simp only [z, ite_eq_left hk]; norm_num),
    fun k hk => (hsign k).2.2 (by simp only [z, ite_eq_right hk]; norm_num)⟩

omit [Fintype ι] in
open Classical in
/-- Both endpoints of a lower swap edge are strict lower hyperbolic ranges. -/
theorem IsLowerSwap.endpoints [Finite ι] (p : ι → ℝ × ℝ)
    (hgp : LiftedGeneralPosition p) (R : Finset ι) (i j : ι)
    (h : IsLowerSwap p R i j) : IsLowerRange p (insert i R) ∧ IsLowerRange p (insert j R) := by
  classical
  refine ⟨lowerSwap_endpoint p hgp R i j h, lowerSwap_endpoint p hgp R j i ?_⟩
  obtain ⟨c, hc, hi, hj, hR, hO⟩ := h
  exact ⟨c, hc, hj, hi, hR, fun k hk hkj hki => hO k hk hki hkj⟩

/-- A global minimum over the actual convex hull of `m`-set saddle sums. -/
@[expose] def PolytopeMinimum (p : ι → ℝ × ℝ) (m : ℕ) (v : Fin 3 → ℝ) : Prop :=
  v ∈ setPolytope p m ∧ ∀ u ∈ setPolytope p m, saddleObjective m v ≤ saddleObjective m u

/-- The objective and all competitor quantifiers agree between the box and
convex-hull representations. -/
theorem fixedMassOptimal_iff_polytopeMinimum (p : ι → ℝ × ℝ) (m : ℕ) (hm : 0 < m)
    (w : ι → ℝ) (hw : w ∈ hypersimplex m) :
    FixedMassOptimal p m w ↔ PolytopeMinimum p m (liftedSum p w) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  constructor
  · intro ho
    refine ⟨by rw [setPolytope_eq_image]; exact ⟨w, hw, rfl⟩, ?_⟩
    intro v hv
    rw [setPolytope_eq_image] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [saddleObjective_liftedSum p m (ne_of_gt hm) w hw,
      saddleObjective_liftedSum p m (ne_of_gt hm) u hu]
    exact (div_le_div_iff_of_pos_right hmR).mpr (ho.2 u hu)
  · intro ho
    refine ⟨hw, fun u hu => ?_⟩
    have h := ho.2 (liftedSum p u) (by rw [setPolytope_eq_image]; exact ⟨u, hu, rfl⟩)
    rw [saddleObjective_liftedSum p m (ne_of_gt hm) w hw,
      saddleObjective_liftedSum p m (ne_of_gt hm) u hu] at h
    exact (div_le_div_iff_of_pos_right hmR).mp h

/-- Actual polytope attainment follows from compact box optimization. -/
theorem exists_polytopeMinimum (p : ι → ℝ × ℝ) (m : ℕ) (hm : 0 < m)
    (hn : m ≤ Fintype.card ι) : ∃ v, PolytopeMinimum p m v := by
  obtain ⟨w, hw⟩ := exists_fixedMassOptimal p m hn
  exact ⟨liftedSum p w, (fixedMassOptimal_iff_polytopeMinimum p m hm w hw.1).mp hw⟩

open Classical in
/-- The lifted sum of an original subset. -/
@[expose] def subsetSum (p : ι → ℝ × ℝ) (S : Finset ι) : Fin 3 → ℝ :=
  liftedSum p (fun i => if i ∈ S then 1 else 0)

open Classical in
/-- The original subset-sum interpretation of the linear map. -/
theorem subsetSum_eq_sum (p : ι → ℝ × ℝ) (S : Finset ι) :
    subsetSum p S = ∑ i ∈ S, saddle p i := by
  classical
  simp [subsetSum, liftedSum, ite_smul]

open Classical in
/-- For the right cardinality, the relaxed objective agrees with the ordinary
subset cross-scatter. Thus a subset attaining the relaxation is also an integral
minimum among all subsets of that size. -/
theorem saddleObjective_subsetSum (p : ι → ℝ × ℝ) (S : Finset ι) :
    saddleObjective S.card (subsetSum p S) = scatter p S := by
  rw [subsetSum_eq_sum]
  simp [saddleObjective, saddle, scatter, Finset.sum_apply]

open Classical in
/-- Lifted general position excludes collapsed swap edges. -/
theorem swap_endpoints_ne (p : ι → ℝ × ℝ) (hgp : LiftedGeneralPosition p)
    (R : Finset ι) (i j : ι) (hij : i ≠ j) (hiR : i ∉ R) (hjR : j ∉ R) :
    subsetSum p (insert i R) ≠ subsetSum p (insert j R) := by
  classical
  intro he
  rw [subsetSum_eq_sum, subsetSum_eq_sum, Finset.sum_insert hiR,
    Finset.sum_insert hjR] at he
  have hs : saddle p i = saddle p j := add_right_cancel he
  have hl : lift p i = lift p j := by
    ext k
    have h0 := congrFun hs 0
    have h1 := congrFun hs 1
    have h2 := congrFun hs 2
    fin_cases k
    · simpa [lift, saddle] using h0
    · simpa [lift, saddle] using h1
    · simpa [lift, saddle] using h2
    · simp [lift]
  have hind := hgp {i, j} (by simp [hij])
  have hij' := hind.injective (show (fun k : ({i, j} : Finset ι) => lift p k)
      ⟨i, by simp⟩ = (fun k : ({i, j} : Finset ι) => lift p k) ⟨j, by simp⟩ from hl)
  exact hij (congrArg Subtype.val hij')

open Classical in
/-- Proposition 5.2, with existence and both branches in the actual convex-hull
model. The first branch is a tight lower-vertex optimum. Otherwise every global
minimizer lies strictly between adjacent lower hyperbolic-range sums with a
strictly anti-monotone exchanged pair. The lower supporting plane has exactly
the two exchanged observations on its boundary, so it exposes precisely this
swap edge, rather than a larger face. No sign or nonsingularity premise is used. -/
theorem fixedSize_relaxation (p : ι → ℝ × ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hn : m < Fintype.card ι) (hgp : LiftedGeneralPosition p) :
    (∃ v, PolytopeMinimum p m v) ∧
    ((∃ S : Finset ι, S.card = m ∧ IsLowerRange p S ∧
      PolytopeMinimum p m (subsetSum p S)) ∨
    (∀ v, PolytopeMinimum p m v →
      ∃ (R : Finset ι) (i j : ι) (t : ℝ), i ≠ j ∧ i ∉ R ∧ j ∉ R ∧
        R.card + 1 = m ∧ 0 < t ∧ t < 1 ∧ IsLowerSwap p R i j ∧
        IsLowerRange p (insert i R) ∧ IsLowerRange p (insert j R) ∧
        subsetSum p (insert i R) ≠ subsetSum p (insert j R) ∧
        ((p i).1 - (p j).1) * ((p i).2 - (p j).2) < 0 ∧
        v = (1 - t) • subsetSum p (insert i R) + t • subsetSum p (insert j R))) := by
  classical
  have hm0 : 0 < m := by omega
  refine ⟨exists_polytopeMinimum p m hm0 hn.le, ?_⟩
  obtain h | h := fixedMass_dichotomy p m hm0 hgp
  · left
    obtain ⟨S, hS, hlow, ho⟩ := h
    exact ⟨S, hS, hlow, (fixedMassOptimal_iff_polytopeMinimum p m hm0 _ ho.1).mp ho⟩
  · right
    intro v hv
    have hvK := hv.1
    rw [setPolytope_eq_image] at hvK
    obtain ⟨w, hw, rfl⟩ := hvK
    have ho := (fixedMassOptimal_iff_polytopeMinimum p m hm0 w hw).mpr hv
    obtain ⟨R, i, j, t, hij, hiR, hjR, hcard, ht, ht1, hlow, hpair, hform⟩ := h w ho
    obtain ⟨hli, hlj⟩ := hlow.endpoints p hgp R i j
    refine ⟨R, i, j, t, hij, hiR, hjR, hcard, ht, ht1, hlow, hli, hlj,
      swap_endpoints_ne p hgp R i j hij hiR hjR, hpair, ?_⟩
    have he : w = (1 - t) • (fun k => if k ∈ insert i R then (1 : ℝ) else 0) +
        t • (fun k => if k ∈ insert j R then (1 : ℝ) else 0) := by
      funext k
      rw [hform]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hk : k ∈ R
      · simp [hk]
      · by_cases hki : k = i
        · subst k; simp [hiR, hij]
        · by_cases hkj : k = j
          · subst k; simp [hjR, hij.symm]
          · simp [hk, hki, hkj]
    rw [he, map_add, map_smul, map_smul]
    rfl

end Cslib.LeastSquares.Geometry
