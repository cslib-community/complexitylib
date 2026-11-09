/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Convex/Ellipsoid.lean`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Module

/-!
# Ellipsoids and the central-cut update

For a positive definite `A : Matrix ι ι ℝ` and `c : ι → ℝ`, the ellipsoid
`Matrix.ellipsoid A c = {x | (x - c) ⬝ᵥ A⁻¹ *ᵥ (x - c) ≤ 1}` has volume `√(det A)` times the
volume of the Euclidean unit ball. A *central cut* through the center `c` in direction `a ≠ 0`
keeps the half `{x | a ⬝ᵥ x ≤ a ⬝ᵥ c}`. With `n = card ι` and `b = A a / √(aᵀ A a)`, the
central-cut update

`c' = c - b / (n + 1)`,  `A' = n² / (n² - 1) · (A - 2 / (n + 1) · b bᵀ)`

(for `n ≥ 2`; for `n = 1` it is bisection, `A' = A / 4`) gives an ellipsoid `E(A', c')` that
contains the half-ellipsoid and whose volume is smaller by the factor
`(n² / (n² - 1)) ^ ((n - 1) / 2) · n / (n + 1) < exp (-1 / (2 (n + 1)))`. This is the geometric
step of Khachiyan's ellipsoid method; the iteration with a separation oracle is
`Cslib.Algorithms.Ellipsoid`.

`centralCutShape` is written as `n² / (n² - 1) · (A - b bᵀ) + (n / (n + 1))² · b bᵀ`, which equals
the formula above for `n ≥ 2` (`centralCutShape_of_two_le_card`). For `n = 1` the matrix
`A - b bᵀ` vanishes, so the same expression is `A / 4` (`centralCutShape_of_card_eq_one`) and
every statement below holds for all `n ≥ 1` without a case split in the definition.

The proofs are direct: the inverse of `A'` is
`(n² - 1) / n² · A⁻¹ + 2 (n + 1) / n² · a aᵀ / (aᵀ A a)` (`inv_centralCutShape`), containment
reduces to Cauchy–Schwarz for `A⁻¹`, the determinant follows from the matrix determinant lemma,
and the volume formula uses `CFC.sqrt A` and Mathlib's `addHaar_preimage_linearMap` and
`EuclideanSpace.volume_closedBall`.

## Main definitions

* `Matrix.ellipsoid`: the ellipsoid `{x | (x - c) ⬝ᵥ A⁻¹ *ᵥ (x - c) ≤ 1}`.
* `Matrix.centralCutDir`, `Matrix.centralCutCenter`, `Matrix.centralCutShape`: the central-cut
  update.

## Main results

* `Matrix.convex_ellipsoid`: ellipsoids with positive definite shape are convex.
* `Matrix.volume_ellipsoid`: `vol E(A, c) = √(det A) · vol E(1, 0)`, and
  `Matrix.volume_ellipsoid_one_zero` identifies `E(1, 0)` with the Euclidean unit ball.
* `Matrix.PosDef.centralCutShape`: the updated shape is positive definite.
* `Matrix.ellipsoid_inter_halfspace_subset`: `E(A, c) ∩ {x | a ⬝ᵥ x ≤ a ⬝ᵥ c} ⊆ E(A', c')`.
* `Matrix.det_centralCutShape`:
  `det A' = (n² / (n² - 1)) ^ (n - 1) · (n / (n + 1))² · det A`.
* `Matrix.volume_ellipsoid_centralCut_lt`: `vol E(A', c') < exp (-1 / (2 (n + 1))) · vol E(A, c)`.

## References

* [BertsimasTsitsiklis1997], Section 8.2, Theorem 8.1
* [GrotschelLovaszSchrijver1988], Section 3.1
* [Khachiyan1979]
-/

public section

open MeasureTheory

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ellipsoid `{x | (x - c) ⬝ᵥ A⁻¹ *ᵥ (x - c) ≤ 1}` with shape matrix `A` and center `c`. It is
the usual ellipsoid when `A` is positive definite [GrotschelLovaszSchrijver1988, Section 3.1]. -/
def ellipsoid (A : Matrix ι ι ℝ) (c : ι → ℝ) : Set (ι → ℝ) :=
  {x | (x - c) ⬝ᵥ (A⁻¹ *ᵥ (x - c)) ≤ 1}

theorem mem_ellipsoid {A : Matrix ι ι ℝ} {c x : ι → ℝ} :
    x ∈ ellipsoid A c ↔ (x - c) ⬝ᵥ (A⁻¹ *ᵥ (x - c)) ≤ 1 := Iff.rfl

theorem center_mem_ellipsoid (A : Matrix ι ι ℝ) (c : ι → ℝ) : c ∈ ellipsoid A c := by
  simp [mem_ellipsoid]

omit [DecidableEq ι] in
/-- The quadratic form `q v = v ⬝ᵥ M *ᵥ v` of a positive semidefinite `M` is convex:
`q (s u + t v) ≤ s q u + t q v` for `s, t ≥ 0` with `s + t = 1`. -/
private lemma quadForm_combo_le {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (u v : ι → ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    (s • u + t • v) ⬝ᵥ (M *ᵥ (s • u + t • v)) ≤
      s * (u ⬝ᵥ (M *ᵥ u)) + t * (v ⬝ᵥ (M *ᵥ v)) := by
  have hnn : 0 ≤ (u - v) ⬝ᵥ (M *ᵥ (u - v)) := by
    simpa using hM.dotProduct_mulVec_nonneg (u - v)
  have hsym : u ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ (M *ᵥ u) := hM.isHermitian.isSymm.dotProduct_mulVec_comm
  simp only [mulVec_add, mulVec_sub, mulVec_smul, dotProduct_add, dotProduct_sub, add_dotProduct,
    sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hnn ⊢
  have hst' : t = 1 - s := by linarith
  subst hst'
  nlinarith [mul_nonneg hs ht]

/-- An ellipsoid with positive definite shape is convex. -/
theorem convex_ellipsoid {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ι → ℝ) :
    Convex ℝ (ellipsoid A c) := by
  intro x hx y hy s t hs ht hst
  rw [mem_ellipsoid] at hx hy ⊢
  have hxy : s • x + t • y - c = s • (x - c) + t • (y - c) := by
    have hc : c = s • c + t • c := by rw [← add_smul, hst, one_smul]
    conv_lhs => rw [hc]
    rw [smul_sub, smul_sub]
    abel
  rw [hxy]
  calc _ ≤ s * ((x - c) ⬝ᵥ (A⁻¹ *ᵥ (x - c))) + t * ((y - c) ⬝ᵥ (A⁻¹ *ᵥ (y - c))) :=
        quadForm_combo_le hA.inv.posSemidef _ _ hs ht hst
    _ ≤ s * 1 + t * 1 := by gcongr
    _ = 1 := by rw [mul_one, mul_one, hst]

/-- The ellipsoid with shape `r² • 1` is the closed Euclidean ball of radius `r`. -/
theorem ellipsoid_sq_smul_one {r : ℝ} (hr : r ≠ 0) (z : ι → ℝ) :
    ellipsoid ((r ^ 2) • (1 : Matrix ι ι ℝ)) z = {x | (x - z) ⬝ᵥ (x - z) ≤ r ^ 2} := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hinv : ((r ^ 2) • (1 : Matrix ι ι ℝ))⁻¹ = (r ^ 2)⁻¹ • (1 : Matrix ι ι ℝ) := by
    refine inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, Matrix.one_mul, inv_mul_cancel₀ hr2.ne', one_smul]
  ext x
  rw [mem_ellipsoid, hinv, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
    inv_mul_le_iff₀ hr2, mul_one, Set.mem_ofPred_eq]

omit [Fintype ι] in
theorem PosDef.sq_smul_one {r : ℝ} (hr : r ≠ 0) : ((r ^ 2) • (1 : Matrix ι ι ℝ)).PosDef :=
  PosDef.one.smul (by positivity)

section Volume

/-- The unit ellipsoid `E(1, 0)` is the preimage of the closed unit ball of `EuclideanSpace ℝ ι`. -/
theorem ellipsoid_one_zero :
    ellipsoid (1 : Matrix ι ι ℝ) 0 =
      WithLp.toLp 2 ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ ι) 1 := by
  ext x
  simp only [mem_ellipsoid, sub_zero, inv_one, one_mulVec, Set.mem_preimage,
    mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Real.sqrt_le_one,
    dotProduct, ← sq]

/-- The volume of the unit ellipsoid is that of the Euclidean unit ball, so it is
`π ^ (n / 2) / Γ (n / 2 + 1)` by `EuclideanSpace.volume_closedBall`. -/
theorem volume_ellipsoid_one_zero :
    volume (ellipsoid (1 : Matrix ι ι ℝ) 0) =
      volume (Metric.closedBall (0 : EuclideanSpace ℝ ι) 1) := by
  rw [ellipsoid_one_zero, (PiLp.volume_preserving_toLp ι).measure_preimage
    measurableSet_closedBall.nullMeasurableSet]

theorem volume_ellipsoid_one_zero_pos : 0 < volume (ellipsoid (1 : Matrix ι ι ℝ) 0) := by
  rw [volume_ellipsoid_one_zero]
  exact Metric.measure_closedBall_pos _ _ one_pos

theorem volume_ellipsoid_one_zero_lt_top : volume (ellipsoid (1 : Matrix ι ι ℝ) 0) < ⊤ := by
  rw [volume_ellipsoid_one_zero]
  exact measure_closedBall_lt_top

open scoped MatrixOrder in
/-- **Volume of an ellipsoid**: `vol E(A, c) = √(det A) · vol E(1, 0)` for positive definite `A`
[GrotschelLovaszSchrijver1988, Section 3.1]. -/
theorem volume_ellipsoid {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ι → ℝ) :
    volume (ellipsoid A c) = ENNReal.ofReal √A.det * volume (ellipsoid (1 : Matrix ι ι ℝ) 0) := by
  have htrans : ellipsoid A c = (fun x => -c + x) ⁻¹' ellipsoid A 0 := by
    ext x
    simp only [mem_ellipsoid, Set.mem_preimage, sub_zero, neg_add_eq_sub]
  rw [htrans, measure_preimage_add]
  set S := CFC.sqrt A
  have hSn : 0 ≤ S := CFC.sqrt_nonneg A
  have hSherm : S.IsHermitian := (nonneg_iff_posSemidef.mp hSn).isHermitian
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSdet : S.det = √A.det := by simpa using hA.posSemidef.det_sqrt
  have hSdet0 : S.det ≠ 0 := by rw [hSdet]; exact (Real.sqrt_pos.mpr hA.det_pos).ne'
  have hST : Sᵀ = S := hSherm.isSymm.eq
  have hpre : ellipsoid A 0 = toLin' S⁻¹ ⁻¹' ellipsoid 1 0 := by
    ext x
    simp only [mem_ellipsoid, Set.mem_preimage, sub_zero, inv_one, one_mulVec, toLin'_apply]
    rw [dotProduct_mulVec (S⁻¹ *ᵥ x), ← mulVec_transpose, transpose_nonsing_inv, hST,
      mulVec_mulVec, ← Matrix.mul_inv_rev, hSS, dotProduct_comm]
  rw [hpre, Measure.addHaar_preimage_linearMap]
  · rw [LinearMap.det_toLin', det_nonsing_inv, Ring.inverse_eq_inv', inv_inv, hSdet,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  · rw [LinearMap.det_toLin', det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero hSdet0

theorem volume_ellipsoid_pos {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ι → ℝ) :
    0 < volume (ellipsoid A c) := by
  rw [volume_ellipsoid hA]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hA.det_pos)).ne'
    volume_ellipsoid_one_zero_pos.ne'

theorem volume_ellipsoid_lt_top {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ι → ℝ) :
    volume (ellipsoid A c) < ⊤ := by
  rw [volume_ellipsoid hA]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top volume_ellipsoid_one_zero_lt_top

/-- The ball `E(r² • 1, z)` of radius `r > 0` has volume `rⁿ · vol E(1, 0)`. -/
theorem volume_ellipsoid_sq_smul_one {r : ℝ} (hr : 0 < r) (z : ι → ℝ) :
    volume (ellipsoid ((r ^ 2) • (1 : Matrix ι ι ℝ)) z) =
      ENNReal.ofReal (r ^ Fintype.card ι) * volume (ellipsoid (1 : Matrix ι ι ℝ) 0) := by
  rw [volume_ellipsoid (PosDef.sq_smul_one hr.ne'), det_smul, det_one, mul_one, ← pow_mul,
    mul_comm 2, pow_mul, Real.sqrt_sq (by positivity)]

end Volume

/-- The direction `b = A a / √(aᵀ A a)` of a central cut with normal `a`: the new center moves from
`c` by `-b / (n + 1)`. -/
@[expose] noncomputable def centralCutDir (A : Matrix ι ι ℝ) (a : ι → ℝ) : ι → ℝ :=
  (√(a ⬝ᵥ (A *ᵥ a)))⁻¹ • (A *ᵥ a)

/-- The center `c - b / (n + 1)` of the ellipsoid after a central cut of `E(A, c)` with normal
`a`, keeping `{x | a ⬝ᵥ x ≤ a ⬝ᵥ c}`. Here `n = card ι` and `b = centralCutDir A a`. -/
@[expose] noncomputable def centralCutCenter (A : Matrix ι ι ℝ) (c a : ι → ℝ) : ι → ℝ :=
  c - ((Fintype.card ι : ℝ) + 1)⁻¹ • centralCutDir A a

/-- The shape `n² / (n² - 1) · (A - b bᵀ) + (n / (n + 1))² · b bᵀ` of the ellipsoid after a
central cut with normal `a`, where `n = card ι` and `b = centralCutDir A a`. For `n ≥ 2` this is
the textbook `n² / (n² - 1) · (A - 2 / (n + 1) · b bᵀ)` (`centralCutShape_of_two_le_card`); for
`n = 1` it is `A / 4` (`centralCutShape_of_card_eq_one`). -/
noncomputable def centralCutShape (A : Matrix ι ι ℝ) (a : ι → ℝ) : Matrix ι ι ℝ :=
  ((Fintype.card ι : ℝ) ^ 2 / ((Fintype.card ι : ℝ) ^ 2 - 1)) •
      (A - vecMulVec (centralCutDir A a) (centralCutDir A a)) +
    ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) + 1)) ^ 2 •
      vecMulVec (centralCutDir A a) (centralCutDir A a)

omit [DecidableEq ι] in
/-- For `n ≥ 2`, `centralCutShape` is the update of [GrotschelLovaszSchrijver1988, Section 3.1]
and [BertsimasTsitsiklis1997, Theorem 8.1]. -/
theorem centralCutShape_of_two_le_card (A : Matrix ι ι ℝ) (a : ι → ℝ)
    (h : 2 ≤ Fintype.card ι) :
    centralCutShape A a = ((Fintype.card ι : ℝ) ^ 2 / ((Fintype.card ι : ℝ) ^ 2 - 1)) •
      (A - (2 / ((Fintype.card ι : ℝ) + 1)) •
        vecMulVec (centralCutDir A a) (centralCutDir A a)) := by
  have h2 : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast h
  have hnn : (Fintype.card ι : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hn1 : (Fintype.card ι : ℝ) + 1 ≠ 0 := by linarith
  simp only [centralCutShape]
  match_scalars <;> field_simp; ring

section Cut

variable {A : Matrix ι ι ℝ} {a : ι → ℝ}

omit [DecidableEq ι] in
private lemma card_pos_of_ne_zero (ha : a ≠ 0) : 0 < Fintype.card ι := by
  rw [Fintype.card_pos_iff]
  by_contra h
  rw [not_nonempty_iff] at h
  exact ha (Subsingleton.elim _ _)

/-- The dual vector `a / √(aᵀ A a)`, with `A *ᵥ cutDual A a = centralCutDir A a`. -/
private noncomputable def cutDual (A : Matrix ι ι ℝ) (a : ι → ℝ) : ι → ℝ :=
  (√(a ⬝ᵥ (A *ᵥ a)))⁻¹ • a

omit [DecidableEq ι] in
private lemma mulVec_cutDual : A *ᵥ cutDual A a = centralCutDir A a := by
  simp [cutDual, centralCutDir, mulVec_smul]

private lemma inv_mulVec_centralCutDir (hA : A.PosDef) :
    A⁻¹ *ᵥ centralCutDir A a = cutDual A a := by
  rw [← mulVec_cutDual, mulVec_mulVec,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA.isUnit), one_mulVec]

omit [DecidableEq ι] in
private lemma centralCutDir_dotProduct_cutDual (hA : A.PosDef) (ha : a ≠ 0) :
    centralCutDir A a ⬝ᵥ cutDual A a = 1 := by
  have hs : 0 < a ⬝ᵥ (A *ᵥ a) := by simpa using hA.dotProduct_mulVec_pos ha
  simp only [cutDual, centralCutDir, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (A *ᵥ a) a, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hs.le,
    inv_mul_cancel₀ hs.ne']

private lemma vecMulVec_centralCutDir_mul_inv (hA : A.PosDef) :
    vecMulVec (centralCutDir A a) (centralCutDir A a) * A⁻¹ =
      vecMulVec (centralCutDir A a) (cutDual A a) := by
  rw [vecMulVec_mul, ← mulVec_transpose, hA.inv.isHermitian.isSymm.eq,
    inv_mulVec_centralCutDir hA]

private lemma vecMulVec_eq_one_of_card_eq_one (h : Fintype.card ι = 1) {u v : ι → ℝ}
    (huv : u ⬝ᵥ v = 1) : vecMulVec u v = 1 := by
  obtain ⟨hu⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp h
  ext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  simpa [vecMulVec_apply, dotProduct] using huv

/-- The inverse of `centralCutShape A a`. -/
private noncomputable def cutInv (A : Matrix ι ι ℝ) (a : ι → ℝ) : Matrix ι ι ℝ :=
  (((Fintype.card ι : ℝ) ^ 2 - 1) / (Fintype.card ι : ℝ) ^ 2) • A⁻¹ +
    (2 * ((Fintype.card ι : ℝ) + 1) / (Fintype.card ι : ℝ) ^ 2) •
      vecMulVec (cutDual A a) (cutDual A a)

private lemma centralCutShape_mul_cutInv (hA : A.PosDef) (ha : a ≠ 0) :
    centralCutShape A a * cutInv A a = 1 := by
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast card_pos_of_ne_zero ha
  have hba := centralCutDir_dotProduct_cutDual hA ha
  have hAA : A * A⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hBA := vecMulVec_centralCutDir_mul_inv (a := a) hA
  have hAW : A * vecMulVec (cutDual A a) (cutDual A a) =
      vecMulVec (centralCutDir A a) (cutDual A a) := by
    rw [mul_vecMulVec, mulVec_cutDual]
  have hBW : vecMulVec (centralCutDir A a) (centralCutDir A a) *
      vecMulVec (cutDual A a) (cutDual A a) = vecMulVec (centralCutDir A a) (cutDual A a) := by
    rw [vecMulVec_mul_vecMulVec, hba, one_smul]
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have key : centralCutShape A a * cutInv A a =
      (n ^ 2 / (n ^ 2 - 1) * ((n ^ 2 - 1) / n ^ 2)) • (1 : Matrix ι ι ℝ) +
        ((n / (n + 1)) ^ 2 * ((n ^ 2 - 1) / n ^ 2) + (n / (n + 1)) ^ 2 * (2 * (n + 1) / n ^ 2) -
          n ^ 2 / (n ^ 2 - 1) * ((n ^ 2 - 1) / n ^ 2)) •
          vecMulVec (centralCutDir A a) (cutDual A a) := by
    simp only [centralCutShape, cutInv, ← hn_def, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.sub_mul, hAA, hBA, hAW, hBW]
    module
  have hβ : (n / (n + 1)) ^ 2 * ((n ^ 2 - 1) / n ^ 2) + (n / (n + 1)) ^ 2 * (2 * (n + 1) / n ^ 2)
      = 1 := by
    field_simp
    ring
  rw [key, hβ]
  rcases hn1.eq_or_lt with h1 | h2
  · have hc : Fintype.card ι = 1 := by
      have : (Fintype.card ι : ℝ) = 1 := by rw [← hn_def]; exact h1.symm
      exact_mod_cast this
    rw [vecMulVec_eq_one_of_card_eq_one hc hba, ← h1]
    norm_num
  · have : n ^ 2 - 1 ≠ 0 := by nlinarith
    have hαγ : n ^ 2 / (n ^ 2 - 1) * ((n ^ 2 - 1) / n ^ 2) = 1 := by
      field_simp
    rw [hαγ]
    simp

/-- The inverse of the updated shape is `(n² - 1) / n² · A⁻¹ + 2 (n + 1) / n² · a aᵀ / (aᵀ A a)`. -/
theorem inv_centralCutShape (hA : A.PosDef) (ha : a ≠ 0) :
    (centralCutShape A a)⁻¹ =
      (((Fintype.card ι : ℝ) ^ 2 - 1) / (Fintype.card ι : ℝ) ^ 2) • A⁻¹ +
        (2 * ((Fintype.card ι : ℝ) + 1) / ((Fintype.card ι : ℝ) ^ 2 * (a ⬝ᵥ (A *ᵥ a)))) •
          vecMulVec a a := by
  have hs : 0 < a ⬝ᵥ (A *ᵥ a) := by simpa using hA.dotProduct_mulVec_pos ha
  have hW : vecMulVec (cutDual A a) (cutDual A a) = (a ⬝ᵥ (A *ᵥ a))⁻¹ • vecMulVec a a := by
    rw [cutDual, smul_vecMulVec, vecMulVec_smul, smul_smul, ← mul_inv,
      Real.mul_self_sqrt hs.le]
  rw [inv_eq_right_inv (centralCutShape_mul_cutInv hA ha), cutInv, hW, smul_smul]
  congr 1
  congr 1
  field_simp

private lemma posSemidef_cutInv (hA : A.PosDef) (ha : a ≠ 0) : (cutInv A a).PosSemidef := by
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast card_pos_of_ne_zero ha
  refine PosSemidef.add (hA.inv.posSemidef.smul ?_) (PosSemidef.smul ?_ ?_)
  · apply div_nonneg <;> nlinarith
  · simpa using posSemidef_vecMulVec_self_star (cutDual A a)
  · apply div_nonneg <;> nlinarith

omit [DecidableEq ι] in
/-- The updated shape matrix is positive definite, so the update can be iterated. -/
theorem PosDef.centralCutShape (hA : A.PosDef) (ha : a ≠ 0) : (centralCutShape A a).PosDef := by
  classical
  have hunit : IsUnit (cutInv A a) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_det_of_left_inverse (centralCutShape_mul_cutInv hA ha))
  have := ((posSemidef_cutInv hA ha).posDef_iff_isUnit.mpr hunit).inv
  rwa [inv_eq_left_inv (centralCutShape_mul_cutInv hA ha)] at this

omit [DecidableEq ι] in
/-- In dimension one the central cut is bisection: the new shape is `A / 4`. -/
theorem centralCutShape_of_card_eq_one (hA : A.PosDef) (ha : a ≠ 0) (h : Fintype.card ι = 1) :
    centralCutShape A a = (1 / 4 : ℝ) • A := by
  classical
  have hB : vecMulVec (centralCutDir A a) (centralCutDir A a) = A := by
    have h1 : vecMulVec (centralCutDir A a) (centralCutDir A a) * A⁻¹ * A = A := by
      rw [vecMulVec_centralCutDir_mul_inv hA,
        vecMulVec_eq_one_of_card_eq_one h (centralCutDir_dotProduct_cutDual hA ha), Matrix.one_mul]
    rwa [Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA.isUnit),
      Matrix.mul_one] at h1
  simp only [centralCutShape, hB, h, sub_self, smul_zero, zero_add]
  norm_num

/-- **Half-ellipsoid containment**: the updated ellipsoid contains the half of `E(A, c)` on the side
`a ⬝ᵥ x ≤ a ⬝ᵥ c` of the hyperplane through the center [GrotschelLovaszSchrijver1988, Section 3.1],
[BertsimasTsitsiklis1997, Theorem 8.1(a)] (with the opposite sign convention for `a`). -/
theorem ellipsoid_inter_halfspace_subset (hA : A.PosDef) (ha : a ≠ 0) (c : ι → ℝ) :
    ellipsoid A c ∩ {x | a ⬝ᵥ x ≤ a ⬝ᵥ c} ⊆
      ellipsoid (centralCutShape A a) (centralCutCenter A c a) := by
  rintro x ⟨hxE, hxH⟩
  rw [Set.mem_ofPred_eq] at hxH
  rw [mem_ellipsoid] at hxE ⊢
  rw [inv_eq_right_inv (centralCutShape_mul_cutInv hA ha)]
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast card_pos_of_ne_zero ha
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  set y := x - c with hy
  set b := centralCutDir A a with hb
  set a' := cutDual A a with ha'
  have hz : x - centralCutCenter A c a = y + (n + 1)⁻¹ • b := by
    simp only [centralCutCenter, hy, hb, ← hn_def]
    abel
  rw [hz]
  have hba : b ⬝ᵥ a' = 1 := centralCutDir_dotProduct_cutDual hA ha
  have hab : a' ⬝ᵥ b = 1 := by rw [dotProduct_comm]; exact hba
  have hAb : A⁻¹ *ᵥ b = a' := inv_mulVec_centralCutDir hA
  have hW (v : ι → ℝ) : vecMulVec a' a' *ᵥ v = (a' ⬝ᵥ v) • a' := by
    rw [vecMulVec_mulVec, op_smul_eq_smul]
  set q := y ⬝ᵥ (A⁻¹ *ᵥ y) with hq
  set t := a' ⬝ᵥ y with ht
  have hyb : y ⬝ᵥ a' = t := dotProduct_comm _ _
  have ht0 : t ≤ 0 := by
    rw [ht, ha', cutDual, smul_dotProduct, hy, dotProduct_sub, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  -- Cauchy–Schwarz for `A⁻¹`: `(yᵀ A⁻¹ b)² ≤ (yᵀ A⁻¹ y)(bᵀ A⁻¹ b) = q`.
  have htq : t ^ 2 ≤ q := by
    have := hA.inv.star_dotProduct_mulVec_mul_le y b
    simp only [star_trivial, hAb, hyb, hba, mul_one] at this
    nlinarith
  have hbAy : b ⬝ᵥ (A⁻¹ *ᵥ y) = t := by
    rw [hA.inv.isHermitian.isSymm.dotProduct_mulVec_comm, hAb, hyb]
  simp only [cutInv, ← hn_def, ← ha', add_mulVec, smul_mulVec, hW, mulVec_add, mulVec_smul, hAb,
    dotProduct_add, dotProduct_smul, add_dotProduct, smul_dotProduct, hba, hab, hyb, ← ht, ← hq,
    hbAy, smul_eq_mul]
  have hn0 : n ≠ 0 := by positivity
  have hγ : 0 ≤ (n ^ 2 - 1) / n ^ 2 := by apply div_nonneg <;> nlinarith
  have hδ : 0 ≤ 2 * (n + 1) / n ^ 2 := by positivity
  have ht1 : -1 ≤ t := by nlinarith
  calc _ = 1 + (n ^ 2 - 1) / n ^ 2 * (q - 1) + 2 * (n + 1) / n ^ 2 * (t * (t + 1)) := by
        field_simp
        ring
    _ ≤ 1 := by
        have h1 := mul_nonpos_of_nonneg_of_nonpos hγ (show q - 1 ≤ 0 by linarith)
        have h2 := mul_nonpos_of_nonneg_of_nonpos hδ
          (mul_nonpos_of_nonpos_of_nonneg ht0 (show 0 ≤ t + 1 by linarith))
        linarith

/-- The determinant of the updated shape:
`det A' = (n² / (n² - 1)) ^ (n - 1) · (n / (n + 1))² · det A`, for every `n ≥ 1` (for `n = 1` the
first factor is `1`). -/
theorem det_centralCutShape (hA : A.PosDef) (ha : a ≠ 0) :
    (centralCutShape A a).det =
      ((Fintype.card ι : ℝ) ^ 2 / ((Fintype.card ι : ℝ) ^ 2 - 1)) ^ (Fintype.card ι - 1) *
        ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) + 1)) ^ 2 * A.det := by
  have hba := centralCutDir_dotProduct_cutDual hA ha
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 :=
    ⟨_, (Nat.sub_add_cancel (card_pos_of_ne_zero ha)).symm⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · rw [centralCutShape_of_card_eq_one hA ha hm, det_smul, hm]
    norm_num
  rw [hm, Nat.add_sub_cancel]
  push_cast
  set n : ℝ := (m : ℝ) + 1 with hn_def
  have hn2 : (2 : ℝ) ≤ n := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    linarith
  have hnn : n ^ 2 - 1 ≠ 0 := by nlinarith
  have hshape : centralCutShape A a = (n ^ 2 / (n ^ 2 - 1)) •
      (A + vecMulVec (-(2 / (n + 1)) • centralCutDir A a) (cutDual A a) * A) := by
    have hAW : vecMulVec (-(2 / (n + 1)) • centralCutDir A a) (cutDual A a) * A =
        (-(2 / (n + 1))) • vecMulVec (centralCutDir A a) (centralCutDir A a) := by
      rw [vecMulVec_mul, ← mulVec_transpose, hA.isHermitian.isSymm.eq, mulVec_cutDual,
        smul_vecMulVec]
    rw [hAW]
    simp only [centralCutShape, hm]
    push_cast
    rw [← hn_def]
    match_scalars <;> field_simp; ring
  -- the matrix determinant lemma, with `bᵀ A⁻¹ b = 1`
  have hrank : (A + vecMulVec (-(2 / (n + 1)) • centralCutDir A a) (cutDual A a) * A).det =
      (1 - 2 / (n + 1)) * A.det := by
    have hab : cutDual A a ⬝ᵥ centralCutDir A a = 1 := by rw [dotProduct_comm]; exact hba
    rw [show ∀ U : Matrix ι ι ℝ, A + U * A = (1 + U) * A by
        intro U; rw [Matrix.add_mul, Matrix.one_mul], det_mul, vecMulVec_eq Unit,
      det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hab, smul_eq_mul]
    ring
  rw [hshape, det_smul, hrank, hm, pow_succ]
  field_simp
  ring

private lemma cut_ratio_lt {k : ℕ} (hk : 1 ≤ k) :
    ((k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1)) ^ (k - 1) * ((k : ℝ) / ((k : ℝ) + 1)) ^ 2 <
      Real.exp (-1 / ((k : ℝ) + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  rw [Nat.add_sub_cancel]
  push_cast
  set n : ℝ := (m : ℝ) + 1 with hn_def
  have hn1 : (1 : ℝ) ≤ n := by rw [hn_def]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  -- `(n² / (n² - 1)) ^ (n - 1) ≤ exp ((n - 1) / (n² - 1)) = exp (1 / (n + 1))`
  have h1 : (n ^ 2 / (n ^ 2 - 1)) ^ m ≤ Real.exp (1 / (n + 1)) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp only [pow_zero]
      exact Real.one_le_exp (div_nonneg zero_le_one (by linarith))
    · have hn2 : (2 : ℝ) ≤ n := by
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
        linarith
      have hnn : 0 < n ^ 2 - 1 := by nlinarith
      have hbase : n ^ 2 / (n ^ 2 - 1) ≤ Real.exp (1 / (n ^ 2 - 1)) := by
        calc n ^ 2 / (n ^ 2 - 1) = 1 / (n ^ 2 - 1) + 1 := by field_simp; ring
          _ ≤ _ := Real.add_one_le_exp _
      calc (n ^ 2 / (n ^ 2 - 1)) ^ m ≤ Real.exp (1 / (n ^ 2 - 1)) ^ m :=
            pow_le_pow_left₀ (div_nonneg (by positivity) hnn.le) hbase m
        _ = Real.exp (m * (1 / (n ^ 2 - 1))) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (1 / (n + 1)) := by
            congr 1
            have hm : (m : ℝ) = n - 1 := by rw [hn_def]; ring
            have hn1' : n + 1 ≠ 0 := by linarith
            rw [hm]
            field_simp
            ring
  -- `(n / (n + 1))² < exp (-2 / (n + 1))`
  have h2 : (n / (n + 1)) ^ 2 < Real.exp (-2 / (n + 1)) := by
    have hlt : n / (n + 1) < Real.exp (-1 / (n + 1)) := by
      have h := Real.add_one_lt_exp (x := -1 / (n + 1)) (by
        have : (0 : ℝ) < n + 1 := by positivity
        exact div_ne_zero (by norm_num) this.ne')
      calc n / (n + 1) = -1 / (n + 1) + 1 := by field_simp; ring
        _ < _ := h
    calc (n / (n + 1)) ^ 2 < Real.exp (-1 / (n + 1)) ^ 2 :=
          pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
      _ = Real.exp (-2 / (n + 1)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
  calc (n ^ 2 / (n ^ 2 - 1)) ^ m * (n / (n + 1)) ^ 2
      < Real.exp (1 / (n + 1)) * Real.exp (-2 / (n + 1)) :=
        mul_lt_mul' h1 h2 (by positivity) (Real.exp_pos _)
    _ = Real.exp (-1 / (n + 1)) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- **Volume ratio** of a central cut: `vol E(A', c') < exp (-1 / (2 (n + 1))) · vol E(A, c)`
[BertsimasTsitsiklis1997, Theorem 8.1(b)], [GrotschelLovaszSchrijver1988, Section 3.1]. Bertsimas
and Tsitsiklis state it for `n ≥ 2`; it is proved here for every `n ≥ 1`, the case `n = 1`
(bisection, ratio `1 / 2 < exp (-1 / 4)`) being added. The proof bounds the exact ratio
`√(det A' / det A)` from `det_centralCutShape` using `1 + x ≤ exp x`. -/
theorem volume_ellipsoid_centralCut_lt (hA : A.PosDef) (ha : a ≠ 0) (c : ι → ℝ) :
    volume (ellipsoid (centralCutShape A a) (centralCutCenter A c a)) <
      ENNReal.ofReal (Real.exp (-1 / (2 * ((Fintype.card ι : ℝ) + 1)))) *
        volume (ellipsoid A c) := by
  have hk := card_pos_of_ne_zero ha
  rw [volume_ellipsoid (hA.centralCutShape ha), volume_ellipsoid hA, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.mul_lt_mul_left volume_ellipsoid_one_zero_pos.ne'
    volume_ellipsoid_one_zero_lt_top.ne ?_
  have hdet := hA.det_pos
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity), det_centralCutShape hA ha]
  have hρlt := cut_ratio_lt hk
  have hρ0 : 0 ≤ ((Fintype.card ι : ℝ) ^ 2 / ((Fintype.card ι : ℝ) ^ 2 - 1)) ^
      (Fintype.card ι - 1) * ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) + 1)) ^ 2 := by
    refine mul_nonneg (pow_nonneg ?_ _) (by positivity)
    have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hk
    apply div_nonneg <;> nlinarith
  rw [Real.sqrt_mul hρ0]
  refine mul_lt_mul_of_pos_right ?_ (Real.sqrt_pos.mpr hdet)
  rw [Real.sqrt_lt' (Real.exp_pos _), ← Real.exp_nat_mul]
  convert hρlt using 2
  push_cast
  field_simp

end Cut

end Matrix
