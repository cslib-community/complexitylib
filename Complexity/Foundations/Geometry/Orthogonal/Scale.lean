/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.Simple
import Mathlib.Analysis.Convex.Basic

/-!
# Integer dilation of orthogonal drawings

Positive integer dilation preserves continuous route supports, proper orthogonality, and
simplicity, multiplies Manhattan wire length, and preserves the number of listed segments.

## Main definitions

* `dilateRoute`: multiply every integer coordinate by a natural factor.

## Main results

* `support_dilateRoute`, `isOrthogonal_dilateRoute_iff`, `isSimple_dilateRoute_iff`.
* `wireLength_dilateRoute`, `consecutivePairs_length_dilateRoute`.

## References

These elementary affine-coordinate lemmas and proofs are original.
-/

@[expose] public section

namespace Cslib.Orthogonal


/-- Dilate each listed integer point by the same natural factor. -/
def dilateRoute (k : ℕ) (r : Route) : Route := r.map (k • ·)

/-- Integer dilation commutes with inclusion into the real plane. -/
theorem realPoint_nsmul (k : ℕ) (p : Point) :
    realPoint (k • p) = (k : ℝ) • realPoint p := by
  rcases p with ⟨px, py⟩
  ext <;> simp [realPoint, Prod.smul_mk]

/-- Positive integer dilation is injective on grid points. -/
theorem nsmul_point_injective {k : ℕ} (hk : k ≠ 0) :
    Function.Injective (fun p : Point => k • p) := by
  rintro ⟨ax, ay⟩ ⟨bx, by'⟩ h
  have hk' : (k : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  simp only [Prod.smul_mk, Int.nsmul_eq_mul, Prod.mk.injEq] at h
  exact Prod.ext (mul_left_cancel₀ hk' h.1) (mul_left_cancel₀ hk' h.2)

private theorem real_nsmul_point_injective {k : ℕ} (hk : k ≠ 0) :
    Function.Injective (fun p : ℝ × ℝ => (k : ℝ) • p) := by
  rintro ⟨ax, ay⟩ ⟨bx, by'⟩ h
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq] at h
  exact Prod.ext (mul_left_cancel₀ hk' h.1) (mul_left_cancel₀ hk' h.2)

/-- The segment between dilated endpoints is the dilation of the original real segment. -/
theorem segment_nsmul (k : ℕ) (a b : Point) :
    segment (k • a) (k • b) = (fun p : ℝ × ℝ => (k : ℝ) • p) '' segment a b := by
  have h := image_segment ℝ ((k : ℝ) • AffineMap.id ℝ (ℝ × ℝ))
    (realPoint a) (realPoint b)
  change (fun p : ℝ × ℝ => (k : ℝ) • p) '' _root_.segment ℝ (realPoint a) (realPoint b) =
    _root_.segment ℝ ((k : ℝ) • realPoint a) ((k : ℝ) • realPoint b) at h
  simpa only [Orthogonal.segment, realPoint_nsmul] using h.symm

/-- Membership in a dilated segment is exactly dilated membership. -/
theorem mem_segment_nsmul_iff {k : ℕ} (hk : k ≠ 0) (a b : Point) (p : ℝ × ℝ) :
    (k : ℝ) • p ∈ segment (k • a) (k • b) ↔ p ∈ segment a b := by
  rw [segment_nsmul]
  exact (real_nsmul_point_injective hk).mem_set_image

/-- Dilation maps the consecutive segments in their unchanged order. -/
theorem consecutivePairs_dilateRoute (k : ℕ) (r : Route) :
    (dilateRoute k r).consecutivePairs =
      r.consecutivePairs.map (fun e => (k • e.1, k • e.2)) := by
  simp only [dilateRoute, List.consecutivePairs, ← List.map_tail, List.zip_map]
  rfl

/-- Dilation leaves the number of listed segments unchanged. -/
theorem consecutivePairs_length_dilateRoute (k : ℕ) (r : Route) :
    (dilateRoute k r).consecutivePairs.length = r.consecutivePairs.length := by
  rw [consecutivePairs_dilateRoute, List.length_map]

/-- Dilation maps the entire real polygonal support, including singleton routes. -/
theorem support_dilateRoute (k : ℕ) (r : Route) :
    support (dilateRoute k r) = (fun p : ℝ × ℝ => (k : ℝ) • p) '' support r := by
  ext p
  simp only [support, Set.mem_ofPred_eq, consecutivePairs_dilateRoute]
  simp only [dilateRoute, List.mem_map, Set.mem_image]
  constructor
  · rintro (⟨_, ⟨a, ha, rfl⟩, rfl⟩ | ⟨_, ⟨e, he, rfl⟩, hp⟩)
    · exact ⟨realPoint a, Or.inl ⟨a, ha, rfl⟩, (realPoint_nsmul k a).symm⟩
    · obtain ⟨q, hq, rfl⟩ := (segment_nsmul k e.1 e.2) ▸ hp
      exact ⟨q, Or.inr ⟨e, he, hq⟩, rfl⟩
  · rintro ⟨q, ⟨a, ha, rfl⟩ | ⟨e, he, hq⟩, rfl⟩
    · exact Or.inl ⟨k • a, ⟨a, ha, rfl⟩, (realPoint_nsmul k a).symm⟩
    · exact Or.inr ⟨(k • e.1, k • e.2), ⟨e, he, rfl⟩,
        (segment_nsmul k e.1 e.2) ▸ Set.mem_image_of_mem _ hq⟩

/-- Proper axis alignment is invariant under positive integer dilation. -/
theorem axisAligned_nsmul_iff {k : ℕ} (hk : k ≠ 0) (a b : Point) :
    AxisAligned (k • a) (k • b) ↔ AxisAligned a b := by
  have hk' : (k : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hm (x y : ℤ) : (k : ℤ) * x = (k : ℤ) * y ↔ x = y :=
    ⟨mul_left_cancel₀ hk', congrArg _⟩
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, by'⟩
  simp only [AxisAligned, Prod.smul_mk, Int.nsmul_eq_mul, hm,
    Prod.mk.injEq, ne_eq]

/-- Proper orthogonality is invariant under positive integer dilation. -/
theorem isOrthogonal_dilateRoute_iff {k : ℕ} (hk : k ≠ 0) (r : Route) :
    IsOrthogonal (dilateRoute k r) ↔ IsOrthogonal r := by
  simp only [IsOrthogonal, consecutivePairs_dilateRoute, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, axisAligned_nsmul_iff hk]

/-- Every Manhattan segment length is multiplied by the dilation factor. -/
theorem length_nsmul (k : ℕ) (a b : Point) :
    length (k • a) (k • b) = k * length a b := by
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, by'⟩
  simp [length, Prod.smul_mk, ← mul_sub, Int.natAbs_mul, Nat.mul_add]

/-- Total Manhattan wire length is multiplied by the dilation factor. -/
theorem wireLength_dilateRoute (k : ℕ) (r : Route) :
    wireLength (dilateRoute k r) = k * wireLength r := by
  simp only [wireLength, consecutivePairs_dilateRoute, List.map_map, Function.comp_def,
    length_nsmul, List.sum_map_mul_left]

/-- Endpoint-only segment contacts are invariant under positive integer dilation. -/
theorem endpointContacts_nsmul_iff {k : ℕ} (hk : k ≠ 0) (a b c d : Point) :
    EndpointContacts (k • a) (k • b) (k • c) (k • d) ↔ EndpointContacts a b c d := by
  constructor
  · intro h p hp hq
    have hh := h ((k : ℝ) • p) ((mem_segment_nsmul_iff hk a b p).2 hp)
      ((mem_segment_nsmul_iff hk c d p).2 hq)
    simp only [realPoint_nsmul] at hh
    exact ⟨hh.1.imp (fun h => real_nsmul_point_injective hk h)
        (fun h => real_nsmul_point_injective hk h),
      hh.2.imp (fun h => real_nsmul_point_injective hk h)
        (fun h => real_nsmul_point_injective hk h)⟩
  · intro h p hp hq
    obtain ⟨q, hqa, rfl⟩ := (segment_nsmul k a b) ▸ hp
    have hqc := (mem_segment_nsmul_iff hk c d q).1 hq
    have hh := h q hqa hqc
    simp only [realPoint_nsmul]
    exact ⟨hh.1.imp (congrArg _) (congrArg _), hh.2.imp (congrArg _) (congrArg _)⟩

/-- Continuous simplicity is invariant under positive integer dilation. -/
theorem isSimple_dilateRoute_iff {k : ℕ} (hk : k ≠ 0) (r : Route) :
    IsSimple (dilateRoute k r) ↔ IsSimple r := by
  simp only [IsSimple, consecutivePairs_dilateRoute]
  simp only [dilateRoute, List.nodup_map_iff (nsmul_point_injective hk), List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, endpointContacts_nsmul_iff hk]
  simp only [ne_eq, Prod.mk.injEq, (nsmul_point_injective hk).eq_iff, ← Prod.ext_iff]

end Cslib.Orthogonal
