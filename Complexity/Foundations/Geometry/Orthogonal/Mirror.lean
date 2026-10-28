/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.Simple
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring

/-!
# Horizontal reflection of orthogonal routes

## Main definitions

* `mirrorPoint`, `mirrorReal`, `mirrorRoute`: reflection in the vertical axis.

## Main results

* `support_mirrorRoute`, `isOrthogonal_mirrorRoute_iff`, `isSimple_mirrorRoute_iff`.
* `wireLength_mirrorRoute`: reflection preserves Manhattan wire length.

## References

These elementary affine-coordinate lemmas and proofs are original.
-/

@[expose] public section

namespace Cslib.Orthogonal


/-- Horizontal reflection of integer points. -/
def mirrorPoint (p : Point) : Point := (-p.1, p.2)

/-- The corresponding horizontal reflection in the real plane. -/
def mirrorReal (p : ℝ × ℝ) : ℝ × ℝ := (-p.1, p.2)

/-- Reflect every listed point. -/
def mirrorRoute (r : Route) : Route := r.map mirrorPoint

private def mirrorLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := mirrorReal
  map_add' p q := by ext <;> simp [mirrorReal, add_comm]
  map_smul' s p := by ext <;> simp [mirrorReal]

/-- Integer and real reflections commute with inclusion of the lattice. -/
theorem realPoint_mirrorPoint (p : Point) :
    realPoint (mirrorPoint p) = mirrorReal (realPoint p) := by
  ext <;> simp [mirrorPoint, mirrorReal, realPoint]

private theorem mirrorPoint_involutive : Function.Involutive mirrorPoint := by
  intro p
  ext <;> simp [mirrorPoint]

private theorem mirrorReal_involutive : Function.Involutive mirrorReal := by
  intro p
  ext <;> simp [mirrorReal]

/-- Reflection maps complete real segments. -/
theorem segment_mirrorPoint (a b : Point) :
    segment (mirrorPoint a) (mirrorPoint b) = mirrorReal '' segment a b := by
  have h := image_segment ℝ mirrorLinear.toAffineMap (realPoint a) (realPoint b)
  change mirrorReal '' _root_.segment ℝ (realPoint a) (realPoint b) =
    _root_.segment ℝ (mirrorReal (realPoint a)) (mirrorReal (realPoint b)) at h
  simpa only [Orthogonal.segment, realPoint_mirrorPoint] using h.symm

/-- Reflected segment membership is reflected membership. -/
theorem mem_segment_mirrorPoint_iff (a b : Point) (p : ℝ × ℝ) :
    mirrorReal p ∈ segment (mirrorPoint a) (mirrorPoint b) ↔ p ∈ segment a b := by
  rw [segment_mirrorPoint]
  exact mirrorReal_involutive.injective.mem_set_image

/-- Reflection maps every listed segment without changing its index. -/
theorem consecutivePairs_mirrorRoute (r : Route) :
    (mirrorRoute r).consecutivePairs =
      r.consecutivePairs.map (fun e => (mirrorPoint e.1, mirrorPoint e.2)) := by
  simp only [mirrorRoute, List.consecutivePairs, ← List.map_tail, List.zip_map]
  rfl

/-- Reflection maps the entire continuous route support. -/
theorem support_mirrorRoute (r : Route) : support (mirrorRoute r) = mirrorReal '' support r := by
  ext p
  simp only [support, Set.mem_ofPred_eq, consecutivePairs_mirrorRoute]
  simp only [mirrorRoute, List.mem_map, Set.mem_image]
  constructor
  · rintro (⟨_, ⟨a, ha, rfl⟩, rfl⟩ | ⟨_, ⟨e, he, rfl⟩, hp⟩)
    · exact ⟨realPoint a, Or.inl ⟨a, ha, rfl⟩, (realPoint_mirrorPoint a).symm⟩
    · obtain ⟨q, hq, rfl⟩ := (segment_mirrorPoint e.1 e.2) ▸ hp
      exact ⟨q, Or.inr ⟨e, he, hq⟩, rfl⟩
  · rintro ⟨q, ⟨a, ha, rfl⟩ | ⟨e, he, hq⟩, rfl⟩
    · exact Or.inl ⟨mirrorPoint a, ⟨a, ha, rfl⟩, (realPoint_mirrorPoint a).symm⟩
    · exact Or.inr ⟨(mirrorPoint e.1, mirrorPoint e.2), ⟨e, he, rfl⟩,
        (segment_mirrorPoint e.1 e.2) ▸ Set.mem_image_of_mem _ hq⟩

private theorem axisAligned_mirrorPoint_iff (a b : Point) :
    AxisAligned (mirrorPoint a) (mirrorPoint b) ↔ AxisAligned a b := by
  simp [AxisAligned, mirrorPoint, Prod.ext_iff]

/-- Reflection preserves proper orthogonality. -/
theorem isOrthogonal_mirrorRoute_iff (r : Route) :
    IsOrthogonal (mirrorRoute r) ↔ IsOrthogonal r := by
  simp only [IsOrthogonal, consecutivePairs_mirrorRoute, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, axisAligned_mirrorPoint_iff]

private theorem endpointContacts_mirrorPoint_iff (a b c d : Point) :
    EndpointContacts (mirrorPoint a) (mirrorPoint b) (mirrorPoint c) (mirrorPoint d) ↔
      EndpointContacts a b c d := by
  constructor
  · intro h p hp hq
    have hh := h (mirrorReal p) ((mem_segment_mirrorPoint_iff a b p).2 hp)
      ((mem_segment_mirrorPoint_iff c d p).2 hq)
    simp only [realPoint_mirrorPoint] at hh
    exact ⟨hh.1.imp (fun h => mirrorReal_involutive.injective h)
        (fun h => mirrorReal_involutive.injective h),
      hh.2.imp (fun h => mirrorReal_involutive.injective h)
        (fun h => mirrorReal_involutive.injective h)⟩
  · intro h p hp hq
    obtain ⟨q, hqa, rfl⟩ := (segment_mirrorPoint a b) ▸ hp
    have hh := h q hqa ((mem_segment_mirrorPoint_iff c d q).1 hq)
    simp only [realPoint_mirrorPoint]
    exact ⟨hh.1.imp (congrArg _) (congrArg _), hh.2.imp (congrArg _) (congrArg _)⟩

/-- Reflection preserves continuous simplicity. -/
theorem isSimple_mirrorRoute_iff (r : Route) : IsSimple (mirrorRoute r) ↔ IsSimple r := by
  simp only [IsSimple, consecutivePairs_mirrorRoute]
  simp only [mirrorRoute, List.nodup_map_iff mirrorPoint_involutive.injective, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, endpointContacts_mirrorPoint_iff]
  simp only [ne_eq, Prod.mk.injEq, mirrorPoint_involutive.injective.eq_iff, ← Prod.ext_iff]

private theorem length_mirrorPoint (a b : Point) :
    length (mirrorPoint a) (mirrorPoint b) = length a b := by
  have hx : -b.1 - -a.1 = -(b.1 - a.1) := by ring
  simp only [length, mirrorPoint, hx, Int.natAbs_neg]

/-- Reflection preserves total Manhattan wire length. -/
theorem wireLength_mirrorRoute (r : Route) : wireLength (mirrorRoute r) = wireLength r := by
  simp only [wireLength, consecutivePairs_mirrorRoute, List.map_map, Function.comp_def,
    length_mirrorPoint]

end Cslib.Orthogonal
