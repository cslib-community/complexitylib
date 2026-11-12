/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Affine

/-!
# A small neighborhood of a finite straight-segment arrangement

A sufficiently small ball about any point avoids every segment of a finite arrangement
that does not contain that point. The proof uses compactness of actual real segments and
finite union, rather than a local-disk provider.
-/

public section

namespace Cslib.Polygonal

/-- A finite family of genuine planar segments has a neighborhood of `z` meeting only
segments that already contain `z`. Degenerate segments are allowed in this general lemma. -/
theorem exists_ball_only_incident_segments {ι : Type*} [Finite ι] (a b : ι → ℂ) (z : ℂ) :
    ∃ ε > 0, ∀ i w, w ∈ Metric.ball z ε → w ∈ segment ℝ (a i) (b i) →
      z ∈ segment ℝ (a i) (b i) := by
  classical
  let K : Set ℂ := ⋃ i, if z ∈ segment ℝ (a i) (b i) then ∅ else segment ℝ (a i) (b i)
  have hc : IsClosed K := by
    apply isClosed_iUnion_of_finite
    intro i
    split_ifs
    · exact isClosed_empty
    · rw [segment_eq_image_lineMap]
      exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  have hz : z ∈ Kᶜ := by simp [K]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hc.isOpen_compl z hz
  refine ⟨ε, hε, fun i w hw hseg => ?_⟩
  by_contra hzi
  apply hball hw
  exact Set.mem_iUnion.mpr ⟨i, by simpa only [hzi, ↓reduceIte] using hseg⟩

end Cslib.Polygonal
