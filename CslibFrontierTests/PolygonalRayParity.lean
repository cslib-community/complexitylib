/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.FaceColorsRayParity
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Points
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star
import CslibFrontier.Foundations.Geometry.Polygonal.Noncrossing

/-!
Actual real-parameter and half-open endpoint tests. The drawing tests use genuine embeddings
and test local ray parity. The completed geometric-to-numerical endpoint is tested separately
in `PolygonalConverse`.
-/

namespace CslibFrontierTests.PolygonalRayParity

open Cslib Polygonal Cslib.Complexity Graph

-- Every real parameter below the upper endpoint contributes, including the lower endpoint.
example (t : ℝ) (ht : t ∈ Set.Ico 0 1) : RayCrosses ⟨1, 0⟩ ⟨1, 1⟩ ⟨0, t⟩ := by
  simpa [RayCrosses, horizontalIntercept] using ht

example : ¬RayCrosses ⟨1, 0⟩ ⟨1, 1⟩ ⟨0, 1⟩ := by
  norm_num [RayCrosses]

example : ¬RayCrosses ⟨1, 0⟩ ⟨1, 1⟩ ⟨1, 0⟩ := by
  norm_num [RayCrosses, horizontalIntercept]

example (x h : ℝ) : ¬RayCrosses ⟨-1, h⟩ ⟨1, h⟩ ⟨x, h⟩ :=
  not_rayCrosses_of_im_eq (a := ⟨-1, h⟩) (b := ⟨1, h⟩) rfl _

example (a b z : ℂ) : RayCrosses b a z ↔ RayCrosses a b z := rayCrosses_reverse a b z

example (t : ℝ) (ht : t ∈ Set.Ico 0 1) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1,
      (AffineMap.lineMap (⟨1, 0⟩ : ℂ) ⟨1, 1⟩ s).im = t ∧
      0 < (AffineMap.lineMap (⟨1, 0⟩ : ℂ) ⟨1, 1⟩ s).re ∧ t < 1 := by
  have h : RayCrosses ⟨1, 0⟩ ⟨1, 1⟩ ⟨0, t⟩ := by
    simpa [RayCrosses, horizontalIntercept] using ht
  simpa using (rayCrosses_iff_exists _ _ _).mp h

-- The two lower-endpoint contributions at a V cancel, with both occurrences retained.
example : rayParity (fun _ : Fin 2 => (⟨1, 0⟩ : ℂ))
    (fun i => if i = 0 then (⟨0, 1⟩ : ℂ) else ⟨2, 1⟩) (fun _ => true) ⟨0, 0⟩ = false := by
  simp only [rayParity, Fin.sum_univ_two, Bool.add_eq_xor]
  norm_num [RayCrosses, horizontalIntercept]

-- Repeated geometric segments remain separate indexed occurrences and cancel modulo two.
example : rayParity (fun _ : Fin 2 => (⟨1, 0⟩ : ℂ))
    (fun _ => (⟨1, 1⟩ : ℂ)) (fun _ => true) ⟨0, (1 / 2 : ℝ)⟩ = false := by
  simp only [rayParity, Fin.sum_univ_two, Bool.add_eq_xor]
  norm_num [RayCrosses, horizontalIntercept]

open Classical in
example : ∀ᶠ w in nhds (⟨0, 0⟩ : ℂ),
    (decide (RayCrosses ⟨1, 0⟩ ⟨1, 1⟩ w) ^^
      decide (RayCrosses ⟨1, 0⟩ ⟨1, 1⟩ ⟨0, 0⟩)) = !decide (0 ≤ w.im) := by
  simpa using eventually_rayCrosses_endpoint_jump ⟨1, 0⟩ ⟨1, 1⟩ ⟨0, 0⟩
    (by norm_num) rfl (by norm_num)

-- Generic direction selection includes horizontal and vertical pairs simultaneously.
example : ∃ u : ℂ, u ≠ 0 ∧ Set.InjOn (fun z => (u * z).im)
    (↑({0, 1, Complex.I, 1 + Complex.I} : Finset ℂ) : Set ℂ) :=
  exists_mul_im_injOn _

-- A single selected segment has odd incidence at its ends, but its endpoint jumps vanish
-- below both ends. The weaker shared criterion still proves local constancy there.
open Classical in
example :
    ¬(∀ p : ℂ, (∑ _ : Unit, ((if (⟨1, 1⟩ : ℂ) = p then true else 0) +
      (if (⟨1, 2⟩ : ℂ) = p then true else 0))) = false) ∧
    ∀ᶠ w in nhds (0 : ℂ),
      rayParity (fun _ : Unit => (⟨1, 1⟩ : ℂ)) (fun _ => ⟨1, 2⟩) (fun _ => true) w =
        rayParity (fun _ : Unit => (⟨1, 1⟩ : ℂ)) (fun _ => ⟨1, 2⟩) (fun _ => true) 0 := by
  constructor
  · intro h
    have hp := h ⟨1, 1⟩
    norm_num at hp
  · apply eventually_rayParity_eq_of_endpoint_jumps_eq_zero
      (fun _ : Unit => (⟨1, 1⟩ : ℂ)) (fun _ => ⟨1, 2⟩) (fun _ => true)
    · intro i
      norm_num
    · intro i hi h
      rw [segment_eq_image_lineMap] at h
      obtain ⟨t, ht, heq⟩ := h
      have hre := congrArg Complex.re heq
      norm_num [AffineMap.lineMap_apply_module'] at hre
    · norm_num [Bool.zero_eq_false, Bool.mul_eq_and, Bool.add_eq_xor]
      rfl

private abbrev loopGraph : Graph := ([7, 7], [(7, 7)])

private def loopDrawing : PolygonalDrawing loopGraph where
  vertex := fun _ => 0
  route := fun _ => portLoop (-1) 1
  endpoint_eq := by intro e b; exact endpoint_portLoop (-1) 1 b

private theorem loop_embedding : loopDrawing.IsEmbedding where
  vertices_injective := by
    intro a ha b hb _
    have ha' : a = 7 := by simpa using ha
    have hb' : b = 7 := by simpa using hb
    exact ha'.trans hb'.symm
  simple := fun _ => isSimple_portLoop (by norm_num)
  vertex_contacts := by
    intro e i t ht v hv heq
    obtain ⟨b, hb⟩ := atEnd_of_eval_portLoop_eq_zero
      (by norm_num : (-1 : ℝ) ≠ 1) i ht heq
    refine ⟨b, hb, ?_⟩
    have hv' : v = 7 := by simpa using hv
    subst v
    have he : e = 0 := Subsingleton.elim (α := Fin 1) _ _
    subst e
    cases b <;> rfl
  edge_contacts := by
    intro e f hne
    exact (hne (Subsingleton.elim (α := Fin 1) _ _)).elim

private theorem loop_even : loopGraph.VertexEven (fun _ => true) := by
  intro v
  simp only [vertexParity, Dart, Fintype.sum_prod_type, Fintype.sum_bool]
  change (∑ i : Fin 1, ((if Dart.vertex (G := loopGraph) (i, true) = v then true else 0) +
    (if Dart.vertex (G := loopGraph) (i, false) = v then true else 0))) = false
  rw [Fin.sum_univ_one]
  change ((if 7 = v then true else 0) + (if 7 = v then true else 0)) = false
  rw [Bool.add_eq_xor, Bool.xor_self]

-- This genuinely embedded loop yields a constructed generic direction and a locally
-- constant ray parity, for every point off the rotated support. No face colors are supplied.
example : ∃ u : ℂ, u ≠ 0 ∧ ∀ z : ℂ,
    (∀ s : loopDrawing.SegmentIndex,
      z ∉ segment ℝ (u * loopDrawing.segmentStart s) (u * loopDrawing.segmentFinish s)) →
    ∀ᶠ w in nhds z,
      rayParity (fun s => u * loopDrawing.segmentStart s)
        (fun s => u * loopDrawing.segmentFinish s) (fun _ => true) w =
      rayParity (fun s => u * loopDrawing.segmentStart s)
        (fun s => u * loopDrawing.segmentFinish s) (fun _ => true) z := by
  obtain ⟨u, hu, h⟩ := loop_embedding.exists_rayParity_locally_constant
  exact ⟨u, hu, fun z hz => h _ loop_even z (fun s _ => hz s)⟩

-- Genuine high-degree geometry, sparse duplicated points and the empty arrangement use
-- the same local theorem. These statements assert no numerical-genus characterization.
private abbrev LocalParity {G : Graph} (D : PolygonalDrawing G) (u : ℂ) : Prop :=
  ∀ x : Fin G.2.length → Bool, G.VertexEven x → ∀ z : ℂ,
    (∀ s : D.SegmentIndex, x s.1 = true →
      z ∉ segment ℝ (u * D.segmentStart s) (u * D.segmentFinish s)) →
    ∀ᶠ w in nhds z,
      rayParity (fun s => u * D.segmentStart s) (fun s => u * D.segmentFinish s)
          (fun s => x s.1) w =
        rayParity (fun s => u * D.segmentStart s) (fun s => u * D.segmentFinish s)
          (fun s => x s.1) z

example (n : ℕ) : ∃ u : ℂ, u ≠ 0 ∧ LocalParity (PolygonalDrawing.star n) u :=
  (PolygonalDrawing.star_isEmbedding n).exists_rayParity_locally_constant

example : ∃ u : ℂ, u ≠ 0 ∧
    LocalParity (PolygonalDrawing.points [2 ^ 100, 7, 7, 23]) u :=
  (PolygonalDrawing.points_isEmbedding [2 ^ 100, 7, 7, 23]).exists_rayParity_locally_constant

example : ∃ u : ℂ, u ≠ 0 ∧ LocalParity (PolygonalDrawing.points []) u :=
  (PolygonalDrawing.points_isEmbedding []).exists_rayParity_locally_constant

end CslibFrontierTests.PolygonalRayParity
