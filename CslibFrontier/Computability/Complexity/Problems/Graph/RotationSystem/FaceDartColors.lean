/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CycleSpace
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CycleSpaceConverse

/-!
# Clockwise dart colors for actual face boundaries

A face coloring gives the color at the clockwise corner following a dart by reading the
face of its reverse. With the existing `faceNext = rotate⁻¹ ∘ reverse`, these colors satisfy
`P (rotate d) = P d.reverse`. The reversal is essential: reading the face of `d` directly
would give the opposite recurrence. Conversely this recurrence descends to actual face colors.
The existing cycle-space converse then gives a numerical genus criterion in these coordinates.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

variable {G : Graph} (r : RotationSystem G)

/-- The actual face color at the clockwise corner following an indexed dart. -/
@[expose] def faceDartColor (q : r.Face → Bool) (d : Dart G) : Bool :=
  q (Quotient.mk _ d.reverse)

/-- Positive vertex rotation moves to the clockwise color at the reverse dart. -/
theorem faceDartColor_rotate (q : r.Face → Bool) (d : Dart G) :
    r.faceDartColor q (r.rotate d) = r.faceDartColor q d.reverse := by
  have h := congrArg q (r.face_eq_next ((r.rotate d).reverse))
  have hnext : r.faceNext (r.rotate d).reverse = d := by
    unfold faceNext
    change r.rotate.symm (r.rotate d).reverse.reverse = d
    rw [Dart.reverse_reverse, r.rotate.symm_apply_apply]
  rw [hnext] at h
  simpa only [faceDartColor, Dart.reverse_reverse] using h.symm

/-- The colors at the two indexed ends recover the original face-boundary edge bit. -/
theorem faceDartColor_xor_reverse (q : r.Face → Bool) (d : Dart G) :
    (r.faceDartColor q d ^^ r.faceDartColor q d.reverse) = r.faceBoundary q d.1 := by
  rw [r.faceBoundary_dart]
  simp only [faceDartColor, Dart.reverse_reverse]
  exact Bool.xor_comm _ _

/-- Clockwise dart colors satisfying the actual rotation recurrence descend to face colors,
with exactly the same edge boundary. No genus, connectedness or degree premise is needed. -/
theorem exists_faceColors_of_dartColors (x : Fin G.edges.length → Bool)
    (P : Dart G → Bool) (hP : ∀ d, P (r.rotate d) = P d.reverse)
    (hx : ∀ d, (P d ^^ P d.reverse) = x d.1) :
    ∃ q : r.Face → Bool, r.faceBoundary q = x := by
  let Q : Dart G → Bool := fun d => P d.reverse
  have hQ : Function.Semiconj Q r.faceNext (1 : Equiv.Perm Bool) := by
    intro d
    have h := hP (r.faceNext d)
    have he : r.rotate (r.faceNext d) = d.reverse :=
      r.rotate.apply_symm_apply d.reverse
    rw [he] at h
    exact h.symm
  let q : r.Face → Bool := Quotient.lift Q fun d e he =>
    Equiv.Perm.sameCycle_one.mp (he.map_of_semiconj hQ)
  refine ⟨q, funext fun i => ?_⟩
  change (P (i, true) ^^ P (i, false)) = x i
  exact hx (i, true)

/-- Face boundaries are exactly the edge labels obtained from compatible clockwise dart
colors. This equivalence requires neither genus zero nor any endpoint declaration premise. -/
theorem exists_faceColors_iff_exists_dartColors (x : Fin G.edges.length → Bool) :
    (∃ q : r.Face → Bool, r.faceBoundary q = x) ↔
      ∃ P : Dart G → Bool, (∀ d, P (r.rotate d) = P d.reverse) ∧
        ∀ d, (P d ^^ P d.reverse) = x d.1 := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨r.faceDartColor q, r.faceDartColor_rotate q, r.faceDartColor_xor_reverse q⟩
  · rintro ⟨P, hP, hx⟩
    exact r.exists_faceColors_of_dartColors x P hP hx

/-- The existing componentwise numerical genus criterion in explicit clockwise coordinates.
Applications must construct the colors from each actual vertex-even edge labeling. -/
theorem numericalGenusZero_of_vertexEven_dartColors
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (hcolor : ∀ x : Fin G.edges.length → Bool, G.VertexEven x →
      ∃ P : Dart G → Bool, (∀ d, P (r.rotate d) = P d.reverse) ∧
        ∀ d, (P d ^^ P d.reverse) = x d.1) : r.NumericalGenusZero := by
  apply r.numericalGenusZero_of_vertexEven_faceBoundary hG
  intro x hx
  obtain ⟨P, hP, he⟩ := hcolor x hx
  exact r.exists_faceColors_of_dartColors x P hP he

end Cslib.Complexity.Graph.RotationSystem
