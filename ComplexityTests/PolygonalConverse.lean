/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Converse
import ComplexityTests.PolygonalDrawing
import ComplexityTests.RotationCycleSpaceConverse
import Complexity.Foundations.Geometry.Polygonal.NoncrossingOrder

/-!
Concrete applications of the finite geometric converse to actual real-affine embeddings.
No numerical-genus hypothesis is supplied to any application.
-/

namespace ComplexityTests.PolygonalConverse

open Cslib Cslib.Complexity Cslib.Complexity.Graph
open Polygonal RotationSystem

-- Reuse the frozen checked geometric fixtures, without copying their segment proofs or
-- changing their visibility in the original test. The namespaced aliases are test scaffolding.
open Lean Elab Command in
run_cmd do
  let fixtures : List (Name × Name) :=
    [(`ComplexityTests.PolygonalDrawing.loopDrawing, `loopDrawing),
     (`ComplexityTests.PolygonalDrawing.loopRotation, `loopRotation),
     (`ComplexityTests.PolygonalDrawing.loop_embedding, `loopEmbedding),
     (`ComplexityTests.PolygonalDrawing.digonDrawing, `digonDrawing),
     (`ComplexityTests.PolygonalDrawing.digonRotation, `digonRotation),
     (`ComplexityTests.PolygonalDrawing.digon_embedding, `digonEmbedding),
     (`ComplexityTests.RotationCycleSpaceConverse.torusRotation, `torusRotation)]
  let env := (← getEnv).setExporting false
  let mut found : List Name := []
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    if moduleName == `ComplexityTests.PolygonalDrawing ||
        moduleName == `ComplexityTests.RotationCycleSpaceConverse then
      for name in data.constNames do
        if let some original := privateToUserName? name then
          for (fixture, shortName) in fixtures do
            if original == fixture then
              if found.contains fixture then throwError "duplicate fixture {fixture}"
              found := fixture :: found
              let target := (← getCurrNamespace) ++ shortName
              modifyEnv fun env => addAlias env target name
  unless found.length == fixtures.length do throwError "missing checked drawing fixtures"

private theorem lowDegree_realizes {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (r : RotationSystem G)
    (hdegree : ∀ a b c : Dart G, a.vertex = b.vertex → b.vertex = c.vertex →
      a = b ∨ b = c ∨ a = c) : D.Realizes r where
  nonzero := hD.germ_ne_zero
  directions_injective := hD.directions_injective
  clockwise := by
    intro a b c hv hw hab hbc hac
    rcases hdegree a b c hv hw with h | h | h
    · exact (hab h).elim
    · exact (hbc h).elim
    · exact (hac h).elim

-- A closed triangular loop, including its two separately indexed route ends.
example : loopRotation.NumericalGenusZero :=
  loopEmbedding.numericalGenusZero (by decide)
    (lowDegree_realizes loopEmbedding loopRotation (by decide))

-- The new face-color construction carries a nonzero loop label, so it must separate
-- the two actual face orbits. No face colors or genus fact are supplied.
example : ∃ q : loopRotation.Face → Bool,
    q (Quotient.mk _ (0, false)) ≠ q (Quotient.mk _ (0, true)) := by
  have hx : Graph.VertexEven ([7, 7], [(7, 7)]) (fun _ => true) := by
    intro v
    change (∑ d : Fin 1 × Bool,
      if Dart.vertex (G := ([7, 7], [(7, 7)])) d = v then (true : Bool) else 0) = false
    rw [Fintype.sum_prod_type, Fin.sum_univ_one, Fintype.sum_bool]
    change (if 7 = v then (true : Bool) else 0) + (if 7 = v then true else 0) = false
    rw [BooleanRing.add_self, Bool.zero_eq_false]
  obtain ⟨q, hq⟩ := loopEmbedding.exists_faceColors
    (lowDegree_realizes loopEmbedding loopRotation (by decide)) (by decide) (fun _ => true) hx
  refine ⟨q, fun h => ?_⟩
  have hbit := congrFun hq 0
  simp [RotationSystem.faceBoundary, h] at hbit

-- The actual two bowed parallel routes have the same listed endpoint pair.
example : digonRotation.NumericalGenusZero :=
  digonEmbedding.numericalGenusZero (by decide)
    (lowDegree_realizes digonEmbedding digonRotation (by decide))

-- A genuine bridge, with singleton rotations at its two different vertices.
example : (starRotation 1).NumericalGenusZero :=
  (PolygonalDrawing.star_isEmbedding 1).numericalGenusZero (by decide)
    (lowDegree_realizes (PolygonalDrawing.star_isEmbedding 1) (starRotation 1) (by decide))

private def starDistance (i j : Fin 5) : ℕ := (j.val + 5 - i.val) % 5

private theorem star_distance (i j : Fin 5) :
    (starRotation 5).rotationDistance (starDartEquiv 5 (i, true))
      (starDartEquiv 5 (j, true)) = starDistance i j := by
  have hpow : ∀ i j : Fin 5,
      ((starRotation 5).rotate ^ starDistance i j) (starDartEquiv 5 (i, true)) =
        starDartEquiv 5 (j, true) := by decide
  have hmin : ∀ i j k : Fin 5, k.val < starDistance i j →
      ((starRotation 5).rotate ^ k.val) (starDartEquiv 5 (i, true)) ≠
        starDartEquiv 5 (j, true) := by decide
  apply (starRotation 5).rotationDistance_eq _ _ (by simp) _ (hpow i j)
  intro k hk
  have hbound : starDistance i j < 5 := Nat.mod_lt _ (by decide)
  exact hmin i j ⟨k, by omega⟩ hk

private theorem star_interval (i j k : Fin 5) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    starDartEquiv 5 (j, true) ∈ (starRotation 5).rotationInterval
      (starDartEquiv 5 (i, true)) (starDartEquiv 5 (k, true)) ↔
    (i.val < j.val ∧ j.val < k.val) ∨ (j.val < k.val ∧ k.val < i.val) ∨
      (k.val < i.val ∧ i.val < j.val) := by
  have hfinite : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k →
      (starDartEquiv 5 (j, true) ∈ (Finset.range (starDistance i k)).image
        (fun n => ((starRotation 5).rotate ^ (n + 1)) (starDartEquiv 5 (i, true))) ↔
      (i.val < j.val ∧ j.val < k.val) ∨ (j.val < k.val ∧ k.val < i.val) ∨
        (k.val < i.val ∧ i.val < j.val)) := by decide
  unfold RotationSystem.rotationInterval
  rw [star_distance]
  exact hfinite i j k hij hjk hik

private theorem star_five_realizes : (PolygonalDrawing.star 5).Realizes (starRotation 5) where
  nonzero := (PolygonalDrawing.star_isEmbedding 5).germ_ne_zero
  directions_injective := (PolygonalDrawing.star_isEmbedding 5).directions_injective
  clockwise := by
    intro a b c hv hw hab hbc hac
    have hcenter : ∀ a b : Dart (starGraph 5), a.vertex = b.vertex → a ≠ b →
        a.2 = true ∧ b.2 = true := by decide
    obtain ⟨⟨i, bi⟩, rfl⟩ := (starDartEquiv 5).surjective a
    obtain ⟨⟨j, bj⟩, rfl⟩ := (starDartEquiv 5).surjective b
    obtain ⟨⟨k, bk⟩, rfl⟩ := (starDartEquiv 5).surjective c
    have hbi := (hcenter _ _ hv hab).1
    have hbj := (hcenter _ _ hv hab).2
    have hbk := (hcenter _ _ hw hbc).2
    change bi = true at hbi
    change bj = true at hbj
    change bk = true at hbk
    subst bi
    subst bj
    subst bk
    have hdir (i : Fin 5) :
        (PolygonalDrawing.star 5).direction (starDartEquiv 5 (i, true)) =
          ((⟨(i.val : ℝ) + 1, 1⟩ : ℂ).arg : Real.Angle) := by
      simp [PolygonalDrawing.direction, PolygonalDrawing.germ, PolygonalDrawing.star,
        starDartEquiv, Route.germ, Route.line, Route.finish]
    have hij : (i.val : ℝ) + 1 ≠ (j.val : ℝ) + 1 := by
      intro h
      have hnat : i.val = j.val := by exact_mod_cast add_right_cancel h
      exact hab (congrArg (fun i => starDartEquiv 5 (i, true)) (Fin.ext hnat))
    have hjk : (j.val : ℝ) + 1 ≠ (k.val : ℝ) + 1 := by
      intro h
      have hnat : j.val = k.val := by exact_mod_cast add_right_cancel h
      exact hbc (congrArg (fun i => starDartEquiv 5 (i, true)) (Fin.ext hnat))
    have hik : (i.val : ℝ) + 1 ≠ (k.val : ℝ) + 1 := by
      intro h
      have hnat : i.val = k.val := by exact_mod_cast add_right_cancel h
      exact hac (congrArg (fun i => starDartEquiv 5 (i, true)) (Fin.ext hnat))
    rw [hdir, hdir, hdir, clockwise_ports_iff (by positivity) (by positivity)
      (by positivity) hij hjk hik]
    simp only [add_lt_add_iff_right, Nat.cast_lt]
    exact (star_interval i j k (fun h => hab (by rw [h]))
      (fun h => hbc (by rw [h])) (fun h => hac (by rw [h]))).symm

-- The degree-five center checks the orientation and unbounded-degree endpoint together.
example : (starRotation 5).NumericalGenusZero :=
  (PolygonalDrawing.star_isEmbedding 5).numericalGenusZero (by decide) star_five_realizes

-- Arbitrary sparse/duplicate declarations, including empty declarations and isolates.
example (vs : List ℕ) (r : RotationSystem (vs, [])) : r.NumericalGenusZero := by
  apply (PolygonalDrawing.points_isEmbedding vs).numericalGenusZero
    (by intro v hv; simp [incidenceVertices] at hv)
  exact PolygonalDrawing.points_realizes vs r

example (r : RotationSystem ([7, 7, 1000000000, 3, 1000000000], [])) :
    r.NumericalGenusZero :=
  (PolygonalDrawing.points_isEmbedding _).numericalGenusZero
    (by intro v hv; simp [incidenceVertices] at hv) (PolygonalDrawing.points_realizes _ r)

example (r : RotationSystem ([], [])) : r.NumericalGenusZero :=
  (PolygonalDrawing.points_isEmbedding _).numericalGenusZero
    (by intro v hv; simp [incidenceVertices] at hv) (PolygonalDrawing.points_realizes _ r)

-- This rules out realization of this interlaced rotation of a planar underlying bouquet.
-- It does not assert nonplanarity of the underlying graph.
example (D : PolygonalDrawing ([0, 9, 9], [(0, 0), (0, 0)])) (hD : D.IsEmbedding) :
    ¬D.Realizes torusRotation := by
  intro hR
  have hg := hD.numericalGenusZero (by decide) hR
  have hv := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation torusRotation (by decide))).mpr
      ((RotationCertificate.decode_ofRotation torusRotation (by decide)).symm ▸ hg)
  exact (by decide : RotationCertificate.verifyEuler _
    (RotationCertificate.ofRotation torusRotation) ≠ true) hv

end ComplexityTests.PolygonalConverse
