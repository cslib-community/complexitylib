/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntersectionParity
import Mathlib.Tactic.FinCases

/-!
Finite face-boundary and closed-passage regression cases. Numerical genus is checked through
the actual certificate verifier. The torus example checks an odd local crossing and failure
of numerical genus zero, rather than assuming a geometric characterization.
-/

namespace CslibFrontierTests.RotationIntersection

open Cslib Cslib.Complexity Cslib.Complexity.Graph

private abbrev bridge : Graph := ([0, 1], [(0, 1)])
private abbrev loopGraph : Graph := ([0], [(0, 0)])
private abbrev digon : Graph := ([0, 1], [(0, 1), (0, 1)])
private abbrev bouquet : Graph := ([0], [(0, 0), (0, 0)])

private def bridgeRotation : RotationSystem bridge where
  rotate := Equiv.refl _
  sameCycle_iff := by decide

private def loopRotation : RotationSystem loopGraph where
  rotate := Dart.reversal loopGraph
  sameCycle_iff := by decide

private def digonRotation : RotationSystem digon where
  rotate := Equiv.prodCongr (Equiv.swap (0 : Fin 2) 1) (Equiv.refl Bool)
  sameCycle_iff := by decide

-- Consecutive loop ends: clockwise word 0-, 0+, 1-, 1+.
private def sphereRotation : RotationSystem bouquet where
  rotate := ((Dart.indexEquiv bouquet).trans (finRotate 4)).trans
    (Dart.indexEquiv bouquet).symm
  sameCycle_iff := by decide

-- Interlaced loop ends: clockwise word 0-, 1-, 0+, 1+.
private def torusRotation : RotationSystem bouquet where
  rotate := ((Dart.indexEquiv bouquet).trans
    (Equiv.swap (1 : Fin 4) 2 * finRotate 4 * Equiv.swap (1 : Fin 4) 2)).trans
      (Dart.indexEquiv bouquet).symm
  sameCycle_iff := by decide

private theorem genus_of_verify {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (h : RotationCertificate.verifyEuler G (RotationCertificate.ofRotation r) = true) :
    r.NumericalGenusZero := by
  have he := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation r hG)).mp h
  exact RotationCertificate.decode_ofRotation r hG ▸ he

private theorem sphereGenus : sphereRotation.NumericalGenusZero :=
  genus_of_verify sphereRotation (by decide) (by decide)

private def emptyPassages (G : Graph) : ClosedPassages G (fun _ => false) where
  count := 0
  ports :=
    { toFun := fun p => Fin.elim0 p.1
      invFun := fun d => False.elim (Bool.false_ne_true d.property)
      left_inv := fun p => Fin.elim0 p.1
      right_inv := fun d => False.elim (Bool.false_ne_true d.property) }
  vertex_eq := fun i => Fin.elim0 i

private def loopPassages {G : Graph} (e : Fin G.2.length)
    (he : (Dart.vertex (G := G) (e, false)) = Dart.vertex (e, true)) :
    ClosedPassages G (fun i => decide (i = e)) where
  count := 1
  ports :=
    { toFun := fun p => ⟨(e, p.2), by simp⟩
      invFun := fun d => (0, d.val.2)
      left_inv := by
        rintro ⟨i, b⟩
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
      right_inv := by
        rintro ⟨⟨i, b⟩, hi⟩
        have hei : i = e := of_decide_eq_true hi
        subst i
        rfl }
  vertex_eq := fun _ => he

private def firstLoop := loopPassages (G := bouquet) 0 (by decide)
private def secondLoop := loopPassages (G := bouquet) 1 (by decide)

-- A bridge cannot carry a nonzero vertex-even label; its one face has equal colors on both ends.
example (x : Fin 1 → Bool) (hx : bridge.VertexEven x) : x 0 = false := by
  have h := hx 0
  simpa [vertexParity, Dart, Fintype.sum_prod_type, Fintype.sum_bool,
    Dart.vertex, edgeEndpoint] using h

example (q : bridgeRotation.Face → Bool) : bridgeRotation.faceBoundary q 0 = false := by
  have hf : (Quotient.mk _ ((0, false) : Dart bridge) : bridgeRotation.Face) =
      Quotient.mk _ (0, true) := Quotient.sound
        (show bridgeRotation.faceNext.SameCycle (0, false) (0, true) from by decide)
  simp [RotationSystem.faceBoundary, hf]

private theorem loops_even {G : Graph}
    (h : ∀ i : Fin G.2.length, Dart.vertex (G := G) (i, false) = Dart.vertex (i, true))
    (x : Fin G.2.length → Bool) : G.VertexEven x := by
  intro v
  simp only [vertexParity, Dart, Fintype.sum_prod_type, Fintype.sum_bool]
  apply Finset.sum_eq_zero
  intro i _
  rw [h i]
  split_ifs <;> simp [BooleanRing.add_self, Bool.zero_eq_false]

-- Loop incidences cancel at their vertex, but singleton faces allow either boundary bit.
example (x : Fin 1 → Bool) : loopGraph.VertexEven x :=
  loops_even (G := loopGraph) (by decide) x

example (x : Fin 1 → Bool) : ∃ q, loopRotation.faceBoundary q = x :=
  (loopRotation.vertexEven_iff_exists_faceColors (by decide)
    (genus_of_verify loopRotation (by decide) (by decide)) x).mp
      (loops_even (G := loopGraph) (by decide) x)

example : Nat.card loopRotation.Face = 2 := by
  rw [← loopRotation.card_dual_vertices]
  decide

private def digonPassages : ClosedPassages digon (fun _ => true) where
  count := 2
  ports :=
    { toFun := fun p => ⟨(if p.2 then 1 else 0, decide (p.1 = 1)), rfl⟩
      invFun := fun d => (if d.val.2 then 1 else 0, decide (d.val.1 = 1))
      left_inv := by decide
      right_inv := by decide }
  vertex_eq := by decide

private theorem digonEven : digon.VertexEven (fun _ => true) := digonPassages.vertexEven

example : ∃ q, digonRotation.faceBoundary q = (fun _ => true) :=
  (digonRotation.vertexEven_iff_exists_faceColors (by decide)
    (genus_of_verify digonRotation (by decide) (by decide)) _).mp digonEven

-- Two edge-disjoint cycles with a common vertex, on a numerically spherical bouquet.
example : sphereRotation.intersectionParity firstLoop secondLoop = false :=
  sphereRotation.intersectionParity_eq_false (by decide) sphereGenus firstLoop secondLoop
    (by decide)

private theorem sphereDistance :
    sphereRotation.rotationDistance (1, false) (1, true) = 1 := by
  apply sphereRotation.rotationDistance_eq _ _ (by decide) 1 (by decide)
  intro k hk
  have : k = 0 := by omega
  subst k
  decide

private theorem torusDistance :
    torusRotation.rotationDistance (1, false) (1, true) = 2 := by
  apply torusRotation.rotationDistance_eq _ _ (by decide) 2 (by decide)
  intro k hk
  have : k = 0 ∨ k = 1 := by omega
  rcases this with rfl | rfl <;> decide

private theorem sphereInterval :
    sphereRotation.rotationInterval (1, false) (1, true) = {(1, true)} := by
  unfold RotationSystem.rotationInterval
  rw [sphereDistance, Finset.range_one, Finset.image_singleton]
  congr 1

private theorem torusInterval :
    torusRotation.rotationInterval (1, false) (1, true) = {(0, true), (1, true)} := by
  unfold RotationSystem.rotationInterval
  rw [torusDistance, show Finset.range 2 = {0, 1} by decide,
    Finset.image_insert, Finset.image_singleton]
  congr 1

-- Actual cyclic order, with the same darts and pairings in both examples.
example : ¬ sphereRotation.Alternates (0, false) (0, true) (1, false) (1, true) := by
  unfold RotationSystem.Alternates
  rw [sphereInterval]
  simp only [Finset.mem_singleton]
  decide

private theorem torusAlternates :
    torusRotation.Alternates (0, false) (0, true) (1, false) (1, true) := by
  unfold RotationSystem.Alternates
  rw [torusInterval]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  decide

private theorem torusOdd : torusRotation.intersectionParity firstLoop secondLoop = true := by
  classical
  unfold RotationSystem.intersectionParity
  change (∑ _ : Fin 1, ∑ _ : Fin 1,
    decide (torusRotation.Alternates (0, false) (0, true) (1, false) (1, true))) = true
  simp only [Fin.sum_univ_one]
  exact decide_eq_true_eq.mpr torusAlternates

-- The torus also refutes face-boundary exactness without its numerical genus hypothesis.
example : ¬ ∃ q, torusRotation.faceBoundary q = (fun e => decide (e = 0)) := by
  rintro ⟨q, hq⟩
  have he := torusRotation.intersectionParity_faceBoundary firstLoop secondLoop
    (by decide) q hq
  rw [torusOdd] at he
  cases he

example : ¬ torusRotation.NumericalGenusZero := by
  intro h
  have he := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation torusRotation (by decide))).mpr
      ((RotationCertificate.decode_ofRotation torusRotation (by decide)).symm ▸ h)
  have hn : RotationCertificate.verifyEuler bouquet
      (RotationCertificate.ofRotation torusRotation) ≠ true := by decide
  exact hn he

-- Empty support is honest empty passage data, for either side and even in positive genus.
example : torusRotation.intersectionParity (emptyPassages bouquet) firstLoop = false := by
  unfold RotationSystem.intersectionParity
  rfl

example : torusRotation.intersectionParity firstLoop (emptyPassages bouquet) = false := by
  unfold RotationSystem.intersectionParity
  exact Finset.sum_eq_zero (fun (j : Fin 0) _ => Fin.elim0 j)

-- Degree eight, with two visits per system and a self-crossing pairing of the first support.
private abbrev fourLoops : Graph := ([0], [(0, 0), (0, 0), (0, 0), (0, 0)])

private def degreeEightRotation : RotationSystem fourLoops where
  rotate := ((Dart.indexEquiv fourLoops).trans (finRotate 8)).trans
    (Dart.indexEquiv fourLoops).symm
  sameCycle_iff := by decide

private def evenLoopPassages :
    ClosedPassages fourLoops (fun e => decide (e = 0 ∨ e = 2)) where
  count := 2
  ports :=
    { toFun := fun p => ⟨(if p.2 then 2 else 0, decide (p.1 = 1)), by cases p.2 <;> rfl⟩
      invFun := fun d => (if d.val.2 then 1 else 0, decide (d.val.1 = 2))
      left_inv := by decide
      right_inv := by decide }
  vertex_eq := by decide

private def oddLoopPassages :
    ClosedPassages fourLoops (fun e => decide (e = 1 ∨ e = 3)) where
  count := 2
  ports :=
    { toFun := fun p => ⟨(if p.2 then 3 else 1, decide (p.1 = 1)), by cases p.2 <;> rfl⟩
      invFun := fun d => (if d.val.2 then 1 else 0, decide (d.val.1 = 3))
      left_inv := by decide
      right_inv := by decide }
  vertex_eq := by decide

private theorem degreeEightDistance :
    degreeEightRotation.rotationDistance (1, false) (3, false) = 4 := by
  apply degreeEightRotation.rotationDistance_eq _ _ (by decide) 4 (by decide)
  intro k hk
  interval_cases k <;> decide

private theorem degreeEightInterval :
    degreeEightRotation.rotationInterval (1, false) (3, false) =
      {(1, true), (2, false), (2, true), (3, false)} := by
  unfold RotationSystem.rotationInterval
  rw [degreeEightDistance, show Finset.range 4 = {0, 1, 2, 3} by decide,
    Finset.image_insert, Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  congr 1

-- A local crossing really occurs; the second passage gives another crossing and cancels it.
example : degreeEightRotation.Alternates (0, false) (2, false) (1, false) (3, false) := by
  unfold RotationSystem.Alternates
  rw [degreeEightInterval]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  decide

example : degreeEightRotation.Alternates (0, true) (2, true) (1, false) (3, false) := by
  unfold RotationSystem.Alternates
  rw [degreeEightInterval]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  decide

-- The first system's two passages themselves alternate: self-crossing pairings are retained.
example : degreeEightRotation.Alternates (0, false) (2, false) (0, true) (2, true) := by
  have hd : degreeEightRotation.rotationDistance (0, true) (2, true) = 4 := by
    apply degreeEightRotation.rotationDistance_eq _ _ (by decide) 4 (by decide)
    intro k hk
    interval_cases k <;> decide
  have hi : degreeEightRotation.rotationInterval (0, true) (2, true) =
      {(1, false), (1, true), (2, false), (2, true)} := by
    unfold RotationSystem.rotationInterval
    rw [hd, show Finset.range 4 = {0, 1, 2, 3} by decide,
      Finset.image_insert, Finset.image_insert, Finset.image_insert, Finset.image_singleton]
    congr 1
  unfold RotationSystem.Alternates
  rw [hi]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  decide

example : degreeEightRotation.intersectionParity evenLoopPassages oddLoopPassages = false :=
  degreeEightRotation.intersectionParity_eq_false (by decide)
    (genus_of_verify degreeEightRotation (by decide) (by decide))
    evenLoopPassages oddLoopPassages (by decide)

-- Sparse disconnected components, duplicate declared vertices, and two isolated points.
private abbrev sparseGraph : Graph :=
  ([2 ^ 100, 7, 2 ^ 100, 19, 23], [(2 ^ 100, 2 ^ 100), (7, 7)])

private def sparseRotation : RotationSystem sparseGraph where
  rotate := Dart.reversal sparseGraph
  sameCycle_iff := by decide

example (x : Fin 2 → Bool) : ∃ q, sparseRotation.faceBoundary q = x :=
  (sparseRotation.vertexEven_iff_exists_faceColors (by decide)
    (genus_of_verify sparseRotation (by decide) (by decide)) x).mp
      (loops_even (G := sparseGraph) (by decide) x)

example : sparseRotation.intersectionParity
    (loopPassages (G := sparseGraph) 0 (by decide))
    (loopPassages (G := sparseGraph) 1 (by decide)) = false :=
  sparseRotation.intersectionParity_eq_false (by decide)
    (genus_of_verify sparseRotation (by decide) (by decide)) _ _ (by decide)

-- Two disjoint length-two cycles retain their parallel edge occurrences and four vertices.
private abbrev twoDigons : Graph :=
  ([0, 1, 2, 3], [(0, 1), (0, 1), (2, 3), (2, 3)])

private def twoDigonRotation : RotationSystem twoDigons where
  rotate := Equiv.prodCongr
    (Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) (Equiv.refl Bool)
  sameCycle_iff := by decide

private def leftDigonPassages : ClosedPassages twoDigons (fun e => decide (e < 2)) where
  count := 2
  ports :=
    { toFun := fun p => ⟨(if p.2 then 1 else 0, decide (p.1 = 1)), by cases p.2 <;> rfl⟩
      invFun := fun d => (if d.val.2 then 1 else 0, decide (d.val.1 = 1))
      left_inv := by decide
      right_inv := by decide }
  vertex_eq := by decide

private def rightDigonPassages : ClosedPassages twoDigons (fun e => decide (2 ≤ e)) where
  count := 2
  ports :=
    { toFun := fun p => ⟨(if p.2 then 3 else 2, decide (p.1 = 1)), by cases p.2 <;> rfl⟩
      invFun := fun d => (if d.val.2 then 1 else 0, decide (d.val.1 = 3))
      left_inv := by decide
      right_inv := by decide }
  vertex_eq := by decide

example : twoDigonRotation.intersectionParity leftDigonPassages rightDigonPassages = false :=
  twoDigonRotation.intersectionParity_eq_false (by decide)
    (genus_of_verify twoDigonRotation (by decide) (by decide)) _ _ (by decide)

private abbrev pointsGraph : Graph := ([13, 13, 2 ^ 100], [])

private def pointsRotation : RotationSystem pointsGraph where
  rotate := Equiv.refl _
  sameCycle_iff := by decide

example : pointsRotation.NumericalGenusZero :=
  genus_of_verify pointsRotation (by decide) (by decide)

example (x : Fin 0 → Bool) : ∃ q, pointsRotation.faceBoundary q = x :=
  ⟨fun _ => false, funext fun i => Fin.elim0 i⟩

private def emptyRotation : RotationSystem ([], []) where
  rotate := Equiv.refl _
  sameCycle_iff := by decide

example : emptyRotation.NumericalGenusZero :=
  genus_of_verify emptyRotation (by decide) (by decide)

example : emptyRotation.intersectionParity (emptyPassages ([], []))
    (emptyPassages ([], [])) = false :=
  emptyRotation.intersectionParity_eq_false (by decide)
    (genus_of_verify emptyRotation (by decide) (by decide)) _ _ (by decide)

end CslibFrontierTests.RotationIntersection
