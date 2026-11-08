/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Lifting
import Mathlib.Tactic.FinCases

/-! Canonical dual data and actual face multiplicities for bridges, loops and parallel digons. -/

open Cslib Cslib.Complexity Cslib.Complexity.Graph

private abbrev bridge : Graph := ([0, 1], [(0, 1)])
private abbrev loopGraph : Graph := ([0], [(0, 0)])
private abbrev digon : Graph := ([0, 1], [(0, 1), (0, 1)])
private abbrev torusBouquet : Graph := ([0], [(0, 0), (0, 0)])

private def bridgeRotation : RotationSystem bridge where
  rotate := Equiv.refl _
  sameCycle_iff := by decide

private def loopRotation : RotationSystem loopGraph where
  rotate := Dart.reversal loopGraph
  sameCycle_iff := by decide

private def digonRotation : RotationSystem digon where
  rotate := Equiv.prodCongr (Equiv.swap (0 : Fin 2) 1) (Equiv.refl Bool)
  sameCycle_iff := by decide

private def torusRotation : RotationSystem torusBouquet where
  rotate := ((Dart.indexEquiv torusBouquet).trans
    (Equiv.swap (1 : Fin 4) 2 * finRotate 4 * Equiv.swap (1 : Fin 4) 2)).trans
      (Dart.indexEquiv torusBouquet).symm
  sameCycle_iff := by decide

-- The bridge's single source face becomes a loop, retaining its two different darts.
example : bridgeRotation.dualGraph = ([0], [(0, 0)]) := by decide

example : bridgeRotation.dualRotation.faceNext
    (bridgeRotation.dualDartEquiv (0, false)) =
      bridgeRotation.dualDartEquiv (0, false) := by decide

example : bridgeRotation.dualRotation.faceNext
    (bridgeRotation.dualDartEquiv (0, true)) =
      bridgeRotation.dualDartEquiv (0, true) := by decide

-- A sphere loop has two singleton source faces; its dual is an ordinary edge.
example : loopRotation.dualGraph = ([0, 1], [(0, 1)]) := by decide

example : loopRotation.dualRotation.rotate
    (loopRotation.dualDartEquiv (0, false)) =
      loopRotation.dualDartEquiv (0, false) := by decide

-- Distinct parallel edge positions survive dualization.
example : digonRotation.dualGraph.2 = [(0, 1), (1, 0)] := by decide

example : digonRotation.faceId (0, false) = digonRotation.faceId (1, true) := by decide

example : digonRotation.faceId (0, false) ≠ digonRotation.faceId (1, false) := by decide

-- All four torus darts lie in one face, despite two different listed loop positions.
example : torusRotation.faceId (0, false) = torusRotation.faceId (1, true) := by decide

example : ¬ torusRotation.NumericalGenusZero := by
  intro h
  have hG : ∀ v ∈ torusBouquet.incidenceVertices, v ∈ torusBouquet.1 := by decide
  have hd := RotationCertificate.decode_ofRotation torusRotation hG
  have he := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation torusRotation hG)).mpr (hd.symm ▸ h)
  have hn : RotationCertificate.verifyEuler torusBouquet
      (RotationCertificate.ofRotation torusRotation) ≠ true := by decide
  exact hn he

-- Every ordinary vertex assignment telescopes, even in the positive-genus example.
example (spin : ℕ → Bool) : torusRotation.FaceEven (torusBouquet.edgeGradient spin) :=
  torusRotation.faceEven_edgeGradient spin

example (spin : ℕ → Bool) : bridgeRotation.FaceEven (bridge.edgeGradient spin) :=
  bridgeRotation.faceEven_edgeGradient spin

private theorem bridgeGenus : bridgeRotation.NumericalGenusZero := by
  have hG : ∀ v ∈ bridge.incidenceVertices, v ∈ bridge.1 := by decide
  have h := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation bridgeRotation hG)).mp (by decide)
  exact RotationCertificate.decode_ofRotation bridgeRotation hG ▸ h

-- Symbolic lifting of any bridge label: its one face traverses the edge twice.
example (x : Fin 1 → Bool) : ∃ spin : ℕ → Bool, bridge.edgeGradient spin = x := by
  apply (bridgeRotation.faceEven_iff_exists_vertexSpins (by decide) bridgeGenus x).mp
  apply (bridgeRotation.faceEven_iff_dart x).mpr
  intro d
  have hc : ∀ d e : Dart bridge, bridgeRotation.faceNext.SameCycle d e := by decide
  rw [bridgeRotation.faceParity_mk]
  simp only [hc, Finset.filter_true, parityOn_eq_sum]
  simp only [Dart, Fintype.sum_prod_type, Fintype.sum_bool, BooleanRing.add_self,
    Finset.sum_const_zero]
  exact Bool.zero_eq_false

-- Numerical Euler is preserved by the actual dual, including the loop/bridge interchange.
example : bridgeRotation.dualRotation.NumericalGenusZero :=
  (bridgeRotation.numericalGenusZero_dual_iff (by decide)).mpr bridgeGenus

-- A torus bouquet has one face; every assignment has even dart multiplicity there.
example (x : Fin 2 → Bool) : torusRotation.FaceEven x := by
  apply (torusRotation.faceEven_iff_dart x).mpr
  intro d
  have hc : ∀ d e : Dart torusBouquet, torusRotation.faceNext.SameCycle d e := by decide
  rw [torusRotation.faceParity_mk]
  simp only [hc, Finset.filter_true, parityOn_eq_sum]
  simp only [Dart, Fintype.sum_prod_type, Fintype.sum_bool, BooleanRing.add_self,
    Finset.sum_const_zero]
  exact Bool.zero_eq_false

example : ¬ ∃ spin : ℕ → Bool,
    torusBouquet.edgeGradient spin = (fun i => decide (i = 0)) := by
  rintro ⟨spin, h⟩
  have he := congrFun h 0
  have hz : torusBouquet.edgeGradient spin 0 = false := by
    simp [edgeGradient, Dart.vertex, edgeEndpoint]
  exact Bool.false_ne_true (by simpa only [hz, decide_true] using he)

private abbrev pointGraph : Graph := ([2 ^ 100, 2 ^ 100, 7], [])

private def pointRotation : RotationSystem pointGraph where
  rotate := Equiv.refl _
  sameCycle_iff := by intro d; exact d.1.elim0

example : pointRotation.dualGraph = ([], []) := by decide

-- Sparse labels and duplicate declared point records require no finite instance on Nat.
example (x : Fin 0 → Bool) : ∃ spin : ℕ → Bool, pointGraph.edgeGradient spin = x := by
  have hG : ∀ v ∈ pointGraph.incidenceVertices, v ∈ pointGraph.1 := by decide
  have hgenus : pointRotation.NumericalGenusZero := by
    intro root _
    have hn : ¬ ∃ d : Dart pointGraph, d.vertex = root := by
      rintro ⟨d, -⟩
      exact d.1.elim0
    simp only [hn, ite_false]
  apply (pointRotation.faceEven_iff_exists_vertexSpins hG hgenus x).mp
  intro f
  induction f using Quotient.inductionOn with | _ d => exact d.1.elim0

-- A singleton loop face counts its edge once, rather than discarding a fixed point.
example (x : Fin 1 → Bool) :
    loopRotation.faceParity x (Quotient.mk _ (0, false)) = x 0 := by
  rw [loopRotation.faceParity_mk]
  have hf : (Finset.univ.filter fun e : Dart loopGraph =>
      loopRotation.faceNext.SameCycle (0, false) e) = {(0, false)} := by decide
  rw [hf, parityOn_singleton]

-- A digon face counts the two different parallel positions once each.
example (x : Fin 2 → Bool) :
    digonRotation.faceParity x (Quotient.mk _ (0, false)) = (x 0 ^^ x 1) := by
  rw [digonRotation.faceParity_mk]
  have hf : (Finset.univ.filter fun e : Dart digon =>
      digonRotation.faceNext.SameCycle (0, false) e) = {(0, false), (1, true)} := by decide
  rw [hf, parityOn_eq_sum, Finset.sum_pair (by decide)]
  rfl

private abbrev sparseMixed : Graph :=
  ([2 ^ 100, 2 ^ 100 + 7, 2 ^ 100 + 7, 5, 900000], [(2 ^ 100, 2 ^ 100 + 7), (5, 5)])

private def sparseMixedRotation : RotationSystem sparseMixed where
  rotate :=
    { toFun := fun (i, b) => (i, if i = 0 then b else !b)
      invFun := fun (i, b) => (i, if i = 0 then b else !b)
      left_inv := by rintro ⟨i, b⟩; fin_cases i <;> cases b <;> rfl
      right_inv := by rintro ⟨i, b⟩; fin_cases i <;> cases b <;> rfl }
  sameCycle_iff := by decide

-- Disconnected bridge, loop and point components; duplicate and very large vertex names.
example (x : Fin 2 → Bool) (hx : x 1 = false) :
    ∃ spin : ℕ → Bool, sparseMixed.edgeGradient spin = x := by
  have hG : ∀ v ∈ sparseMixed.incidenceVertices, v ∈ sparseMixed.1 := by decide
  have hgenus := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation sparseMixedRotation hG)).mp (by decide)
  have hgenus' : sparseMixedRotation.NumericalGenusZero :=
    RotationCertificate.decode_ofRotation sparseMixedRotation hG ▸ hgenus
  let seed (v : ℕ) := if v = 2 ^ 100 + 7 then x 0 else false
  have hseed : sparseMixed.edgeGradient seed = x := by
    funext i
    fin_cases i <;> simp [edgeGradient, Dart.vertex, edgeEndpoint, seed, hx]
  apply (sparseMixedRotation.faceEven_iff_exists_vertexSpins hG hgenus' x).mp
  rw [← hseed]
  exact sparseMixedRotation.faceEven_edgeGradient seed

private abbrev undeclaredBouquet : Graph := ([], [(0, 0), (0, 0)])

private def undeclaredRotation : RotationSystem undeclaredBouquet where
  rotate := torusRotation.rotate
  sameCycle_iff := torusRotation.sameCycle_iff

-- The endpoint guard is essential: undeclared roots make the Euler predicate vacuous.
example : undeclaredRotation.NumericalGenusZero := by
  intro _ h
  cases h

example : ¬ (∀ v ∈ undeclaredBouquet.incidenceVertices, v ∈ undeclaredBouquet.1) := by decide
