/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem

/-! Indexed-end and face tests for empty graphs, bridges, loops and parallel edges. -/

open Cslib.Complexity Cslib.Complexity.Graph

private abbrev bridge : Graph := ⟨[0, 1], [(0, 1)]⟩
private abbrev loopGraph : Graph := ⟨[0], [(0, 0)]⟩

private def bridgeRotation : RotationSystem bridge where
  rotate := Equiv.refl _
  sameCycle_iff := by decide

private def loopRotation : RotationSystem loopGraph where
  rotate := Dart.reversal loopGraph
  sameCycle_iff := by decide

example : bridgeRotation.faceNext (0, false) = (0, true) := by decide

example : Dart.vertex (G := loopGraph) (0, false) = Dart.vertex (G := loopGraph) (0, true) := by
  decide

example : ((0, false) : Dart loopGraph) ≠ ((0, true) : Dart loopGraph) := by decide

example : loopRotation.faceNext = Equiv.refl _ := by decide

-- Both singleton face orbits survive; a nontrivial-cycle-only representation would lose them.
example : (Quotient.mk _ (0, false) : loopRotation.Face) ≠ Quotient.mk _ (0, true) := by
  intro h
  have hc := Quotient.exact h
  have he : loopRotation.faceNext = Equiv.refl _ := by decide
  rw [he] at hc
  have hd := Equiv.Perm.sameCycle_one.mp hc
  exact Bool.false_ne_true (congrArg Prod.snd hd)

example : (Quotient.mk _ (0, false) : bridgeRotation.Face) = Quotient.mk _ (0, true) := by
  apply Quotient.sound
  change bridgeRotation.faceNext.SameCycle (0, false) (0, true)
  decide

example : ((⟨0, by decide⟩, false) : Dart ⟨[0, 1], [(0, 1), (0, 1)]⟩) ≠
    (⟨1, by decide⟩, false) := by decide

example : Fintype.card (Dart ⟨[], []⟩) = 0 := by decide

example : RotationSystem ⟨[], []⟩ where
  rotate := Equiv.refl _
  sameCycle_iff := by intro d; exact d.1.elim0
