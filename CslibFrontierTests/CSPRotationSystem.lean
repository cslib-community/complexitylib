/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem

/-! Ordered constraint ports retain direction, cyclic wraparound and repeated positions. -/

open Cslib.Complexity Cslib.Logic.PL
open Cslib.Complexity.CSP

private abbrev star : CSP Unit ℕ := [((), [10, 20, 30])]

private def starRotate : Equiv.Perm (Graph.Dart (incidenceGraph star)) where
  toFun d := (if d.2 then finRotate _ d.1 else d.1, d.2)
  invFun d := (if d.2 then (finRotate _).symm d.1 else d.1, d.2)
  left_inv := by
    rintro ⟨i, b⟩
    cases b
    · rfl
    · exact Prod.ext ((finRotate _).symm_apply_apply i) rfl
  right_inv := by
    rintro ⟨i, b⟩
    cases b
    · rfl
    · exact Prod.ext ((finRotate _).apply_symm_apply i) rfl

private def starRotation : Graph.RotationSystem (incidenceGraph star) where
  rotate := starRotate
  sameCycle_iff := by decide

example : RespectsArgumentOrder starRotation := by
  unfold RespectsArgumentOrder
  decide

-- Mirroring the rotation reverses the three argument ports, which is a different order.
example : ¬ RespectsArgumentOrder starRotation.mirror := by
  unfold RespectsArgumentOrder
  decide

example : argumentSuccessor (F := star) ⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩ =
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ := by decide

private abbrev repeated : CSP Unit ℕ := [((), [7, 7, 9])]

example : CSP.Occurrence.var (F := repeated) ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ =
    (argumentSuccessor (F := repeated) ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩).var := by decide

example : incidenceDart (F := repeated) ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ true ≠
    incidenceDart (F := repeated) ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩ true := by decide

example (r : Graph.RotationSystem (incidenceGraph ([((), [])] : CSP Unit ℕ))) :
    RespectsArgumentOrder r := by
  rintro ⟨i, j⟩
  have hi : i.val = 0 := by
    have h := i.isLt
    change i.val < 1 at h
    omega
  have he : i = ⟨0, by decide⟩ := Fin.ext hi
  cases he
  exact j.elim0
