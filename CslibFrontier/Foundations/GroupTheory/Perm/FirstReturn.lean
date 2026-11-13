/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate (Mathlib Dynamics/PeriodicPts)

public import CslibFrontier.Init
public import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.List.Basic

/-!
# A bounded first-return scan lists one complete periodic orbit

The scan's clock may exceed the orbit length. Stopping just before the first return
produces the literal directed orbit word, retaining a singleton for a fixed point.
The bound is independent of the representation of the orbit's elements.
-/

public section

namespace Function

variable {α : Type*} [DecidableEq α]

/-- A bounded first-return scan is exactly one directed orbit period, including period one.
No assumption is made about the behavior of the function outside the selected orbit. -/
theorem firstReturnWord_eq (f : α → α) (a : α) (bound : ℕ)
    (hpos : 0 < minimalPeriod f a) (hbound : minimalPeriod f a ≤ bound) :
    let following := (List.range bound).map fun k => f^[k + 1] a
    a :: following.take (following.idxOf a) =
      (List.range (minimalPeriod f a)).map fun k => f^[k] a := by
  let p := minimalPeriod f a
  let following := (List.range bound).map fun k => f^[k + 1] a
  have hi : p - 1 < following.length := by
    simp only [following, List.length_map, List.length_range]
    omega
  have hidx : following.idxOf a = p - 1 := by
    change following.findIdx (fun b => b == a) = p - 1
    apply (List.findIdx_eq hi).mpr
    constructor
    · simp only [following, List.getElem_map, List.getElem_range, beq_iff_eq]
      rw [Nat.sub_add_cancel hpos]
      exact iterate_minimalPeriod
    · intro j hj
      simp only [following, List.getElem_map, List.getElem_range, beq_eq_false_iff_ne]
      intro he
      have hle : p ≤ j + 1 := IsPeriodicPt.minimalPeriod_le (Nat.succ_pos j) he
      omega
  change a :: following.take (following.idxOf a) = _
  rw [hidx]
  apply List.ext_getElem
  · simp only [List.length_cons, List.length_take, List.length_map, List.length_range,
      following]
    omega
  · intro i hi hj
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.getElem_cons_succ, List.getElem_take, following, List.getElem_map,
        List.getElem_range]

end Function
