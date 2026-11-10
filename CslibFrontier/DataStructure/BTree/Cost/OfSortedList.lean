/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.OfSortedList
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Node-building cost of B-tree bulk loading

`ofSortedListT` instantiates `ofSortedListM` at `TimeM ℕ` with `visit := tick 1`, so the time of
a run is the number of nodes it builds; nothing else is charged.

A round cuts the `r` triples of a level into `ss.length + 1` groups and builds one node per
group, and the next level keeps one triple per cut, `ss.length` of them. Since every group holds
a triple and the triples between groups are distinct from them, `2 * ss.length < r`
(`IsGrouping.two_mul_length_lt`), so a round and everything above it build at most `r` nodes.

## Main definitions

* `packT`, `buildT`, `ofSortedListT`: the instrumented round, rounds and bulk loading.

## Main results

* `ret_ofSortedListT`: the value of `ofSortedListT` is `ofSortedList`.
* `time_packT_le`, `time_buildT_le`: the nodes built by a round and by all rounds.
* `time_ofSortedListT`: bulk loading `n` entries builds at most `n` nodes, for every `t`.

Ported from `cslib-community/EpsilonEridani` at commit `1966ab476`:
[EpsilonEridani/Algorithms/Lean/BTree/Cost/OfSortedList.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Algorithms/Lean/BTree/Cost/OfSortedList.lean).
-/

public section

open Cslib.Algorithms.Lean (TimeM)
open Cslib.Algorithms.Lean.TimeM (tick)

namespace Cslib.DataStructure.BTree

section NodeVisits

variable {α β : Type} {t : ℕ}

/-- Cutting a level, charging one tick per node built. -/
def packT (first : BTree α β) (rest : List (Triple α β)) (ss : List ℕ) :
    TimeM ℕ (BTree α β × List (Triple α β)) :=
  packM (tick 1) first rest ss

/-- `packT` is `packM` with one tick per node built. -/
theorem packT_def (first : BTree α β) (rest : List (Triple α β)) (ss : List ℕ) :
    packT first rest ss = packM (tick 1) first rest ss := (rfl)

/-- Rounds of bulk loading, charging one tick per node built. -/
def buildT (t fuel : ℕ) (first : BTree α β) (rest : List (Triple α β)) :
    TimeM ℕ (BTree α β) :=
  buildM t (tick 1) fuel first rest

/-- `buildT` is `buildM` with one tick per node built. -/
theorem buildT_def (fuel : ℕ) (first : BTree α β) (rest : List (Triple α β)) :
    buildT t fuel first rest = buildM t (tick 1) fuel first rest := (rfl)

/-- Bulk loading, charging one tick per node built. -/
def ofSortedListT (t : ℕ) (l : List (α × β)) : TimeM ℕ (BTree α β) :=
  ofSortedListM t (tick 1) l

/-- `ofSortedListT` is `ofSortedListM` with one tick per node built. -/
theorem ofSortedListT_def (l : List (α × β)) :
    ofSortedListT t l = ofSortedListM t (tick 1) l := (rfl)

/-- The value of `packT` is `pack`. -/
@[simp] theorem ret_packT (first : BTree α β) (rest : List (Triple α β)) (ss : List ℕ) :
    (packT first rest ss).ret = pack first rest ss := by
  simpa only [pack_def, packT, Id.run_pure, TimeM.ret_tick] using
    (Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_packM (tick 1) first rest ss))

/-- The value of `buildT` is `build`. -/
@[simp] theorem ret_buildT (fuel : ℕ) (first : BTree α β) (rest : List (Triple α β)) :
    (buildT t fuel first rest).ret = build t fuel first rest := by
  simpa only [build_def, buildT, Id.run_pure, TimeM.ret_tick] using
    (Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_buildM t (tick 1) fuel first rest))

/-- The value of `ofSortedListT` is `ofSortedList`. -/
@[simp] theorem ret_ofSortedListT (l : List (α × β)) :
    (ofSortedListT t l).ret = ofSortedList t l := by
  simpa only [ofSortedList_def, ofSortedListT, Id.run_pure, TimeM.ret_tick] using
    (Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_ofSortedListM t (tick 1) l))

/-- Cutting a level by `ss` builds at most one node per group, `ss.length + 1`. -/
theorem time_packT_le (first : BTree α β) (rest : List (Triple α β)) (ss : List ℕ) :
    (packT first rest ss).time ≤ ss.length + 1 := by
  induction ss generalizing first rest with
  | nil => simp [packT, packM_nil]
  | cons s ss ih =>
    simp only [packT, packM_cons] at ih ⊢
    split
    · simp
    · simpa [Nat.add_comm 1] using ih _ _

/-- At minimum degree at least `2`, the rounds of bulk loading build at most as many nodes as
the level has triples. -/
theorem time_buildT_le (ht : 2 ≤ t) (fuel : ℕ) (first : BTree α β)
    (rest : List (Triple α β)) : (buildT t fuel first rest).time ≤ rest.length := by
  induction fuel generalizing first rest with
  | zero =>
    rcases rest with _ | ⟨e, es⟩
    · simp [buildT_def]
    · rw [buildT_def, buildM_cons]
      split <;> simp
  | succ fuel ih =>
    rcases rest with _ | ⟨e, es⟩
    · simp [buildT_def]
    · rw [buildT_def, buildM_cons]
      split
      · simp
      · generalize hss : groupSizes t (e :: es).length (e :: es).length = ss
        have hg : IsGrouping t (e :: es).length ss :=
          hss ▸ isGrouping_groupSizes (by omega) le_rfl
        have h₁ := time_packT_le first (e :: es) ss
        have h₂ := ih (pack first (e :: es) ss).1 (pack first (e :: es) ss).2
        rw [length_pack hg rfl] at h₂
        have h₃ := hg.two_mul_length_lt ht
        have hr : (packM (tick 1) first (e :: es) ss).ret = pack first (e :: es) ss :=
          ret_packT first (e :: es) ss
        rw [packT_def] at h₁
        rw [buildT_def] at h₂
        simp only [TimeM.time_bind, hr]
        omega

/-- Bulk loading the empty list builds no node. -/
@[simp] theorem time_ofSortedListT_nil : (ofSortedListT t ([] : List (α × β))).time = 0 := by
  simp [ofSortedListT_def]

/-- Bulk loading `n` entries builds at most `n` nodes, for every `t`. -/
theorem time_ofSortedListT (l : List (α × β)) : (ofSortedListT t l).time ≤ l.length := by
  simpa [ofSortedListT, ofSortedListM_def, buildT_def] using
    time_buildT_le (Nat.le_max_right t 2) l.length .leaf (l.map fun p => (p.1, p.2, .leaf))

end NodeVisits

end Cslib.DataStructure.BTree
