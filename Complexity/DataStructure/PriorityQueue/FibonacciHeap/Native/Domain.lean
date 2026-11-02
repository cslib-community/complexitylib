/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Native.Update

/-!
# Source forest domains for native Fibonacci updates

The existing forest and record proofs supply the pointer and exact-subtraction conditions
needed by native source blocks. These are consequences of the existing `Cascading` invariant,
not a replacement heap model or a complete native decrease-key theorem.

## Main results

* `cutSafe_of_cascading`: the existing forest invariant and allocated layout supply the native
  cut's entry and actual intermediate-state domains.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

/-- The source forest conditions supply the intermediate root-list and mark/count conditions
needed to move an unlinked child to the roots. In particular, the subtraction premise follows
from the original marked-set interpretation of the count. -/
private theorem wp_unlink_rootFields {n K w : ℕ} {s : IndexedMinPQ.State n} {g : Cell → ℕ}
    {v m cur p : Fin n} {pending : Option (Fin n)} {ts : List (FHTree n)}
    (h : Cascading n K s (view n g) v m pending ts)
    (hcur : cur ∈ forestNodes ts) (hpar : (view n g).par cur = p.val + 1)
    (hfit : Fits w n) :
    Record.wp (Cell.ok n) w (unlink cur p) (fun _ g' _ =>
      (view n g').minRoot = m.val + 1 ∧
        (∃ r : Fin n, (view n g').right m = r.val) ∧
        (view n g').mark cur ≤ (view n g').numMarked) g := by
  obtain ⟨T, hT, hdesc⟩ := h.desc_of_par hcur (by omega)
  obtain ⟨_, _, _, hin, hmark, _, _⟩ := exists_parent_info (h.valid T hT).1 hdesc hpar
  have hmark_count : (view n g).mark cur ≤ (view n g).numMarked := by
    rw [h.numMarked]
    by_cases hm : (view n g).mark cur = 0
    · simp [hm]
    · have hpos : 0 < markedCount (view n g) :=
        Finset.card_pos.mpr ⟨cur, by simp [markedSet, hin, hm]⟩
      omega
  obtain ⟨rtail, hcirc, hperm⟩ := h.roots
  obtain ⟨hdeg, htwo, hdeg_le, hroots, _, _⟩ := h.cut_pre hperm hcur hpar
  refine wp_unlink hdeg htwo hdeg_le hfit fun g' _ _ left right child hunlink hview => ?_
  obtain ⟨r, hr⟩ := exists_right_min_of_unlink htwo hcirc hroots hunlink
  rw [hview]
  exact ⟨h.minRoot, ⟨r, hr⟩, hmark_count⟩

/-- The original `Cascading` forest supplies every cut domain, including the mark/count
subtraction after the actual unlink run. The lower refinement transports the source record
facts to literal memory addresses; the full heap invariant need not hold between the blocks. -/
theorem cutSafe_of_cascading {n K w base : ℕ} {s : IndexedMinPQ.State n}
    {mem : Memory.State} {v m cur p : Fin n} {pending : Option (Fin n)} {ts : List (FHTree n)}
    (hfit : Fits w (base + (9 * n + 5))) (halloc : (layout n base).Inv mem)
    (h : Cascading n K s (view n ((layout n base).abs mem)) v m pending ts)
    (hcur : cur ∈ forestNodes ts)
    (hpar : (view n ((layout n base).abs mem)).par cur = p.val + 1) :
    cutSafe w ![n, base, cur.val, p.val] mem := by
  have hn : Fits w n := hfit.of_le (by omega)
  have hw := wp_unlink_rootFields h hcur hpar hn
  obtain ⟨hv, hfields⟩ := (Record.wp_iff _ _ _).mp hw
  obtain ⟨_, _, habs, _⟩ :=
    (Record.refinement (layout n base) w).simulates_client (unlink cur p) halloc hv
  dsimp only [Record.refinement] at habs
  change (layout n base).abs ((Memory.spec w).clientState mem
      (DataStructure.link (E := Memory.spec w) ((layout n base).methods w) (unlink cur p))) =
    (Record.spec (Cell.ok n) w).clientState ((layout n base).abs mem) (unlink cur p) at habs
  rw [Realization.clientState_width w] at habs
  have hprogram : DataStructure.link (E := Memory.spec w) ((layout n base).methods w)
      (unlink cur p) = DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0)
        (unlink cur p) := by
    have hmethods : ((layout n base).methods w :
        (o : Record.Op Cell) → Memory.Prog (Record.Op.Result o)) =
        ((layout n base).methods 0 : (o : Record.Op Cell) → Memory.Prog (Record.Op.Result o)) := by
      funext o
      cases o <;> rfl
    exact congrArg (fun methods => PFunctor.FreeM.liftM methods (unlink cur p)) hmethods
  rw [hprogram] at habs
  rw [← habs] at hfields
  let next := (Memory.spec 0).clientState mem
    (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) (unlink cur p))
  have hmin : next.mem (base + 9 * n + 1) = m.val + 1 := by
    simpa only [view, Record.Layout.abs, Cell.ok, ite_true, layout, next] using hfields.1
  obtain ⟨r, hr⟩ := hfields.2.1
  have hright : next.mem (base + 4 * n + m.val) = r.val := by
    simpa only [view, Record.Layout.abs, Cell.ok, m.isLt, ite_true, layout, next] using hr
  have hmark : next.mem (base + 6 * n + cur.val) ≤ next.mem (base + 9 * n + 3) := by
    simpa only [view, Record.Layout.abs, Cell.ok, cur.isLt, ite_true, layout, next]
      using hfields.2.2
  obtain ⟨_, _, hperm⟩ := h.roots
  have hpos := (h.cut_pre hperm hcur hpar).1
  have hdeg : 1 ≤ mem.mem (base + 5 * n + p.val) := by
    simpa only [view, Record.Layout.abs, Cell.ok, p.isLt, ite_true, layout] using hpos
  change Fits w (base + (9 * n + 5)) ∧ cur.val < n ∧ p.val < n ∧
    1 ≤ mem.mem (base + 5 * n + p.val) ∧ _
  refine ⟨hfit, cur.isLt, p.isLt, hdeg, ?_⟩
  change 1 ≤ next.mem (base + 9 * n + 1) ∧ next.mem (base + 9 * n + 1) ≤ n ∧
    next.mem (base + 4 * n + (next.mem (base + 9 * n + 1) - 1)) < n ∧
    next.mem (base + 6 * n + cur.val) ≤ next.mem (base + 9 * n + 3)
  rw [hmin, Nat.add_sub_cancel, hright]
  exact ⟨by omega, by have := m.isLt; omega, r.isLt, hmark⟩

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
