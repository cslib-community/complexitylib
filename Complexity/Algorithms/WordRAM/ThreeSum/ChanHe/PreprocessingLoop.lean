/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingStep

/-!
# Complete native frontend-root loop

Every iteration loads the next actual descriptor, executes its complete bounded recursion and
increments the native index. Remaining-root reservations pay for every later iteration.

## Main results

* `forest_body_exec`: actual root execution preserves the global resource and output invariant.
* `forest_exec`: the entire actual outer loop emits exactly the finite frontend forest.

These composition proofs are original and use the existing charged native loop rule.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)

private theorem entries_drop_cons {l : Frontend.Layout} {U : ℕ} {rs : List (ℕ × ℕ)}
    {i : ℕ} (hi : i < l.count) :
    (entries l U rs).drop i =
      entry l U (Cslib.Algorithms.ThreeSum.ChanHe.fuel l.n) rs i ::
        (entries l U rs).drop (i + 1) := by
  have hlen : i < (entries l U rs).length := by
    simpa only [entries, List.length_map, List.length_range] using hi
  rw [List.drop_eq_getElem_cons hlen]
  simp only [entries, List.getElem_map, List.getElem_range]

/-- An actual root execution leaves enough heap and table capacity for all later roots. -/
theorem forest_body_exec {a : Traversal.Arena} {w U : ℕ} {l : Frontend.Layout}
    {input : List ℤ} {rs : List (ℕ × ℕ)} {s : ForestCursor} {x : Data 128}
    (ha : a.Separated) (hw : a.Ready w) (h : s.Invariant a w l U rs x)
    (hc : (Cond.lt current roots).Holds x)
    (hn : a.n = l.n + 1) (hU : a.U = 2 * U)
    (hf : a.fuel = Cslib.Algorithms.ThreeSum.ChanHe.fuel l.n)
    (hfront : l.endpoint ≤ a.stack)
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hnd : (rs.map Prod.fst).Nodup) (hcard : rs.length ≤ l.n)
    (hvalues : ∀ z ∈ input, |z| ≤ (U : ℤ)) :
    ∃ (s' : ForestCursor) (y : Data 128),
      ExecWithin (w + 2) body x y (Traversal.rootTime a.fuel a.n a.m a.N + 15) ∧
      s'.Invariant a w l U rs y ∧ l.count - s'.index < l.count - s.index := by
  have hi : s.index < l.count := by
    simpa only [Cond.holds_lt, h.current, h.roots] using hc
  obtain ⟨out, y, he, hy, hout, hprefix, hregs⟩ :=
    execute_next_root ha hw h hc hn hU hfront hkeys hnd hcard hvalues
  have yi : y.regs current = s.index := (hregs _ (by decide) (by decide)).trans h.current
  have yo : y.regs one = 1 := (hregs _ (by decide) (by decide)).trans h.one
  have hfit : Fits (w + 2) (s.index + 1) := (h.bounded.1 roots).of_le (by
    rw [h.roots]
    omega)
  let z := y.set current (s.index + 1)
  have hz : Exec (B := .standard) (w + 2) (.op (.bin .add current current one)) y z 1 := by
    ram_eval [z, yi, yo, hfit]
  have zreg (i : Fin 128) (hi : i ≠ current) : z.regs i = y.regs i := by
    simp only [z, Data.set_regs, Function.update_of_ne hi]
  have zouter (i : Fin 128) (hi : 109 ≤ i.val) (hc : i ≠ current) (ha : i ≠ address) :
      z.regs i = x.regs i := (zreg i hc).trans (hregs i hi ha)
  let s' : ForestCursor := ⟨s.index + 1, out⟩
  refine ⟨s', z, ?_, ?_, by dsimp only [s']; omega⟩
  · obtain ⟨t, ht, he⟩ := he
    cases he with
    | seq hload hroot =>
      exact ⟨_, by omega, hload.seq (hroot.seq hz)⟩
  · constructor
    · exact hz.bounded hy.bounded
    · exact hy.controls.congr (by
        intro i hi
        apply zreg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        intro he
        subst i
        norm_num [current] at hi)
    · exact h.frontend.frame hcard (fun p hp => hprefix p (hp.trans_le hfront))
    · exact (zouter _ (by decide) (by decide) (by decide)).trans h.descriptors
    · exact (zouter _ (by decide) (by decide) (by decide)).trans h.roots
    · rfl
    · exact (zouter _ (by decide) (by decide) (by decide)).trans h.levels
    · exact (zouter _ (by decide) (by decide) (by decide)).trans h.stride
    · exact (zouter _ (by decide) (by decide) (by decide)).trans h.one
    · dsimp only [s']; omega
    · exact hy.bitmap
    · simpa only [rootArena, zreg Traversal.heap (by decide)] using hy.floor
    · have hh : y.regs Traversal.heap ≤ x.regs Traversal.heap +
          Traversal.Math.work a.fuel * Traversal.allocationSize a.n a.m a.N := by
        simpa only [rootArena, Traversal.Cursor.work, List.map_nil,
          Traversal.Math.potential, List.sum_nil, Nat.zero_mul, Nat.add_zero] using hy.heapBudget
      have hg := h.heapBudget
      have hrem : l.count - s.index = (l.count - (s.index + 1)) + 1 := by omega
      rw [hrem, Nat.add_mul, Nat.one_mul] at hg
      change z.regs Traversal.heap + (l.count - (s.index + 1)) * _ ≤ _
      rw [zreg _ (by decide)]
      omega
    · exact (zreg _ (by decide)).trans hy.count
    · have ht : out.length ≤ s.nodes.length + Traversal.Math.work a.fuel := by
        simpa only [rootArena, Traversal.Cursor.work, List.map_nil,
          Traversal.Math.potential, List.sum_nil, Nat.add_zero] using hy.tableBudget
      have hg := h.tableBudget
      have hrem : l.count - s.index = (l.count - (s.index + 1)) + 1 := by omega
      rw [hrem, Nat.add_mul, Nat.one_mul] at hg
      change out.length + (l.count - (s.index + 1)) * _ ≤ _
      omega
    · exact hy.output
    · simpa only [s', rootArena, zreg Traversal.heap (by decide)] using hy.outputBounds
    · change out.map Prod.snd ++ _ = _
      rw [hout, List.append_assoc]
      have hm := h.exactOutput
      rw [entries_drop_cons hi, List.map_cons, Traversal.Math.output,
        List.flatMap_cons] at hm
      rw [hf]
      exact hm
    · intro p hp
      exact (hprefix p hp).trans (h.protectedMemory p hp)

/-- Execute every native frontend root with exact finite output and all loop control charged. -/
theorem forest_exec {a : Traversal.Arena} {w U : ℕ} {l : Frontend.Layout}
    {input : List ℤ} {rs : List (ℕ × ℕ)} {s : ForestCursor} {x : Data 128}
    (ha : a.Separated) (hw : a.Ready w) (h : s.Invariant a w l U rs x)
    (hn : a.n = l.n + 1) (hU : a.U = 2 * U)
    (hf : a.fuel = Cslib.Algorithms.ThreeSum.ChanHe.fuel l.n)
    (hfront : l.endpoint ≤ a.stack)
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hnd : (rs.map Prod.fst).Nodup) (hcard : rs.length ≤ l.n)
    (hvalues : ∀ z ∈ input, |z| ≤ (U : ℤ)) :
    ∃ (s' : ForestCursor) (y : Data 128),
      ExecWithin (w + 2) forest x y
        ((l.count - s.index) * (Traversal.rootTime a.fuel a.n a.m a.N + 17) + 2) ∧
      s'.Invariant a w l U rs y ∧ s'.index = l.count ∧
      s'.nodes.map Prod.snd = Traversal.Math.output (Nat.primesLE a.m) a.Λ
        ((entries l U rs).map Traversal.Entry.task) := by
  obtain ⟨s', y, he, hy, hc⟩ := ExecWithin.loop_invariant_state
    (fun (s : ForestCursor) y => s.Invariant a w l U rs y)
    (fun s => l.count - s.index)
    (fun s x hi hc => forest_body_exec ha hw hi hc hn hU hf hfront hkeys hnd hcard hvalues) h
  have hend : s'.index = l.count := by
    have hge : l.count ≤ s'.index := by
      simpa only [Cond.holds_lt, hy.current, hy.roots, not_lt] using hc
    exact hy.index_le.antisymm hge
  refine ⟨s', y, he, hy, hend, ?_⟩
  have hlen : (entries l U rs).length = l.count := by
    simp only [entries, List.length_map, List.length_range]
  simpa only [hend, ← hlen, List.drop_length, List.map_nil, Traversal.Math.output,
    List.flatMap_nil, List.append_nil] using hy.exactOutput

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
