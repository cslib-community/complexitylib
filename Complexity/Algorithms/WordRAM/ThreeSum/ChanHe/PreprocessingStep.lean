/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingInvariant

/-!
# Executing the next actual frontend root

The actual descriptor loads establish the complete root program's ABI. Global remaining-root
reservations derive its local arena, rather than supplying another assumed execution contract.

## Main results

* `execute_next_root`: actual loads followed by the complete native traversal, with exact output.

The native composition and resource proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)

/-- Execute the next actual descriptor and its full recursion within that root's own budget. -/
theorem execute_next_root {a : Traversal.Arena} {w U : ℕ} {l : Frontend.Layout}
    {input : List ℤ} {rs : List (ℕ × ℕ)} {s : ForestCursor} {x : Data 128}
    (ha : a.Separated) (hw : a.Ready w) (h : s.Invariant a w l U rs x)
    (hc : (Cond.lt current roots).Holds x)
    (hn : a.n = l.n + 1) (hU : a.U = 2 * U)
    (hfront : l.endpoint ≤ a.stack)
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hnd : (rs.map Prod.fst).Nodup) (hcard : rs.length ≤ l.n)
    (hvalues : ∀ z ∈ input, |z| ≤ (U : ℤ)) :
    let e := entry l U a.fuel rs s.index
    ∃ (out : List (ℕ × Node)) (y : Data 128),
      ExecWithin (w + 2) (.seq loadRoot Traversal.oneRoot) x y
        (14 + Traversal.rootTime a.fuel a.n a.m a.N) ∧
      (Traversal.Cursor.mk [] out).Invariant (rootArena a x s.nodes) w
        (s.nodes.map Prod.snd ++ e.task.output (Nat.primesLE a.m) a.Λ) y ∧
      out.map Prod.snd = s.nodes.map Prod.snd ++ e.task.output (Nat.primesLE a.m) a.Λ ∧
      (∀ p < a.stack, y.mem p = x.mem p) ∧
      ∀ i : Fin 128, 109 ≤ i.val → i ≠ address → y.regs i = x.regs i := by
  let e := entry l U a.fuel rs s.index
  let b := rootArena a x s.nodes
  have hi : s.index < l.count := by
    simpa only [Cond.holds_lt, h.current, h.roots] using hc
  obtain ⟨hceil, htable⟩ := h.root_budgets hc
  have hheap : x.regs Traversal.heap ≤ a.ceiling := by
    have := h.heapBudget
    omega
  have hstack : a.stack ≤ x.regs Traversal.heap := by
    have ht := ha.2.1
    have hg := ha.2.2.1
    have := h.floor
    omega
  have haddr : l.descriptors + 6 * s.index + 5 ≤ a.ceiling := by
    have hd := l.descriptor_before (entry_slot hi (2 : Fin 3)) l.arrays
    change l.descriptors + 2 * (3 * s.index + 2) + 2 ≤ l.endpoint at hd
    omega
  have hsum := Traversal.envelope_ge_sum a.ceiling a.n a.m a.Λ a.U a.N
  have hfit := (Signed.unsigned_fits_of_signed hw.2.2).of_le (haddr.trans (by omega))
  obtain ⟨p, hp, hloaded, hmem, hpr⟩ := loadRoot_exec x h.bounded hi h.current
    h.descriptors h.levels h.stride h.one hfit h.frontend
  have pheap : p.regs Traversal.heap = x.regs Traversal.heap := hpr _ (by decide) (by decide)
  have pcount : p.regs Traversal.outputCount = s.nodes.length :=
    (hpr _ (by decide) (by decide)).trans h.count
  have hb : b.Separated := by
    refine ⟨ha.1, ha.2.1, ?_, ha.2.2.2⟩
    have hg := ha.2.2.1
    change a.table + (s.nodes.length + Traversal.Math.work a.fuel) ≤ a.floor
    change s.nodes.length + Traversal.Math.work a.fuel ≤ a.outputCapacity at htable
    omega
  have hready : b.Ready w := rootArena_ready hw hceil
  have hinput : Traversal.RootInput b w e s.nodes p := by
    refine ⟨hp.bounded h.bounded, ?_, hloaded, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_,
      pcount, le_rfl, ?_, ?_, ?_⟩
    · exact h.controls.congr (fun i hi => hpr i (Or.inr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        omega)) (by
          intro he
          subst i
          norm_num [address] at hi))
    · rw [hmem]
      exact entry_stored hkeys h.frontend hi
    · dsimp only [b, rootArena]
      rw [hn, hU]
      exact entry_valid l U a.fuel s.index hkeys hnd hcard hvalues
    · simpa only [b, rootArena, Traversal.Arena.Bitmap, hmem] using h.bitmap
    · intro j
      apply Or.inl
      exact (entry_ends l U a.fuel rs hcard hi j).trans hfront
    · intro j
      rw [pheap]
      exact (entry_ends l U a.fuel rs hcard hi j).trans (hfront.trans hstack)
    · simpa only [b, rootArena, pheap] using h.floor
    · dsimp only [b, rootArena, e, entry]
      rw [pheap]
    · simpa only [b, rootArena, hmem] using h.output
    · simpa only [b, rootArena, pheap] using h.outputBounds
    · simpa only [b, rootArena, hmem] using h.protectedMemory
  obtain ⟨out, y, he, hfinal, hout, hprefix, hregs⟩ :=
    Traversal.root_exec e s.nodes p hb hready hinput
  refine ⟨out, y, hp.within.seq he, hfinal, hout, ?_, ?_⟩
  · intro q hq
    exact (hprefix q hq).trans (congrFun hmem q)
  · intro i hi hj
    exact (hregs i hi).trans (hpr i (Or.inr (by omega)) hj)

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
