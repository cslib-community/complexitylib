/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingLoad
import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Frame

/-!
# Internal forest invariant and execution proof

Each native iteration loads the next frontend descriptor and executes its complete recursion.
The invariant reserves heap and pointer cells for every remaining root, so a root cannot consume
another root's budget. The private loop proof charges all control instructions and establishes
exact finite forest output. These native composition and resource proofs are original.
-/

-- Proof-only companion; PreprocessingExecute imports these helpers with `import all`.
set_option linter.privateModule false

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)

/-- Restrict a root call to its own heap and pointer-table allowance. All addresses stay fixed. -/
private def rootArena (a : Traversal.Arena) (x : Data 128)
    (ns : List (ℕ × Node)) : Traversal.Arena :=
  { a with
    ceiling := x.regs Traversal.heap +
      Traversal.Math.work a.fuel * Traversal.allocationSize a.n a.m a.N
    outputCapacity := ns.length + Traversal.Math.work a.fuel }

/-- Monotonicity of the existing polynomial envelope derives every root's actual local fit. -/
private theorem rootArena_ready {a : Traversal.Arena} {w : ℕ} {x : Data 128}
    {ns : List (ℕ × Node)} (hw : a.Ready w)
    (hh : (rootArena a x ns).ceiling ≤ a.ceiling) : (rootArena a x ns).Ready w := by
  refine ⟨hw.1, hw.2.1, ?_⟩
  apply GenericRAM.Signed.Fits.of_natAbs_le hw.2.2
  simp only [Int.natAbs_natCast]
  dsimp only [Traversal.envelope]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [rootArena] at *; omega) 4)

/-- Mathematical proof state of the native outer descriptor loop. -/
private structure ForestCursor where
  /-- Number of root descriptors already executed. -/
  index : ℕ
  /-- Actual native pointer and existing-node pairs already emitted. -/
  nodes : List (ℕ × Node)

/-- Exact frontend output, native controller registers and all remaining-root reservations. -/
private structure ForestCursor.Invariant (a : Traversal.Arena) (w : ℕ) (l : Frontend.Layout)
    (U : ℕ) (rs : List (ℕ × ℕ)) (s : ForestCursor) (x : Data 128) : Prop where
  /-- Every actual word fits. -/
  bounded : x.Bounded (w + 2)
  /-- The traversal constants remain actual registers. -/
  controls : a.Controls x
  /-- Every frontend descriptor and compact array is still available. -/
  frontend : Frontend.Output l U rs x.mem
  /-- Actual descriptor base and root count. -/
  descriptors : x.regs descriptors = l.descriptors
  roots : x.regs roots = l.count
  /-- Actual root index and shared fuel. -/
  current : x.regs current = s.index
  levels : x.regs levels = a.fuel
  /-- Native descriptor stride and outer increment constant. -/
  stride : x.regs stride = 6
  one : x.regs one = 1
  /-- The actual index never passes the last descriptor. -/
  index_le : s.index ≤ l.count
  /-- Every candidate prime still has its actual bitmap bit. -/
  bitmap : a.Bitmap x.mem
  /-- The heap avoids all shared reservations. -/
  floor : a.floor ≤ x.regs Traversal.heap
  /-- All unprocessed roots retain their complete allocation budgets. -/
  heapBudget : x.regs Traversal.heap + (l.count - s.index) *
    (Traversal.Math.work a.fuel * Traversal.allocationSize a.n a.m a.N) ≤ a.ceiling
  /-- The native count agrees with the emitted list. -/
  count : x.regs Traversal.outputCount = s.nodes.length
  /-- All unprocessed roots retain their complete pointer-table budgets. -/
  tableBudget : s.nodes.length + (l.count - s.index) * Traversal.Math.work a.fuel ≤
    a.outputCapacity
  /-- Exact native pointer-table and packed-cell readback. -/
  output : Traversal.StoredNodes a.U a.N a.table s.nodes x.mem
  /-- Every earlier packed array is safely below the current fresh allocation. -/
  outputBounds : ∀ i : Fin s.nodes.length,
    a.floor ≤ s.nodes[i.val].1 ∧ s.nodes[i.val].1 + 4 * a.N ≤ x.regs Traversal.heap
  /-- The emitted prefix and untouched roots give exactly the original finite forest. -/
  exactOutput : s.nodes.map Prod.snd ++
    Traversal.Math.output (Nat.primesLE a.m) a.Λ
      (((entries l U rs).drop s.index).map Traversal.Entry.task) =
    Traversal.Math.output (Nat.primesLE a.m) a.Λ
      ((entries l U rs).map Traversal.Entry.task)
  /-- Original memory below the shared stack is retained throughout the forest. -/
  protectedMemory : ∀ p < a.stack, x.mem p = a.retained p

/-- A live outer iteration has room for the one root it is about to execute. -/
private theorem ForestCursor.Invariant.root_budgets {a : Traversal.Arena} {w U : ℕ}
    {l : Frontend.Layout} {rs : List (ℕ × ℕ)} {s : ForestCursor} {x : Data 128}
    (h : s.Invariant a w l U rs x)
    (hc : (Cond.lt Preprocessing.current Preprocessing.roots).Holds x) :
    (rootArena a x s.nodes).ceiling ≤ a.ceiling ∧
      (rootArena a x s.nodes).outputCapacity ≤ a.outputCapacity := by
  have hi : s.index < l.count := by
    simpa only [Cond.holds_lt, h.current, h.roots] using hc
  have hm : 1 ≤ l.count - s.index := by omega
  have hh := Nat.mul_le_mul_left
    (Traversal.Math.work a.fuel * Traversal.allocationSize a.n a.m a.N) hm
  have ht := Nat.mul_le_mul_left (Traversal.Math.work a.fuel) hm
  rw [Nat.mul_one, Nat.mul_comm _ (l.count - s.index)] at hh ht
  constructor <;> dsimp only [rootArena]
  · have := h.heapBudget
    omega
  · have := h.tableBudget
    omega

/-- Execute the next actual descriptor and its full recursion within that root's own budget. -/
private theorem execute_next_root {a : Traversal.Arena} {w U : ℕ} {l : Frontend.Layout}
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
private theorem forest_body_exec {a : Traversal.Arena} {w U : ℕ} {l : Frontend.Layout}
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
  have hheap := h.heapBudget
  have htable := h.tableBudget
  have hrem : l.count - s.index = (l.count - (s.index + 1)) + 1 := by omega
  rw [hrem, Nat.add_mul, Nat.one_mul] at hheap htable
  let s' : ForestCursor := ⟨s.index + 1, out⟩
  refine ⟨s', z, ?_, ?_, by dsimp only [s']; omega⟩
  · obtain ⟨t, ht, he⟩ := he
    cases he with
    | seq hload hroot =>
      exact ⟨_, by omega, hload.seq (hroot.seq hz)⟩
  · constructor
    · exact hz.bounded hy.bounded
    · exact hy.controls.congr fun i hi => zreg i (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        simp only [ne_eq, Fin.ext_iff, current]
        omega)
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
      change z.regs Traversal.heap + (l.count - (s.index + 1)) * _ ≤ _
      rw [zreg _ (by decide)]
      omega
    · exact (zreg _ (by decide)).trans hy.count
    · have ht : out.length ≤ s.nodes.length + Traversal.Math.work a.fuel := by
        simpa only [rootArena, Traversal.Cursor.work, List.map_nil,
          Traversal.Math.potential, List.sum_nil, Nat.add_zero] using hy.tableBudget
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
private theorem forest_exec {a : Traversal.Arena} {w U : ℕ} {l : Frontend.Layout}
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
