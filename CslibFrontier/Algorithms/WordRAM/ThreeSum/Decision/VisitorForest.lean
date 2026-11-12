/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.VisitorForestInvariant
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.VisitorRoot
import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingLoad
import CslibFrontier.Algorithms.WordRAM.ThreeSum.Frontend.Frame
import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Registers

/-!
# Complete native frontend forest with in-place node consumption

Each actual iteration loads the next native frontend descriptor, executes its complete root
visitor and increments the real descriptor index. Root-local allocation ceilings preserve
space for every later root. Solver work is charged once for each actual mathematical node,
including its order and multiplicity; skipped native descriptors carry traversal charges only.

## Main results

* `execute_next_root`: actual descriptor loading and complete root consumption.
* `forest_body_exec`: actual index advancement and complete forest invariant preservation.
* `forest_exec`: every actual native root, with exact Boolean fold and charged loop control.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)
open ChanHe.Traversal

/-- Execute the next actual frontend descriptor within its own root allocation allowance. -/
theorem execute_next_root {r κ n w U : ℕ} {a : Arena} {l : Frontend.Layout}
    {input : List ℤ} {rs : List (ℕ × ℕ)} {s : ForestCursor} {x : Data (registerCount r)}
    (c : Host.Callee r) (hw : width κ c.widthCoefficient n ≤ w + 2)
    (ha : a.Separated)
    (hresources : a.ceiling ≤ (n + 2) ^ envelopeExponent κ ∧
      4 * a.N < (n + 2) ^ envelopeExponent κ ∧
      60 * a.U + 40 ≤ (n + 2) ^ envelopeExponent κ)
    (hready : a.Ready w) (h : s.Invariant a w κ n l U rs x)
    (hc : (Cond.lt (preprocessingRegisters r ChanHe.Preprocessing.current)
      (preprocessingRegisters r ChanHe.Preprocessing.roots)).Holds x)
    (hn : a.n = l.n + 1) (hU : a.U = 2 * U) (hfront : l.endpoint ≤ a.stack)
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hnd : (rs.map Prod.fst).Nodup) (hcard : rs.length ≤ l.n)
    (hvalues : ∀ z ∈ input, |z| ≤ (U : ℤ)) :
    let e := ChanHe.Preprocessing.entry l U a.fuel rs s.index
    let T := Host.callerTime (4 * a.N)
      (c.time (Host.sideLength (4 * a.N)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 8
    ∃ y, ExecWithin (w + 2)
        (.seq (ChanHe.Preprocessing.loadRoot.rename (preprocessingRegisters r)) (oneRoot c.code))
        x y (14 + rootTime a.fuel a.n a.m a.N +
          (e.task.output (Nat.primesLE a.m) a.Λ).length * T) ∧
      (Cursor.mk [] (s.nodes ++ e.task.output (Nat.primesLE a.m) a.Λ)).Invariant
        (rootArena a x) w κ n (s.nodes ++ e.task.output (Nat.primesLE a.m) a.Λ) y ∧
      (∀ p < a.stack, y.mem p = x.mem p) ∧
      ∀ i : Fin 128, 109 ≤ i.val → i ≠ ChanHe.Preprocessing.address →
        y.regs (preprocessingRegisters r i) = x.regs (preprocessingRegisters r i) := by
  let e := ChanHe.Preprocessing.entry l U a.fuel rs s.index
  let b := rootArena a x
  have hi : s.index < l.count := by
    simpa only [Cond.holds_lt, h.current, h.roots] using hc
  have hceil := h.root_budget hc
  have hheap : x.regs (preprocessingRegisters r heap) ≤ a.ceiling := by
    have := h.heapBudget
    omega
  have hstack : a.stack ≤ x.regs (preprocessingRegisters r heap) := by
    have ht := ha.2.1
    have hg := ha.2.2.1
    have := h.floor
    omega
  have haddr : l.descriptors + 6 * s.index + 5 ≤ a.ceiling := by
    have hd := l.descriptor_before (ChanHe.Preprocessing.entry_slot hi (2 : Fin 3)) l.arrays
    change l.descriptors + 2 * (3 * s.index + 2) + 2 ≤ l.endpoint at hd
    omega
  have hsum := envelope_ge_sum a.ceiling a.n a.m a.Λ a.U a.N
  have hfit := (Signed.unsigned_fits_of_signed hready.2.2).of_le (haddr.trans (by omega))
  have hload := ChanHe.Preprocessing.loadRoot_exec (x.comap (preprocessingRegisters r))
    ⟨fun i => h.bounded.1 (preprocessingRegisters r i), h.bounded.2⟩ hi h.current
    h.descriptors h.levels h.stride h.increment hfit h.frontend
  obtain ⟨p, hp, ⟨hloaded, hmem, hpr⟩, hpouter⟩ :=
    Exec.rename_post (preprocessing_injective r) hload
  change p.mem = x.mem at hmem
  have pheap : p.regs (preprocessingRegisters r heap) =
      x.regs (preprocessingRegisters r heap) := hpr _ (by decide) (by decide)
  have pm (i : Fin 16) : p.regs (controllerRegisters r i) = x.regs (controllerRegisters r i) :=
    hpouter _ (fun j => (controller_ne_preprocessing i j).symm)
  have hinput : RootInput b w κ n e s.nodes p := by
    refine {
      bounded := hp.bounded h.bounded
      controls := h.controls.of_regs_71_96 fun i hi hi' => hpr i (Or.inr hi) (by
        simp only [ne_eq, Fin.ext_iff, ChanHe.Preprocessing.address]; omega)
      loaded := hloaded
      stored := ?_
      valid := ?_
      bitmap := ?_
      around := ?_
      ends := ?_
      fuel := rfl
      floor := ?_
      heapBudget := ?_
      packedLength := ?_
      envelopeValue := (pm _).trans h.envelopeValue
      unit := (pm _).trans h.unit
      boolean := (pm _).symm ▸ h.boolean
      verdict := ?_
      protectedMemory := ?_ }
    · rw [show p.mem = x.mem from hmem]
      exact ChanHe.Preprocessing.entry_stored hkeys h.frontend hi
    · dsimp only [b, rootArena]
      rw [hn, hU]
      exact ChanHe.Preprocessing.entry_valid l U a.fuel s.index hkeys hnd hcard hvalues
    · simpa only [b, rootArena, Arena.Bitmap, Data.comap_mem, hmem] using h.bitmap
    · intro j
      apply Or.inl
      exact (ChanHe.Preprocessing.entry_ends l U a.fuel rs hcard hi j).trans hfront
    · intro j
      rw [pheap]
      exact (ChanHe.Preprocessing.entry_ends l U a.fuel rs hcard hi j).trans (hfront.trans hstack)
    · simpa only [b, rootArena, pheap] using h.floor
    · dsimp only [b, rootArena, e, ChanHe.Preprocessing.entry]
      rw [pheap]
    · exact (hpr _ (by decide) (by decide)).trans h.packedLength
    · rw [pm]
      exact h.verdict
    · simpa only [b, rootArena, Data.comap_mem, hmem] using h.protectedMemory
  obtain ⟨y, he, hfinal, hprefix, hregs⟩ := root_exec (a := b) c e s.nodes p hw ha
    (rootArena_resources hceil hresources) (rootArena_ready hready hceil) hinput
  refine ⟨y, (hp.within.seq he).mono ?_, hfinal, ?_, ?_⟩
  · dsimp only [rootTime, b, rootArena, e, ChanHe.Preprocessing.entry]
    omega
  · intro q hq
    exact (hprefix q hq).trans (congrFun hmem q)
  · intro i hi hj
    exact (hregs i hi).trans (hpr i (Or.inr (by omega)) hj)

/-- A real descriptor load, complete root visit and index increment preserve every later root's
allocation allowance. The remaining exact node count pays only actual solver calls. -/
theorem forest_body_exec {r κ n w U : ℕ} {a : Arena} {l : Frontend.Layout}
    {input : List ℤ} {rs : List (ℕ × ℕ)} {s : ForestCursor} {x : Data (registerCount r)}
    (c : Host.Callee r) (hw : width κ c.widthCoefficient n ≤ w + 2)
    (ha : a.Separated)
    (hresources : a.ceiling ≤ (n + 2) ^ envelopeExponent κ ∧
      4 * a.N < (n + 2) ^ envelopeExponent κ ∧
      60 * a.U + 40 ≤ (n + 2) ^ envelopeExponent κ)
    (hready : a.Ready w) (h : s.Invariant a w κ n l U rs x)
    (hc : (Cond.lt (preprocessingRegisters r ChanHe.Preprocessing.current)
      (preprocessingRegisters r ChanHe.Preprocessing.roots)).Holds x)
    (hn : a.n = l.n + 1) (hU : a.U = 2 * U)
    (hf : a.fuel = Cslib.Algorithms.ThreeSum.ChanHe.fuel l.n)
    (hfront : l.endpoint ≤ a.stack)
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hnd : (rs.map Prod.fst).Nodup) (hcard : rs.length ≤ l.n)
    (hvalues : ∀ z ∈ input, |z| ≤ (U : ℤ)) :
    let T := Host.callerTime (4 * a.N)
      (c.time (Host.sideLength (4 * a.N)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 8
    ∃ (s' : ForestCursor) (y : Data (registerCount r)) (t : ℕ),
      ExecWithin (w + 2)
        (.seq (ChanHe.Preprocessing.loadRoot.rename (preprocessingRegisters r))
          (.seq (oneRoot c.code) (.op (.bin .add
            (preprocessingRegisters r ChanHe.Preprocessing.current)
            (preprocessingRegisters r ChanHe.Preprocessing.current)
            (preprocessingRegisters r ChanHe.Preprocessing.one))))) x y t ∧
      s'.Invariant a w κ n l U rs y ∧
      t + 2 + s'.credit a l U rs T ≤ s.credit a l U rs T := by
  let e := ChanHe.Preprocessing.entry l U a.fuel rs s.index
  let T := Host.callerTime (4 * a.N)
    (c.time (Host.sideLength (4 * a.N)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 8
  have hi : s.index < l.count := by
    simpa only [Cond.holds_lt, h.current, h.roots] using hc
  obtain ⟨y, he, hy, hprefix, hregs⟩ :=
    execute_next_root c hw ha hresources hready h hc hn hU hfront hkeys hnd hcard hvalues
  have yi : y.regs (preprocessingRegisters r ChanHe.Preprocessing.current) = s.index :=
    (hregs _ (by decide) (by decide)).trans h.current
  have yo : y.regs (preprocessingRegisters r ChanHe.Preprocessing.one) = 1 :=
    (hregs _ (by decide) (by decide)).trans h.increment
  have hfit : Fits (w + 2) (s.index + 1) :=
    (h.bounded.1 (preprocessingRegisters r ChanHe.Preprocessing.roots)).of_le (by
      rw [h.roots]
      omega)
  let current := preprocessingRegisters r ChanHe.Preprocessing.current
  let one := preprocessingRegisters r ChanHe.Preprocessing.one
  let z := y.set current (s.index + 1)
  have hz : Exec (B := .standard) (w + 2) (.op (.bin .add current current one)) y z 1 := by
    ram_eval [z, yi, yo, hfit, current, one]
  have zreg (i : Fin 128) (hi : i ≠ ChanHe.Preprocessing.current) :
      z.regs (preprocessingRegisters r i) = y.regs (preprocessingRegisters r i) := by
    have hne : preprocessingRegisters r i ≠ current :=
      fun he => hi ((preprocessing_injective r) he)
    simp only [z, Data.set_regs, Function.update_of_ne hne]
  have zouter (i : Fin 128) (hi : 109 ≤ i.val) (hc : i ≠ ChanHe.Preprocessing.current)
      (ha : i ≠ ChanHe.Preprocessing.address) :
      z.regs (preprocessingRegisters r i) = x.regs (preprocessingRegisters r i) :=
    (zreg i hc).trans (hregs i hi ha)
  have zm (i : Fin 16) : z.regs (controllerRegisters r i) = y.regs (controllerRegisters r i) := by
    simp only [z, current, Data.set_regs, Function.update_apply,
      controller_ne_preprocessing, ↓reduceIte]
  have hheap := h.heapBudget
  have hrem : l.count - s.index = (l.count - (s.index + 1)) + 1 := by omega
  rw [hrem, Nat.add_mul, Nat.one_mul] at hheap
  let s' : ForestCursor := ⟨s.index + 1, s.nodes ++ e.task.output (Nat.primesLE a.m) a.Λ⟩
  refine ⟨s', z, rootTime a.fuel a.n a.m a.N + 15 +
    (e.task.output (Nat.primesLE a.m) a.Λ).length * T, ?_, ?_, ?_⟩
  · obtain ⟨t, ht, he⟩ := he
    cases he with
    | seq hload hroot =>
      exact (hload.seq (hroot.seq hz)).within.mono (by dsimp only [e, T] at *; omega)
  · refine {
      bounded := hz.bounded hy.bounded
      controls := hy.controls.of_regs_71_96 (fun i _ hi => zreg i (by
        simp only [ne_eq, Fin.ext_iff, ChanHe.Preprocessing.current]; omega))
      frontend := h.frontend.frame hcard (fun p hp => hprefix p (hp.trans_le hfront))
      descriptors := (zouter _ (by decide) (by decide) (by decide)).trans h.descriptors
      roots := (zouter _ (by decide) (by decide) (by decide)).trans h.roots
      current := rfl
      levels := (zouter _ (by decide) (by decide) (by decide)).trans h.levels
      stride := (zouter _ (by decide) (by decide) (by decide)).trans h.stride
      increment := (zouter _ (by decide) (by decide) (by decide)).trans h.increment
      index_le := by dsimp only [s']; omega
      bitmap := hy.bitmap
      floor := ?_
      heapBudget := ?_
      packedLength := (zreg _ (by decide)).trans hy.packedLength
      envelopeValue := (zm _).trans hy.envelopeValue
      unit := (zm _).trans hy.unit
      boolean := (zm _).symm ▸ hy.boolean
      verdict := ?_
      exactOutput := ?_
      protectedMemory := hy.protectedMemory }
    · simpa only [rootArena, zreg heap (by decide)] using hy.floor
    · have hh : y.regs (preprocessingRegisters r heap) ≤
          x.regs (preprocessingRegisters r heap) +
            Math.work a.fuel * allocationSize a.n a.m a.N := by
        simpa only [rootArena, Cursor.work, List.map_nil, Math.potential, List.sum_nil,
          Nat.zero_mul, Nat.add_zero] using hy.heapBudget
      change z.regs (preprocessingRegisters r heap) + (l.count - (s.index + 1)) * _ ≤ _
      rw [zreg _ (by decide)]
      omega
    · rw [zm]
      exact hy.verdict
    · change (s.nodes ++ e.task.output (Nat.primesLE a.m) a.Λ) ++ _ = _
      rw [List.append_assoc, ← s.remaining_step s'.nodes hi hf]
      exact h.exactOutput
  · have hpay := s.credit_step (U := U) (rs := rs) s'.nodes T hi hf
    change s.credit a l U rs T = _ at hpay
    rw [hpay]
    dsimp only [e, T, s']
    omega

/-- Execute the entire actual descriptor loop with exact mathematical output and Boolean fold.
The final loop test and every native descriptor increment are included in the charge. -/
theorem forest_exec {r κ n w U : ℕ} {a : Arena} {l : Frontend.Layout}
    {input : List ℤ} {rs : List (ℕ × ℕ)} {s : ForestCursor} {x : Data (registerCount r)}
    (c : Host.Callee r) (hw : width κ c.widthCoefficient n ≤ w + 2)
    (ha : a.Separated)
    (hresources : a.ceiling ≤ (n + 2) ^ envelopeExponent κ ∧
      4 * a.N < (n + 2) ^ envelopeExponent κ ∧
      60 * a.U + 40 ≤ (n + 2) ^ envelopeExponent κ)
    (hready : a.Ready w) (h : s.Invariant a w κ n l U rs x)
    (hn : a.n = l.n + 1) (hU : a.U = 2 * U)
    (hf : a.fuel = Cslib.Algorithms.ThreeSum.ChanHe.fuel l.n)
    (hfront : l.endpoint ≤ a.stack)
    (hkeys : ∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode)
    (hnd : (rs.map Prod.fst).Nodup) (hcard : rs.length ≤ l.n)
    (hvalues : ∀ z ∈ input, |z| ≤ (U : ℤ)) :
    let T := Host.callerTime (4 * a.N)
      (c.time (Host.sideLength (4 * a.N)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 8
    ∃ (s' : ForestCursor) (y : Data (registerCount r)),
      ExecWithin (w + 2) (forest c.code) x y (s.credit a l U rs T + 2) ∧
      s'.Invariant a w κ n l U rs y ∧ s'.index = l.count ∧
      s'.nodes = Math.output (Nat.primesLE a.m) a.Λ
        ((ChanHe.Preprocessing.entries l U rs).map Entry.task) := by
  let T := Host.callerTime (4 * a.N)
    (c.time (Host.sideLength (4 * a.N)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 8
  obtain ⟨s', y, he, hy, hc⟩ := ExecWithin.loop_potential_state
    (fun (s : ForestCursor) y => s.Invariant a w κ n l U rs y)
    (fun s => s.credit a l U rs T)
    (fun s x hi hc => forest_body_exec c hw ha hresources hready hi hc
      hn hU hf hfront hkeys hnd hcard hvalues) h
  have hend : s'.index = l.count := by
    have hge : l.count ≤ s'.index := by
      simpa only [Cond.holds_lt, hy.current, hy.roots, not_lt] using hc
    exact hy.index_le.antisymm hge
  refine ⟨s', y, he, hy, hend, ?_⟩
  have hlen : (ChanHe.Preprocessing.entries l U rs).length = l.count := by
    simp only [ChanHe.Preprocessing.entries, List.length_map, List.length_range]
  simpa only [ForestCursor.remaining, hend, ← hlen, List.drop_length, List.map_nil,
    Math.output, List.flatMap_nil, List.append_nil] using hy.exactOutput

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor
