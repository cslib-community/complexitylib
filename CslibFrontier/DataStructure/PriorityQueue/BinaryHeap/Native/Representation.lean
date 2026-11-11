/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Program

/-!
# The compact heap's raw native representation

The representation is the existing Backend representation on the global method/initialization
family, together with its four persistent layout words. It uses the original `space n` compact
block and the existing memory heap invariant; no register-held heap model is introduced.

## Main definitions

* `Rep`: Backend's represented heap and its persistent runtime layout words.

## Main results

* `Rep.bounded`: the represented native data is word-bounded.
* `Rep.congr`: changing memory outside the compact block preserves the represented heap,
  provided the frontier does not shrink and the layout words remain live.
* `Rep.supported`: the existing finite-block/persistent-register support obligation.
* `initFresh_rep`: the actual local-zero native initializer establishes this representation.

This is a representation/locality bridge, not a method-dispatch certificate or a legacy clock
claim. The one-run fresh initializer requires local zero; arbitrary dirty storage is not cleared
in constant time, and local zero is not a generic allocator precondition.
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.Representation

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.PriorityQueue.BinaryHeap (space)

/-- The existing Backend representation specialized to compact storage and the global register
family. Only the four persistent layout words are added to its invariant. -/
def Rep {w n K : ℕ} (base : ℕ) (hn : Fits w n) (hK : Fits w K)
    (s : (indexedMinPQSpec n K).State) (x : Data Program.registers) : Prop :=
  (Backend.implementation
    ((implements (Memory.compactLayout n base) (Memory.valid_compactLayout hn hK)).extend
      Program.initialization)).rep s x ∧
    ∀ i : Fin 4, x.regs (Program.argument (Fin.castAdd 2 i)) =
      layoutWords ⟨n, Memory.compactLayout n base⟩ i

/-- Word boundedness is supplied by Backend's existing representation. -/
theorem Rep.bounded {w n K base : ℕ} {hn : Fits w n} {hK : Fits w K}
    {s : (indexedMinPQSpec n K).State} {x : Data Program.registers}
    (hr : Rep base hn hK s x) : x.Bounded w :=
  ((Backend.rep_iff _ _ _).mp hr.1).2.2

/-- The inherited Backend relation is local to the compact block. Increasing the frontier and
retaining the live layout words do not require equality of memory outside that block. -/
theorem Rep.congr {w n K base : ℕ} {hn : Fits w n} {hK : Fits w K}
    {s : (indexedMinPQSpec n K).State} {x x' : Data Program.registers}
    (hr : Rep base hn hK s x)
    (hmem : ∀ a ∈ (Block.mk base (space n)).footprint, x'.mem a = x.mem a)
    (hfrontier : x.regs (Backend.frontier Program.family) ≤
      x'.regs (Backend.frontier Program.family))
    (hwords : ∀ i : Fin 4,
      x'.regs (Program.argument (Fin.castAdd 2 i)) = x.regs (Program.argument (Fin.castAdd 2 i)))
    (hx' : x'.Bounded w) : Rep base hn hK s x' := by
  obtain ⟨hi, ha, _⟩ := (Backend.rep_iff _ _ _).mp hr.1
  have hm : ∀ a ∈ (Memory.compactLayout n base).footprint,
      (memoryState (Backend.frontier Program.family) x').mem a =
        (memoryState (Backend.frontier Program.family) x).mem a := by
    rw [Memory.compactLayout_footprint]
    exact hmem
  refine ⟨(Backend.rep_iff _ _ _).mpr ⟨?_, ?_, hx'⟩, fun i => (hwords i).trans (hr.2 i)⟩
  · exact Memory.Inv.congr (Memory.valid_compactLayout hn hK) hi hm hfrontier
  · exact (Memory.abs_congr hm).trans ha

/-- The exact support shape used by `SubroutineBase`: agreement on persistent registers and
the original compact block suffices, provided the replacement data remains word-bounded. -/
theorem Rep.supported {w n K base : ℕ} {hn : Fits w n} {hK : Fits w K}
    {s : (indexedMinPQSpec n K).State} {x x' : Data Program.registers}
    (hreg : ∀ i, Program.code.input i = false → x'.regs i = x.regs i)
    (hmem : ∀ a ∈ (Block.mk base (space n)).footprint, x'.mem a = x.mem a)
    (hx' : x'.Bounded w) (hr : Rep base hn hK s x) : Rep base hn hK s x' :=
  hr.congr hmem (le_of_eq (hreg _ Program.code_input_frontier).symm)
    (fun i => hreg _ (Program.code_input_argument i)) hx'

/-- The single global native fresh initializer produces the existing Backend representation
and the actual persistent layout words. Its local-zero assumption is restricted to `space n`;
all other memory cells, including inaccessible cells, remain literally unchanged. -/
theorem initFresh_rep {w n K base : ℕ} (hn : Fits w n) (hK : Fits w K)
    (x : Data Program.registers) (hx : x.Bounded w)
    (hfront : x.regs Program.code.frontierReg = base)
    (hnlive : x.regs Program.code.nReg = n)
    (hfit : Fits w (base + space n))
    (hz : ∀ a, (Block.mk base (space n)).Owns a → x.mem a = 0) :
    ∃ y, ExecWithin w Program.code.initFresh x y
        (2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor) ∧
      y.mem = x.mem ∧ y.regs Program.code.frontierReg = base + space n ∧
      Rep base hn hK (IndexedMinPQ.empty n) y := by
  obtain ⟨y, he, hb, hm, hf, hyn, hybase, hcount, hlen, hi, ha⟩ :=
    Program.initFresh_exec x hx hfront hnlive hfit hz
  rw [Program.code_frontier] at hi ha
  refine ⟨y, he, hm, hf, (Backend.rep_iff _ _ _).mpr ⟨hi, ha, hb⟩, ?_⟩
  intro i
  fin_cases i
  · change y.regs (Program.argument 0) = n
    rwa [Program.code_nReg] at hyn
  · change y.regs (Program.argument 1) = base + n
    exact hcount
  · change y.regs (Program.argument 2) = 1
    exact hlen
  · change y.regs (Program.argument 3) = base
    rwa [Program.code_baseReg] at hybase

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.Representation
