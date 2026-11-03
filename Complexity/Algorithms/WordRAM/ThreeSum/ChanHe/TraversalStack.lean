/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Stack.Record

/-!
# Native stack calls for Chan–He traversal records

Traversal keeps a seven-word record in registers 64–70 and the existing bounded stack in
registers 96–104. Registers below 64 remain available to the complete modulus and node programs.
Each record contains fuel followed by three base/length pairs. The stack stores words, so a
record is pushed in reverse order and popped in forward order.

The dispatcher, representation and memory frame are reused from `Cslib.WordRAM.Stack`.
Argument delivery and result copies here are actual native instructions and are charged.

## Main definitions

* `slot`: the seven persistent traversal-record registers.
* `registers`: the existing nine-register stack dispatcher inside the 128-register controller.
* `pushFrame`, `popFrame`: fixed-bank transfers through the bounded-stack record API.

## Main results

* `pushFrame_exec`, `popFrame_exec`: complete seven-word record transfers in 64 and 99 instructions.

The native controller and its composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- Fuel and the three base/length pairs, retained across both 64-register native kernels. -/
def slot (i : Fin 7) : Fin 128 := ⟨64 + i.val, by omega⟩

/-- Pointer word of the selected pending set. -/
def arraySource (j : Fin 3) : Fin 128 := slot ⟨1 + 2 * j.val, by omega⟩

/-- Length word of the selected pending set. -/
def arrayLength (j : Fin 3) : Fin 128 := slot ⟨2 + 2 * j.val, by omega⟩

/-- The existing stack's workspace lies above every 64-register node-kernel register. -/
def registers (i : Fin 9) : Fin 128 := ⟨96 + i.val, by omega⟩

private theorem registers_injective : Function.Injective registers :=
  fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

/-- Caller-owned registers outside the stack dispatcher. -/
abbrev Outside (i : Fin 128) : Prop := i.val < 96 ∨ 105 ≤ i.val

private theorem outside_ne (i : Fin 128) (hi : Outside i) (j : Fin 9) :
    i ≠ registers j := by
  intro h
  have := congrArg Fin.val h
  dsimp [registers, Outside] at *
  omega

private theorem slot_ne_registers (i : Fin 7) (j : Fin 9) : slot i ≠ registers j :=
  outside_ne _ (Or.inl (by dsimp [slot]; omega)) j

/-- Push all seven record words in reverse order through the generic bounded-stack record API. -/
def pushFrame : Code .standard 128 := Stack.pushRecord registers slot (slot 0)

/-- The complete native frame push charges all seven dispatches and argument delivery.
There is no host-level record write, and the exact seven-word sequence is at the stack top. -/
theorem pushFrame_exec {w base capacity : ℕ} (x : Data 128) (vs : List ℕ)
    (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    (hr : Stack.Rep w base capacity vs (x.comap registers))
    (hw : ∀ i, Fits w (x.regs (slot i))) (hv : 7 + vs.length ≤ capacity) :
    ∃ y, Exec w pushFrame x y 64 ∧
      Stack.Rep w base capacity
        ([x.regs (slot 0), x.regs (slot 1), x.regs (slot 2), x.regs (slot 3),
          x.regs (slot 4), x.regs (slot 5), x.regs (slot 6)] ++ vs) (y.comap registers) ∧
      Modifies (Stack.footprint base capacity) x.mem y.mem ∧
      ∀ j, Outside j → y.regs j = x.regs j := by
  obtain ⟨y, hy, hry, hfy, hpy⟩ :=
    Stack.pushRecord_exec registers registers_injective slot (slot 0)
      slot_ne_registers x vs h2 hcap hr hw hv
  refine ⟨y, hy, ?_, hfy, fun j hj => hpy j (outside_ne j hj)⟩
  simpa [List.ofFn_succ, Fin.succ] using hry

/-- Pop all seven record words in forward order through the generic bounded-stack record API. -/
def popFrame : Code .standard 128 := Stack.popRecord registers slot (slot 0)

/-- The complete record pop charges every argument, dispatch and result-copy instruction.
The seven restored words have their original order; other caller registers are preserved. -/
theorem popFrame_exec {w base capacity : ℕ} (x : Data 128) (vs : List ℕ) (a : Fin 7 → ℕ)
    (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    (hr : Stack.Rep w base capacity
      ([a 0, a 1, a 2, a 3, a 4, a 5, a 6] ++ vs) (x.comap registers)) :
    ∃ y, Exec w popFrame x y 99 ∧ Stack.Rep w base capacity vs (y.comap registers) ∧
      (∀ i, y.regs (slot i) = a i) ∧
      Modifies (Stack.footprint base capacity) x.mem y.mem ∧
      ∀ j, Outside j → (j.val < 64 ∨ 71 ≤ j.val) → y.regs j = x.regs j := by
  have hr' : Stack.Rep w base capacity (List.ofFn a ++ vs) (x.comap registers) := by
    simpa [List.ofFn_succ, Fin.succ] using hr
  obtain ⟨y, hy, hry, hya, hfy, hpy⟩ :=
    Stack.popRecord_exec registers registers_injective slot (slot 0)
      (fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val h)))
      slot_ne_registers x vs a h2 hcap hr'
  refine ⟨y, hy, hry, hya, hfy, ?_⟩
  intro j hj hj'
  apply hpy j (outside_ne j hj)
  intro i h
  have := congrArg Fin.val h
  dsimp [slot] at this
  omega

/-- Record transfers do not inspect the physical word width. -/
theorem not_readsWidth : ¬pushFrame.ReadsWidth ∧ ¬popFrame.ReadsWidth :=
  ⟨Stack.pushRecord_not_readsWidth registers slot (slot 0),
    Stack.popRecord_not_readsWidth registers slot (slot 0)⟩

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
