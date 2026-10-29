/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Stack
import Mathlib.Tactic.FinCases

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
* `pushSlot`: native argument delivery followed by the complete bounded-stack dispatcher.
* `popSlot`: native dispatch and result delivery to one traversal-record register.

## Main results

* `pushSlot_exec`: a nine-instruction push, with the exact stack, memory and register frames.
* `popSlot_exec`: a fourteen-instruction nonempty pop with the same exact frames.
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

private theorem registers_injective : Function.Injective registers := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [registers] at this
  omega

/-- Caller-owned registers outside the stack dispatcher. -/
abbrev Outside (i : Fin 128) : Prop := i.val < 96 ∨ 105 ≤ i.val

private theorem outside_ne (i : Fin 128) (hi : Outside i) (j : Fin 9) :
    i ≠ registers j := by
  intro h
  have := congrArg Fin.val h
  dsimp [registers, Outside] at *
  omega

private theorem extend_outside (a : Data 9) (x : Data 128) (i : Fin 128) (hi : Outside i) :
    (a.extend registers x).regs i = x.regs i := by
  change Function.extend registers a.regs x.regs i = x.regs i
  apply Function.extend_apply'
  rintro ⟨j, hj⟩
  exact outside_ne i hi j hj.symm

/-- Deliver the push tag and actual record word, then execute the existing stack program. -/
def pushSlot (i : Fin 7) : Code .standard 128 :=
  let tag := registers Stack.tag
  let arg := registers Stack.arg
  let src := slot i
  .seq (ram[ tag ← #0; arg ← src ]) (Stack.program.rename registers)

/-- Each native push includes both argument instructions, not a host-level stack operation.
Every register outside 96–104 and every memory cell outside the reserved stack is preserved. -/
theorem pushSlot_exec {w base capacity : ℕ} (i : Fin 7) (x : Data 128) (vs : List ℕ)
    (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    (hr : Stack.Rep w base capacity vs (x.comap registers))
    (hw : Fits w (x.regs (slot i))) (hv : vs.length < capacity) :
    ∃ y, Exec w (pushSlot i) x y 9 ∧
      Stack.Rep w base capacity (x.regs (slot i) :: vs) (y.comap registers) ∧
      Modifies (Stack.footprint base capacity) x.mem y.mem ∧
      ∀ j, Outside j → y.regs j = x.regs j := by
  let q := (x.set (registers Stack.tag) 0).set (registers Stack.arg) (x.regs (slot i))
  have hs : slot i ≠ registers Stack.tag := outside_ne _ (Or.inl (by dsimp [slot]; omega)) _
  have hp : Exec (B := .standard) w
      (.seq (.op (.const (registers Stack.tag) 0))
        (.op (.copy (registers Stack.arg) (slot i)))) x q 2 := by
    ram_eval [q, hs]
  have hq : q.comap registers =
      (Stack.implementation w capacity).prepare (.push (x.regs (slot i)))
        (x.comap registers) := by
    ext j
    · fin_cases j <;>
        simp +decide [q, Data.comap, Data.set, registers, Stack.implementation,
          DynamicProgram.prepare, Stack.tag, Stack.arg]
    · rfl
  obtain ⟨a, ha, _, hra, hframe⟩ := Stack.execute h2 hcap hr (.push (x.regs (slot i))) ⟨hv, hw⟩
  have hcall : Exec w Stack.program (q.comap registers) a 7 := by
    simpa only [hq, Stack.bodyCost] using ha
  let y := a.extend registers q
  refine ⟨y, ?_, ?_, hframe, ?_⟩
  · exact hp.seq (hcall.rename registers_injective)
  · simpa only [y, Data.comap_extend registers_injective] using hra
  · intro j hj
    rw [extend_outside a q j hj]
    simp only [q, Data.set_regs, Function.update_of_ne (outside_ne j hj Stack.arg),
      Function.update_of_ne (outside_ne j hj Stack.tag)]

private def pushSlots : List (Fin 7) → Code .standard 128
  | [] => .op (.copy (slot 0) (slot 0))
  | i :: is => .seq (pushSlot i) (pushSlots is)

private theorem pushSlots_exec {w base capacity : ℕ} (is : List (Fin 7)) (x : Data 128)
    (vs : List ℕ) (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    (hr : Stack.Rep w base capacity vs (x.comap registers))
    (hw : ∀ i, Fits w (x.regs (slot i))) (hv : is.length + vs.length ≤ capacity) :
    ∃ y, Exec w (pushSlots is) x y (9 * is.length + 1) ∧
      Stack.Rep w base capacity (is.reverse.map (fun i => x.regs (slot i)) ++ vs)
        (y.comap registers) ∧
      Modifies (Stack.footprint base capacity) x.mem y.mem ∧
      ∀ j, Outside j → y.regs j = x.regs j := by
  induction is generalizing x vs with
  | nil =>
    have he : Exec (B := .standard) w (.op (.copy (slot 0) (slot 0))) x x 1 := by
      convert (Exec.copy (B := Basis.standard) (w := w) (x := x)
        (d := slot 0) (s := slot 0)) using 1
      ext j <;> simp [Data.set]
    exact ⟨x, he, hr, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons i is ih =>
    have hv' : vs.length < capacity := by simp only [List.length_cons] at hv; omega
    obtain ⟨z, hz, hrz, hfz, hpz⟩ := pushSlot_exec i x vs h2 hcap hr (hw i) hv'
    have hslots : (fun i => z.regs (slot i)) = fun i => x.regs (slot i) := by
      funext i
      exact hpz _ (Or.inl (by dsimp [slot]; omega))
    obtain ⟨y, hy, hry, hfy, hpy⟩ := ih z (x.regs (slot i) :: vs) hrz
      (by intro j; rw [hpz _ (Or.inl (by dsimp [slot]; omega))]; exact hw j)
      (by simp only [List.length_cons] at hv ⊢; omega)
    refine ⟨y, ?_, ?_, ?_, fun j hj => (hpy j hj).trans (hpz j hj)⟩
    · simpa only [pushSlots, List.length_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz.seq hy
    · simpa only [hslots, List.reverse_cons, List.map_append, List.map_singleton,
        List.append_assoc, List.singleton_append] using hry
    · intro a ha
      exact (hfy a ha).trans (hfz a ha)

/-- Push all seven words in reverse order, so the next seven pops recover the record in order.
The trailing self-copy gives the fixed empty suffix an ordinary native instruction. -/
def pushFrame : Code .standard 128 :=
  .seq (pushSlot 6) (.seq (pushSlot 5) (.seq (pushSlot 4) (.seq (pushSlot 3)
    (.seq (pushSlot 2) (.seq (pushSlot 1) (.seq (pushSlot 0) (.op (.copy (slot 0) (slot 0)))))))))

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
  simpa only [pushFrame, pushSlots, List.length_cons, List.length_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append,
    List.map_cons, List.map_nil, List.map_append, List.map_singleton, Nat.reduceAdd,
    Nat.reduceMul] using pushSlots_exec [6, 5, 4, 3, 2, 1, 0] x vs h2 hcap hr hw hv

private theorem comap_set_slot (x : Data 128) (i : Fin 7) (v : ℕ) :
    (x.set (slot i) v).comap registers = x.comap registers := by
  ext j
  · change Function.update x.regs (slot i) v (registers j) = x.regs (registers j)
    apply Function.update_of_ne
    exact (outside_ne _ (Or.inl (by dsimp [slot]; omega)) j).symm
  · rfl

/-- Deliver the pop tag, execute the complete dispatcher, and copy its answer to the record. -/
def popSlot (i : Fin 7) : Code .standard 128 :=
  let tag := registers Stack.tag
  let arg := registers Stack.arg
  .seq (ram[ tag ← #1; arg ← #0 ])
    (.seq (Stack.program.rename registers) (.op (.copy (slot i) (registers Stack.out))))

/-- A nonempty native pop includes both argument instructions and the actual result copy.
Only the selected record register, stack workspace and reserved stack memory may change. -/
theorem popSlot_exec {w base capacity : ℕ} (i : Fin 7) (x : Data 128) (v : ℕ) (vs : List ℕ)
    (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    (hr : Stack.Rep w base capacity (v :: vs) (x.comap registers)) :
    ∃ y, Exec w (popSlot i) x y 14 ∧
      Stack.Rep w base capacity vs (y.comap registers) ∧ y.regs (slot i) = v ∧
      Modifies (Stack.footprint base capacity) x.mem y.mem ∧
      ∀ j, Outside j → j ≠ slot i → y.regs j = x.regs j := by
  let q := (x.set (registers Stack.tag) 1).set (registers Stack.arg) 0
  have h1 : Fits w 1 := h2.of_le (by decide)
  have hp : Exec (B := .standard) w
      (.seq (.op (.const (registers Stack.tag) 1))
        (.op (.const (registers Stack.arg) 0))) x q 2 := by
    ram_eval [q, h1]
  have hq : q.comap registers =
      (Stack.implementation w capacity).prepare .pop (x.comap registers) := by
    ext j
    · fin_cases j <;>
        simp +decide [q, Data.comap, Data.set, registers, Stack.implementation,
          DynamicProgram.prepare, Stack.tag, Stack.arg]
    · rfl
  obtain ⟨a, ha, hans, hra, hframe⟩ := Stack.execute h2 hcap hr .pop trivial
  have hcall : Exec w Stack.program (q.comap registers) a 11 := by
    simpa only [hq, Stack.bodyCost, List.cons_ne_nil, ↓reduceIte] using ha
  have hout : a.regs Stack.out = v := by
    change some (if a.regs Stack.present = 0 then none else some (a.regs Stack.out)) =
      some (some v) at hans
    split at hans
    · cases hans
    · exact Option.some.inj (Option.some.inj hans)
  have hread : (a.extend registers q).regs (registers Stack.out) = v := by
    change Function.extend registers a.regs q.regs (registers Stack.out) = v
    rw [registers_injective.extend_apply, hout]
  let y := (a.extend registers q).set (slot i) v
  have hcopy : Exec (B := .standard) w
      (.op (.copy (slot i) (registers Stack.out))) (a.extend registers q) y 1 := by
    simpa only [y, hread] using
      (Exec.copy (B := Basis.standard) (w := w) (x := a.extend registers q)
        (d := slot i) (s := registers Stack.out))
  refine ⟨y, hp.seq ((hcall.rename registers_injective).seq hcopy), ?_, ?_, hframe, ?_⟩
  · simpa only [y, comap_set_slot, Data.comap_extend registers_injective, List.tail_cons] using hra
  · exact Function.update_self ..
  · intro j hj hji
    change Function.update (a.extend registers q).regs (slot i) v j = x.regs j
    rw [Function.update_of_ne hji, extend_outside a q j hj]
    simp only [q, Data.set_regs, Function.update_of_ne (outside_ne j hj Stack.arg),
      Function.update_of_ne (outside_ne j hj Stack.tag)]

private def popSlots : List (Fin 7) → Code .standard 128
  | [] => .op (.copy (slot 0) (slot 0))
  | i :: is => .seq (popSlot i) (popSlots is)

private def restore : List (Fin 7) → List ℕ → (Fin 128 → ℕ) → Fin 128 → ℕ
  | i :: is, v :: vs, rs => restore is vs (Function.update rs (slot i) v)
  | _, _, rs => rs

private theorem restore_congr_at (is : List (Fin 7)) (vs : List ℕ)
    (rs ss : Fin 128 → ℕ) (j : Fin 128) (h : rs j = ss j) :
    restore is vs rs j = restore is vs ss j := by
  induction is generalizing vs rs ss with
  | nil => exact h
  | cons i is ih =>
    cases vs with
    | nil => exact h
    | cons v vs =>
      apply ih
      by_cases he : j = slot i
      · simp [he]
      · simpa only [Function.update_of_ne he] using h

private theorem popSlots_exec {w base capacity : ℕ} (is : List (Fin 7)) (ws : List ℕ)
    (x : Data 128) (vs : List ℕ) (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    (hr : Stack.Rep w base capacity (ws ++ vs) (x.comap registers))
    (hlen : ws.length = is.length) :
    ∃ y, Exec w (popSlots is) x y (14 * is.length + 1) ∧
      Stack.Rep w base capacity vs (y.comap registers) ∧
      Modifies (Stack.footprint base capacity) x.mem y.mem ∧
      ∀ j, Outside j → y.regs j = restore is ws x.regs j := by
  induction is generalizing ws x with
  | nil =>
    have hws : ws = [] := List.length_eq_zero_iff.mp hlen
    subst ws
    have he : Exec (B := .standard) w (.op (.copy (slot 0) (slot 0))) x x 1 := by
      convert (Exec.copy (B := Basis.standard) (w := w) (x := x)
        (d := slot 0) (s := slot 0)) using 1
      ext j <;> simp [Data.set]
    exact ⟨x, he, hr, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons i is ih =>
    cases ws with
    | nil => simp at hlen
    | cons v ws =>
      obtain ⟨z, hz, hrz, hout, hfz, hpz⟩ := popSlot_exec i x v (ws ++ vs) h2 hcap hr
      obtain ⟨y, hy, hry, hfy, hpy⟩ := ih ws z hrz (by simpa using hlen)
      refine ⟨y, ?_, hry, ?_, ?_⟩
      · simpa only [popSlots, List.length_cons, Nat.mul_add, Nat.mul_one,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz.seq hy
      · intro a ha
        exact (hfy a ha).trans (hfz a ha)
      · intro j hj
        rw [hpy j hj]
        apply restore_congr_at
        by_cases he : j = slot i
        · simpa only [he, Function.update_self] using hout
        · simpa only [Function.update_of_ne he] using hpz j hj he

/-- Pop all seven words into the record, in forward order, using the native dispatcher. -/
def popFrame : Code .standard 128 :=
  .seq (popSlot 0) (.seq (popSlot 1) (.seq (popSlot 2) (.seq (popSlot 3)
    (.seq (popSlot 4) (.seq (popSlot 5) (.seq (popSlot 6) (.op (.copy (slot 0) (slot 0)))))))))

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
  obtain ⟨y, hy, hry, hfy, hpy⟩ :=
    popSlots_exec [0, 1, 2, 3, 4, 5, 6] [a 0, a 1, a 2, a 3, a 4, a 5, a 6]
      x vs h2 hcap hr rfl
  refine ⟨y, hy, hry, ?_, hfy, ?_⟩
  · intro i
    have h := hpy (slot i) (Or.inl (by dsimp [slot]; omega))
    fin_cases i <;> simpa +decide [restore, slot] using h
  · intro j hj hj'
    have hne (i : Fin 7) : j ≠ slot i := by
      intro h
      have := congrArg Fin.val h
      dsimp [slot] at this
      omega
    simpa only [restore, Function.update_of_ne (hne 0), Function.update_of_ne (hne 1),
      Function.update_of_ne (hne 2), Function.update_of_ne (hne 3),
      Function.update_of_ne (hne 4), Function.update_of_ne (hne 5),
      Function.update_of_ne (hne 6)] using hpy j hj

/-- Record transfers do not inspect the physical word width. -/
theorem not_readsWidth : ¬pushFrame.ReadsWidth ∧ ¬popFrame.ReadsWidth := by decide

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
