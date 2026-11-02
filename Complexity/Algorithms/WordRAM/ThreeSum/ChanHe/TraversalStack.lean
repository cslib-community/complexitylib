/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Allocation
public import Complexity.Computability.WordRAM.Heap
import Mathlib.Tactic.FinCases

/-!
# Native stack calls for Chan–He traversal records

Traversal keeps a seven-word record in registers 64–70 and its word stack in
registers 96–104. Registers below 64 remain available to the complete modulus and node programs.
Each record contains fuel followed by three base/length pairs. The stack stores words, so a
record is pushed in reverse order and popped in forward order.

The word stack is a fixed nine-register program, `WordStack.program`, that dispatches on an
operation tag: push = 0, pop = 1, size = 2. It occupies a fixed consecutive memory block, with
its top at the highest live address; a pop leaves the old cell in place. Traversal's time bound
adds up exact instruction counts, so the two calls it makes, a push with spare capacity and a pop
from a nonempty stack, are proved instruction by instruction. The library's bounded stack is
`Stack.Memory`, which `Stack.Native` runs on the word RAM; this dispatcher is part of the
hand-stepped traversal and goes with it. Argument delivery and result copies here are actual
native instructions and are charged.

## Main definitions

* `WordStack.program`, `WordStack.prepare`: the dispatcher and its argument delivery.
* `WordStack.Rep`, `WordStack.footprint`: the top-first list representation and the reserved
  memory block.
* `slot`: the seven persistent traversal-record registers.
* `registers`: the nine-register stack dispatcher inside the 128-register controller.
* `pushSlot`: native argument delivery followed by the complete bounded-stack dispatcher.
* `popSlot`: native dispatch and result delivery to one traversal-record register.

## Main results

* `WordStack.exec_push`, `WordStack.exec_pop`: a push in seven instructions and a nonempty pop in
  eleven.
* `pushSlot_exec`: a nine-instruction push, with the exact stack, memory and register frames.
* `popSlot_exec`: a fourteen-instruction nonempty pop with the same exact frames.
* `pushFrame_exec`, `popFrame_exec`: complete seven-word record transfers in 64 and 99 instructions.

The native controller and its composition proofs are original.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 10.1][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

namespace WordStack

/-- Encoded operation tag: push = 0, pop = 1, size = 2. -/
abbrev tag : Fin 9 := 0
/-- Caller-supplied push value. -/
abbrev arg : Fin 9 := 1
/-- Persistent number of live entries. -/
abbrev len : Fin 9 := 2
/-- Persistent base address of the reserved region. -/
abbrev ptr : Fin 9 := 3
/-- Temporary cell address. -/
abbrev addr : Fin 9 := 4
/-- Returned value. -/
abbrev out : Fin 9 := 5
/-- Constant zero. -/
abbrev zero : Fin 9 := 6
/-- Constant one. -/
abbrev one : Fin 9 := 7
/-- Presence bit distinguishing `none` from a returned zero word. -/
abbrev present : Fin 9 := 8

/-- Fixed operation dispatch. No code is generated from an operation or its payload. -/
def program : Code .standard 9 := ram[
  zero ← #0; one ← #1;
  if tag = zero then [
    ⟪writeAt addr ptr len arg⟫; len ← len + one; out ← zero
  ] else [
    if tag = one then [
      if len = zero then [ out ← zero; present ← zero ] else [
        len ← len - one; ⟪readAt addr out ptr len⟫; present ← one
      ]
    ] else [ out ← len ]
  ] ]

/-- Deliver an operation tag and a push value. -/
def prepare (t v : ℕ) (x : Data 9) : Data 9 := (x.set tag t).set arg v

/-- Persistent register, bounded-word, and live array invariants. Cells above the live prefix
may contain old popped values; they are part of the reserved footprint. -/
structure Rep (w base capacity : ℕ) (vs : List ℕ) (x : Data 9) : Prop where
  bounded : x.Bounded w
  pointer : x.regs ptr = base
  length_eq : x.regs len = vs.length
  capacity_le : vs.length ≤ capacity
  contents : ∀ i : Fin vs.length, x.mem (base + i.val) = vs.reverse[i.val]

/-- Reserved memory footprint; it stays fixed through pushes and pops. -/
def footprint (base capacity : ℕ) : Finset ℕ :=
  (Block.mk base capacity).footprint

/-- A push with spare capacity writes the value above the top in seven instructions. -/
theorem exec_push {w base capacity : ℕ} (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    {vs : List ℕ} {x : Data 9} {v : ℕ} (hr : Rep w base capacity vs x)
    (hv : vs.length < capacity) (hw : Fits w v) :
    ∃ y, Exec w program (prepare 0 v x) y 7 ∧
      Rep w base capacity (v :: vs) y ∧ Modifies (footprint base capacity) x.mem y.mem := by
  have h1 : Fits w 1 := h2.of_le (by decide)
  have haddr : Fits w (base + vs.length) := hcap.of_le (by omega)
  have hinc : Fits w (vs.length + 1) := hcap.of_le (by omega)
  let y := (((((prepare 0 v x).set zero 0).set one 1).set
    addr (base + vs.length)).write (base + vs.length) v |>.set len (vs.length + 1)).set out 0
  have he : Exec w program (prepare 0 v x) y 7 := by
    ram_eval [program, prepare, writeAt, y, hr.pointer, hr.length_eq, h1, haddr, hinc]
  refine ⟨y, he, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact he.bounded ((hr.bounded.set (fits_zero w)).set hw)
  · simp +decide [y, Data.set, Data.write, prepare, hr.pointer]
  · simp +decide [y, Data.set, Data.write, prepare]
  · simpa using hv
  · intro i
    by_cases hi : i.val < vs.length
    · have hne : base + i.val ≠ base + vs.length := by omega
      simpa [y, Data.set, Data.write, prepare, List.reverse_cons, List.getElem_append, hi,
        Function.update_of_ne hne] using hr.contents ⟨i.val, hi⟩
    · have hi' : i.val = vs.length := by
        have := i.isLt
        simp only [List.length_cons] at this
        omega
      simp [y, Data.set, Data.write, prepare, List.reverse_cons, hi']
  · exact Modifies.write_of_owns ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hv _⟩ v

/-- A pop from a nonempty stack returns its top in eleven instructions and writes no memory. -/
theorem exec_pop {w base capacity : ℕ} (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    {vs : List ℕ} {x : Data 9} {v : ℕ} (hr : Rep w base capacity (v :: vs) x) :
    ∃ y, Exec w program (prepare 1 0 x) y 11 ∧ y.regs out = v ∧
      Rep w base capacity vs y ∧ Modifies (footprint base capacity) x.mem y.mem := by
  have h1 : Fits w 1 := h2.of_le (by decide)
  have hl : x.regs len = vs.length + 1 := hr.length_eq
  have hsub : Fits w vs.length := hcap.of_le (by have := hr.capacity_le; simp_all; omega)
  have ha : Fits w (base + vs.length) := hcap.of_le (by have := hr.capacity_le; simp_all; omega)
  have hread : x.mem (base + vs.length) = v := by
    have h := hr.contents ⟨vs.length, by simp⟩
    simpa [List.reverse_cons] using h
  let y := (((((prepare 1 0 x).set zero 0).set one 1).set
    len vs.length).set addr (base + vs.length)).set out v |>.set present 1
  have he : Exec w program (prepare 1 0 x) y 11 := by
    ram_eval [program, prepare, readAt, y, hr.pointer, hl, h1, ha, hsub, Nat.add_sub_cancel,
      Nat.add_eq_zero_iff, and_false, hread]
  refine ⟨y, he, by simp +decide [y, Data.set], ⟨?_, ?_, ?_, ?_, ?_⟩, Modifies.refl _ _⟩
  · exact he.bounded ((hr.bounded.set (h2.of_le (by decide))).set (fits_zero w))
  · simp +decide [y, Data.set, prepare, hr.pointer]
  · simp +decide [y, Data.set]
  · have := hr.capacity_le
    simp only [List.length_cons] at this
    omega
  · intro i
    have hi : i.val < (v :: vs).length := by
      simp only [List.length_cons]
      omega
    have h := hr.contents ⟨i.val, hi⟩
    simpa [y, Data.set, prepare, List.reverse_cons, List.getElem_append, i.isLt] using h

end WordStack

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
  let tag := registers WordStack.tag
  let arg := registers WordStack.arg
  let src := slot i
  .seq (ram[ tag ← #0; arg ← src ]) (WordStack.program.rename registers)

/-- Each native push includes both argument instructions, not a host-level stack operation.
Every register outside 96–104 and every memory cell outside the reserved stack is preserved. -/
theorem pushSlot_exec {w base capacity : ℕ} (i : Fin 7) (x : Data 128) (vs : List ℕ)
    (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    (hr : WordStack.Rep w base capacity vs (x.comap registers))
    (hw : Fits w (x.regs (slot i))) (hv : vs.length < capacity) :
    ∃ y, Exec w (pushSlot i) x y 9 ∧
      WordStack.Rep w base capacity (x.regs (slot i) :: vs) (y.comap registers) ∧
      Modifies (WordStack.footprint base capacity) x.mem y.mem ∧
      ∀ j, Outside j → y.regs j = x.regs j := by
  let q :=
    (x.set (registers WordStack.tag) 0).set (registers WordStack.arg) (x.regs (slot i))
  have hs : slot i ≠ registers WordStack.tag := outside_ne _ (Or.inl (by dsimp [slot]; omega)) _
  have hp : Exec (B := .standard) w
      (.seq (.op (.const (registers WordStack.tag) 0))
        (.op (.copy (registers WordStack.arg) (slot i)))) x q 2 := by
    ram_eval [q, hs]
  have hq : q.comap registers = WordStack.prepare 0 (x.regs (slot i)) (x.comap registers) := by
    ext j
    · fin_cases j <;>
        simp +decide [q, Data.comap, Data.set, registers, WordStack.prepare, WordStack.tag,
          WordStack.arg]
    · rfl
  obtain ⟨a, ha, hra, hframe⟩ := WordStack.exec_push h2 hcap hr hv hw
  have hcall : Exec w WordStack.program (q.comap registers) a 7 := by
    simpa only [hq] using ha
  let y := a.extend registers q
  refine ⟨y, ?_, ?_, hframe, ?_⟩
  · exact hp.seq (hcall.rename registers_injective)
  · simpa only [y, Data.comap_extend registers_injective] using hra
  · intro j hj
    rw [extend_outside a q j hj]
    simp only [q, Data.set_regs, Function.update_of_ne (outside_ne j hj WordStack.arg),
      Function.update_of_ne (outside_ne j hj WordStack.tag)]

private def pushSlots : List (Fin 7) → Code .standard 128
  | [] => .op (.copy (slot 0) (slot 0))
  | i :: is => .seq (pushSlot i) (pushSlots is)

private theorem pushSlots_exec {w base capacity : ℕ} (is : List (Fin 7)) (x : Data 128)
    (vs : List ℕ) (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    (hr : WordStack.Rep w base capacity vs (x.comap registers))
    (hw : ∀ i, Fits w (x.regs (slot i))) (hv : is.length + vs.length ≤ capacity) :
    ∃ y, Exec w (pushSlots is) x y (9 * is.length + 1) ∧
      WordStack.Rep w base capacity (is.reverse.map (fun i => x.regs (slot i)) ++ vs)
        (y.comap registers) ∧
      Modifies (WordStack.footprint base capacity) x.mem y.mem ∧
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
    (hr : WordStack.Rep w base capacity vs (x.comap registers))
    (hw : ∀ i, Fits w (x.regs (slot i))) (hv : 7 + vs.length ≤ capacity) :
    ∃ y, Exec w pushFrame x y 64 ∧
      WordStack.Rep w base capacity
        ([x.regs (slot 0), x.regs (slot 1), x.regs (slot 2), x.regs (slot 3),
          x.regs (slot 4), x.regs (slot 5), x.regs (slot 6)] ++ vs) (y.comap registers) ∧
      Modifies (WordStack.footprint base capacity) x.mem y.mem ∧
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
  let tag := registers WordStack.tag
  let arg := registers WordStack.arg
  .seq (ram[ tag ← #1; arg ← #0 ])
    (.seq (WordStack.program.rename registers)
      (.op (.copy (slot i) (registers WordStack.out))))

/-- A nonempty native pop includes both argument instructions and the actual result copy.
Only the selected record register, stack workspace and reserved stack memory may change. -/
theorem popSlot_exec {w base capacity : ℕ} (i : Fin 7) (x : Data 128) (v : ℕ) (vs : List ℕ)
    (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    (hr : WordStack.Rep w base capacity (v :: vs) (x.comap registers)) :
    ∃ y, Exec w (popSlot i) x y 14 ∧
      WordStack.Rep w base capacity vs (y.comap registers) ∧ y.regs (slot i) = v ∧
      Modifies (WordStack.footprint base capacity) x.mem y.mem ∧
      ∀ j, Outside j → j ≠ slot i → y.regs j = x.regs j := by
  let q := (x.set (registers WordStack.tag) 1).set (registers WordStack.arg) 0
  have h1 : Fits w 1 := h2.of_le (by decide)
  have hp : Exec (B := .standard) w
      (.seq (.op (.const (registers WordStack.tag) 1))
        (.op (.const (registers WordStack.arg) 0))) x q 2 := by
    ram_eval [q, h1]
  have hq : q.comap registers = WordStack.prepare 1 0 (x.comap registers) := by
    ext j
    · fin_cases j <;>
        simp +decide [q, Data.comap, Data.set, registers, WordStack.prepare, WordStack.tag,
          WordStack.arg]
    · rfl
  obtain ⟨a, ha, hout, hra, hframe⟩ := WordStack.exec_pop h2 hcap hr
  have hcall : Exec w WordStack.program (q.comap registers) a 11 := by
    simpa only [hq] using ha
  have hread : (a.extend registers q).regs (registers WordStack.out) = v := by
    change Function.extend registers a.regs q.regs (registers WordStack.out) = v
    rw [registers_injective.extend_apply, hout]
  let y := (a.extend registers q).set (slot i) v
  have hcopy : Exec (B := .standard) w
      (.op (.copy (slot i) (registers WordStack.out))) (a.extend registers q) y 1 := by
    simpa only [y, hread] using
      (Exec.copy (B := Basis.standard) (w := w) (x := a.extend registers q)
        (d := slot i) (s := registers WordStack.out))
  refine ⟨y, hp.seq ((hcall.rename registers_injective).seq hcopy), ?_, ?_, hframe, ?_⟩
  · simpa only [y, comap_set_slot, Data.comap_extend registers_injective, List.tail_cons] using hra
  · exact Function.update_self ..
  · intro j hj hji
    change Function.update (a.extend registers q).regs (slot i) v j = x.regs j
    rw [Function.update_of_ne hji, extend_outside a q j hj]
    simp only [q, Data.set_regs, Function.update_of_ne (outside_ne j hj WordStack.arg),
      Function.update_of_ne (outside_ne j hj WordStack.tag)]

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
    (hr : WordStack.Rep w base capacity (ws ++ vs) (x.comap registers))
    (hlen : ws.length = is.length) :
    ∃ y, Exec w (popSlots is) x y (14 * is.length + 1) ∧
      WordStack.Rep w base capacity vs (y.comap registers) ∧
      Modifies (WordStack.footprint base capacity) x.mem y.mem ∧
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
    (hr : WordStack.Rep w base capacity
      ([a 0, a 1, a 2, a 3, a 4, a 5, a 6] ++ vs) (x.comap registers)) :
    ∃ y, Exec w popFrame x y 99 ∧ WordStack.Rep w base capacity vs (y.comap registers) ∧
      (∀ i, y.regs (slot i) = a i) ∧
      Modifies (WordStack.footprint base capacity) x.mem y.mem ∧
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
