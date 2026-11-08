/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Allocation
public import Complexity.Computability.WordRAM.Heap
import Complexity.Computability.WordRAM.Call
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases
import Complexity.Tactic.Fits

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

Fixed-length records are transferred through the same dispatcher. Pushing visits a register bank
in reverse order; popping visits it in forward order, restoring the same record order. A final
self-copy on `idle` supplies the empty-bank case. The reserved stack memory may be dirty outside
its live prefix, and popped cells are not cleared.

## Main definitions

* `WordStack.program`, `WordStack.prepare`: the dispatcher and its argument delivery.
* `WordStack.Rep`, `WordStack.footprint`: the top-first list representation and the reserved
  memory block.
* `WordStack.pushRecord`, `WordStack.popRecord`: native transfers of a finite register bank.
* `slot`: the seven persistent traversal-record registers.
* `registers`: the nine-register stack dispatcher inside the 128-register controller.
* `pushFrame`, `popFrame`: the seven-word traversal-record transfers.

## Main results

* `WordStack.exec_push`, `WordStack.exec_pop`: a push in seven instructions and a nonempty pop in
  eleven.
* `WordStack.pushRecord_exec`, `WordStack.popRecord_exec`: push `n` words in `9 * n + 1`
  instructions and pop them in `14 * n + 1`, with exact stack, memory and register frames.
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
  have h1 : Fits w 1 := by fits
  have haddr : Fits w (base + vs.length) := by fits
  have hinc : Fits w (vs.length + 1) := by fits
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
  have h1 : Fits w 1 := by fits
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
  · exact he.bounded ((hr.bounded.set (by fits)).set (fits_zero w))
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

section Record

variable {r n : ℕ}

/-- Push a register bank in reverse order, leaving its words in forward order at the stack top.
The terminal self-copy preserves the entire state, including for a zero-length record. -/
def pushRecord (reg : Fin 9 → Fin r) :
    {n : ℕ} → (Fin n → Fin r) → Fin r → Code .standard r
  | 0, _, idle => .op (.copy idle idle)
  | n + 1, src, idle =>
    let tagReg := reg tag
    let argReg := reg arg
    let word := src (Fin.last n)
    .seq (.seq (ram[ tagReg ← #0; argReg ← word ]) (program.rename reg))
      (pushRecord reg (fun i : Fin n => src i.castSucc) idle)

/-- Pop into successive record registers, charging dispatch and delivery for every word.
The terminal self-copy supplies the zero-length case. -/
def popRecord (reg : Fin 9 → Fin r) :
    {n : ℕ} → (Fin n → Fin r) → Fin r → Code .standard r
  | 0, _, idle => .op (.copy idle idle)
  | n + 1, dst, idle =>
    let tagReg := reg tag
    let argReg := reg arg
    .seq (.seq (ram[ tagReg ← #1; argReg ← #0 ])
      (.seq (program.rename reg) (.op (.copy (dst 0) (reg out)))))
      (popRecord reg (fun i : Fin n => dst i.succ) idle)

/-- Pushing a fixed record does not inspect the physical word width. -/
theorem pushRecord_not_readsWidth (reg : Fin 9 → Fin r) (src : Fin n → Fin r) (idle : Fin r) :
    ¬(pushRecord reg src idle).ReadsWidth := by
  induction n <;>
    simp_all [pushRecord, Code.ReadsWidth, Op.ReadsWidth, program, Code.rename, Op.rename,
      writeAt, readAt, Op.bin]

/-- Popping a fixed record does not inspect the physical word width. -/
theorem popRecord_not_readsWidth (reg : Fin 9 → Fin r) (dst : Fin n → Fin r) (idle : Fin r) :
    ¬(popRecord reg dst idle).ReadsWidth := by
  induction n <;>
    simp_all [popRecord, Code.ReadsWidth, Op.ReadsWidth, program, Code.rename, Op.rename,
      writeAt, readAt, Op.bin]

/-- Push all record words with exact instruction cost, preserving caller registers and memory
outside the reserved stack. Repeated source registers are permitted. -/
theorem pushRecord_exec (reg : Fin 9 → Fin r) (hi : Function.Injective reg)
    (src : Fin n → Fin r) (idle : Fin r) (hd : ∀ i j, src i ≠ reg j)
    {w base capacity : ℕ} (x : Data r) (vs : List ℕ)
    (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    (hr : Rep w base capacity vs (x.comap reg))
    (hw : ∀ i, Fits w (x.regs (src i))) (hv : n + vs.length ≤ capacity) :
    ∃ y, Exec w (pushRecord reg src idle) x y (9 * n + 1) ∧
      Rep w base capacity (List.ofFn (fun i => x.regs (src i)) ++ vs) (y.comap reg) ∧
      Modifies (footprint base capacity) x.mem y.mem ∧
      ∀ j, (∀ i, j ≠ reg i) → y.regs j = x.regs j := by
  induction n generalizing x vs with
  | zero =>
    have he : Exec (B := .standard) w (.op (.copy idle idle)) x x 1 := by
      simpa [Data.set] using (Exec.copy (B := Basis.standard) (w := w) (x := x)
        (d := idle) (s := idle))
    exact ⟨x, he, hr, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ n ih =>
    let q := (x.set (reg tag) 0).set (reg arg) (x.regs (src (Fin.last n)))
    have hp : Exec (B := .standard) w
        (.seq (.op (.const (reg tag) 0)) (.op (.copy (reg arg) (src (Fin.last n))))) x q 2 := by
      ram_eval [q, hd (Fin.last n) tag]
    have hq : q.comap reg = prepare 0 (x.regs (src (Fin.last n))) (x.comap reg) := by
      simp only [q, prepare, Data.comap_set hi]
    obtain ⟨b, hb, hrb, hfb⟩ := exec_push h2 hcap hr (by omega) (hw (Fin.last n))
    have hcall : Exec w program (q.comap reg) b 7 := hq ▸ hb
    obtain ⟨z, hz, ⟨hrz, hfz⟩, hpz⟩ := Exec.rename_post hi
      (Q := fun b => Rep w base capacity (x.regs (src (Fin.last n)) :: vs) b ∧
        Modifies (footprint base capacity) x.mem b.mem) ⟨b, hcall, hrb, hfb⟩
    have hframe (j) (hj : ∀ i, j ≠ reg i) : z.regs j = x.regs j := by
      rw [hpz j (fun i => (hj i).symm)]
      simp only [q, Data.set_regs, Function.update_of_ne (hj arg), Function.update_of_ne (hj tag)]
    obtain ⟨y, hy, hry, hfy, hpy⟩ := ih (fun i : Fin n => src i.castSucc)
      (fun i => hd i.castSucc) z (x.regs (src (Fin.last n)) :: vs) hrz
      (fun i => by rw [hframe _ (hd i.castSucc)]; exact hw i.castSucc)
      (by simp only [List.length_cons]; omega)
    refine ⟨y, ?_, ?_, ?_, fun j hj => (hpy j hj).trans (hframe j hj)⟩
    · simpa [pushRecord, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (hp.seq hz).seq hy
    · have hslots : (fun i : Fin n => z.regs (src i.castSucc)) =
          fun i : Fin n => x.regs (src i.castSucc) := funext fun i => hframe _ (hd i.castSucc)
      simpa only [hslots, List.ofFn_succ', List.concat_eq_append, List.append_assoc,
        List.singleton_append] using hry
    · intro a ha
      exact (hfy a ha).trans (hfz a ha)

/-- Pop a complete record into distinct registers with exact cost. Memory outside the reserved
stack and registers outside the dispatcher and destination bank are preserved. -/
theorem popRecord_exec (reg : Fin 9 → Fin r) (hi : Function.Injective reg)
    (dst : Fin n → Fin r) (idle : Fin r) (hinj : Function.Injective dst)
    (hd : ∀ i j, dst i ≠ reg j) {w base capacity : ℕ}
    (x : Data r) (vs : List ℕ) (a : Fin n → ℕ) (h2 : Fits w 2)
    (hcap : Fits w (base + capacity))
    (hr : Rep w base capacity (List.ofFn a ++ vs) (x.comap reg)) :
    ∃ y, Exec w (popRecord reg dst idle) x y (14 * n + 1) ∧
      Rep w base capacity vs (y.comap reg) ∧ (∀ i, y.regs (dst i) = a i) ∧
      Modifies (footprint base capacity) x.mem y.mem ∧
      ∀ j, (∀ i, j ≠ reg i) → (∀ i, j ≠ dst i) → y.regs j = x.regs j := by
  induction n generalizing x with
  | zero =>
    have he : Exec (B := .standard) w (.op (.copy idle idle)) x x 1 := by
      simpa [Data.set] using (Exec.copy (B := Basis.standard) (w := w) (x := x)
        (d := idle) (s := idle))
    exact ⟨x, he, hr, fun i => Fin.elim0 i, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ n ih =>
    rw [List.ofFn_succ, List.cons_append] at hr
    let q := (x.set (reg tag) 1).set (reg arg) 0
    have h1 : Fits w 1 := by fits
    have hp : Exec (B := .standard) w
        (.seq (.op (.const (reg tag) 1)) (.op (.const (reg arg) 0))) x q 2 := by
      ram_eval [q, h1]
    have hq : q.comap reg = prepare 1 0 (x.comap reg) := by
      simp only [q, prepare, Data.comap_set hi]
    obtain ⟨b, hb, hout, hrb, hfb⟩ := exec_pop h2 hcap hr
    have hcall : Exec w program (q.comap reg) b 11 := hq ▸ hb
    obtain ⟨z, hz, ⟨hrz, hout, hfz⟩, hpz⟩ :=
      Exec.rename_post hi
        (Q := fun b => Rep w base capacity (List.ofFn (fun i : Fin n => a i.succ) ++ vs) b ∧
          b.regs out = a 0 ∧ Modifies (footprint base capacity) x.mem b.mem)
        ⟨b, hcall, hrb, hout, hfb⟩
    change z.regs (reg out) = a 0 at hout
    let copied := z.set (dst 0) (a 0)
    have hcopy : Exec (B := .standard) w (.op (.copy (dst 0) (reg out))) z copied 1 := by
      simpa only [copied, hout] using (Exec.copy (B := Basis.standard) (w := w) (x := z)
        (d := dst 0) (s := reg out))
    have hcopied : copied.comap reg = z.comap reg :=
      Data.comap_set_of_forall_ne z (dst 0) (a 0) (fun j => (hd 0 j).symm)
    obtain ⟨y, hy, hry, hya, hfy, hpy⟩ := ih (fun i : Fin n => dst i.succ)
      (fun i j h => Fin.succ_injective _ (hinj h)) (fun i => hd i.succ)
      copied (fun i => a i.succ) (by simpa only [hcopied, List.tail_cons] using hrz)
    refine ⟨y, ?_, hry, ?_, ?_, ?_⟩
    · simpa [popRecord, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (hp.seq (hz.seq hcopy)).seq hy
    · intro i
      refine Fin.cases ?_ (fun j => hya j) i
      rw [hpy (dst 0) (hd 0) (fun j h => Fin.succ_ne_zero j (hinj h).symm)]
      exact Function.update_self ..
    · intro a ha
      exact (hfy a ha).trans (hfz a ha)
    · intro j hj hdst
      rw [hpy j hj (fun i => hdst i.succ)]
      change Function.update z.regs (dst 0) (a 0) j = x.regs j
      rw [Function.update_of_ne (hdst 0), hpz j (fun i => (hj i).symm)]
      simp only [q, Data.set_regs, Function.update_of_ne (hj arg), Function.update_of_ne (hj tag)]

end Record

end WordStack

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

/-- Push all seven record words in reverse order through the record transfers. -/
def pushFrame : Code .standard 128 := WordStack.pushRecord registers slot (slot 0)

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
  obtain ⟨y, hy, hry, hfy, hpy⟩ :=
    WordStack.pushRecord_exec registers registers_injective slot (slot 0)
      slot_ne_registers x vs h2 hcap hr hw hv
  refine ⟨y, hy, ?_, hfy, fun j hj => hpy j (outside_ne j hj)⟩
  simpa [List.ofFn_succ, Fin.succ] using hry

/-- Pop all seven record words in forward order through the record transfers. -/
def popFrame : Code .standard 128 := WordStack.popRecord registers slot (slot 0)

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
  have hr' : WordStack.Rep w base capacity (List.ofFn a ++ vs) (x.comap registers) := by
    simpa [List.ofFn_succ, Fin.succ] using hr
  obtain ⟨y, hy, hry, hya, hfy, hpy⟩ :=
    WordStack.popRecord_exec registers registers_injective slot (slot 0)
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
  ⟨WordStack.pushRecord_not_readsWidth registers slot (slot 0),
    WordStack.popRecord_not_readsWidth registers slot (slot 0)⟩

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
