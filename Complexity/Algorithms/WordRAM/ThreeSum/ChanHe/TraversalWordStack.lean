/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Allocation
public import Complexity.Computability.WordRAM.Heap

/-!
# The word stack inside Chan–He traversal

Traversal keeps its pending records on a bounded stack of words, run by a fixed nine-register
program that dispatches on an operation tag: push = 0, pop = 1, size = 2. The stack occupies a
fixed consecutive memory block, with its top at the highest live address; a pop leaves the old
cell in place. This file proves the two calls traversal makes, a push with spare capacity and a
pop from a nonempty stack, instruction by instruction: traversal's time bound adds up their exact
instruction counts.

The library's bounded stack is `Stack.Memory`, which `Stack.Native` runs on the word RAM. This
dispatcher is part of the hand-stepped traversal and goes with it.

## Main definitions

* `tag`, `arg`, `len`, `ptr`, `addr`, `out`, `zero`, `one`, `present`: the nine registers.
* `program`: the fixed dispatcher.
* `prepare`: argument delivery of an operation tag and a value.
* `Rep`, `footprint`: the top-first list representation and the reserved memory block.

## Main results

* `exec_push`: a push in seven instructions.
* `exec_pop`: a nonempty pop in eleven instructions.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 10.1][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal.WordStack

open Cslib.WordRAM

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

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal.WordStack
