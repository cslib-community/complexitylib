/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Dynamic
public import Complexity.Algorithms.Lean.Queue

/-!
# A fixed-program bounded stack on the word RAM

A nine-register program dispatches push, pop, and size operations using an encoded operation
tag. The stack occupies a fixed consecutive memory block, with its top at the highest live
address. A pop from an empty stack returns `none`; other pops return a word and decrease the
length without clearing the old cell. Push requires spare capacity and a fitting value.

The semantic certificate is independent of the separate instruction certificate. Every call
includes its final halt; argument delivery and the initial reserved block are calling-convention
assumptions. This realizes a bounded restriction of the mathematical stack, not its unrestricted
interface. A native instruction theorem for an arbitrary free-monad client still excludes
execution of the client's pure controller.

## Main definitions

* `spec`: the mathematical stack with explicit bounded-operation admissibility.
* `tag`, `arg`, `len`, `ptr`, `addr`, `out`, `zero`, `one`, `present`: named registers of the
  nine-register dispatcher.
* `program`, `implementation`, `bodyCost`: fixed dispatch program, dynamic calling convention, and
  per-operation instruction count.
* `Rep`, `footprint`, `initial`: top-first list representation, reserved memory block, and initial
  calling-convention state.
* `certificate`: semantic realization over native word-RAM traces.

## Main results

* `execute`: actual per-operation execution, representation, and frame guarantee.
* `instruction_bound`: at most twelve instructions per admissible operation.
* `initial_rep`: a concrete empty represented stack.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 10.1][CLRS2009]

The abstract stack interface is shared with `Cslib.Algorithms.Lean.Queue`. Array indexing and
machine execution reuse the checked `WordRAM.Allocation` and `WordRAM.Structured` substrate.
-/

@[expose] public section

namespace Cslib.WordRAM.Stack

open Cslib.Algorithms.Lean.Queue

/-- A fixed-capacity restriction of the same mathematical stack interface. -/
abbrev spec (w capacity : ℕ) : Stateful.Spec :=
  { stack ℕ with
    valid := fun vs o => match o with
      | .push v => vs.length < capacity ∧ Fits w v
      | .pop | .size => True }

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

/-- Calling convention for the fixed dispatch program. Answers inspect only output registers. -/
def implementation (w capacity : ℕ) : DynamicProgram (spec w capacity) 9 where
  code := program
  output := out
  input i := i == tag || i == arg
  encode o i := if i = tag then
      match o with | .push _ => 0 | .pop => 1 | .size => 2
    else match o with | .push v => v | .pop | .size => 0
  decode o regs := match o with
    | .push _ => some ()
    | .pop => some (if regs present = 0 then none else some (regs out))
    | .size => some (regs out)

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

/-- Encoded input registers fit in a `w`-bit word for every admissible stack operation. -/
theorem arguments_fit {w capacity : ℕ} (h2 : Fits w 2) {vs : List ℕ} (o : StackOp ℕ)
    (hv : (spec w capacity).valid vs o) (i : Fin 9) :
    Fits w ((implementation w capacity).encode o i) := by
  cases o with
  | push v =>
    change Fits w (if i = tag then 0 else v)
    split <;> first | exact fits_zero w | exact hv.2
  | pop =>
    change Fits w (if i = tag then 1 else 0)
    split
    · exact h2.of_le (by decide)
    · exact fits_zero w
  | size =>
    change Fits w (if i = tag then 2 else 0)
    split <;> first | exact h2 | exact fits_zero w

private theorem prepare_bounded {w capacity : ℕ} (h2 : Fits w 2)
    {vs : List ℕ} {x : Data 9} {o : StackOp ℕ}
    (hx : x.Bounded w) (hv : (spec w capacity).valid vs o) :
    ((implementation w capacity).prepare o x).Bounded w :=
  (implementation w capacity).prepare_bounded hx (fun i _ => arguments_fit h2 o hv i)

/-- Actual instructions excluding the final halt. -/
def bodyCost (vs : List ℕ) : StackOp ℕ → ℕ
  | .push _ => 7
  | .pop => if vs = [] then 8 else 11
  | .size => 7

private theorem execute_push {w base capacity : ℕ} (h2 : Fits w 2)
    (hcap : Fits w (base + capacity)) {vs : List ℕ} {x : Data 9}
    (hr : Rep w base capacity vs x) (v : ℕ) (hv : vs.length < capacity) (hw : Fits w v) :
    ∃ y, Exec w program ((implementation w capacity).prepare (.push v) x) y 7 ∧
      Rep w base capacity (v :: vs) y ∧ Modifies (footprint base capacity) x.mem y.mem := by
  have h1 : Fits w 1 := h2.of_le (by decide)
  have haddr : Fits w (base + vs.length) := hcap.of_le (by omega)
  have hinc : Fits w (vs.length + 1) := hcap.of_le (by omega)
  let y := ((((((implementation w capacity).prepare (.push v) x).set zero 0).set one 1).set
    addr (base + vs.length)).write (base + vs.length) v |>.set len (vs.length + 1)).set out 0
  have he : Exec w program ((implementation w capacity).prepare (.push v) x) y 7 := by
    ram_eval [program, implementation, DynamicProgram.prepare, writeAt, y,
      hr.pointer, hr.length_eq, h1, haddr, hinc]
  refine ⟨y, he, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact he.bounded (prepare_bounded (capacity := capacity) (vs := vs)
        (o := .push v) h2 hr.bounded ⟨hv, hw⟩)
    · simp +decide [y, Data.set, Data.write, implementation, DynamicProgram.prepare, hr.pointer]
    · simp +decide [y, Data.set, Data.write, implementation, DynamicProgram.prepare]
    · simpa using hv
    · intro i
      by_cases hi : i.val < vs.length
      · have hne : base + i.val ≠ base + vs.length := by omega
        simpa [y, Data.set, Data.write, implementation, DynamicProgram.prepare,
          List.reverse_cons, List.getElem_append, hi, Function.update_of_ne hne] using
          hr.contents ⟨i.val, hi⟩
      · have hi' : i.val = vs.length := by
          have := i.isLt
          simp only [List.length_cons] at this
          omega
        simp [y, Data.set, Data.write, implementation, DynamicProgram.prepare,
          List.reverse_cons, hi']
  · exact Modifies.write_of_owns ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hv _⟩ v

private theorem execute_pop_cons {w base capacity : ℕ} (h2 : Fits w 2)
    (hcap : Fits w (base + capacity)) {vs : List ℕ} {x : Data 9} {v : ℕ}
    (hr : Rep w base capacity (v :: vs) x) :
    ∃ y, Exec w program ((implementation w capacity).prepare .pop x) y 11 ∧
      (implementation w capacity).decode .pop y.regs = some (some v) ∧
      Rep w base capacity vs y ∧ Modifies (footprint base capacity) x.mem y.mem := by
  have h1 : Fits w 1 := h2.of_le (by decide)
  have hl : x.regs len = vs.length + 1 := hr.length_eq
  have hsub : Fits w vs.length := hcap.of_le (by have := hr.capacity_le; simp_all; omega)
  have ha : Fits w (base + vs.length) := hcap.of_le (by have := hr.capacity_le; simp_all; omega)
  have hread : x.mem (base + vs.length) = v := by
    have h := hr.contents ⟨vs.length, by simp⟩
    simpa [List.reverse_cons] using h
  let y := ((((((implementation w capacity).prepare .pop x).set zero 0).set one 1).set
    len vs.length).set addr (base + vs.length)).set out v |>.set present 1
  have he : Exec w program ((implementation w capacity).prepare .pop x) y 11 := by
    ram_eval [program, implementation, DynamicProgram.prepare, readAt, y,
      hr.pointer, hl, h1, ha, hsub, Nat.add_sub_cancel, Nat.add_eq_zero_iff, and_false, hread]
  refine ⟨y, he, ?_, ?_, Modifies.refl _ _⟩
  · simp +decide [implementation, y, Data.set]
  · refine ⟨he.bounded (prepare_bounded (vs := v :: vs) h2 hr.bounded trivial), ?_, ?_, ?_, ?_⟩
    · simp +decide [y, Data.set, implementation, DynamicProgram.prepare, hr.pointer]
    · simp +decide [y, Data.set]
    · have := hr.capacity_le
      simp only [List.length_cons] at this
      omega
    · intro i
      have hi : i.val < (v :: vs).length := by
        simp only [List.length_cons]
        omega
      have h := hr.contents ⟨i.val, hi⟩
      simpa [y, Data.set, DynamicProgram.prepare, List.reverse_cons,
        List.getElem_append, i.isLt] using h

private theorem execute_pop_nil {w base capacity : ℕ} (h2 : Fits w 2)
    {x : Data 9} (hr : Rep w base capacity [] x) :
    ∃ y, Exec w program ((implementation w capacity).prepare .pop x) y 8 ∧
      (implementation w capacity).decode .pop y.regs = some none ∧
      Rep w base capacity [] y ∧ Modifies (footprint base capacity) x.mem y.mem := by
  have h1 : Fits w 1 := h2.of_le (by decide)
  have hl : x.regs len = 0 := hr.length_eq
  let y := ((((implementation w capacity).prepare .pop x).set zero 0).set one 1).set
    out 0 |>.set present 0
  have he : Exec w program ((implementation w capacity).prepare .pop x) y 8 := by
    ram_eval [program, implementation, DynamicProgram.prepare, y, hl, h1]
  refine ⟨y, he, ?_, ?_, Modifies.refl _ _⟩
  · simp +decide [implementation, y, Data.set]
  · refine ⟨he.bounded (prepare_bounded (vs := []) h2 hr.bounded trivial), ?_, ?_,
      Nat.zero_le _, fun i => Fin.elim0 i⟩
    · simp +decide [y, Data.set, implementation, DynamicProgram.prepare, hr.pointer]
    · simp +decide [y, Data.set, implementation, DynamicProgram.prepare, hl]

private theorem execute_size {w base capacity : ℕ} (h2 : Fits w 2)
    {vs : List ℕ} {x : Data 9} (hr : Rep w base capacity vs x) :
    ∃ y, Exec w program ((implementation w capacity).prepare .size x) y 7 ∧
      (implementation w capacity).decode .size y.regs = some vs.length ∧
      Rep w base capacity vs y ∧ Modifies (footprint base capacity) x.mem y.mem := by
  have h1 : Fits w 1 := h2.of_le (by decide)
  let y := (((implementation w capacity).prepare .size x).set zero 0).set one 1 |>.set
    out vs.length
  have he : Exec w program ((implementation w capacity).prepare .size x) y 7 := by
    ram_eval [program, implementation, DynamicProgram.prepare, y, hr.length_eq, h1]
  refine ⟨y, he, ?_, ?_, Modifies.refl _ _⟩
  · simp [implementation, y, Data.set]
  · refine ⟨he.bounded (prepare_bounded (vs := vs) h2 hr.bounded trivial), ?_, ?_,
      hr.capacity_le, hr.contents⟩
    · simp +decide [y, Data.set, implementation, DynamicProgram.prepare, hr.pointer]
    · simp +decide [y, Data.set, implementation, DynamicProgram.prepare, hr.length_eq]

/-- Every admissible operation executes the fixed dispatcher with an exact instruction count,
returns the specified answer, and preserves memory outside the reserved region. -/
theorem execute {w base capacity : ℕ} (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    {vs : List ℕ} {x : Data 9} (hr : Rep w base capacity vs x) (o : StackOp ℕ)
    (hv : (spec w capacity).valid vs o) :
    ∃ y, Exec w program ((implementation w capacity).prepare o x) y (bodyCost vs o) ∧
      (implementation w capacity).decode o y.regs = some ((spec w capacity).step vs o).2 ∧
      Rep w base capacity ((spec w capacity).step vs o).1 y ∧
      Modifies (footprint base capacity) x.mem y.mem := by
  cases o with
  | push v =>
    obtain ⟨y, he, hr, hf⟩ := execute_push h2 hcap hr v hv.1 hv.2
    exact ⟨y, he, rfl, hr, hf⟩
  | pop =>
    cases vs with
    | nil => exact execute_pop_nil h2 hr
    | cons v vs =>
      simpa only [bodyCost, List.cons_ne_nil, ↓reduceIte, List.head?_cons, List.tail_cons] using
        execute_pop_cons h2 hcap hr
  | size => exact execute_size h2 hr

/-- Semantic realization of the bounded stack, independently of its performance theorem. -/
def certificate {w base capacity : ℕ} (h2 : Fits w 2) (hcap : Fits w (base + capacity)) :
    DynamicCertificate (implementation w capacity) w where
  rep := Rep w base capacity
  bounded h := h.bounded
  arguments_fit o hv i _ := arguments_fit h2 o hv i
  execute o hr hv := by
    obtain ⟨y, he, ha, hr, _⟩ := Stack.execute h2 hcap hr o hv
    exact ⟨y, _, he, ha, hr⟩

/-- Actual instruction count, including dispatch and the final halt, for every native call. -/
theorem instructions_eq {w base capacity : ℕ} (h2 : Fits w 2)
    (hcap : Fits w (base + capacity)) {vs : List ℕ} {x y : Data 9} {o : StackOp ℕ}
    {a : (spec w capacity).Result o} {trace : DynamicProgram.OperationTrace}
    (hr : Rep w base capacity vs x) (hv : (spec w capacity).valid vs o)
    (he : (implementation w capacity).ExecOp w x o a y trace) :
    trace.instructions = bodyCost vs o + 1 := by
  obtain ⟨z, hz, _, _, _⟩ := execute h2 hcap hr o hv
  exact (he.eq_of_exec hz).2

/-- Every admissible call has a separate worst-case bound of twelve native instructions. -/
theorem instruction_bound {w base capacity : ℕ} (h2 : Fits w 2)
    (hcap : Fits w (base + capacity)) :
    Stateful.Bound (certificate h2 hcap).realization
      DynamicProgram.OperationTrace.instructions (fun _ _ => 12) :=
  (certificate h2 hcap).instruction_bound_const 12 fun o hr hv => by
    obtain ⟨y, he, _⟩ := execute h2 hcap hr o hv
    refine ⟨y, bodyCost _ o, he, ?_⟩
    cases o with
    | push | size => simp +decide [bodyCost]
    | pop => dsimp only [bodyCost]; split <;> decide

/-- Every concrete call preserves all memory outside the same reserved stack block. -/
theorem modifies {w base capacity : ℕ} (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    {vs : List ℕ} {x y : Data 9} {o : StackOp ℕ}
    {a : (spec w capacity).Result o} {trace : DynamicProgram.OperationTrace}
    (hr : Rep w base capacity vs x) (hv : (spec w capacity).valid vs o)
    (he : (implementation w capacity).ExecOp w x o a y trace) :
    Modifies (footprint base capacity) x.mem y.mem :=
  (certificate h2 hcap).modifies_of_execute
    (fun o hr' hv' => let ⟨z, hz, _, _, hf⟩ := execute h2 hcap hr' o hv'; ⟨z, _, hz, hf⟩)
    hr hv he

/-- The machine stack preserves any disjoint heap representation. -/
theorem frame {w base capacity : ℕ} (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    {vs : List ℕ} {x y : Data 9} {o : StackOp ℕ}
    {a : (spec w capacity).Result o} {trace : DynamicProgram.OperationTrace}
    (hr : Rep w base capacity vs x) (hv : (spec w capacity).valid vs o)
    (he : (implementation w capacity).ExecOp w x o a y trace)
    {Q : HeapAssertion} (hQ : Q.holds x.mem)
    (hd : Disjoint Q.footprint (footprint base capacity)) : Q.holds y.mem :=
  HeapAssertion.frame hQ hd (modifies h2 hcap hr hv he)

/-- An empty reserved block, with all memory zero and the persistent pointer installed.
This is a calling-convention initial state, not an uncharged allocation instruction. -/
def initial (base : ℕ) : Data 9 where
  regs i := if i = ptr then base else 0
  mem _ := 0

/-- The initial representation is inhabited for every fitting reserved block. -/
theorem initial_rep {w base capacity : ℕ} (hcap : Fits w (base + capacity)) :
    Rep w base capacity [] (initial base) := by
  refine ⟨⟨fun i => ?_, fun _ => fits_zero w⟩, ?_, ?_, Nat.zero_le _, fun i => Fin.elim0 i⟩
  · change Fits w (if i = ptr then base else 0)
    split
    · exact hcap.of_le (Nat.le_add_right _ _)
    · exact fits_zero w
  · simp [initial]
  · simp +decide [initial]

/-- One-operation realization and an independent resource certificate compose across arbitrary
admissible adaptive clients. The client controller itself is external to the machine code. -/
theorem run_client {w base capacity : ℕ} (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    {α : Type} (p : (spec w capacity).Client α) {vs : List ℕ} {x : Data 9}
    (hr : Rep w base capacity vs x)
    (hv : (spec w capacity).ValidHistory vs ((spec w capacity).runClient vs p).2.2) :
    ∃ y traces, Stateful.Executes ((implementation w capacity).ExecOp w) p x
        ((spec w capacity).runClient vs p).1 y traces ∧
      Rep w base capacity ((spec w capacity).runClient vs p).2.1 y ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces ≤
        ((spec w capacity).runClient vs p).2.2.length * 12 :=
  (certificate h2 hcap).run_client_const (instruction_bound h2 hcap) p hr hv

end Cslib.WordRAM.Stack
