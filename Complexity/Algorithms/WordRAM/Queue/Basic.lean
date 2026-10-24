/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Queue.Model
public import Complexity.Computability.WordRAM.Dynamic

/-!
# Two stacks implementing a queue in shared RAM

Two disjoint reserved blocks hold bottom-first stack arrays. Enqueue pushes onto the rear;
dequeue transfers the rear into an empty front before popping. All address arithmetic, memory
accesses, loop tests and operation dispatch are machine instructions. Empty live prefixes do
not require clearing the reserved memory.

## Main definitions

* `tag`, `arg`, `frontLen`, `frontBase`, `backLen`, `backBase`, `addr`, `out`, `present`, `zero`,
  `one`: register allocation for the two-stack queue.
* `Rep`, `footprint`: the bounded shared-memory representation of the two top-first lists and its
  reserved memory footprint.
* `enqueue`, `move`, `transfer`, `pop`, `dequeue`, `program`, `bodyCost`: structured queue
  operations, the fixed operation dispatcher, and its per-operation instruction count.
* `implementation`: its argument and result conventions.
* `initializeCode`: six charged writes installing an empty representation.

## Main results

* `execute`: exact instruction execution, observations, representation and memory frame.
* `initialize_exec`: initialization from arbitrary bounded machine data without clearing memory.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Queue

open Cslib.Algorithms.Lean.Queue

/-- Operation tag: enqueue zero, dequeue one. -/
abbrev tag : Fin 11 := 0
/-- Enqueued word. -/
abbrev arg : Fin 11 := 1
/-- Front stack length. -/
abbrev frontLen : Fin 11 := 2
/-- Front block base. -/
abbrev frontBase : Fin 11 := 3
/-- Rear stack length. -/
abbrev backLen : Fin 11 := 4
/-- Rear block base. -/
abbrev backBase : Fin 11 := 5
/-- Temporary address. -/
abbrev addr : Fin 11 := 6
/-- Returned word. -/
abbrev out : Fin 11 := 7
/-- Returned presence flag. -/
abbrev present : Fin 11 := 8
/-- Constant zero. -/
abbrev zero : Fin 11 := 9
/-- Constant one. -/
abbrev one : Fin 11 := 10

/-- Both stack arrays live in one bounded memory, with one common capacity bound. -/
structure Rep (w base capacity : ℕ) (front back : List ℕ) (x : Data 11) : Prop where
  bounded : x.Bounded w
  frontBase_eq : x.regs frontBase = base
  backBase_eq : x.regs backBase = base + capacity
  frontLen_eq : x.regs frontLen = front.length
  backLen_eq : x.regs backLen = back.length
  zero_eq : x.regs zero = 0
  one_eq : x.regs one = 1
  size_le : front.length + back.length ≤ capacity
  front_contents : ∀ i : Fin front.length, x.mem (base + i.val) = front.reverse[i.val]
  back_contents : ∀ i : Fin back.length,
    x.mem (base + capacity + i.val) = back.reverse[i.val]

/-- The fixed reserved region, including currently unused cells. -/
def footprint (base capacity : ℕ) : Finset ℕ :=
  (Block.mk base (2 * capacity)).footprint

/-- Enqueue writes the next rear cell and advances the rear length. -/
def enqueue : Code .standard 11 := ram[
  addr ← backBase + backLen; *addr ← arg; backLen ← backLen + one; out ← zero ]

/-- Move the top rear word onto the front stack. -/
def move : Code .standard 11 := ram[
  backLen ← backLen - one; addr ← backBase + backLen; out ← *addr;
  addr ← frontBase + frontLen; *addr ← out; frontLen ← frontLen + one ]

/-- Reverse the rear stack onto the front, testing each iteration on machine registers. -/
def transfer : Code .standard 11 := ram[while zero < backLen do [ ⟪move⟫ ]]

/-- Pop the front, distinguishing the empty queue from a returned zero. -/
def pop : Code .standard 11 := ram[
  if frontLen = zero then [ out ← zero; present ← zero ] else [
    frontLen ← frontLen - one; addr ← frontBase + frontLen; out ← *addr; present ← one ] ]

/-- Transfer only when the front is empty. -/
def dequeue : Code .standard 11 := ram[
  if frontLen = zero then [ ⟪transfer⟫; ⟪pop⟫ ] else [ ⟪pop⟫ ] ]

/-- One fixed dispatcher, independent of queue contents, capacity, and operation arguments. -/
def program : Code .standard 11 := ram[
  if tag = zero then [ ⟪enqueue⟫ ] else [ ⟪dequeue⟫ ] ]

/-- Register calling convention for the fixed queue dispatcher. -/
def implementation (w capacity : ℕ) : DynamicProgram (spec w capacity) 11 where
  code := program
  output := out
  input i := i == tag || i == arg
  encode o i := if i = tag then
    match o with | .enqueue _ => 0 | .dequeue => 1
    else match o with | .enqueue v => v | .dequeue => 0
  decode o regs := match o with
    | .enqueue _ => some ()
    | .dequeue => some (if regs present = 0 then none else some (regs out))

/-- Enqueue body correctness with an exact four-instruction execution. -/
private theorem enqueue_exec {w base capacity v : ℕ} {front back : List ℕ} {x : Data 11}
    (hc : Fits w (base + 2 * capacity)) (hr : Rep w base capacity front back x)
    (hs : front.length + back.length < capacity) (hv : x.regs arg = v) :
    ∃ y, Exec w enqueue x y 4 ∧ Rep w base capacity front (v :: back) y ∧
      Modifies (footprint base capacity) x.mem y.mem := by
  have ha : Fits w (base + capacity + back.length) := hc.of_le (by omega)
  have hl : Fits w (back.length + 1) := hc.of_le (by omega)
  let y := ((x.set addr (base + capacity + back.length)).write
    (base + capacity + back.length) v).set backLen (back.length + 1) |>.set out 0
  have he : Exec w enqueue x y 4 := by
    ram_eval [enqueue, y, hr.backBase_eq, hr.backLen_eq, hr.one_eq, hr.zero_eq, hv, ha, hl]
  refine ⟨y, he, ⟨he.bounded hr.bounded, ?_, ?_, ?_, ?_, ?_, ?_,
    by simp only [List.length_cons]; omega, ?_, ?_⟩, ?_⟩
  · simpa +decide [y, Data.set, Data.write] using hr.frontBase_eq
  · simpa +decide [y, Data.set, Data.write] using hr.backBase_eq
  · simpa +decide [y, Data.set, Data.write] using hr.frontLen_eq
  · simp +decide [y, Data.set, Data.write]
  · simpa +decide [y, Data.set, Data.write] using hr.zero_eq
  · simpa +decide [y, Data.set, Data.write] using hr.one_eq
  · intro i
    have hne : base + i.val ≠ base + capacity + back.length := by have := i.isLt; omega
    simpa [y, Data.set, Data.write, Function.update_of_ne hne] using hr.front_contents i
  · intro i
    by_cases hi : i.val < back.length
    · have hne : base + capacity + i.val ≠ base + capacity + back.length := by omega
      simpa [y, Data.set, Data.write, List.reverse_cons, List.getElem_append, hi,
        Function.update_of_ne hne] using hr.back_contents ⟨i.val, hi⟩
    · have hi' : i.val = back.length := by
        have := i.isLt
        simp only [List.length_cons] at this
        omega
      simp [y, Data.set, Data.write, List.reverse_cons, hi']
  · exact Modifies.write_of_owns ⟨by omega, by omega⟩ v

/-- A rear-to-front move performs six instructions and preserves the reserved-region frame. -/
private theorem move_exec {w base capacity v : ℕ} {front back : List ℕ} {x : Data 11}
    (hc : Fits w (base + 2 * capacity)) (hr : Rep w base capacity front (v :: back) x) :
    ∃ y, Exec w move x y 6 ∧ Rep w base capacity (v :: front) back y ∧
      Modifies (footprint base capacity) x.mem y.mem := by
  have hs := hr.size_le
  simp only [List.length_cons] at hs
  have hl : x.regs backLen = back.length + 1 := hr.backLen_eq
  have hb : Fits w back.length := hc.of_le (by omega)
  have ha : Fits w (base + capacity + back.length) := hc.of_le (by omega)
  have hf : Fits w (base + front.length) := hc.of_le (by omega)
  have hi : Fits w (front.length + 1) := hc.of_le (by omega)
  have hread : x.mem (base + capacity + back.length) = v := by
    simpa [List.reverse_cons] using hr.back_contents ⟨back.length, by simp⟩
  let y := (((((x.set backLen back.length).set addr (base + capacity + back.length)).set
    out v).set addr (base + front.length)).write (base + front.length) v).set
    frontLen (front.length + 1)
  have he : Exec w move x y 6 := by
    ram_eval [move, y, hr.frontBase_eq, hr.backBase_eq, hr.frontLen_eq, hl, hr.one_eq,
      Nat.add_sub_cancel, hb, ha, hf, hi, hread]
  refine ⟨y, he, ⟨he.bounded hr.bounded, ?_, ?_, ?_, ?_, ?_, ?_,
    by simp only [List.length_cons]; omega, ?_, ?_⟩, ?_⟩
  · simpa +decide [y, Data.set, Data.write] using hr.frontBase_eq
  · simpa +decide [y, Data.set, Data.write] using hr.backBase_eq
  · simp +decide [y, Data.set, Data.write]
  · simp +decide [y, Data.set, Data.write]
  · simpa +decide [y, Data.set, Data.write] using hr.zero_eq
  · simpa +decide [y, Data.set, Data.write] using hr.one_eq
  · intro i
    by_cases hij : i.val < front.length
    · have hne : base + i.val ≠ base + front.length := by omega
      simpa [y, Data.set, Data.write, List.reverse_cons, List.getElem_append, hij,
        Function.update_of_ne hne] using hr.front_contents ⟨i.val, hij⟩
    · have hi' : i.val = front.length := by
        have := i.isLt
        simp only [List.length_cons] at this
        omega
      simp [y, Data.set, Data.write, List.reverse_cons, hi']
  · intro i
    have hne : base + capacity + i.val ≠ base + front.length := by omega
    have hr' := hr.back_contents ⟨i.val, by simp⟩
    simpa [y, Data.set, Data.write, List.reverse_cons, List.getElem_append, i.isLt,
      Function.update_of_ne hne] using hr'
  · exact Modifies.write_of_owns ⟨by omega, by omega⟩ v

/-- Transfer costs eight instructions per moved word and two instructions to exit the loop. -/
private theorem transfer_exec {w base capacity : ℕ} {front back : List ℕ} {x : Data 11}
    (hc : Fits w (base + 2 * capacity)) (hr : Rep w base capacity front back x) :
    ∃ y, Exec w transfer x y (8 * back.length + 2) ∧
      Rep w base capacity (back.reverse ++ front) [] y ∧
      Modifies (footprint base capacity) x.mem y.mem := by
  induction back generalizing front x with
  | nil =>
    refine ⟨x, ?_, hr, Modifies.refl _ _⟩
    apply Exec.loop_exit
    change ¬x.regs zero < x.regs backLen
    rw [hr.zero_eq, hr.backLen_eq]
    simp
  | cons v back ih =>
    obtain ⟨y, he, hy, hf⟩ := move_exec hc hr
    obtain ⟨z, hz, hrz, hfz⟩ := ih hy
    refine ⟨z, ?_, ?_, ?_⟩
    · have he' := Exec.loop_iter (c := Cond.lt zero backLen) (by
        change x.regs zero < x.regs backLen
        rw [hr.zero_eq, hr.backLen_eq]
        simp) he hz
      convert he' using 1
      · rfl
      · simp only [List.length_cons]
        omega
    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hrz
    · exact fun a ha => (hfz a ha).trans (hf a ha)

/-- Front-pop execution counts include the empty/nonempty branch and distinguish returned zero. -/
private theorem pop_exec {w base capacity : ℕ} {front back : List ℕ} {x : Data 11}
    (hc : Fits w (base + 2 * capacity)) (hr : Rep w base capacity front back x) :
    ∃ y, Exec w pop x y (if front = [] then 3 else 6) ∧
      Rep w base capacity front.tail back y ∧
      (if y.regs present = 0 then none else some (y.regs out)) = front.head? ∧
      y.mem = x.mem := by
  cases front with
  | nil =>
    let y := (x.set out 0).set present 0
    have he : Exec w pop x y 3 := by
      ram_eval [pop, y, hr.frontLen_eq, hr.zero_eq]
    refine ⟨y, he, ⟨he.bounded hr.bounded, ?_, ?_, ?_, ?_, ?_, ?_, hr.size_le,
      fun i => Fin.elim0 i, hr.back_contents⟩, ?_, rfl⟩
    · simpa +decide [y, Data.set] using hr.frontBase_eq
    · simpa +decide [y, Data.set] using hr.backBase_eq
    · simpa +decide [y, Data.set] using hr.frontLen_eq
    · simpa +decide [y, Data.set] using hr.backLen_eq
    · simpa +decide [y, Data.set] using hr.zero_eq
    · simpa +decide [y, Data.set] using hr.one_eq
    · simp [y, Data.set]
  | cons v front =>
    have hs := hr.size_le
    simp only [List.length_cons] at hs
    have hl : x.regs frontLen = front.length + 1 := hr.frontLen_eq
    have hf : Fits w front.length := hc.of_le (by omega)
    have ha : Fits w (base + front.length) := hc.of_le (by omega)
    have hread : x.mem (base + front.length) = v := by
      simpa [List.reverse_cons] using hr.front_contents ⟨front.length, by simp⟩
    let y := (((x.set frontLen front.length).set addr (base + front.length)).set out v).set
      present 1
    have he : Exec w pop x y 6 := by
      ram_eval [pop, y, hl, hr.zero_eq, hr.one_eq, hr.frontBase_eq, hread, hf, ha,
        Nat.add_sub_cancel, Nat.add_eq_zero_iff, and_false]
    refine ⟨y, he, ⟨he.bounded hr.bounded, ?_, ?_, ?_, ?_, ?_, ?_,
      by change front.length + back.length ≤ capacity; omega,
      ?_, hr.back_contents⟩, ?_, rfl⟩
    · simpa +decide [y, Data.set] using hr.frontBase_eq
    · simpa +decide [y, Data.set] using hr.backBase_eq
    · simp +decide [y, Data.set]
    · simpa +decide [y, Data.set] using hr.backLen_eq
    · simpa +decide [y, Data.set] using hr.zero_eq
    · simpa +decide [y, Data.set] using hr.one_eq
    · intro i
      have hij : i.val < front.length := i.isLt
      have hr' := hr.front_contents ⟨i.val, by simp only [List.length_cons]; omega⟩
      simpa [y, Data.set, List.reverse_cons, List.getElem_append, hij] using hr'
    · simp +decide [y, Data.set]

/-- Exact instruction count of a dispatched operation, excluding the final halt. -/
def bodyCost (front back : List ℕ) : QueueOp ℕ → ℕ
  | .enqueue _ => 5
  | .dequeue => if front = [] then 8 * back.length + (if back = [] then 8 else 11) else 10

/-- Encoded operation arguments for any valid queue operation fit in a `w`-bit word. -/
theorem arguments_fit {w capacity : ℕ} (h1 : Fits w 1) {q : List ℕ} (o : QueueOp ℕ)
    (hv : (spec w capacity).valid q o) (i : Fin 11) :
    Fits w ((implementation w capacity).encode o i) := by
  cases o with
  | enqueue v =>
    change Fits w (if i = tag then 0 else v)
    split
    · exact fits_zero w
    · exact hv.2
  | dequeue =>
    change Fits w (if i = tag then 1 else 0)
    split
    · exact h1
    · exact fits_zero w

private theorem prepare_rep {w base capacity : ℕ} {front back : List ℕ} {x : Data 11}
    (hr : Rep w base capacity front back x) (o : QueueOp ℕ)
    (hv : (spec w capacity).valid (contents (front, back)) o) :
    Rep w base capacity front back ((implementation w capacity).prepare o x) := by
  have hb : ((implementation w capacity).prepare o x).Bounded w :=
    (implementation w capacity).prepare_bounded hr.bounded
      (fun i _ => arguments_fit (hr.one_eq ▸ hr.bounded.1 one) o hv i)
  refine ⟨hb, ?_, ?_, ?_, ?_, ?_, ?_, hr.size_le, hr.front_contents, hr.back_contents⟩
  all_goals first
    | simpa +decide [implementation, DynamicProgram.prepare] using hr.frontBase_eq
    | simpa +decide [implementation, DynamicProgram.prepare] using hr.backBase_eq
    | simpa +decide [implementation, DynamicProgram.prepare] using hr.frontLen_eq
    | simpa +decide [implementation, DynamicProgram.prepare] using hr.backLen_eq
    | simpa +decide [implementation, DynamicProgram.prepare] using hr.zero_eq
    | simpa +decide [implementation, DynamicProgram.prepare] using hr.one_eq

/-- Every valid operation executes the fixed dispatcher with its exact instruction count,
implements the two-stack transition, and preserves every cell outside the reserved region. -/
theorem execute {w base capacity : ℕ} {front back : List ℕ} {x : Data 11}
    (hc : Fits w (base + 2 * capacity)) (hr : Rep w base capacity front back x)
    (o : QueueOp ℕ) (hv : (spec w capacity).valid (contents (front, back)) o) :
    ∃ y, Exec w program ((implementation w capacity).prepare o x) y (bodyCost front back o) ∧
      (implementation w capacity).decode o y.regs = some (pairStep (front, back) o).2 ∧
      Rep w base capacity (pairStep (front, back) o).1.1 (pairStep (front, back) o).1.2 y ∧
      Modifies (footprint base capacity) x.mem y.mem := by
  have hp := prepare_rep hr o hv
  cases o with
  | enqueue v =>
    have hs : front.length + back.length < capacity := by
      simpa only [contents_length] using hv.1
    have ha : ((implementation w capacity).prepare (.enqueue v) x).regs arg = v := by
      simp +decide [implementation, DynamicProgram.prepare]
    obtain ⟨y, he, hy, hf⟩ := enqueue_exec hc hp hs ha
    refine ⟨y, ?_, rfl, hy, hf⟩
    exact Exec.branch_pos (by
      change _ = _
      simp +decide [implementation, DynamicProgram.prepare, hr.zero_eq]) he
  | dequeue =>
    have ht : ¬(Cond.eq tag zero).Holds ((implementation w capacity).prepare .dequeue x) := by
      change ¬_ = _
      simp +decide [implementation, DynamicProgram.prepare, hr.zero_eq]
    cases front with
    | nil =>
      obtain ⟨y, he, hy, hf⟩ := transfer_exec hc hp
      have hy' : Rep w base capacity back.reverse [] y := by simpa using hy
      obtain ⟨z, hz, hrz, ha, hm⟩ := pop_exec hc hy'
      refine ⟨z, ?_, ?_, hrz, ?_⟩
      · have hbranch := Exec.branch_neg (pos := enqueue) ht
          (Exec.branch_pos (c := Cond.eq frontLen zero) (neg := pop) (by
            change _ = _
            rw [hp.frontLen_eq, hp.zero_eq]
            rfl) (Exec.seq he hz))
        convert hbranch using 1
        · rfl
        · simp only [bodyCost, ↓reduceIte, List.reverse_eq_nil_iff]
          split <;> omega
      · exact congrArg some ha
      · intro a hab
        rw [hm]
        exact hf a hab
    | cons v front =>
      obtain ⟨y, he, hy, ha, hm⟩ := pop_exec hc hp
      refine ⟨y, ?_, congrArg some ha, hy, ?_⟩
      · exact Exec.branch_neg ht (Exec.branch_neg (by
          change ¬_ = _
          rw [hp.frontLen_eq, hp.zero_eq]
          simp) he)
      · intro a _
        exact congrFun hm a

/-- Install an empty queue using six register instructions, with no writes to reserved memory. -/
def initializeCode (base capacity : ℕ) : Code .standard 11 := ram[
  frontBase ← #base; backBase ← #(base + capacity); frontLen ← #0; backLen ← #0;
  zero ← #0; one ← #1 ]

/-- Initialization accepts arbitrary bounded registers and memory. Only the six representation
registers change; both reserved live prefixes are empty, so memory remains untouched. -/
theorem initialize_exec {w base capacity : ℕ} {x : Data 11} (hx : x.Bounded w)
    (h1 : Fits w 1) (hc : Fits w (base + 2 * capacity)) :
    ∃ y, Exec w (initializeCode base capacity) x y 6 ∧ Rep w base capacity [] [] y ∧
      y.mem = x.mem := by
  let y := (((((x.set frontBase base).set backBase (base + capacity)).set frontLen 0).set
    backLen 0).set zero 0).set one 1
  have hf : Fits w base := hc.of_le (by omega)
  have hb : Fits w (base + capacity) := hc.of_le (by omega)
  have he : Exec w (initializeCode base capacity) x y 6 := by
    ram_eval [initializeCode, y, hf, hb, h1]
  refine ⟨y, he, ⟨he.bounded hx, ?_, ?_, ?_, ?_, ?_, ?_, Nat.zero_le _,
    fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩, rfl⟩
  all_goals simp +decide [y, Data.set]

end Cslib.WordRAM.Queue
