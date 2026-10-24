/-
Copyright (c) 2026 lean-trominoes contributors, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate (based on edemaine/lean-trominoes @6d5b36c1)

public import Complexity.Computability.WordRAM.Basis
public import Cslib.Foundations.Relation.RelatesInSteps
public import Mathlib.Data.Fin.VecNotation

/-!
# Word RAMs

A *word RAM* is a random-access machine whose registers and memory cells hold `w`-bit words, and
whose every instruction costs one unit of time. The word size must accommodate the input and
its addresses; it may exceed `O(log n)` when input words do
[Cormen et al., Section 2.2][CLRS2009] [Fredman and Willard][FredmanWillard1993]
[Hagerup][Hagerup1998]. This file chooses an instruction-count model, parameterized by a basis of
word operations (`Cslib.WordRAM.Basis`); the standard basis `Cslib.WordRAM.Basis.standard` has
unit-cost multiplication, division, bitwise operations and shifts. It does not establish a bit-cost
simulation.

The existing `Cslib.RAM`, inspired by Cook and Reckhow [Cook and Reckhow][CookReckhow1973], has
unbounded natural-number registers and supports both unit and logarithmic cost measures.
`Cslib.WordRAM` instead supplies bounded, faulting operational semantics, a finite named register
file with indirect memory, and a different input and halting convention. Changing a cost measure
alone does not change these operational choices. No simulation between these models or Turing
machines is proved here.

This file defines the machine and its runs. `Cslib.WordRAM.DecidableInTime` allows width-indexed
code of uniformly bounded length, width-dependent encodings and time bounds, and arbitrary
admissible input/width pairs. `Cslib.WordRAM.UniformDecidableInTime` uses one fixed program.
Structured programs
(`Cslib.WordRAM.Code`) compile
to the flat programs of this file with the same instruction counts.

## The model

* A program (`Cslib.WordRAM.Program B r`) over a basis `B` is a list of instructions over a
  finite register file `Fin r`; besides the registers there is a memory indexed by natural numbers.
* Registers and memory cells hold natural numbers below `2 ^ w` (`Cslib.WordRAM.Fits`).
* The data instructions (`Cslib.WordRAM.Op`) load a constant, copy a register, apply an operation
  of the basis to registers, and read or write the memory cell whose address is held in a
  register. The standard basis has the arithmetic, bitwise and shift operations
  (`Cslib.WordRAM.BinOp`, applied by `Cslib.WordRAM.Op.bin`) and reads the word size `w`
  (`Cslib.WordRAM.Op.width`); the exact basis (`Cslib.WordRAM.Basis.exact`) has the same
  operations, with subtraction below zero and division by zero undefined. The control
  instructions jump, branch on an equality or unsigned
  comparison of two registers, and halt with the contents of a register as output.
* A run starts at instruction `0` with all registers `0`, the input length at address `0` and the
  input words at addresses `1, …, n` (`Cslib.WordRAM.State.init`); all other cells hold `0`.
  Installing this initial input and extracting the halting output are uncharged; executing the
  final `halt` costs one instruction.
* On a run from an input whose length and words fit a word (`Cslib.WordRAM.InputFits`), an
  instruction that would write a number of more than `w` bits into a register *faults*, and so do
  an operation whose value is undefined and running off the end of the program. A fault is not a
  result: only runs that halt count. Registers and memory hold words throughout such a run
  (`Cslib.WordRAM.Runs.bounded_init`), so every address is a word and the memory has `2 ^ w`
  usable cells.

## Design notes

The definitions are adapted from the Lean formalization accompanying
[MIT–ULB CompGeom Group][Tromino2025]. The modelling choices are these.

* Overflow faults instead of wrapping around modulo `2 ^ w`. This formalizes the standard
  assumption that every value an algorithm computes fits a word
  [Cormen et al., Section 2.2][CLRS2009]: a run that succeeds never relies on wrapping. Hence a
  successful run of a program that does not read the word size never depends on it: such a run
  succeeds identically at every larger word size (`Cslib.WordRAM.Executes.mono_width`).
  Algorithms that use arithmetic modulo `2 ^ w` [Hagerup][Hagerup1998] must reduce explicitly,
  for instance with the word size and half-word arithmetic; this is not formalized here.
* Words are unsigned [Hagerup][Hagerup1998]. In the standard basis subtraction is truncated, and
  division and remainder by zero follow Lean's conventions `x / 0 = 0` and `x % 0 = x`. In the
  exact basis these values are undefined, so the operation faults. These are part of this
  machine's semantics; transfer to a model with other conventions requires a separate simulation.
* The operations form a parameter, as the gates of a circuit do: word-RAM models differ in their
  instruction sets [Hagerup][Hagerup1998]. The standard basis has addition, subtraction,
  multiplication, bitwise operations and shifts as in Hagerup's multiplication RAM, together with
  division, remainder and an operation reading the word size, which word-RAM algorithms may use
  [Fredman and Willard][FredmanWillard1993]. Everything else about the machine is the same for
  every basis.
* Only constants and operations check that the number they write fits a word. Copies,
  loads and stores move words already held by the machine, and every address held in a register
  is a word, so on a run from an input that fits such checks could never fail
  (`Cslib.WordRAM.Runs.bounded_init`); omitting them spares every program proof their side
  conditions.
* Memory starts zeroed beyond the input, so a program may use any cell before writing it.
* The program counter is not required to fit a word. Each execution uses a finite program;
  the complexity predicates additionally bound code length independently of word size.
* Data instructions have one semantics, `Cslib.WordRAM.Op.eval`, shared by flat and structured
  programs; runs are counted with cslib's `Relation.RelatesInSteps`.

Compared with the source formalization, words are unsigned rather than two's-complement integers;
the operations form a basis, whose standard instance adds bitwise operations, shifts and the word
size to the source's arithmetic (`Cslib.WordRAM.Basis.arithmetic`); copies, loads,
addresses and the halting output are not checked against the word size; the program counter is
unbounded; the time classes of `Cslib.WordRAM.LinearTime` measure the word size by the number
of binary digits of the size rather than by `log₂ (size + 2) + 2`; and an operation may be
undefined, which faults. In particular, the exact basis faults on subtraction below zero and on
division and remainder by zero. The source does not reject these cases as such: its signed
subtraction may give a negative word, its division and remainder follow Lean's integer conventions
`x / 0 = 0` and `x % 0 = x`, and only its usual check that the result fits a signed word applies.
The current classes allow width-indexed code; the `Uniform` variants retain the fixed-program
convention.

## Main definitions

* `Cslib.WordRAM.Fits`: a number fits a `w`-bit word.
* `Cslib.WordRAM.Cond`, `Cslib.WordRAM.Cond.Holds`, `Cslib.WordRAM.Op`, `Cslib.WordRAM.Instr`,
  `Cslib.WordRAM.Program`: conditions, their satisfaction, data instructions, instructions and
  programs over a basis.
* `Cslib.WordRAM.Op.bin`, `Cslib.WordRAM.Op.width`: the data instructions of the standard basis;
  `Cslib.WordRAM.Op.exactBin`, `Cslib.WordRAM.Op.exactWidth`: those of the exact basis.
* `Cslib.WordRAM.Data`, `Cslib.WordRAM.Data.set`, `Cslib.WordRAM.Data.write`,
  `Cslib.WordRAM.Data.put`, `Cslib.WordRAM.State`: registers with memory, register/memory updates,
  and state with a program counter.
* `Cslib.WordRAM.Op.eval`: the effect of a data instruction, `none` on a fault.
* `Cslib.WordRAM.Outcome`, `Cslib.WordRAM.step`, `Cslib.WordRAM.Next`: step outcome, one step of a
  program, and the single-step transition relation.
* `Cslib.WordRAM.Runs`, `Cslib.WordRAM.Executes`: runs of a given number of steps, and runs that
  halt with a given output after a given number of instructions, the `halt` included.
* `Cslib.WordRAM.Data.init`, `Cslib.WordRAM.State.init`, `Cslib.WordRAM.InputFits`,
  `Cslib.WordRAM.Data.Bounded`: initial data/state on an input, inputs whose length and words fit a
  word, and word-bounded machine data.
* `Cslib.WordRAM.Op.ReadsWidth`, `Cslib.WordRAM.Instr.ReadsWidth`,
  `Cslib.WordRAM.Program.ReadsWidth`: predicates for reading the word size `w`.
* `Cslib.WordRAM.run`: a computable interpreter with a step budget.

## Main results

* `Cslib.WordRAM.executes_iff_exists_run_eq`: the interpreter computes exactly the halting runs.
* `Cslib.WordRAM.Executes.unique`: output and instruction count are determined by the program,
  the word size and the state.
* `Cslib.WordRAM.Runs.bounded_init`: from an input that fits, every reachable register and memory
  cell holds a `w`-bit word.
* `Cslib.WordRAM.Executes.mono_width`: a program that does not read the word size halts in the
  same way at every larger word size.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
* [M. L. Fredman and D. E. Willard, *Surpassing the information theoretic bound with fusion
  trees*][FredmanWillard1993]
* [T. Hagerup, *Sorting and searching on the word RAM*][Hagerup1998]
* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ}

/-! ## Words -/

/-- A number fits a `w`-bit word if it is below `2 ^ w`. -/
def Fits (w v : ℕ) : Prop := v < 2 ^ w

/-- Decidability of `Fits w v`. -/
instance (w v : ℕ) : Decidable (Fits w v) := inferInstanceAs (Decidable (v < 2 ^ w))

/-- `Fits w v` unfolds to `v < 2 ^ w`. -/
theorem fits_iff {w v : ℕ} : Fits w v ↔ v < 2 ^ w := Iff.rfl

/-- A word that fits in `w` bits also fits in any larger word width `w'`. -/
theorem Fits.mono {w w' v : ℕ} (h : Fits w v) (hw : w ≤ w') : Fits w' v :=
  h.trans_le (Nat.pow_le_pow_right Nat.two_pos hw)

/-- Any value at most a `w`-bit word also fits in `w` bits. -/
theorem Fits.of_le {w u v : ℕ} (h : Fits w v) (huv : u ≤ v) : Fits w u := huv.trans_lt h

/-- Zero fits in every word width `w`. -/
@[simp]
theorem fits_zero (w : ℕ) : Fits w 0 := Nat.two_pow_pos w

/-- One fits in every nonzero word width `w`. -/
theorem fits_one {w : ℕ} (hw : w ≠ 0) : Fits w 1 :=
  Nat.one_lt_two_pow hw

/-- The word size fits a word, so that a program may read it. -/
theorem fits_self (w : ℕ) : Fits w w := Nat.lt_two_pow_self

/-! ## Instructions -/

/-- The conditions on which a program branches: equality and unsigned comparison of two
registers. -/
inductive Cond (r : ℕ) where
  /-- Registers `i` and `j` hold equal words. -/
  | eq (i j : Fin r)
  /-- Register `i` holds a smaller word than register `j`. -/
  | lt (i j : Fin r)
  deriving DecidableEq, Repr

/-- The data instructions over the basis `B`. Registers are named in the instruction; memory is
addressed through the contents of a register. -/
inductive Op (B : Basis) (r : ℕ) where
  /-- `const d v` sets register `d` to the constant `v`. -/
  | const (d : Fin r) (v : ℕ)
  /-- `copy d s` sets register `d` to the contents of register `s`. -/
  | copy (d s : Fin r)
  /-- `alu f d args` sets register `d` to the operation `f` of the basis applied to the
  registers `args`. -/
  | alu (f : B.Op) (d : Fin r) (args : Fin (B.Arity f) → Fin r)
  /-- `load d a` sets register `d` to the memory cell whose address is in register `a`. -/
  | load (d a : Fin r)
  /-- `store a s` sets the memory cell whose address is in register `a` to register `s`. -/
  | store (a s : Fin r)
  deriving DecidableEq

/-- `bin f d i j` sets register `d` to the standard binary operation `f` applied to registers `i`
and `j`. -/
def Op.bin (f : BinOp) (d i j : Fin r) : Op .standard r := .alu (.bin f) d ![i, j]

/-- `width d` sets register `d` to the word size. -/
def Op.width (d : Fin r) : Op .standard r := .alu .width d ![]

/-- `exactBin f d i j` sets register `d` to the exact value of the binary operation `f` applied
to registers `i` and `j`. -/
def Op.exactBin (f : BinOp) (d i j : Fin r) : Op .exact r := .alu (.bin f) d ![i, j]

/-- `exactWidth d` sets register `d` to the word size, over the exact basis. -/
def Op.exactWidth (d : Fin r) : Op .exact r := .alu .width d ![]

/-- Instructions over the basis `B`: data instructions, jumps, conditional branches and halting.
Jump and branch targets are instruction indices. -/
inductive Instr (B : Basis) (r : ℕ) where
  /-- Execute a data instruction and proceed to the next instruction. -/
  | op (o : Op B r)
  /-- Proceed to instruction `t`. -/
  | jump (t : ℕ)
  /-- Proceed to instruction `t` if `c` holds, and to the next instruction otherwise. -/
  | branch (c : Cond r) (t : ℕ)
  /-- Halt with the contents of register `i` as output. -/
  | halt (i : Fin r)
  deriving DecidableEq

/-- A program over the basis `B` and `r` registers is a list of instructions, indexed by the
program counter. -/
abbrev Program (B : Basis) (r : ℕ) := List (Instr B r)

/-! ## Data and states -/

/-- The data of a machine: register contents and memory. -/
@[ext]
structure Data (r : ℕ) where
  /-- The contents of the registers. -/
  regs : Fin r → ℕ
  /-- The contents of memory, by address. -/
  mem : ℕ → ℕ

namespace Data

/-- Set register `i` to `v`. -/
def set (x : Data r) (i : Fin r) (v : ℕ) : Data r := ⟨Function.update x.regs i v, x.mem⟩

/-- Set the memory cell at address `a` to `v`. -/
def write (x : Data r) (a v : ℕ) : Data r := ⟨x.regs, Function.update x.mem a v⟩

/-- Setting register `i` updates the register file at `i`. -/
@[simp]
theorem set_regs (x : Data r) (i : Fin r) (v : ℕ) :
    (x.set i v).regs = Function.update x.regs i v := rfl

/-- Setting register `i` leaves memory unchanged. -/
@[simp]
theorem set_mem (x : Data r) (i : Fin r) (v : ℕ) : (x.set i v).mem = x.mem := rfl

/-- Writing to memory leaves the register file unchanged. -/
@[simp]
theorem write_regs (x : Data r) (a v : ℕ) : (x.write a v).regs = x.regs := rfl

/-- Writing `v` at address `a` updates memory at `a`. -/
@[simp]
theorem write_mem (x : Data r) (a v : ℕ) :
    (x.write a v).mem = Function.update x.mem a v := rfl

/-- Set register `i` to `v` if `v` fits a `w`-bit word, and fault otherwise. -/
def put (w : ℕ) (x : Data r) (i : Fin r) (v : ℕ) : Option (Data r) :=
  if Fits w v then some (x.set i v) else none

/-- When `v` fits in `w` bits, `put` succeeds and sets register `i` to `v`. -/
theorem put_of_fits {w : ℕ} {x : Data r} {i : Fin r} {v : ℕ} (h : Fits w v) :
    x.put w i v = some (x.set i v) := by
  simp [put, h]

/-- `put` returns `some y` iff `v` fits in `w` bits and `y = x.set i v`. -/
theorem put_eq_some {w : ℕ} {x y : Data r} {i : Fin r} {v : ℕ} :
    x.put w i v = some y ↔ Fits w v ∧ x.set i v = y := by
  unfold put
  split <;> simp_all

end Data

/-- A machine state: the index of the next instruction, and the data. -/
@[ext]
structure State (r : ℕ) where
  /-- The program counter: the index of the next instruction. -/
  pc : ℕ
  /-- Register contents and memory. -/
  data : Data r

/-! ## Semantics of instructions -/

/-- Whether a condition holds of the register contents. -/
def Cond.Holds : Cond r → Data r → Prop
  | .eq i j, x => x.regs i = x.regs j
  | .lt i j, x => x.regs i < x.regs j

/-- Decidability of `Cond.Holds`. -/
instance (c : Cond r) (x : Data r) : Decidable (c.Holds x) :=
  match c with
  | .eq i j => inferInstanceAs (Decidable (x.regs i = x.regs j))
  | .lt i j => inferInstanceAs (Decidable (x.regs i < x.regs j))

/-- `Cond.eq i j` holds iff registers `i` and `j` have equal contents. -/
@[simp]
theorem Cond.holds_eq {i j : Fin r} {x : Data r} : (Cond.eq i j).Holds x ↔ x.regs i = x.regs j :=
  Iff.rfl

/-- `Cond.lt i j` holds iff register `i` is strictly less than register `j`. -/
@[simp]
theorem Cond.holds_lt {i j : Fin r} {x : Data r} : (Cond.lt i j).Holds x ↔ x.regs i < x.regs j :=
  Iff.rfl

/-- The effect of a data instruction at word size `w`, or `none` if it faults. Only constants
and operations can produce a number that does not fit a word, and they fault when they do; an
operation also faults when its value is undefined.
Copying, loading and storing need no check: throughout a run from an input that fits, registers
and memory hold words (`Cslib.WordRAM.Runs.bounded_init`), so every address held in a register is
a word too. -/
def Op.eval (w : ℕ) : Op B r → Data r → Option (Data r)
  | .const d v, x => x.put w d v
  | .copy d s, x => some (x.set d (x.regs s))
  | .alu f d args, x => do
      let value ← B.interp w f (x.regs ∘ args)
      x.put w d value
  | .load d a, x => some (x.set d (x.mem (x.regs a)))
  | .store a s, x => some (x.write (x.regs a) (x.regs s))

section Eval

variable (w : ℕ) (x : Data r) {d s a : Fin r}

/-- Evaluating `Op.const d v` writes `v` to register `d` via `Data.put`. -/
@[simp]
theorem Op.eval_const (v : ℕ) : (Op.const (B := B) d v).eval w x = x.put w d v := rfl

/-- Evaluating `Op.copy d s` copies register `s` into register `d`. -/
@[simp]
theorem Op.eval_copy : (Op.copy (B := B) d s).eval w x = some (x.set d (x.regs s)) := rfl

/-- Evaluating `Op.alu f d args` interprets `f` on `args` and writes the result via `Data.put`. -/
@[simp]
theorem Op.eval_alu (f : B.Op) (args : Fin (B.Arity f) → Fin r) :
    (Op.alu f d args).eval w x = (B.interp w f (x.regs ∘ args)).bind (x.put w d) := rfl

/-- Evaluating `Op.load d a` loads the memory word at address `x.regs a` into register `d`. -/
@[simp]
theorem Op.eval_load : (Op.load (B := B) d a).eval w x = some (x.set d (x.mem (x.regs a))) := rfl

/-- Evaluating `Op.store a s` stores `x.regs s` at memory address `x.regs a`. -/
@[simp]
theorem Op.eval_store :
    (Op.store (B := B) a s).eval w x = some (x.write (x.regs a) (x.regs s)) := rfl

end Eval

/-- An operation succeeds when its value is defined and fits a word. -/
theorem Op.eval_alu_eq_some {w : ℕ} {x y : Data r} {f : B.Op} {d : Fin r}
    {args : Fin (B.Arity f) → Fin r} :
    (Op.alu f d args).eval w x = some y ↔
      ∃ v, B.interp w f (x.regs ∘ args) = some v ∧ Fits w v ∧ x.set d v = y := by
  rw [Op.eval_alu]
  cases B.interp w f (x.regs ∘ args) with
  | none => exact ⟨nofun, fun ⟨_, h, _⟩ => nomatch h⟩
  | some v => exact Data.put_eq_some.trans ⟨fun h => ⟨v, rfl, h⟩, fun ⟨_, rfl, h⟩ => h⟩

/-- Evaluating a standard binary operation `Op.bin f d i j` writes `f.eval` via `Data.put`. -/
@[simp]
theorem Op.eval_bin (w : ℕ) (f : BinOp) (d i j : Fin r) (x : Data r) :
    (Op.bin f d i j).eval w x = x.put w d (f.eval (x.regs i) (x.regs j)) := rfl

/-- The word size always fits a word, so reading it never faults. -/
@[simp]
theorem Op.eval_width (w : ℕ) (d : Fin r) (x : Data r) :
    (Op.width d).eval w x = some (x.set d w) :=
  Data.put_of_fits (fits_self w)

/-- Evaluating an exact binary operation `Op.exactBin f d i j` binds `f.evalExact` to `Data.put`. -/
@[simp]
theorem Op.eval_exactBin (w : ℕ) (f : BinOp) (d i j : Fin r) (x : Data r) :
    (Op.exactBin f d i j).eval w x = (f.evalExact (x.regs i) (x.regs j)).bind (x.put w d) :=
  rfl

/-- Reading the word width in the exact basis always succeeds and writes `w`. -/
@[simp]
theorem Op.eval_exactWidth (w : ℕ) (d : Fin r) (x : Data r) :
    (Op.exactWidth d).eval w x = some (x.set d w) :=
  Data.put_of_fits (fits_self w)

/-- The outcome of a step: the next state, halting with an output, or a fault. -/
inductive Outcome (r : ℕ) where
  /-- The run continues in the given state. -/
  | next (s : State r)
  /-- The run halts with the given output. -/
  | halt (v : ℕ)
  /-- The run faults. -/
  | fault

/-- One step of program `p` at word size `w`: execute the instruction at the program counter.
Running off the end of the program faults. -/
def step (w : ℕ) (p : Program B r) (s : State r) : Outcome r :=
  match p[s.pc]? with
  | none => .fault
  | some (.op o) =>
    match o.eval w s.data with
    | some x => .next ⟨s.pc + 1, x⟩
    | none => .fault
  | some (.jump t) => .next ⟨t, s.data⟩
  | some (.branch c t) => .next ⟨if c.Holds s.data then t else s.pc + 1, s.data⟩
  | some (.halt i) => .halt (s.data.regs i)

section Step

variable {w : ℕ} {p : Program B r} {s : State r}

/-- Stepping on a data instruction that evaluates to `some x` advances `pc` by `1` with data `x`. -/
theorem step_op {o : Op B r} {x : Data r} (hp : p[s.pc]? = some (.op o))
    (h : o.eval w s.data = some x) :
    step w p s = .next ⟨s.pc + 1, x⟩ := by
  simp only [step, hp, h]

/-- Stepping on a data instruction that evaluates to `none` faults. -/
theorem step_op_fault {o : Op B r} (hp : p[s.pc]? = some (.op o)) (h : o.eval w s.data = none) :
    step w p s = .fault := by
  simp only [step, hp, h]

/-- Stepping on an unconditional jump sets `pc` to the target `t`. -/
theorem step_jump {t : ℕ} (hp : p[s.pc]? = some (.jump t)) :
    step w p s = .next ⟨t, s.data⟩ := by
  simp only [step, hp]

/-- Stepping on a conditional branch jumps to `t` when `c` holds and advances `pc` otherwise. -/
theorem step_branch {c : Cond r} {t : ℕ} (hp : p[s.pc]? = some (.branch c t)) :
    step w p s = .next ⟨if c.Holds s.data then t else s.pc + 1, s.data⟩ := by
  simp only [step, hp]

/-- Stepping on `halt i` halts with output `s.data.regs i`. -/
theorem step_halt {i : Fin r} (hp : p[s.pc]? = some (.halt i)) :
    step w p s = .halt (s.data.regs i) := by
  simp only [step, hp]

end Step

/-! ## Runs -/

/-- One step of `p` at word size `w` leads from `s` to `t`. -/
def Next (w : ℕ) (p : Program B r) (s t : State r) : Prop := step w p s = .next t

/-- `Runs w p s t n`: running `p` at word size `w` leads from `s` to `t` in exactly `n` steps,
none of which halts or faults. -/
abbrev Runs (w : ℕ) (p : Program B r) : State r → State r → ℕ → Prop :=
  Relation.RelatesInSteps (Next w p)

/-- `Executes w p s v n`: running `p` at word size `w` from `s` halts with output `v` after
exactly `n` instructions, the final `halt` included. A run that faults executes nothing. -/
def Executes (w : ℕ) (p : Program B r) (s : State r) (v n : ℕ) : Prop :=
  ∃ t m, Runs w p s t m ∧ step w p t = .halt v ∧ n = m + 1

/-- Run `p` at word size `w` from `s` for at most `fuel` steps: `some (v, n)` if it halts with
output `v` after `n` instructions, and `none` if it faults or needs more steps. -/
def run (w : ℕ) (p : Program B r) : ℕ → State r → Option (ℕ × ℕ)
  | 0, _ => none
  | fuel + 1, s =>
    match step w p s with
    | .next t => (run w p fuel t).map fun vn => (vn.1, vn.2 + 1)
    | .halt v => some (v, 1)
    | .fault => none

section Executes

variable {w : ℕ} {p : Program B r} {s t u : State r} {v v' m n n' : ℕ}

/-- A state that immediately halts executes in `1` instruction. -/
theorem Executes.halt (h : step w p s = .halt v) : Executes w p s v 1 :=
  ⟨s, 0, .refl s, h, rfl⟩

/-- Prepending a single transition `Next w p s t` increments the instruction count by `1`. -/
theorem Executes.head (h : Next w p s t) (ht : Executes w p t v n) : Executes w p s v (n + 1) := by
  obtain ⟨u, m, hr, hu, rfl⟩ := ht
  exact ⟨u, m + 1, hr.head s t u m h, hu, rfl⟩

/-- A run followed by a halting run is a halting run. -/
theorem Executes.of_runs (h : Runs w p s t m) (ht : Executes w p t v n) :
    Executes w p s v (m + n) := by
  obtain ⟨u, k, hr, hu, rfl⟩ := ht
  exact ⟨u, m + k, h.trans hr, hu, by omega⟩

/-- Every halting execution takes at least one instruction. -/
theorem Executes.pos (h : Executes w p s v n) : 0 < n := by
  obtain ⟨_, _, _, _, rfl⟩ := h
  omega

/-- Unfolding `run` for `n + 1` steps of fuel. -/
theorem run_succ :
    run w p (n + 1) s = match step w p s with
      | .next t => (run w p n t).map fun vn => (vn.1, vn.2 + 1)
      | .halt v => some (v, 1)
      | .fault => none := rfl

/-- The interpreter only finds halting runs. -/
theorem Executes.of_run {fuel : ℕ} (h : run w p fuel s = some (v, n)) : Executes w p s v n := by
  induction fuel generalizing s n with
  | zero => simp [run] at h
  | succ fuel ih =>
    rw [run_succ] at h
    split at h
    · next t ht =>
      obtain ⟨⟨v', k⟩, hk, hvn⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at hvn
      obtain ⟨rfl, rfl⟩ := hvn
      exact (ih hk).head ht
    · next v' hv =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .halt hv
    · simp at h

/-- A halting run of `n` instructions is found by the interpreter with `n` steps of fuel. -/
theorem Executes.run_eq (h : Executes w p s v n) : run w p n s = some (v, n) := by
  obtain ⟨t, m, hr, ht, rfl⟩ := h
  induction hr using Relation.RelatesInSteps.head_induction_on with
  | hrefl => simp [run_succ, ht]
  | hhead hsc _ ih =>
    rw [run_succ, show step w p _ = .next _ from hsc]
    dsimp only
    rw [ih]
    rfl

/-- More fuel does not change a result of the interpreter. -/
theorem run_mono {fuel fuel' : ℕ} {vn : ℕ × ℕ} (h : run w p fuel s = some vn)
    (hle : fuel ≤ fuel') : run w p fuel' s = some vn := by
  induction fuel generalizing s fuel' vn with
  | zero => simp [run] at h
  | succ fuel ih =>
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [run_succ] at h ⊢
    split at h
    · obtain ⟨vn', hk, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [ih hk (by omega)]
      rfl
    · exact h
    · simp at h

/-- The interpreter computes exactly the halting runs. -/
theorem executes_iff_exists_run_eq : Executes w p s v n ↔ ∃ fuel, run w p fuel s = some (v, n) :=
  ⟨fun h => ⟨n, h.run_eq⟩, fun ⟨_, h⟩ => .of_run h⟩

/-- A halting run is determined by the program, the word size and the state: its output and its
number of instructions are unique. -/
theorem Executes.unique (h : Executes w p s v n) (h' : Executes w p s v' n') :
    v = v' ∧ n = n' := by
  have := (run_mono h.run_eq (le_max_left n n')).symm.trans (run_mono h'.run_eq (le_max_right n n'))
  simpa using this

/-- A state from which the step faults has no halting run. -/
theorem not_executes_of_fault (h : step w p s = .fault) : ¬Executes w p s v n := by
  intro he
  have hr := he.run_eq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.pos.ne'
  simp [run_succ, h] at hr

end Executes

/-! ## Inputs -/

/-- The initial data on an input: all registers `0`, the input length at address `0` and the
input words at addresses `1, …, n`, all other memory `0`. Placing the input is the calling
convention, not part of the program's cost. -/
def Data.init (input : List ℕ) : Data r where
  regs _ := 0
  mem a := if a = 0 then input.length else input.getD (a - 1) 0

/-- The initial state on an input: the program counter at `0`, and `Data.init input`. -/
def State.init (input : List ℕ) : State r := ⟨0, .init input⟩

/-- All registers are initialized to `0` in `Data.init`. -/
@[simp]
theorem Data.init_regs (input : List ℕ) (i : Fin r) : (Data.init input).regs i = 0 := rfl

/-- Memory cell `0` holds the input length in `Data.init`. -/
@[simp]
theorem Data.init_mem_zero (input : List ℕ) : (Data.init input : Data r).mem 0 = input.length :=
  rfl

/-- Memory cell `a + 1` holds the `a`-th input word (or `0` out of bounds) in `Data.init`. -/
@[simp]
theorem Data.init_mem_succ (input : List ℕ) (a : ℕ) :
    (Data.init input : Data r).mem (a + 1) = input.getD a 0 := rfl

/-- An input fits word size `w` if its length and all its words do. -/
def InputFits (w : ℕ) (input : List ℕ) : Prop :=
  Fits w input.length ∧ ∀ v ∈ input, Fits w v

/-- Decidability of `InputFits w input`. -/
instance (w : ℕ) (input : List ℕ) : Decidable (InputFits w input) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- An input that fits in word size `w` also fits in any larger word size `w'`. -/
theorem InputFits.mono {w w' : ℕ} {input : List ℕ} (h : InputFits w input) (hw : w ≤ w') :
    InputFits w' input :=
  ⟨h.1.mono hw, fun v hv => (h.2 v hv).mono hw⟩

/-! ## Word bounds

The machine holds only `w`-bit words: from an input that fits, every register and memory cell of
every reachable state does. -/

/-- All registers and memory cells hold `w`-bit words. -/
def Data.Bounded (w : ℕ) (x : Data r) : Prop :=
  (∀ i, Fits w (x.regs i)) ∧ ∀ a, Fits w (x.mem a)

/-- The initial data on an input that fits in `w` bits is word-bounded. -/
theorem Data.Bounded.init {w : ℕ} {input : List ℕ} (h : InputFits w input) :
    (Data.init input : Data r).Bounded w := by
  refine ⟨fun _ => fits_zero w, fun a => ?_⟩
  rcases a with _ | a
  · exact h.1
  · rw [init_mem_succ, List.getD_eq_getElem?_getD]
    cases hv : input[a]? with
    | none => exact fits_zero w
    | some v => exact h.2 v (List.mem_of_getElem? hv)

/-- Setting a register to a `w`-bit word preserves `Data.Bounded w`. -/
theorem Data.Bounded.set {w : ℕ} {x : Data r} (hx : x.Bounded w) {i : Fin r} {v : ℕ}
    (hv : Fits w v) : (x.set i v).Bounded w := by
  refine ⟨fun j => ?_, hx.2⟩
  rcases eq_or_ne j i with rfl | hj
  · simpa using hv
  · simpa [Function.update_of_ne hj] using hx.1 j

/-- Writing a `w`-bit word to memory preserves `Data.Bounded w`. -/
theorem Data.Bounded.write {w : ℕ} {x : Data r} (hx : x.Bounded w) {a v : ℕ} (hv : Fits w v) :
    (x.write a v).Bounded w := by
  refine ⟨hx.1, fun b => ?_⟩
  rcases eq_or_ne b a with rfl | hb
  · simpa using hv
  · simpa [Function.update_of_ne hb] using hx.2 b

/-- Any non-faulting data instruction preserves `Data.Bounded w`. -/
theorem Data.Bounded.op {w : ℕ} {x y : Data r} (hx : x.Bounded w) {o : Op B r}
    (h : o.eval w x = some y) : y.Bounded w := by
  cases o with
  | const =>
    obtain ⟨hv, rfl⟩ := Data.put_eq_some.1 h
    exact hx.set hv
  | alu =>
    obtain ⟨v, -, hv, rfl⟩ := Op.eval_alu_eq_some.1 h
    exact hx.set hv
  | copy d s => cases h; exact hx.set (hx.1 s)
  | load d a => cases h; exact hx.set (hx.2 _)
  | store a s => cases h; exact hx.write (hx.1 s)

/-- A step preserves word bounds. -/
theorem Next.bounded {w : ℕ} {p : Program B r} {s t : State r} (h : Next w p s t)
    (hs : s.data.Bounded w) : t.data.Bounded w := by
  unfold Next WordRAM.step at h
  split at h
  · cases h
  · next o _ =>
    split at h
    · next x hx => cases h; exact hs.op hx
    · cases h
  all_goals first | (cases h; exact hs) | cases h

/-- A run preserves word bounds. -/
theorem Runs.bounded {w : ℕ} {p : Program B r} {s t : State r} {n : ℕ} (h : Runs w p s t n)
    (hs : s.data.Bounded w) : t.data.Bounded w := by
  induction h with
  | refl => exact hs
  | tail _ _ _ _ hstep ih => exact hstep.bounded ih

/-- Every state reachable from an input that fits holds only `w`-bit words. -/
theorem Runs.bounded_init {w : ℕ} {p : Program B r} {input : List ℕ} {t : State r} {n : ℕ}
    (h : Runs w p (State.init input) t n) (hi : InputFits w input) : t.data.Bounded w :=
  h.bounded (Data.Bounded.init hi)

/-! ## Larger word sizes

Overflow faults, so a program that does not read the word size cannot tell word sizes apart on
a run that succeeds: the same run succeeds at every larger word size. -/

/-- The data instruction reads the word size: it applies an operation that the basis marks with
`Basis.ReadsWidth`, such as `Op.width` in the standard basis. -/
def Op.ReadsWidth : Op B r → Prop
  | .alu f _ _ => B.ReadsWidth f
  | _ => False

/-- Decidability of `Op.ReadsWidth`. -/
instance : DecidablePred (Op.ReadsWidth (B := B) (r := r)) := fun o =>
  match o with
  | .alu f _ _ => inferInstanceAs (Decidable (B.ReadsWidth f))
  | .const .. | .copy .. | .load .. | .store .. => isFalse id

/-- A binary ALU instruction `Op.bin` does not read the word width. -/
@[simp]
theorem Op.readsWidth_bin (f : BinOp) (d i j : Fin r) : ¬(Op.bin f d i j).ReadsWidth := by
  simp [Op.bin, Op.ReadsWidth]

/-- The instruction `Op.width` reads the word width. -/
@[simp]
theorem Op.readsWidth_width (d : Fin r) : (Op.width d).ReadsWidth := by
  simp [Op.width, Op.ReadsWidth]

/-- The instruction reads the word size. -/
def Instr.ReadsWidth : Instr B r → Prop
  | .op o => o.ReadsWidth
  | _ => False

/-- Decidability of `Instr.ReadsWidth`. -/
instance : DecidablePred (Instr.ReadsWidth (B := B) (r := r)) := fun i =>
  match i with
  | .op o => inferInstanceAs (Decidable o.ReadsWidth)
  | .jump .. | .branch .. | .halt .. => isFalse id

/-- A program reads the word size if one of its instructions does. -/
def Program.ReadsWidth (p : Program B r) : Prop := ∃ i ∈ p, i.ReadsWidth

/-- Decidability of `Program.ReadsWidth`. -/
instance (p : Program B r) : Decidable p.ReadsWidth :=
  inferInstanceAs (Decidable (∃ i ∈ p, i.ReadsWidth))

/-- A successful evaluation of a data instruction that does not read the word width gives the same
result at any larger width. -/
theorem Op.eval_mono_width {w w' : ℕ} {o : Op B r} {x y : Data r} (ho : ¬o.ReadsWidth)
    (h : o.eval w x = some y) (hw : w ≤ w') : o.eval w' x = some y := by
  cases o with
  | const =>
    obtain ⟨hv, rfl⟩ := Data.put_eq_some.1 h
    exact Data.put_of_fits (hv.mono hw)
  | alu f d args =>
    obtain ⟨v, hf, hv, rfl⟩ := Op.eval_alu_eq_some.1 h
    rw [Op.eval, B.interp_mono_of_not_readsWidth f ho hw hf hv]
    exact Data.put_of_fits (hv.mono hw)
  | copy | load | store => exact h

/-- A single step of a program that does not read the word width is preserved at any larger
width. -/
theorem Next.mono_width {w w' : ℕ} {p : Program B r} {s t : State r} (hp : ¬p.ReadsWidth)
    (h : Next w p s t) (hw : w ≤ w') : Next w' p s t := by
  unfold Next at h ⊢
  cases hpc : p[s.pc]? with
  | none => simp [WordRAM.step, hpc] at h
  | some i =>
    cases i with
    | op o =>
      have ho : ¬o.ReadsWidth := fun ho => hp ⟨_, List.mem_of_getElem? hpc, ho⟩
      cases hx : o.eval w s.data with
      | none => simp [WordRAM.step, hpc, hx] at h
      | some x => rw [step_op hpc hx, ← step_op hpc (Op.eval_mono_width ho hx hw)] at h; exact h
    | jump t => rw [step_jump hpc] at h ⊢; exact h
    | branch c t => rw [step_branch hpc] at h ⊢; exact h
    | halt i => simp [step_halt hpc] at h

private theorem step_halt_mono_width {w w' : ℕ} {p : Program B r} {s : State r} {v : ℕ}
    (h : step w p s = .halt v) : step w' p s = .halt v := by
  cases hpc : p[s.pc]? with
  | none => simp [WordRAM.step, hpc] at h
  | some i =>
    cases i with
    | op o =>
      simp only [WordRAM.step, hpc] at h
      split at h <;> cases h
    | jump t => simp [step_jump hpc] at h
    | branch c t => simp [step_branch hpc] at h
    | halt i => rw [step_halt hpc] at h ⊢; exact h

/-- Multi-step runs of a program that does not read the word width lift to any larger width. -/
theorem Runs.mono_width {w w' : ℕ} {p : Program B r} {s t : State r} {n : ℕ}
    (hp : ¬p.ReadsWidth) (h : Runs w p s t n) (hw : w ≤ w') : Runs w' p s t n := by
  induction h with
  | refl => exact .refl _
  | tail _ _ _ _ hstep ih => exact .tail _ _ _ _ ih (hstep.mono_width hp hw)

/-- **Word-size monotonicity.** A program that does not read the word size halts in the same way
at every larger word size. -/
theorem Executes.mono_width {w w' : ℕ} {p : Program B r} {s : State r} {v n : ℕ}
    (hp : ¬p.ReadsWidth) (h : Executes w p s v n) (hw : w ≤ w') : Executes w' p s v n :=
  let ⟨t, m, hr, ht, hn⟩ := h
  ⟨t, m, hr.mono_width hp hw, step_halt_mono_width ht, hn⟩

end Cslib.WordRAM

end
