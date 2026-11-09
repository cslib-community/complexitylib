/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.WordRAMBridge

/-! # The word RAM: a formal abstract

A short, self-contained account of the word RAM with the standard operations, each computing its
exact value, and of what it means for a problem to be decidable on it in time `T`.

At word size `w`, a *word* is a number below `2 ^ w`. A machine has `r` registers `R[0]`, …,
`R[r - 1]` and a memory cell `M[a]` at every address `a : ℕ`; all hold natural numbers.
Every instruction takes one unit of time.

The machine is defined from scratch, with only Lean and Mathlib. Two theorems at the end connect
it to the deterministic part of the library's word RAM `Cslib.WordRAM` over its exact basis. The
library's instruction type also includes a random-sampling instruction `rand`, on which
deterministic execution faults. Step-for-step equivalence matches programs here with `rand`-free
library programs. Deterministic decidability in time `T` agrees without that restriction. To
check this, a reader only needs to inspect the definitions and theorem statements in this file.
Lean checks the proofs through `WordRAMBridge`, using only Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). `#check_abstract` checks mechanically that every
definition and theorem statement here depends only on this file, Lean, Mathlib, upstream CSLib,
and the modules `Defs`, `Basis` and `Time` of the library's word RAM; these modules appear only
in the last section.

## References

* [T. H. Cormen et al., *Introduction to Algorithms*][CLRS2009]
* [M. L. Fredman and D. E. Willard, *Surpassing the information theoretic bound with fusion
  trees*][FredmanWillard1993]
* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]; the
  fixed-program decision predicate `Decides` is adapted from its accompanying Lean formalization.
-/

namespace ComplexityTests.Abstracts.WordRAMAbstract

universe u

variable {r : ℕ}

/-! ## Words and operations

The machine stores arbitrary natural numbers, but an instruction faults when it would create a
value that is undefined or not a word. There are ten binary operations, and each computes its
exact value. Subtraction `x - y` is undefined for `y > x`, and division `x / y` and remainder
`x % y` are undefined for `y = 0`; otherwise division rounds down. The operations `and`, `or`
and `xor` act bitwise, and `shl` and `shr` shift `x` left and right by `y` bits, that is, give
`x * 2 ^ y` and `x / 2 ^ y` rounded down. In `AluOp.eval`, a case value `n` stands for
`some n`.
-/

/-- The binary operations. Division rounds down, `and`, `or`, `xor` are bitwise, and `shl`,
`shr` shift left and right by `y` bits. -/
inductive AluOp
  | add | sub | mul | div | mod | and | or | xor | shl | shr

/-- The exact value of a binary operation, before any check that it is a word, or `none` where it
is undefined: `x - y` for `y > x`, and `x / 0` and `x % 0`. -/
def AluOp.eval : AluOp → ℕ → ℕ → Option ℕ
  | .add, x, y => x + y
  | .sub, x, y => if y ≤ x then x - y else none
  | .mul, x, y => x * y
  | .div, x, y => if y = 0 then none else x / y
  | .mod, x, y => if y = 0 then none else x % y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .shl, x, y => some (x * 2 ^ y)
  | .shr, x, y => some (x / 2 ^ y)

/-! ## Instructions and programs

The number `r` of registers is a parameter of the types below (the implicit variable `r`).
There are ten instructions; the comment on each gives its effect. Register arguments `d`, `i`,
`j`, `a` range over `Fin r`, that is, `0, …, r - 1` (in `load` and `store`, register `a` holds
the address); a constant `x` and a jump target `t` are arbitrary natural numbers. The
instruction `width` reads the word size `w`, so a program can depend on it.
-/

/-- The instructions over `r` registers. Jump targets are instruction numbers. -/
inductive Instr (r : ℕ)
  | const (d : Fin r) (x : ℕ)         -- `R[d] := x`
  | copy (d i : Fin r)                -- `R[d] := R[i]`
  | alu (f : AluOp) (d i j : Fin r)   -- `R[d] := f(R[i], R[j])`
  | width (d : Fin r)                 -- `R[d] := w`, the word size
  | load (d a : Fin r)                -- `R[d] := M[R[a]]`
  | store (a i : Fin r)               -- `M[R[a]] := R[i]`
  | jump (t : ℕ)                      -- go to instruction `t`
  | branchEq (i j : Fin r) (t : ℕ)    -- go to `t` if `R[i] = R[j]`, else to the next one
  | branchLt (i j : Fin r) (t : ℕ)    -- go to `t` if `R[i] < R[j]`, else to the next one
  | halt (i : Fin r)                  -- stop with output `R[i]`

/-- A program is a list of instructions, numbered from `0`. -/
abbrev Program (r : ℕ) := List (Instr r)

/-! ## States and one step

The memory is a function on all of `ℕ`: there is no allocation and no bound on addresses. One
step executes instruction number `pc`. `const` and `alu` write their value to `R[d]` if it is a
word, and fault otherwise; there is no wrap-around modulo `2 ^ w`, and an `alu` whose value is
undefined (`none`) also faults. `width` writes `w`, which is always a word, since `w < 2 ^ w`.
`copy`, `load` and `store` move a value without a check. `jump` and the two branches set `pc`;
every other instruction except `halt` moves on to instruction `pc + 1`. `halt i` stops with
output `R[i]`. If `pc` is not the number of an instruction, that is, `pc` is at least the length
of the program, the step faults.

Copies, loads and stores need no check: when the input fits (`InputFits`), an induction along
the run shows that every register and memory cell always holds a word, and so every address used
is below `2 ^ w`. This induction is not stated here; it only explains why the check is not
needed. The library states it for its own word RAM as `Cslib.WordRAM.Runs.bounded_init`.
-/

/-- A state: the number `pc` of the next instruction, the registers and the memory. -/
structure State (r : ℕ) where
  /-- The number of the next instruction. -/
  pc : ℕ
  /-- `reg i` is `R[i]`. -/
  reg : Fin r → ℕ
  /-- `mem a` is `M[a]`. -/
  mem : ℕ → ℕ

/-- One step continues in a new state, halts with an output, or faults. -/
inductive Outcome (r : ℕ)
  | next (s : State r)
  | halt (v : ℕ)
  | fault

/-- One step of program `p` at word size `w`. A constant or operation whose value is not a word
faults (no wrap-around), and so do an operation whose value is undefined and running off the end
of the program. Copies, loads and stores are not checked: from an input whose length and words
fit (`InputFits`), they only ever move words. -/
def step (w : ℕ) (p : Program r) (s : State r) : Outcome r :=
  let set (d : Fin r) (x : ℕ) : Outcome r :=  -- `R[d] := x`, then the next instruction
    .next { s with pc := s.pc + 1, reg := Function.update s.reg d x }
  let setWord (d : Fin r) (x : ℕ) : Outcome r := if x < 2 ^ w then set d x else .fault
  match p[s.pc]? with
  | none => .fault
  | some (.const d x) => setWord d x
  | some (.copy d i) => set d (s.reg i)
  | some (.alu f d i j) =>
    match f.eval (s.reg i) (s.reg j) with
    | some x => setWord d x
    | none => .fault
  | some (.width d) => set d w  -- `w < 2 ^ w`, so this never faults
  | some (.load d a) => set d (s.mem (s.reg a))
  | some (.store a i) =>
    .next { s with pc := s.pc + 1, mem := Function.update s.mem (s.reg a) (s.reg i) }
  | some (.jump t) => .next { s with pc := t }
  | some (.branchEq i j t) => .next { s with pc := if s.reg i = s.reg j then t else s.pc + 1 }
  | some (.branchLt i j t) => .next { s with pc := if s.reg i < s.reg j then t else s.pc + 1 }
  | some (.halt i) => .halt (s.reg i)

/-! ## Running time

`Halts w p s v n` says that from state `s`, at word size `w`, program `p` halts with output `v`
after exactly `n` instructions, the final `halt` included. It follows `step` one instruction at a
time: a fault ends the run without halting, and a run that never halts satisfies `Halts` for no
`v` and `n`. Every instruction takes one unit of time, whatever its operands and the word size,
so `n` is the running time.
-/

/-- `Halts w p s v n`: from state `s`, program `p` halts with output `v` after exactly `n`
instructions, the final `halt` included. A run that faults never halts. -/
def Halts (w : ℕ) (p : Program r) : State r → ℕ → ℕ → Prop
  | _, _, 0 => False
  | s, v, n + 1 =>
    match step w p s with
    | .next t => Halts w p t v n
    | .halt x => x = v ∧ n = 0
    | .fault => False

/-! ## Input

An input is a list `x₁, …, xₖ` of natural numbers. A program reads the length of its input at
`M[0]`. The output of a run is the single number `R[i]` at its `halt i`.
-/

/-- The start state on input `x₁, …, xₖ`: instruction `0`, registers `0`, and memory
`k, x₁, …, xₖ` at addresses `0, 1, …, k`, then `0` everywhere. -/
def init (input : List ℕ) : State r :=
  ⟨0, fun _ => 0, fun a => (input.length :: input).getD a 0⟩

/-- An input fits word size `w` if its length and all its entries are words. -/
def InputFits (w : ℕ) (input : List ℕ) : Prop :=
  input.length < 2 ^ w ∧ ∀ x ∈ input, x < 2 ^ w

/-! ## Decision in time `T`

A decision problem is a set `A ⊆ α` of instances, given to the machine by an encoding
`encode : α → List ℕ`. Two functions on instances set the terms: `T a` bounds the running time
on instance `a`, and `bits a` is the word-size threshold: the program must work at every word
size from `bits a` on that the input fits. One program serves every such word size, and can read
it with `width`. Word sizes that the input does not fit impose nothing, so the input need not
fit at `w = bits a` itself. (The length condition gives `k < 2 ^ w`, so all input addresses
`0, …, k` fit in a word; for `k > 0` this is the same as `w > log₂ k`. `bits` can ask for
more.)
-/

/-- `p` decides `A ⊆ α` in time `T`, on instances encoded by `encode`: for every instance `a`
and every word size `w ≥ bits a` at which the input fits, `p` halts within `T a` instructions
with output `1` if `a ∈ A` and `0` if not. One program serves every such word size. -/
def Decides {α : Type*} (p : Program r) (A : Set α) (encode : α → List ℕ) (T bits : α → ℕ) :
    Prop :=
  ∀ a w, bits a ≤ w → InputFits w (encode a) →
    ∃ v n, Halts w p (init (encode a)) v n ∧ n ≤ T a ∧ (a ∈ A → v = 1) ∧ (a ∉ A → v = 0)

/-- `A` is decidable in time `T` (from word size `bits` on) if some program, with some number
of registers, decides it. -/
def DecidableInTime {α : Type*} (A : Set α) (encode : α → List ℕ) (T bits : α → ℕ) : Prop :=
  ∃ r, ∃ p : Program r, Decides p A encode T bits

/-! ## Connection to the library

Two theorems connect the machine of this file to the library's word RAM `Cslib.WordRAM` over its
exact basis `Cslib.WordRAM.Basis.exact`. Names with the prefix `Cslib.WordRAM.` are from the
library: `Cslib.WordRAM.Program .exact r` is a program over the exact basis with `r` registers,
a state `⟨pc, ⟨reg, mem⟩⟩` has the same three parts as here, `Cslib.WordRAM.step` is one
deterministic step, and `Cslib.WordRAM.Executes w q s v n` says that `q` halts from `s` with
output `v` after exactly `n` instructions. The library's instruction type also has `rand` for
randomized algorithms, on which `Cslib.WordRAM.step` faults. The predicate `q.IsRandFree` says
that `q` contains no `rand` instruction. A reader does not need to know how these library
definitions are made: `runsAgree` matches programs of this file with the `rand`-free library
programs for single steps and halting runs, and `decidableInTime_iff` equates the library's
uniform decidability in time `T` (`Cslib.WordRAM.UniformDecidableInTime`) with that of this file
without restriction.
-/

/-- An outcome of this file and an outcome of `Cslib.WordRAM` *agree* if both continue in the
same state (same next instruction, registers and memory), both halt with the same output, or both
fault. -/
def OutcomeAgrees : Outcome r → Cslib.WordRAM.Outcome r → Prop
  | .next s, .next t => t = ⟨s.pc, ⟨s.reg, s.mem⟩⟩
  | .halt v, .halt v' => v = v'
  | .fault, .fault => True
  | _, _ => False

/-- A program `p` of this file and a program `q` of `Cslib.WordRAM` *run alike*: from every
state `⟨pc, reg, mem⟩` and at every word size, one step of each has agreeing outcomes, and both
halt with the same output after the same number of instructions. -/
def Same (p : Program r) (q : Cslib.WordRAM.Program .exact r) : Prop :=
  ∀ w pc reg mem,
    OutcomeAgrees (step w p ⟨pc, reg, mem⟩) (Cslib.WordRAM.step w q ⟨pc, ⟨reg, mem⟩⟩) ∧
    ∀ v n, Halts w p ⟨pc, reg, mem⟩ v n ↔ Cslib.WordRAM.Executes w q ⟨pc, ⟨reg, mem⟩⟩ v n

/-- **Same machine.** Each program of this file runs alike with some `rand`-free program of
`Cslib.WordRAM` over `Basis.exact` with the same registers, and conversely every `rand`-free
program of `Cslib.WordRAM` over `Basis.exact` runs alike with some program of this file. -/
theorem runsAgree (r : ℕ) :
    (∀ p : Program r, ∃ q : Cslib.WordRAM.Program .exact r, q.IsRandFree ∧ Same p q) ∧
      ∀ q : Cslib.WordRAM.Program .exact r, q.IsRandFree → ∃ p : Program r, Same p q :=
  WordRAMBridge.runsAgree
    ⟨AluOp, .add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr, @AluOp.rec, AluOp.eval,
      Instr, .const, .copy, .alu, .width, .load, .store, .jump, .branchEq, .branchLt, .halt,
      @Instr.rec, State, .mk, Outcome, .next, .halt, .fault, step, Halts, OutcomeAgrees⟩
    (by constructor <;> simp_all [step, Halts, OutcomeAgrees, AluOp.eval]) r

/-- **Same time classes.** For every type `α` of instances, problem `A`, encoding, time bound
`T` and word-size threshold `bits`, `A` is decidable in time `T` on the machine of this file
exactly when one program of `Cslib.WordRAM` over `Basis.exact` decides it with the same
encoding and time bound at every word size from the threshold on. So a library theorem that
concludes `Cslib.WordRAM.UniformDecidableInTime .exact A (fun _ => encode) (fun a _ => T a)
(fun a w => bits a ≤ w)` is a time bound on the machine of this file. This theorem does not cover
the library's nonuniform `Cslib.WordRAM.DecidableInTime`, where the program may depend on the
word size, nor encodings and time bounds that depend on the word size. -/
theorem decidableInTime_iff {α : Type u} (A : Set α) (encode : α → List ℕ) (T bits : α → ℕ) :
    DecidableInTime A encode T bits ↔
      Cslib.WordRAM.UniformDecidableInTime .exact A (fun _ => encode) (fun a _ => T a)
        (fun a w => bits a ≤ w) :=
  WordRAMBridge.decidableInTime_iff
    ⟨AluOp, .add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr, @AluOp.rec, AluOp.eval,
      Instr, .const, .copy, .alu, .width, .load, .store, .jump, .branchEq, .branchLt, .halt,
      @Instr.rec, State, .mk, Outcome, .next, .halt, .fault, step, Halts, OutcomeAgrees⟩
    (by constructor <;> simp_all [step, Halts, OutcomeAgrees, AluOp.eval]) A encode T bits

/--
info: abstract audit passed for `ComplexityTests.Abstracts.WordRAMAbstract`: 234 root
declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.WordRAMAbstract allowing [
  Complexity.Computability.WordRAM.Defs,
  Complexity.Computability.WordRAM.Basis,
  Complexity.Computability.WordRAM.Time
]

end ComplexityTests.Abstracts.WordRAMAbstract
