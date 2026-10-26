/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.RandomizedWordRAMBridge
import Cslib.Probability.PMF
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Log

/-! # The randomized word RAM and in-place quicksort: a formal abstract

This file states the randomized word-RAM model, its worst-case and expected running time, and the
correctness and cost bounds of randomized in-place three-way quicksort.

For an `n`-word input, the theorem assumes word-fitting values and
`3 * (Nat.log 2 n + 1) ≤ w`. It sorts the original array using a `2 * n`-word auxiliary range
stack in `[n + 1, 3 * n + 1)`; memory outside the input-and-stack frame is preserved.

At word size `w`, a *word* is a natural number below `2 ^ w`. A machine has `r` registers
`R[0], …, R[r - 1]` and memory `M[a]` for `a : ℕ`. Its ten deterministic instructions, `init`, and
`InputFits` match `WordRAMAbstract` (restated because an abstract cannot import another abstract,
and in-place algorithms inspect final memory at `halt`). Alongside them, `rand d i` reads
`n = R[i]`, faults when `n ≥ 2 ^ w`, and otherwise draws a uniform integer in `{0, …, n}` into
`R[d]` in one step and one random call (`n = 0` returns `0` and still counts as one call).

Simplifications relative to `Cslib.WordRAM` and `Cslib.Algorithms.WordRAM.Quicksort`:

* `AluOp` fixes `Basis.exact` (as in `WordRAMAbstract`) instead of a general `Basis`. The bridge
  lifts `Quicksort` from `Basis.standard` because it uses no division or remainder and no reached
  subtraction underflows.
* `Instr` lists the eleven flat instructions directly instead of `Op`, `Cond`, and `Code`.
* `Comp` specializes `ProbComp` to finite-depth uniform trees over `Fin (n + 1)` with direct
  `CallsAtMost` and `Comp.eval` (`RandBitsBounded` stays in the library).
* `State` and `Cfg.halted` carry `reg` and `mem` directly without `Data`, keeping final registers
  and memory at `halt` for in-place postconditions.
* Array slices and unchanged memory use `slice` and address bounds instead of `Block.Realizes` and
  `Modifies`, and `logWidth 3 n` is written inline as `3 * (Nat.log 2 n + 1)`.

Lean checks the proofs via `RandomizedWordRAMBridge` under `propext`, `Classical.choice`, and
`Quot.sound`; `#check_abstract` verifies zero allowlisted project modules.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
* [M. L. Fredman and D. E. Willard, *Surpassing the information theoretic bound with fusion
  trees*][FredmanWillard1993]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

namespace ComplexityAbstracts.RandomizedWordRAMAbstract

/-! ## Words, operations, and instructions

Each arithmetic, bitwise, or shift operation in `AluOp` computes its exact value on natural
numbers, returning `none` where undefined (`x - y` when `y > x`, and `x / 0` and `x % 0`). In
`AluOp.eval`, a bare natural number stands for `some n`. The instruction `rand d i` draws a
uniform integer in `{0, …, R[i]}`.
-/

/-- The ten exact binary operations on natural numbers. -/
inductive AluOp
  | add | sub | mul | div | mod | and | or | xor | shl | shr

/-- Exact value of a binary operation before word-range checking, or `none` when undefined. -/
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

/-- Instructions over `r` registers: ten deterministic instructions and bounded random sampling
`rand`. -/
inductive Instr (r : ℕ)
  | const (d : Fin r) (x : ℕ)         -- R[d] := x
  | copy (d i : Fin r)                -- R[d] := R[i]
  | alu (f : AluOp) (d i j : Fin r)   -- R[d] := f(R[i], R[j])
  | width (d : Fin r)                 -- R[d] := w, the word size
  | load (d a : Fin r)                -- R[d] := M[R[a]]
  | store (a i : Fin r)               -- M[R[a]] := R[i]
  | jump (t : ℕ)                      -- go to instruction t
  | branchEq (i j : Fin r) (t : ℕ)    -- go to t if R[i] = R[j], else next
  | branchLt (i j : Fin r) (t : ℕ)    -- go to t if R[i] < R[j], else next
  | halt (i : Fin r)                  -- stop with output R[i]
  | rand (d i : Fin r)                -- R[d] ← uniform on {0, …, R[i]}

/-- A program over `r` registers is a list of instructions indexed from `0`. -/
abbrev Program (r : ℕ) := List (Instr r)

/-! ## Finite-depth uniform sampling trees

A clocked execution builds a finite-depth tree `Comp α` of uniform draws `sample n next` over
`Fin (n + 1)` (`{0, …, n}`). Keeping the tree separates output distributions from pathwise call
counts, including `rand` on `0` whose output distribution is a point mass. `Comp.eval` maps a tree
to a discrete probability distribution (`PMF α`), and `Comp.CallsAtMost m R` states that every
branch makes at most `R` draws.
-/

/-- A finite-depth computation tree whose random choices draw uniformly from `Fin (n + 1)`. -/
inductive Comp (α : Type) : Type
  | pure (a : α)
  | sample (n : ℕ) (next : Fin (n + 1) → Comp α)

/-- Sequential composition of sampling trees. -/
def Comp.bind {α β : Type} : Comp α → (α → Comp β) → Comp β
  | .pure a, f => f a
  | .sample n next, f => .sample n fun k => (next k).bind f

/-- Probability distribution induced by answering every `sample n` uniformly on `Fin (n + 1)`. -/
noncomputable def Comp.eval {α : Type} : Comp α → PMF α
  | .pure a => PMF.pure a
  | .sample n next =>
    (Cslib.Probability.PMF.uniformOfFintype (Fin (n + 1))).bind fun k =>
      (next k).eval

/-- Every branch of `m` performs at most `R` random draws. -/
def Comp.CallsAtMost {α : Type} : Comp α → ℕ → Prop
  | .pure _, _ => True
  | .sample _ _, 0 => False
  | .sample _ next, R + 1 => ∀ k, (next k).CallsAtMost R

/-! ## Configurations, clocked runs, and cost measures

A configuration is `running` at a `State`, `halted` with scalar output `v` alongside final registers
`reg` and memory `mem`, or `faulted`. Both `halted` and `faulted` are absorbing: further clock ticks
leave them unchanged and make zero `rand` calls.

At an active state `s`, `rand d i` faults when `s.reg i ≥ 2 ^ w`. When `s.reg i < 2 ^ w`, it draws
`k` uniformly from `Fin (s.reg i + 1)` (`{0, …, s.reg i}`), writes `k` to `R[d]`, and advances `pc`
to `pc + 1` in one step and one `sample` node.

Expected running time `expectedTime w p s` takes values in the extended nonnegative reals `ENNReal`
(`[0, ∞]`). It sums over `t : ℕ` the probability that the configuration after `t` steps is
`running`. Because `halted` and `faulted` are absorbing, a branch that halts after `n` steps is
`running` at horizons `0, 1, …, n - 1` and contributes `n`, while non-terminating mass contributes
`∞`.
-/

/-- Machine state: instruction index `pc`, registers `reg`, and memory `mem`. -/
structure State (r : ℕ) where
  /-- Index of the next instruction. -/
  pc : ℕ
  /-- Register file `R[0], …, R[r - 1]`. -/
  reg : Fin r → ℕ
  /-- Unbounded natural-addressed memory `M[a]`. -/
  mem : ℕ → ℕ

/-- Configuration of a clocked randomized run: active, halted with final data, or faulted. -/
inductive Cfg (r : ℕ)
  | running (s : State r)
  | halted (v : ℕ) (reg : Fin r → ℕ) (mem : ℕ → ℕ)
  | faulted

/-- One step of program `p` at word size `w`. Halted and faulted configurations are absorbing. -/
def stepRand {r : ℕ} (w : ℕ) (p : Program r) : Cfg r → Comp (Cfg r)
  | .halted v reg mem => .pure (.halted v reg mem)
  | .faulted => .pure .faulted
  | .running s =>
    let next (d : Fin r) (x : ℕ) : Comp (Cfg r) :=
      .pure (.running
        { s with pc := s.pc + 1, reg := Function.update s.reg d x })
    let nextWord (d : Fin r) (x : ℕ) : Comp (Cfg r) :=
      if x < 2 ^ w then next d x else .pure .faulted
    match p[s.pc]? with
    | none => .pure .faulted
    | some (.const d x) => nextWord d x
    | some (.copy d i) => next d (s.reg i)
    | some (.alu f d i j) =>
      match f.eval (s.reg i) (s.reg j) with
      | some x => nextWord d x
      | none => .pure .faulted
    | some (.width d) => next d w
    | some (.load d a) => next d (s.mem (s.reg a))
    | some (.store a i) =>
      .pure (.running { s with
        pc := s.pc + 1
        mem := Function.update s.mem (s.reg a) (s.reg i) })
    | some (.jump t) => .pure (.running { s with pc := t })
    | some (.branchEq i j t) =>
      .pure (.running
        { s with pc := if s.reg i = s.reg j then t else s.pc + 1 })
    | some (.branchLt i j t) =>
      .pure (.running
        { s with pc := if s.reg i < s.reg j then t else s.pc + 1 })
    | some (.halt i) => .pure (.halted (s.reg i) s.reg s.mem)
    | some (.rand d i) =>
      if s.reg i < 2 ^ w then
        .sample (s.reg i) fun k => next d k.val
      else .pure .faulted

/-- Clocked `T`-step sampling tree from configuration `cfg`. -/
def runRand {r : ℕ} (w : ℕ) (p : Program r) : ℕ → Cfg r → Comp (Cfg r)
  | 0, cfg => .pure cfg
  | T + 1, cfg => (stepRand w p cfg).bind (runRand w p T)

/-- Distribution over configurations after `T` steps starting from state `s`. -/
noncomputable def evalRand {r : ℕ} (w : ℕ) (p : Program r) (T : ℕ)
    (s : State r) : PMF (Cfg r) :=
  (runRand w p T (.running s)).eval

/-- Every positive-probability outcome after `T` steps from `s` has halted cleanly. -/
def HaltsWithin {r : ℕ} (w : ℕ) (p : Program r) (s : State r) (T : ℕ) : Prop :=
  ∀ cfg ∈ (evalRand w p T s).support, ∃ v reg mem, cfg = .halted v reg mem

/-- Every execution branch over `T` steps from `s` makes at most `R` `rand` calls. -/
def RandCallsBounded {r : ℕ} (w : ℕ) (p : Program r) (s : State r)
    (T R : ℕ) : Prop :=
  (runRand w p T (.running s)).CallsAtMost R

/-- Expected running time in `ENNReal`, as the sum over `t` of the probability of still running. -/
noncomputable def expectedTime {r : ℕ} (w : ℕ) (p : Program r)
    (s : State r) : ENNReal :=
  ∑' t : ℕ,
    (evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = .running u}

/-! ## Input convention, memory slices, and randomized quicksort

An input `x₁, …, xₖ` starts at `init` with `M[0] = k`, `M[1] = x₁, …, M[k] = xₖ`, and `0`
elsewhere; `slice a b mem` reads `[M[a], …, M[b - 1]]`. One fixed 16-register program sorts in
place by iterative three-way randomized quicksort (splitting around a random pivot into `<`, `=`,
and `>`), using `M[n + 1 .. 3 n + 1)` as a `2 n`-word stack. At word size
`w ≥ 3 * (Nat.log 2 n + 1)` (`Nat.log 2 0 = 0`, so `w ≥ 3` addresses `3 n + 3` for all `n`) on any
word-fitting input, every branch halts within `20 n² + 8 n + 32` steps and `n - 1` `rand` calls,
leaving a sorted (`Pairwise (· ≤ ·)`) permutation of `input` in `M[1 .. n + 1)` and preserving
memory outside `1, …, 3 n`. Across all inputs, including duplicates, its expected running time is at
most `120 n (Nat.log 2 n + 1) + 32`.
-/

/-- Start state on `input = [x₁, …, xₖ]`: `pc = 0`, registers `0`, `M[0] = k`, `M[1..k] = input`. -/
def init {r : ℕ} (input : List ℕ) : State r :=
  ⟨0, fun _ => 0, fun a => (input.length :: input).getD a 0⟩

/-- An input fits word size `w` when its length and every element are words below `2 ^ w`. -/
def InputFits (w : ℕ) (input : List ℕ) : Prop :=
  input.length < 2 ^ w ∧ ∀ x ∈ input, x < 2 ^ w

/-- The memory slice `[mem a, mem (a + 1), …, mem (b - 1)]` of length `b - a`. -/
def slice (a b : ℕ) (mem : ℕ → ℕ) : List ℕ :=
  (List.range (b - a)).map fun i => mem (a + i)

/-- **In-place randomized quicksort.** One fixed 16-register program sorts every word-fitting input
of length `n` in place at word size `w ≥ 3 * (Nat.log 2 n + 1)`. Every branch halts within
`20 n² + 8 n + 32` steps and `n - 1` `rand` calls with a sorted permutation of `input` in
`M[1 .. n + 1)` and memory outside `1, …, 3 n` unchanged. Expected running time is at most
`120 n (Nat.log 2 n + 1) + 32`. -/
theorem quicksort :
    ∃ p : Program 16,
      ∀ (w : ℕ) (input : List ℕ),
        3 * (Nat.log 2 input.length + 1) ≤ w →
        InputFits w input →
        let n := input.length
        let T := 20 * n ^ 2 + 8 * n + 32
        HaltsWithin w p (init input) T ∧
        RandCallsBounded w p (init input) T (n - 1) ∧
        (∀ cfg ∈ (evalRand w p T (init input)).support,
          ∃ reg mem, cfg = .halted 0 reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            (slice 1 (n + 1) mem).Perm input ∧
            (slice 1 (n + 1) mem).Pairwise (· ≤ ·) ∧
            (∀ a, a < 1 ∨ 3 * n + 1 ≤ a →
              mem a = (init (r := 16) input).mem a)) ∧
        expectedTime w p (init input) ≤
          ((120 * n * (Nat.log 2 n + 1) + 32 : ℕ) : ENNReal) :=
  RandomizedWordRAMBridge.quicksort
    ⟨AluOp, .add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr,
      @AluOp.rec, AluOp.eval,
      Instr, .const, .copy, .alu, .width, .load, .store, .jump,
      .branchEq, .branchLt, .halt, .rand, @Instr.rec,
      Comp, @Comp.pure, @Comp.sample, @Comp.bind, @Comp.eval,
      @Comp.CallsAtMost,
      State, .mk, Cfg, .running, .halted, .faulted, @stepRand, @runRand⟩
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [AluOp.eval, Comp.bind, Comp.eval, Comp.CallsAtMost,
        stepRand, runRand])

/--
info: abstract audit passed for `ComplexityAbstracts.RandomizedWordRAMAbstract`: 281 root
declarations, 252 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.RandomizedWordRAMAbstract

end ComplexityAbstracts.RandomizedWordRAMAbstract
