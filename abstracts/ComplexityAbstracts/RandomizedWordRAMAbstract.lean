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

/-! # The randomized word RAM, quicksort, and quickselect: a formal abstract

This file states the randomized word-RAM model, its worst-case and expected running time, and the
correctness and cost bounds of randomized in-place three-way quicksort and quickselect.

For an `n`-word input `input` satisfying `InputFits w input` and `3 * (Nat.log 2 n + 1) ≤ w`,
`quicksort` sorts the array in place using a `2 * n`-word auxiliary range stack in
`[n + 1, 3 * n + 1)` and runs in `O(n log n)` expected time. On `init (k :: input)`
(`M[0] = n + 1`, `M[1] = k`, and `M[2 .. n + 2) = input`) satisfying `InputFits w (k :: input)`,
when `k < n` and `2 * (Nat.log 2 n + 1) ≤ w`, `quickselect` selects the `0`-indexed `k`-th
smallest element in place with **zero** auxiliary memory words (modifying only `[2, n + 2)`) and
runs in linear expected time `80 n + 15`. When `InputFits w (k :: input)` and `n ≤ k`,
`quickselect` halts deterministically in `8` steps with output `0` and leaves memory unchanged.

At word size `w`, a *word* is a natural number below `2 ^ w`. A machine has `r` registers
`R[0], …, R[r - 1]` and memory `M[a]` for `a : ℕ`. Its ten deterministic instructions, `init`, and
`InputFits` match `WordRAMAbstract` (restated because an abstract cannot import another abstract,
and in-place algorithms inspect final memory at `halt`). Alongside them, `rand d i` reads
`n = R[i]`, faults when `n ≥ 2 ^ w`, and otherwise draws a uniform integer in `{0, …, n}` into
`R[d]` in one step and one random call (`n = 0` returns `0` and still counts as one call).

Simplifications relative to `Cslib.WordRAM`, `Cslib.Algorithms.WordRAM.Quicksort`, and
`Cslib.Algorithms.WordRAM.Quickselect`:

* `AluOp` fixes `Basis.exact` (as in `WordRAMAbstract`) instead of a general `Basis`. The bridge
  lifts `Quicksort` and `Quickselect` from `Basis.standard` because neither uses division or
  remainder and no reached subtraction underflows.
* `Instr` lists the eleven flat instructions directly instead of `Op`, `Cond`, and `Code`.
* `Comp` specializes `ProbComp` to finite-depth uniform trees over `Fin (n + 1)` with direct
  `CallsAtMost` and `Comp.eval` (`RandBitsBounded` stays in the library).
* `State` and `Cfg.halted` carry `reg` and `mem` directly without `Data`, keeping final registers
  and memory at `halt` for in-place postconditions.
* Array slices and unchanged memory use `slice` and address bounds instead of `Block.Realizes` and
  `Modifies`; `logWidth c n` is written inline as `c * (Nat.log 2 n + 1)`; and for `k < n` the
  `0`-indexed `k`-th order statistic is written `input.mergeSort.getD k 0` (`List.mergeSort` sorts
  `input` in nondecreasing order `(· ≤ ·)`).

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

/-! ## Input convention, memory slices, quicksort, and quickselect

An input `x₁, …, xₖ` starts at `init` with `M[0] = k`, `M[1] = x₁, …, M[k] = xₖ`, and `0`
elsewhere; `slice a b mem` reads `[M[a], …, M[b - 1]]`.

For sorting (`quicksort`), one fixed 16-register program sorts `input` of length `n` in place by
iterative three-way randomized quicksort (splitting around a random pivot into `<`, `=`, and `>`),
using `M[n + 1 .. 3 n + 1)` as a `2 n`-word stack. At word size `w ≥ 3 * (Nat.log 2 n + 1)`
(`Nat.log 2 0 = 0`, so `w ≥ 3` addresses `3 n + 3` for all `n`) on any word-fitting input, every
branch halts within `20 n² + 8 n + 32` steps and makes at most `n - 1` `rand` calls. Each halting
state places a sorted (`Pairwise (· ≤ ·)`) permutation of `input` in `M[1 .. n + 1)` and leaves
memory outside `1, …, 3 n` unchanged. Expected running time is at most
`120 n (Nat.log 2 n + 1) + 32`.

For selection (`quickselect`), `init (k :: input)` places `n + 1` in `M[0]`, the `0`-indexed target
rank `k` in `M[1]`, and the `n`-element array `input` in `M[2 .. n + 2)`. One fixed 16-register
program narrows a single active subarray `[lo, hi)` containing `2 + k` by three-way Dutch National
Flag partitioning with **zero** auxiliary memory words. When `k < n` and
`w ≥ 2 * (Nat.log 2 n + 1)` (`w ≥ 2` addresses `n + 2` for all `n`) on a word-fitting `k :: input`,
every branch halts within `10 n² + 15` steps, makes at most `n - 1` `rand` calls, and returns the
`0`-indexed `k`-th smallest element `ans = input.mergeSort.getD k 0` (where `List.mergeSort` sorts
`input` in nondecreasing order `(· ≤ ·)`). Each halting state permutes `M[2 .. n + 2)` in place so
that `M[2 + k] = ans`, `M[2 + i] ≤ ans` for `i < k`, and `ans ≤ M[2 + i]` for `k < i < n`, and
leaves all memory outside `2, …, n + 1` unchanged. Expected running time is at most `80 n + 15`
uniformly over all `k < n` and duplicate keys. When `n ≤ k` on a word-fitting `k :: input`, the
same program halts deterministically in `8` steps, returns `0`, makes `0` `rand` calls, leaves
memory unchanged, and has `expectedTime = 8`.
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

/-- **In-place randomized quickselect.** One fixed 16-register program selects the `0`-indexed
`k`-th smallest element of every word-fitting `k :: input` of length `n = input.length` in place
with zero auxiliary memory words:
1. When `k < n` and `w ≥ 2 * (Nat.log 2 n + 1)`, every branch halts within `10 n² + 15` steps,
   makes at most `n - 1` `rand` calls, and returns `ans = input.mergeSort.getD k 0`. Each halting
   state permutes `M[2 .. n + 2)` in place so that `M[2 + k] = ans`, `M[2 + i] ≤ ans` for `i < k`,
   and `ans ≤ M[2 + i]` for `k < i < n`, and leaves all memory outside `2, …, n + 1` unchanged.
   Expected running time is at most `80 n + 15`.
2. When `n ≤ k`, the program halts deterministically in `8` steps, returns `0`, makes `0` `rand`
   calls, leaves memory unchanged, and has `expectedTime = 8`. -/
theorem quickselect :
    ∃ p : Program 16,
      (∀ (w k : ℕ) (input : List ℕ),
        k < input.length →
        2 * (Nat.log 2 input.length + 1) ≤ w →
        InputFits w (k :: input) →
        let n := input.length
        let T := 10 * n ^ 2 + 15
        let ans := input.mergeSort.getD k 0
        HaltsWithin w p (init (k :: input)) T ∧
        RandCallsBounded w p (init (k :: input)) T (n - 1) ∧
        (∀ cfg ∈ (evalRand w p T (init (k :: input))).support,
          ∃ reg mem, cfg = .halted ans reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            (slice 2 (n + 2) mem).Perm input ∧
            mem (2 + k) = ans ∧
            (∀ i < k, mem (2 + i) ≤ ans) ∧
            (∀ i, k < i → i < n → ans ≤ mem (2 + i)) ∧
            (∀ a, a < 2 ∨ n + 2 ≤ a →
              mem a = (init (r := 16) (k :: input)).mem a)) ∧
        expectedTime w p (init (k :: input)) ≤
          ((80 * n + 15 : ℕ) : ENNReal)) ∧
      (∀ (w k : ℕ) (input : List ℕ),
        input.length ≤ k →
        InputFits w (k :: input) →
        HaltsWithin w p (init (k :: input)) 8 ∧
        RandCallsBounded w p (init (k :: input)) 8 0 ∧
        (∀ cfg ∈ (evalRand w p 8 (init (k :: input))).support,
          ∃ reg mem, cfg = .halted 0 reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            mem = (init (r := 16) (k :: input)).mem) ∧
        expectedTime w p (init (k :: input)) = 8) :=
  RandomizedWordRAMBridge.quickselect
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
info: abstract audit passed for `ComplexityAbstracts.RandomizedWordRAMAbstract`: 282 root
declarations, 256 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.RandomizedWordRAMAbstract

end ComplexityAbstracts.RandomizedWordRAMAbstract
