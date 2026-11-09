/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.KargerMinCutBridge
import Cslib.Probability.PMF
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Log

/-! # Karger and Karger–Stein global minimum cut on the word RAM: a formal abstract

This file states the randomized word-RAM model, weighted undirected multigraphs and their global
minimum cuts, and the correctness, resource bounds, and success/failure probabilities of Karger's
1993 contraction algorithm and Karger and Stein's 1996 recursive `FastCut` algorithm in five forms:

1. **Single-trial contraction (`kargerSingleTrial`):** one fixed 16-register program contracts an
   `n`-vertex multigraph (`n ≥ 2`) down to two supervertices in `42 * n ^ 2 + 12 * n + 21`
   worst-case steps and at most `n - 2` random draws, always returning the weight of a genuine
   non-trivial cut (`≥ minCut W`), and finding `minCut W` with probability at least
   `2 / (n * (n - 1))` whenever `0 < minCut W`.
2. **Repeated-trial amplification (`kargerAmplified`):** one fixed 22-register program executes `R`
   (`R ≥ 1`) independent contractions on fresh working copies of the input matrix in
   `R * (50 * n ^ 2 + 12 * n + 30) + 16` steps and `R * (n - 2)` random draws, missing `minCut W`
   with probability at most `(1 - 2 / (n * (n - 1))) ^ R` whenever `0 < minCut W`.
3. **High-probability Karger (`kargerHighProb`):** one fixed 22-register program computes
   `R = (n * (n - 1) / 2) * (Nat.log 2 n + 2)` in registers and runs `R` independent contractions
   in `33 * n ^ 4 * (Nat.log 2 n + 2)` worst-case steps, missing `minCut W` with probability at
   most `1 / (2 * n)` whenever `0 < minCut W`.
4. **Karger–Stein recursive `FastCut` (`kargerSteinFastCut`):** one fixed 24-register program
   recursively branches twice down to an integer threshold in `2500 * n ^ 2 * (Nat.log 2 n + 2)`
   (`O(n ^ 2 log n)`) worst-case steps and at most `6 * (n * n)` random draws, using `26 * n ^ 2`
   scratch words, always returning a genuine non-trivial cut weight (`≥ minCut W`), and finding
   `minCut W` with probability at least `1 / (Nat.log 2 n + 15)` whenever `0 < minCut W`.
5. **High-probability Karger–Stein (`kargerSteinHighProb`):** one fixed 24-register program computes
   `R = (Nat.log 2 n + 15) * (Nat.log 2 n + 2)` in registers and runs `R` independent `FastCut`
   trees in `2600 * n ^ 2 * (Nat.log 2 n + 15) * (Nat.log 2 n + 2) ^ 2` (`O(n ^ 2 log ^ 3 n)`)
   worst-case steps, missing `minCut W` with probability at most `1 / (2 * n)` whenever
   `0 < minCut W`.

The single-trial bound `2 / (n * (n - 1))` formalizes `[KargerStein1996]`, Section 2, Theorem 2.2
(via Lemma 2.1; Section 2.1, Corollary 2.4 for weighted graphs), `[Karger1993]`, Section 2,
Theorem 2.1 (whose proof computes the exact product `C(n, 2)⁻¹`; the statement is asymptotic), and
`[MitzenmacherUpfal2017]`, Section 1.5, Theorem 1.8 (paraphrase), where the source's `C(n, 2)⁻¹` is
written `2 / (n * (n - 1))`. The `O(n ^ 2)` step bounds follow the adjacency-matrix and
degree-array implementation of `[KargerStein1996]`, Section 3 (Section 3.2, Corollary 3.2), and
`kargerAmplified` and `kargerHighProb` instantiate the `O(n ^ 2 log n)`-trial amplification of
`[Karger1993]`, Section 2, Corollary 2.1 (paraphrase). Relative to
`[KargerStein1996]`, Section 3, our program uses two implementation variants: (a) whereas
Section 3.1 draws twice (`u` proportional to `D[u]` then `v` proportional to `W[u, v]`), one
unit-cost `rand` draw in `{0, …, S - 1}` resolved by prefix sums over `rowDeg` and `W[u, v]`
achieves the same `2 * W[u, v] / S` distribution of Lemma 3.1; (b) whereas Section 3.2 takes
`O(n)` time per contraction step, swap-compacting active slot `k - 1` into `v` runs each step in
`O(k)` time on `k` active supervertices. The concrete trial count
`R = (n * (n - 1) / 2) * (Nat.log 2 n + 2)` and the `1 / (2 * n)` failure bound are our own
parameter choice, and `0 < minCut W` in the probability clauses is excluded only for proof
convenience (deterministic `S = 0` contraction still halts without faulting and outputs a valid cut
weight).

The recursive `FastCut` theorems (`kargerSteinFastCut` and `kargerSteinHighProb`) formalize
`[KargerStein1996]`, Section 4 ("The Recursive Contraction Algorithm"): Figure 6
(`Recursive-Contract`), Lemma 4.1 (`O(n ^ 2 log n)` running time), Lemma 4.2 (`O(n ^ 2)` space in
the matrix representation), Lemma 4.3 (`Omega(1 / log n)` single-tree success probability via
equation (2)), and the minimum-cut-value part of Theorem 4.4 (paraphrase). Theorem 4.4 finds all
minimum cuts with high probability in `O(n ^ 2 log ^ 3 n)` time and `O(m log(n ^ 2 / m))` space;
`kargerSteinHighProb` proves that the returned value is `minCut W` except with probability at
most `1 / (2 * n)`, within the `O(n ^ 2)` matrix workspace. As in Figure 6, a leaf
(`2 <= k <= 6`) runs one randomized contraction down to `2` vertices; the cutoff follows
equation (2) and the remark at the end of the proof of Lemma 4.3 (recurse for `n >= 7`), whereas
Figure 6 itself tests "fewer than 6 vertices". The `15` in `1 / (Nat.log 2 n + 15)` is the
source's constant: equation (2)'s base-case probability `1 / 15` gives
`p_k = 4 / (z_k + 1) >= 2 / (30 + k)` (from `z_0 = 59` and `z_k < 59 + 2 k` for `k >= 1` in the
proof of Lemma 4.3), evaluated at recursion depth at most `2 * Nat.log 2 n`. This formalization
makes three design choices of its own: (1) instead of `ceil(1 + k / sqrt 2)` (Figure 6), each
internal node (`k >= 7`) contracts to the least integer `t >= 2` with
`k * (k - 1) <= 2 * t * (t - 1)` (never larger than `ceil(1 + k / sqrt 2)`, and strictly smaller
at e.g. `k = 8`, where `t = 6` versus `7`, while keeping survival probability `>= 1 / 2`); (2) the
step constants `2500` and `2600`, the trial count `R = (Nat.log 2 n + 15) * (Nat.log 2 n + 2)`,
and the `1 / (2 * n)` failure target are our own (the proof of Theorem 4.4 uses `O(log ^ 2 n)`
repetitions); and (3) the integer quadratic potential `(k - 4) ^ 2` bounding recursion depth, leaf
count, and internal work without `Real.sqrt` or `Real.log` is original to this formalization.

At word size `w`, a *word* is a natural number below `2 ^ w`, and `Nat.log 2 n` denotes
`floor(log_2 n)` (with `0` at `0`). The Karger (1993) theorems assume `3 * (Nat.log 2 n + 1) ≤ w`
and the Karger–Stein (1996) theorems assume `4 * (Nat.log 2 n + 1) ≤ w` (so workspace addresses and
trial counts fit in a word), alongside
`totalDoubledWeight W < 2 ^ w` (so every edge weight, vertex degree, and total active edge weight
fits in a word across contractions).

Simplifications relative to `Cslib.WordRAM` and `Cslib.Algorithms.WordRAM.Karger`:

* `AluOp` fixes `Basis.exact` (`x - y = none` when `y > x`, and division/modulo by `0` return
  `none`). `KargerMinCutBridge` lifts the structured `Basis.standard` implementations because they
  use no division or modulo and no reached subtraction underflows.
* `Instr`, `Comp`, `State`, and `Cfg` match `RandomizedWordRAMAbstract` (restated because an
  abstract cannot import another abstract), exposing flat instructions, finite-depth uniform
  sampling trees, and final registers and memory at `halt`.
* `flattenMatrix` uses `List.finRange` and `List.flatMap` directly rather than index division, and
  unchanged memory outside the working scratch frame is stated via explicit address inequalities
  instead of `Modifies` and `Block`.

A reader only needs to inspect the definitions and theorem statements in this file to verify that
the formalization proves the intended mathematical claims. Lean checks the proofs via
`KargerMinCutBridge` and `RandomizedWordRAMBridge` under `propext`, `Classical.choice`, and
`Quot.sound`. The audit command `#check_abstract` verifies that all definitions and theorem
statements in this namespace reference no imported project declarations.

## References

* [D. R. Karger, *Global Min-cuts in RNC, and Other Ramifications of a Simple Min-Cut
  Algorithm*][Karger1993]
* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

namespace ComplexityAbstracts.KargerMinCutAbstract

/-! ## Words, operations, and instructions

Each binary operation in `AluOp` computes its exact value on natural numbers, returning `none`
where undefined (`x - y` when `y > x`, and `x / 0` and `x % 0`). In `AluOp.eval`, a bare natural
number stands for `some n`. Alongside the ten deterministic instructions, `rand d i` draws a
uniform integer in `{0, …, R[i]}` into `R[d]`.
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
`Fin (n + 1)` (`{0, …, n}`). `Comp.eval` maps a tree to a discrete probability distribution
(`PMF α`), and `Comp.CallsAtMost m R` states that every branch performs at most `R` random draws.
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
`reg` and memory `mem`, or `faulted`. Both `halted` and `faulted` are absorbing. Starting from
`init input`, `M[0] = input.length`, `M[1 .. input.length]` holds `input`, and all registers and
remaining memory cells are `0`.
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

/-- Start state on `input = [x₁, …, xₖ]`: `pc = 0`, registers `0`, `M[0] = k`, `M[1..k] = input`. -/
def init {r : ℕ} (input : List ℕ) : State r :=
  ⟨0, fun _ => 0, fun a => (input.length :: input).getD a 0⟩

/-! ## Weighted multigraphs, global minimum cuts, and Karger / Karger–Stein contraction

An `n`-vertex weighted undirected multigraph without self-loops is given by a symmetric
zero-diagonal matrix `W : Fin n → Fin n → ℕ`. A non-trivial cut is a nonempty proper vertex subset
`C : Finset (Fin n)`, with cut weight `cutWeight W C` summing `W u v` across `u ∈ C` and `v ∉ C`.
For `n ≥ 2`, `minCut W` is the minimum cut weight over all non-trivial cuts (`0 < minCut W` holds
precisely when every non-trivial cut crosses at least one positive-weight edge).

In `n :: flattenMatrix W`, `M[1] = n` and `M[2 .. 2 + n ^ 2)` stores `W` in row-major order. One
contraction trial maintains active supervertex degrees and total doubled weight in `O(n)` work per
step, completing in `O(n ^ 2)` steps and at most `n - 2` random draws (`0` draws on zero-weight
steps). For `R :: n :: flattenMatrix W`, `kargerAmplified` keeps the input matrix intact in
`M[3 .. 3 + n ^ 2)` and copies it into `M[3 + n ^ 2 .. 3 + 2 * n ^ 2)` before each trial;
`kargerHighProb` does the same on `n :: flattenMatrix W` with scratch space in
`M[2 + n ^ 2 .. 2 + 2 * n ^ 2 + n)` for `R = (n * (n - 1) / 2) * (Nat.log 2 n + 2)` trials.
Karger–Stein's recursive `FastCut` (`kargerSteinFastCut` and `kargerSteinHighProb`) branches twice
from each `k ≥ 7` down to the smallest `t ≥ 2` with `k * (k - 1) ≤ 2 * t * (t - 1)` using an
explicit frame stack inside `M[2 + n ^ 2 .. 2 + 27 * n ^ 2)`.
-/

/-- Symmetric zero-diagonal edge-weight matrix on `n` vertices. -/
def IsMultigraph {n : ℕ} (W : Fin n → Fin n → ℕ) : Prop :=
  (∀ u v, W u v = W v u) ∧ (∀ u, W u u = 0)

/-- A vertex subset `C` is a non-trivial cut when both `C` and its complement are nonempty. -/
def IsNonTrivialCut {n : ℕ} (C : Finset (Fin n)) : Prop :=
  C.Nonempty ∧ C ≠ Finset.univ

/-- Total weight of edges crossing `(C, Finset.univ \ C)`. -/
def cutWeight {n : ℕ} (W : Fin n → Fin n → ℕ) (C : Finset (Fin n)) : ℕ :=
  ∑ u ∈ C, ∑ v ∈ Finset.univ \ C, W u v

/-- Sum of all entries `∑ u, ∑ v, W u v`, equal to twice the total edge weight of `W`. -/
def totalDoubledWeight {n : ℕ} (W : Fin n → Fin n → ℕ) : ℕ :=
  ∑ u : Fin n, ∑ v : Fin n, W u v

/-- Global minimum cut weight over all non-trivial cuts of `W`. -/
noncomputable def minCut {n : ℕ} (W : Fin n → Fin n → ℕ) : ℕ :=
  sInf {k | ∃ C : Finset (Fin n), IsNonTrivialCut C ∧ cutWeight W C = k}

/-- Row-major `n ^ 2`-word encoding `[W 0 0, …, W 0 (n - 1), …, W (n - 1) (n - 1)]` of `W`. -/
def flattenMatrix {n : ℕ} (W : Fin n → Fin n → ℕ) : List ℕ :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => W u v

/-- **Single-trial Karger contraction (`O(n ^ 2)` time).** One fixed 16-register program contracts
any `n`-vertex multigraph (`n ≥ 2`) at word size `w ≥ 3 * (Nat.log 2 n + 1)` with
`totalDoubledWeight W < 2 ^ w` within `42 * n ^ 2 + 12 * n + 21` steps and `n - 2` `rand` calls.
Every branch outputs `cutWeight W C ≥ minCut W` for a non-trivial cut `C` while preserving memory
outside `[2, 2 + n * n + n)`, and when `0 < minCut W` (excluded only for proof convenience; `S = 0`
contraction still halts fault-free with a valid cut weight) it outputs `minCut W` with probability
at least `2 / (n * (n - 1))`. -/
theorem kargerSingleTrial :
    ∃ p : Program 16,
      ∀ (n w : ℕ) (W : Fin n → Fin n → ℕ),
        2 ≤ n →
        IsMultigraph W →
        3 * (Nat.log 2 n + 1) ≤ w →
        totalDoubledWeight W < 2 ^ w →
        let input := n :: flattenMatrix W
        let T := 42 * n ^ 2 + 12 * n + 21
        HaltsWithin w p (init input) T ∧
        RandCallsBounded w p (init input) T (n - 2) ∧
        (∀ cfg ∈ (evalRand w p T (init input)).support,
          ∃ (reg : Fin 16 → ℕ) (mem : ℕ → ℕ) (C : Finset (Fin n)),
            cfg = .halted (cutWeight W C) reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            IsNonTrivialCut C ∧
            minCut W ≤ cutWeight W C ∧
            (∀ a, a < 2 ∨ 2 + n * n + n ≤ a →
              mem a = (init (r := 16) input).mem a)) ∧
        (0 < minCut W →
          (2 : ENNReal) / ((n * (n - 1) : ℕ) : ENNReal) ≤
            (evalRand w p T (init input)).toOuterMeasure
              {cfg | ∃ reg mem, cfg = .halted (minCut W) reg mem}) :=
  KargerMinCutBridge.kargerSingleTrial
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

/-- **`R`-trial amplified Karger (`O(R * n ^ 2)` time).** One fixed 22-register program executes `R`
(`1 ≤ R < 2 ^ w`) independent contraction trials on `R :: n :: flattenMatrix W` within
`R * (50 * n ^ 2 + 12 * n + 30) + 16` steps and `R * (n - 2)` `rand` calls, preserving the input
matrix and all memory outside `[3 + n * n, 3 + 2 * (n * n) + n)`. Every branch outputs a genuine
non-trivial cut weight `≥ minCut W`, and when `0 < minCut W` (excluded only for proof convenience)
the probability of missing `minCut W` is at most `(1 - 2 / (n * (n - 1))) ^ R`. -/
theorem kargerAmplified :
    ∃ p : Program 22,
      ∀ (R n w : ℕ) (W : Fin n → Fin n → ℕ),
        1 ≤ R →
        2 ≤ n →
        IsMultigraph W →
        3 * (Nat.log 2 n + 1) ≤ w →
        R < 2 ^ w →
        totalDoubledWeight W < 2 ^ w →
        let input := R :: n :: flattenMatrix W
        let T := R * (50 * n ^ 2 + 12 * n + 30) + 16
        HaltsWithin w p (init input) T ∧
        RandCallsBounded w p (init input) T (R * (n - 2)) ∧
        (∀ cfg ∈ (evalRand w p T (init input)).support,
          ∃ (reg : Fin 22 → ℕ) (mem : ℕ → ℕ) (C : Finset (Fin n)),
            cfg = .halted (cutWeight W C) reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            IsNonTrivialCut C ∧
            minCut W ≤ cutWeight W C ∧
            (∀ a, a < 3 + n * n ∨ 3 + 2 * (n * n) + n ≤ a →
              mem a = (init (r := 22) input).mem a)) ∧
        (0 < minCut W →
          (evalRand w p T (init input)).toOuterMeasure
              {cfg | ∀ reg mem, cfg ≠ .halted (minCut W) reg mem} ≤
            ((1 : ENNReal) - (2 : ENNReal) / ((n * (n - 1) : ℕ) : ENNReal)) ^ R) :=
  KargerMinCutBridge.kargerAmplified
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

/-- **High-probability global minimum cut (`O(n ^ 4 log n)` time).** One fixed 22-register program
runs `R = (n * (n - 1) / 2) * (Nat.log 2 n + 2)` independent contractions on `n :: flattenMatrix W`
within `33 * n ^ 4 * (Nat.log 2 n + 2)` steps and `R * (n - 2)` `rand` calls, preserving the input
matrix and all memory outside `[2 + n * n, 2 + 2 * (n * n) + n)`. Every branch outputs a genuine
non-trivial cut weight `≥ minCut W`, and when `0 < minCut W` (excluded only for proof convenience)
the probability of missing `minCut W` is at most `1 / (2 * n)`. -/
theorem kargerHighProb :
    ∃ p : Program 22,
      ∀ (n w : ℕ) (W : Fin n → Fin n → ℕ),
        2 ≤ n →
        IsMultigraph W →
        3 * (Nat.log 2 n + 1) ≤ w →
        totalDoubledWeight W < 2 ^ w →
        let input := n :: flattenMatrix W
        let T := 33 * n ^ 4 * (Nat.log 2 n + 2)
        let R := (n * (n - 1) / 2) * (Nat.log 2 n + 2)
        HaltsWithin w p (init input) T ∧
        RandCallsBounded w p (init input) T (R * (n - 2)) ∧
        (∀ cfg ∈ (evalRand w p T (init input)).support,
          ∃ (reg : Fin 22 → ℕ) (mem : ℕ → ℕ) (C : Finset (Fin n)),
            cfg = .halted (cutWeight W C) reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            IsNonTrivialCut C ∧
            minCut W ≤ cutWeight W C ∧
            (∀ a, a < 2 + n * n ∨ 2 + 2 * (n * n) + n ≤ a →
              mem a = (init (r := 22) input).mem a)) ∧
        (0 < minCut W →
          (evalRand w p T (init input)).toOuterMeasure
              {cfg | ∀ reg mem, cfg ≠ .halted (minCut W) reg mem} ≤
            (1 : ENNReal) / ((2 * n : ℕ) : ENNReal)) :=
  KargerMinCutBridge.kargerHighProb
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

/-- **Single-tree Karger–Stein `FastCut` (`O(n ^ 2 log n)` time, `[KargerStein1996]`, Section 4,
Figure 6 and Lemmas 4.1–4.3).** One fixed 24-register program recursively contracts
`n :: flattenMatrix W` (`n ≥ 2`) at word size `w ≥ 4 * (Nat.log 2 n + 1)` with
`totalDoubledWeight W < 2 ^ w` within `2500 * n ^ 2 * (Nat.log 2 n + 2)` steps and
`6 * (n * n)` `rand` calls, preserving the input matrix and all memory outside
`[2 + n * n, 2 + 27 * (n * n))`. Internal nodes (`k >= 7`) contract to the least `t >= 2` with
`k * (k - 1) <= 2 * t * (t - 1)` (an integer variant of Figure 6's `ceil(1 + k / sqrt 2)`), and
leaves (`k <= 6`) run one randomized contraction down to `2` vertices, as in Figure 6 (equation
(2)'s base-case probability `1 / 15` gives the `+ 15` term).
Every branch outputs a genuine non-trivial cut weight `≥ minCut W`, and when `0 < minCut W`
(excluded only for proof convenience) it outputs `minCut W` with probability at least
`1 / (Nat.log 2 n + 15)`. -/
theorem kargerSteinFastCut :
    ∃ p : Program 24,
      ∀ (n w : ℕ) (W : Fin n → Fin n → ℕ),
        2 ≤ n →
        IsMultigraph W →
        4 * (Nat.log 2 n + 1) ≤ w →
        totalDoubledWeight W < 2 ^ w →
        let input := n :: flattenMatrix W
        let T := 2500 * n ^ 2 * (Nat.log 2 n + 2)
        HaltsWithin w p (init input) T ∧
        RandCallsBounded w p (init input) T (6 * (n * n)) ∧
        (∀ cfg ∈ (evalRand w p T (init input)).support,
          ∃ (reg : Fin 24 → ℕ) (mem : ℕ → ℕ) (C : Finset (Fin n)),
            cfg = .halted (cutWeight W C) reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            IsNonTrivialCut C ∧
            minCut W ≤ cutWeight W C ∧
            (∀ a, a < 2 + n * n ∨ 2 + 27 * (n * n) ≤ a →
              mem a = (init (r := 24) input).mem a)) ∧
        (0 < minCut W →
          (1 : ENNReal) / ((Nat.log 2 n + 15 : ℕ) : ENNReal) ≤
            (evalRand w p T (init input)).toOuterMeasure
              {cfg | ∃ reg mem, cfg = .halted (minCut W) reg mem}) :=
  KargerMinCutBridge.kargerSteinFastCut
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

/-- **High-probability Karger–Stein global minimum cut (`O(n ^ 2 log ^ 3 n)` time, the
minimum-cut-value part of `[KargerStein1996]`, Section 4, Theorem 4.4).** One fixed 24-register
program runs our concrete
parameter choice `R = (Nat.log 2 n + 15) * (Nat.log 2 n + 2)` independent `FastCut` trees on
`n :: flattenMatrix W` (`n ≥ 2`) at word size `w ≥ 4 * (Nat.log 2 n + 1)` with
`totalDoubledWeight W < 2 ^ w` within `2600 * n ^ 2 * (Nat.log 2 n + 15) * (Nat.log 2 n + 2) ^ 2`
steps and `R * (6 * (n * n))` `rand` calls, preserving the input matrix and all memory outside
`[2 + n * n, 2 + 27 * (n * n))`. Every branch outputs a genuine non-trivial cut weight
`≥ minCut W`, and when `0 < minCut W` (excluded only for proof convenience) the probability of
missing `minCut W` is at most `1 / (2 * n)`. -/
theorem kargerSteinHighProb :
    ∃ p : Program 24,
      ∀ (n w : ℕ) (W : Fin n → Fin n → ℕ),
        2 ≤ n →
        IsMultigraph W →
        4 * (Nat.log 2 n + 1) ≤ w →
        totalDoubledWeight W < 2 ^ w →
        let input := n :: flattenMatrix W
        let T := 2600 * n ^ 2 * (Nat.log 2 n + 15) * (Nat.log 2 n + 2) ^ 2
        let R := (Nat.log 2 n + 15) * (Nat.log 2 n + 2)
        HaltsWithin w p (init input) T ∧
        RandCallsBounded w p (init input) T (R * (6 * (n * n))) ∧
        (∀ cfg ∈ (evalRand w p T (init input)).support,
          ∃ (reg : Fin 24 → ℕ) (mem : ℕ → ℕ) (C : Finset (Fin n)),
            cfg = .halted (cutWeight W C) reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            IsNonTrivialCut C ∧
            minCut W ≤ cutWeight W C ∧
            (∀ a, a < 2 + n * n ∨ 2 + 27 * (n * n) ≤ a →
              mem a = (init (r := 24) input).mem a)) ∧
        (0 < minCut W →
          (evalRand w p T (init input)).toOuterMeasure
              {cfg | ∀ reg mem, cfg ≠ .halted (minCut W) reg mem} ≤
            (1 : ENNReal) / ((2 * n : ℕ) : ENNReal)) :=
  KargerMinCutBridge.kargerSteinHighProb
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

/-- info:
abstract audit passed for `ComplexityAbstracts.KargerMinCutAbstract`: 288 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.KargerMinCutAbstract

end ComplexityAbstracts.KargerMinCutAbstract
