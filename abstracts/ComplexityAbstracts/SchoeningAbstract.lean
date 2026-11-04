/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.SchoeningBridge
import Cslib.Probability.PMF
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Schöning's algorithm for 3-SAT on the randomized word RAM: a formal abstract

This file states the randomized word RAM, CNF formulas with their word encoding, one trial of
Schöning's algorithm, and the guarantees of one fixed program that runs Schöning's algorithm for
3-SAT with confidence `c` [Schöning][Schoening1999].

On a formula `φ` on the variables `0, …, n - 1`, given as the input `3 :: c :: encode φ` of length
`L`, the program of `schoening3SAT`

* halts on every random path within `⌊900 (n + L + 4) ^ 3 (4 / 3) ^ n (c + 1)⌋` steps, so in time
  `O((n + L) ^ 3 (4 / 3) ^ n (c + 1))`, and makes at most `4 n R` random draws, where
  `R = ⌈(3 n + 1) (4 / 3) ^ n⌉ c` is the number of trials;
* halts with output `0` or `1`, and with output `1` only when it leaves a satisfying assignment of
  `φ` in memory, so it never errs on an unsatisfiable formula;
* fails to output `1` with probability exactly `(1 - p) ^ R`, where `p` is the probability that one
  trial of Schöning's algorithm (`trial`) returns a satisfying assignment: the program runs up to
  `R` independent trials and stops at the first success;
* fails to output `1` with probability at most `e ^ (-c)` when `φ` is satisfiable and its clauses
  have at most three literals.

**Time model.** Time is the number of executed instructions. Every instruction costs one step,
including jumps, branches, and `rand`, which draws a uniform integer in `{0, …, R[i]}` in one step.
The program and its time bound are uniform in `n`, `c`, the formula, and the word size `w`. The
word size must satisfy `L + 8 (n + 3) ^ 2 + 3 c < 2 ^ w`, so `O(log (n + L + c))`-bit words suffice:
the trial count `R`, of `O(n + log (c + 1))` bits (the factor `(4 / 3) ^ n` contributes about
`0.415 n`), is kept in memory one binary digit per word. Both `n` and `L` appear because neither
bounds the other: the clauses may mention few variables, and they may repeat literals.

**Source.** Schöning's paper (Abstract and Section 2, pp. 410–411) describes this algorithm and
shows that its complexity on k-CNF formulas is within a polynomial factor of `(2 (1 - 1 / k)) ^ n`,
which is `(4 / 3) ^ n` for 3-SAT. Its local search flips a random literal of *some* falsified
clause; this formalization takes the first one. Its analysis of one trial, which this formalization
proves with the explicit success probability `(3 / 4) ^ n / (3 n + 1)`, is not needed to read the
statements below: the exact failure probability is stated for the restated `trial`, and the
`e ^ (-c)` bound follows from it. The polynomial factor, the trial count and the constant `900` are
those of this formalization. The model definitions below are restated from Renfei Zhou's
`RandomizedWordRAMAbstract`.

At word size `w`, a *word* is a natural number below `2 ^ w`. A machine has `r` registers
`R[0], …, R[r - 1]` and memory `M[a]` for `a : ℕ`. Its instructions, sampling trees, clocked runs
and input convention match `RandomizedWordRAMAbstract` (restated because an abstract cannot import
another abstract), except for the arithmetic: here `AluOp` follows the standard basis
`Cslib.WordRAM.Basis.standard`, in which subtraction is truncated at zero, `x / 0 = 0` and
`x % 0 = x`, so that no arithmetic operation faults; a result that is not a word still faults.
`RandomizedWordRAMAbstract` uses `Cslib.WordRAM.Basis.exact`, in which those three cases fault.

Simplifications relative to `Cslib.WordRAM` and `Cslib.Algorithms.WordRAM.Schoening`:

* `Instr` lists the eleven flat instructions directly instead of `Op`, `Cond`, and `Code`, and
  `Comp` specializes `ProbComp` to finite-depth uniform trees over `Fin (n + 1)`.
* The trial count `schoeningTrials 3 n c`, the word-size condition, and the clock `ampTime` are
  replaced by the explicit expressions above; the bridge proves that they bound or equal the
  library's.
* A flip in `flipStep` is written with `Function.update` instead of `Cslib.BitString.flipOn`, and
  the local search `walk` iterates one step with `Nat.iterate` instead of recursing on the number
  of steps.

A reader only needs to inspect the definitions and theorem statements in this file to verify that
the formalization proves the intended claim. Lean checks the proof via `SchoeningBridge`, which
identifies the program as `Cslib.Algorithms.WordRAM.Schoening.ampProgram`, under `propext`,
`Classical.choice` and `Quot.sound`; `#check_abstract` verifies that no project module is
allowlisted.

## References

* [U. Schöning, *A probabilistic algorithm for k-SAT and constraint satisfaction
  problems*][Schoening1999]
-/

namespace ComplexityAbstracts.SchoeningAbstract

/-! ## Words, operations, and instructions

Each arithmetic, bitwise, or shift operation in `AluOp` computes its value on natural numbers:
subtraction is truncated at zero (`x - y = 0` when `y > x`), and division and remainder by zero give
`x / 0 = 0` and `x % 0 = x`. The instruction `rand d i` draws a uniform integer in `{0, …, R[i]}`.
-/

/-- The ten binary operations on natural numbers. -/
inductive AluOp
  | add | sub | mul | div | mod | and | or | xor | shl | shr

/-- Value of a binary operation before word-range checking: truncated subtraction, and Lean's
`x / 0 = 0` and `x % 0 = x`. -/
def AluOp.eval : AluOp → ℕ → ℕ → ℕ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .mod, x, y => x % y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .shl, x, y => x * 2 ^ y
  | .shr, x, y => x / 2 ^ y

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
(`PMF α`), and `Comp.CallsAtMost m R` states that every branch makes at most `R` draws.
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

/-! ## Configurations and clocked runs

A configuration is `running` at a `State`, `halted` with scalar output `v` alongside final registers
`reg` and memory `mem`, or `faulted`. Both `halted` and `faulted` are absorbing: further clock ticks
leave them unchanged and make zero `rand` calls. At an active state `s`, `rand d i` faults when
`s.reg i ≥ 2 ^ w`, and otherwise draws `k` uniformly from `{0, …, s.reg i}`, writes it to `R[d]`
and advances `pc` in one step and one `sample` node.
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
    | some (.alu f d i j) => nextWord d (f.eval (s.reg i) (s.reg j))
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

/-- The probability that `p`, run for `T` steps from `s`, has not halted with output `1`. -/
noncomputable def failure {r : ℕ} (w : ℕ) (p : Program r) (T : ℕ) (s : State r) : ℝ :=
  ((evalRand w p T s).toOuterMeasure {cfg | ¬∃ reg mem, cfg = .halted 1 reg mem}).toReal

/-- Start state on `input = [x₁, …, xₖ]`: `pc = 0`, registers `0`, `M[0] = k`, `M[1..k] = input`. -/
def init {r : ℕ} (input : List ℕ) : State r :=
  ⟨0, fun _ => 0, fun a => (input.length :: input).getD a 0⟩

/-! ## CNF formulas

A formula on the variables `0, …, n - 1` is a list of clauses; a clause is a list of literals, and
the literal `(v, b)` is the variable `v` when `b = true` and its negation when `b = false`. An
assignment `σ : Fin n → Bool` satisfies a clause if it makes one of its literals true, and a formula
if it satisfies every clause. A formula is a *3-CNF* if every clause has at most three literals.
-/

variable {n : ℕ}

/-- A clause on the variables `0, …, n - 1`: the disjunction of its literals. -/
abbrev Clause (n : ℕ) := List (Fin n × Bool)

/-- A CNF formula on the variables `0, …, n - 1`: the conjunction of its clauses. -/
abbrev Formula (n : ℕ) := List (Clause n)

/-- Whether `σ` makes some literal of the clause true. -/
def Clause.eval (c : Clause n) (σ : Fin n → Bool) : Bool :=
  c.any fun l => σ l.1 == l.2

/-- Whether `σ` satisfies every clause of `φ`. -/
def Formula.eval (φ : Formula n) (σ : Fin n → Bool) : Bool :=
  φ.all fun c => c.eval σ

/-- `φ` has a satisfying assignment. -/
def Satisfiable (φ : Formula n) : Prop :=
  ∃ σ : Fin n → Bool, φ.eval σ = true

/-! ## Schöning's algorithm

One trial draws a uniformly random assignment and then performs `3 n` steps of local search. A
step finds the first clause that the current assignment falsifies; if there is none, the assignment
stays, and otherwise the step chooses one of the clause's literal occurrences uniformly and flips
its variable. The algorithm repeats independent trials until one returns a satisfying assignment.
-/

/-- The first clause of `φ` that `σ` falsifies, if any. -/
def firstUnsat (φ : Formula n) (σ : Fin n → Bool) : Option (Clause n) :=
  φ.find? fun c => !c.eval σ

/-- Flip the variable of a uniformly chosen literal occurrence of `c`. The empty clause, which no
assignment satisfies, leaves the assignment unchanged. -/
noncomputable def flipStep (c : Clause n) (σ : Fin n → Bool) : PMF (Fin n → Bool) :=
  if h : c.length = 0 then PMF.pure σ else
    haveI : NeZero c.length := ⟨h⟩
    (Cslib.Probability.PMF.uniformOfFintype (Fin c.length)).map fun i =>
      Function.update σ (c.get i).1 (!σ (c.get i).1)

/-- One step of local search: stay at a satisfying assignment, and otherwise flip a uniformly
chosen variable occurrence of the first falsified clause. -/
noncomputable def walkStep (φ : Formula n) (σ : Fin n → Bool) : PMF (Fin n → Bool) :=
  (firstUnsat φ σ).elim (PMF.pure σ) fun c => flipStep c σ

/-- `t` steps of local search from `σ`: the `t`-fold iterate of `walkStep`, a step of a Markov chain
on assignments. -/
noncomputable def walk (φ : Formula n) (t : ℕ) (σ : Fin n → Bool) : PMF (Fin n → Bool) :=
  (fun μ : PMF (Fin n → Bool) => μ.bind (walkStep φ))^[t] (PMF.pure σ)

/-- **One trial of Schöning's algorithm**: a uniformly random assignment followed by `3 n` steps of
local search. -/
noncomputable def trial (φ : Formula n) : PMF (Fin n → Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin n → Bool)).bind (walk φ (3 * n))

/-- The probability that one trial returns a satisfying assignment of `φ`. -/
noncomputable def trialSuccess (φ : Formula n) : ℝ :=
  ((trial φ).toOuterMeasure {σ | φ.eval σ = true}).toReal

/-! ## Representation details

The input is a list of words. The formula `φ` is the number `n` of variables followed by its clauses
in order; a clause is its number of literals followed by the codes `2 v + b` of its literals
`(v, b)`, where `b` counts as `1` when true. The program reads `3 :: c :: encode φ`, so it is told
the clause width `3` and the confidence `c`, and it leaves its final assignment, one word `0` or `1`
per variable, at addresses `L + 1, …, L + n`, where `L` is the input length.
-/

/-- The code `2 v + b` of the literal `(v, b)`. -/
def literalCode (l : Fin n × Bool) : ℕ := 2 * l.1.val + l.2.toNat

/-- A clause as its length followed by the codes of its literals. -/
def encodeClause (c : Clause n) : List ℕ := c.length :: c.map literalCode

/-- A formula as its number of variables followed by its encoded clauses. -/
def encode (φ : Formula n) : List ℕ := n :: φ.flatMap encodeClause

/-! ## The theorem -/

/-- **Schöning's algorithm for 3-SAT on the randomized word RAM.** One fixed 24-register program,
on the input `3 :: c :: encode φ` of length `L` and at every word size `w` with
`L + 8 (n + 3) ^ 2 + 3 c < 2 ^ w`, with `R = ⌈(3 n + 1) (4 / 3) ^ n⌉ c` trials and the step bound
`T = ⌊900 (n + L + 4) ^ 3 (4 / 3) ^ n (c + 1)⌋`:
1. halts on every path within `T` steps and makes at most `4 n R` `rand` calls;
2. halts with output `0` or `1`, and with output `1` only when the words at `L + 1, …, L + n`
   form a satisfying assignment of `φ`;
3. fails to output `1` with probability exactly `(1 - p) ^ R`, where `p = trialSuccess φ` is the
   success probability of one trial of Schöning's algorithm;
4. fails to output `1` with probability at most `e ^ (-c)` when `φ` is a satisfiable 3-CNF. -/
theorem schoening3SAT :
    ∃ p : Program 24, ∀ (n c w : ℕ) (φ : Formula n),
      let input := 3 :: c :: encode φ
      let L := input.length
      let R := ⌈(3 * n + 1 : ℝ) * (4 / 3) ^ n⌉₊ * c
      let T := 900 * (n + L + 4) ^ 3 * 4 ^ n * (c + 1) / 3 ^ n
      L + 8 * (n + 3) ^ 2 + 3 * c < 2 ^ w →
      HaltsWithin w p (init input) T ∧
      RandCallsBounded w p (init input) T (R * (4 * n)) ∧
      (∀ cfg ∈ (evalRand w p T (init input)).support,
        ∃ v reg mem, cfg = .halted v reg mem ∧
          (v = 0 ∨ (v = 1 ∧ φ.eval (fun i : Fin n => decide (mem (L + 1 + i) = 1)) = true))) ∧
      failure w p T (init input) = (1 - trialSuccess φ) ^ R ∧
      (Satisfiable φ → (∀ clause ∈ φ, clause.length ≤ 3) →
        failure w p T (init input) ≤ Real.exp (-c)) :=
  SchoeningBridge.schoening
    ⟨AluOp, .add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr,
      @AluOp.rec, fun f x y => some (AluOp.eval f x y),
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
info: abstract audit passed for `ComplexityAbstracts.SchoeningAbstract`: 291 root
declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.SchoeningAbstract

end ComplexityAbstracts.SchoeningAbstract
