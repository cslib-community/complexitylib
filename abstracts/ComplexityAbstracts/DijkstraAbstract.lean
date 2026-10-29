/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.DijkstraBridge

/-! # Dijkstra's algorithm: shortest paths in `O((m + 1) log n)` and `O(m + n log n)` time

Given a directed graph with `n` vertices, `m` edges and natural-number edge weights, and a source
vertex `s`, the single-source shortest-path problem asks for the distance from `s` to every
vertex. On the word RAM, with the graph given by adjacency lists, Dijkstra's algorithm solves it in
`O((m + 1) log n)` time with a binary heap (`dijkstra_logLinear`) and in `O(m + n log n)` time with
Fredman and Tarjan's Fibonacci heap (`dijkstra_fibonacci`). The theorems below state both bounds.

The graph, its distances, the input and output layouts, the word-size condition and the machine are
all defined here from scratch. The machine, defined in the appendix, is the word RAM over the exact
basis of operations: each operation computes its exact value, and an instruction faults instead of
producing `x - y` for `y > x`, `x / 0`, `x % 0`, or a value that is not a word. Apart from `Runs`,
its definitions are those of `WordRAMAbstract`. To check that the theorems say what is claimed, a
reader only needs to inspect the definitions and theorem statements in this file. Lean checks the
proofs through `DijkstraBridge`, which proves that the distance here is the library's and that the
machine here runs as the library's word RAM `Cslib.WordRAM` over its exact basis, and applies the
library theorems `Cslib.Algorithms.WordRAM.Dijkstra.logLinearStatement` and
`Cslib.Algorithms.WordRAM.Dijkstra.fibonacciStatement`. `#check_abstract` checks mechanically that
every definition and theorem statement here depends only on this file, Lean, Mathlib and upstream
CSLib.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [M. L. Fredman and R. E. Tarjan, *Fibonacci heaps and their uses in improved network optimization
  algorithms*][FredmanTarjan1987], Section 2, Theorem 1 (p. 604) and Section 4 (pp. 609–610).
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Chapter 19 and Section 24.3 (p. 662).
-/

namespace ComplexityAbstracts.DijkstraAbstract

variable {n : ℕ}

/-! ## Graphs and distances

The vertices are `0, …, n - 1` (the type `Fin n`). A walk is a sequence of edges, each leaving
the vertex the previous one enters; vertices and edges may repeat. Its weight is the sum of the
weights of its edges. The distance from `u` to `v` is the least weight of a walk from `u` to `v`,
in `ℕ∞ = ℕ ∪ {⊤}`, and `⊤` when there is no such walk. Weights are natural numbers, so a least
weight exists whenever a walk does.
-/

/-- A directed graph on the vertices `Fin n` with natural-number edge weights, given by adjacency
lists: `G u` holds a pair `(v, c)` for each edge from `u` to `v` of weight `c`. The same pair of
endpoints may appear more than once (parallel edges), and `v` may be `u` (self-loops). -/
abbrev Graph (n : ℕ) := Fin n → List (Fin n × ℕ)

/-- `IsWalk G u l v`: the list `l` of edges `(target, weight)` is a walk from `u` to `v`. Its
first edge is in the list `G u` of edges out of `u`, each later edge is in the list of edges out
of the target of the edge before it, and the target of its last edge is `v`. The empty walk goes
from `u` to `u`. -/
def IsWalk (G : Graph n) : Fin n → List (Fin n × ℕ) → Fin n → Prop
  | u, [], v => u = v
  | u, e :: l, v => e ∈ G u ∧ IsWalk G e.1 l v

/-- The **distance** from `u` to `v`: the least weight of a walk from `u` to `v`, the weight of
a walk being the sum of the weights of its edges, and `⊤` when there is no walk. -/
noncomputable def dist (G : Graph n) (u v : Fin n) : ℕ∞ :=
  ⨅ (l : List (Fin n × ℕ)) (_ : IsWalk G u l v), ((l.map Prod.snd).sum : ℕ∞)

/-- The number `m` of edges. -/
def numEdges (G : Graph n) : ℕ := ∑ u, (G u).length

/-- The largest edge weight, and `0` when there is no edge. -/
def maxWeight (G : Graph n) : ℕ :=
  Finset.univ.sup fun u => ((G u).map Prod.snd).foldr max 0

/-! ## Input, output and cost

The program reads the graph as a list of natural numbers: `n`, the source `s`, the `n + 1` offsets
of the adjacency lists in an array of edges, and then the `m` edges, each as two numbers, its target
and its weight. The input and its length header are placed in memory before the run at no cost;
memory beyond them and all registers start at `0`. When it halts, the memory cell `outAddr G v` of
each vertex `v` holds `0` when `v` is unreachable from `s` and `d + 1` when the distance from `s` to
`v` is `d`. The machine is a word RAM with `w`-bit words, and the theorem
asks `8 (n + m + 2) (W + 2) < 2 ^ w`, where `W` is the largest weight, so a word size
`w = O(log (n + m + W + 2))` suffices. Each instruction costs one unit of time, whatever its
operands. The operations are `+`, `-`, `*`, `/`, `%`, bitwise operations and shifts, each with its
exact value; an instruction faults on `x - y` with `y > x`, on `x / 0` and `x % 0`, and on a
constant or operation value of `2 ^ w` or more. The bound counts the instructions executed, the
final `halt` included. The appendix gives the exact layout (`offset`, `encode`, `outAddr`,
`encodeDist`) and the machine (`Program`, `init`, `step`, `Runs`).
-/

/-! ## Representation details

The input is a list of natural numbers: `n`, the source, the `n + 1` offsets of the adjacency
lists in the edge array, and the edges, in the order of the lists `G 0, …, G (n - 1)`, each as
two numbers, its target and its weight. This is the usual "compressed" layout: the edges out of
`u` are the edges `j` with `offset G u ≤ j < offset G (u + 1)`.

The machine stores the input of length `k = n + 2 m + 3` at addresses `1, …, k` (see `init`
below). The output is the `n` memory cells just past it: the cell of vertex `v` holds `0` when `v`
is unreachable from the source and `d + 1` when its distance is `d`.
-/

/-- The offset of the adjacency list of vertex `u` in the edge array: the number of edges out of
the vertices below `u`. The offset of `n` is the number of edges. -/
def offset (G : Graph n) (u : ℕ) : ℕ :=
  (((List.finRange n).take u).map fun x => (G x).length).sum

/-- The input: `n`, the source `s`, the offsets of the vertices `0, …, n`, and then the edges of
`G 0, …, G (n - 1)` in order, each as its target and its weight. -/
def encode (G : Graph n) (s : Fin n) : List ℕ :=
  n :: (s : ℕ) ::
    ((List.range (n + 1)).map (offset G) ++
      (List.finRange n).flatMap fun u => (G u).flatMap fun e => [(e.1 : ℕ), e.2])

/-- The output address of vertex `v`: the input occupies addresses `0, …, n + 2 m + 3` (its length
at `0`), and the outputs follow it. -/
def outAddr (G : Graph n) (v : Fin n) : ℕ := n + 2 * numEdges G + 4 + v

/-- A distance as an output word: `0` for `⊤` (unreachable) and `d + 1` for distance `d`. -/
def encodeDist (d : ℕ∞) : ℕ := if d = ⊤ then 0 else d.toNat + 1

/-! **The machine.** The word RAM over the exact basis, as in `WordRAMAbstract`. At word size
`w`, a *word* is a number below `2 ^ w`. A machine has `r` registers `R[0]`, …, `R[r - 1]` and a
memory cell `M[a]` at every address `a : ℕ`; all hold natural numbers. The machine stores arbitrary
natural numbers, but an instruction faults when it would create a value that is undefined or not a
word. There are ten binary operations, and each computes its exact value. Subtraction `x - y` is
undefined for `y > x`, and division `x / y` and remainder `x % y` are undefined for `y = 0`;
otherwise division rounds down. The operations `and`, `or` and `xor` act bitwise, and `shl` and
`shr` shift `x` left and right by `y` bits, that is, give `x * 2 ^ y` and `x / 2 ^ y` rounded
down. In `AluOp.eval`, a case value `n` stands for `some n`.
-/

variable {r : ℕ}

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

/-! The number `r` of registers is a parameter of the types below (the implicit variable `r`).
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

/-! The memory is a function on all of `ℕ`: there is no allocation and no bound on addresses. One
step executes instruction number `pc`. `const` and `alu` write their value to `R[d]` if it is a
word, and fault otherwise; there is no wrap-around modulo `2 ^ w`, and an `alu` whose value is
undefined (`none`) also faults. `width` writes `w`, which is always a word, since `w < 2 ^ w`.
`copy`, `load` and `store` move a value without a check. `jump` and the two branches set `pc`;
every other instruction except `halt` moves on to instruction `pc + 1`. `halt i` stops with
output `R[i]`. If `pc` is not the number of an instruction, that is, `pc` is at least the length
of the program, the step faults.

Copies, loads and stores need no check: when the input and its length are words, an induction
along the run shows that every register and memory cell always holds a word, and so every address
used is below `2 ^ w`. This induction is not stated here; it only explains why the check is not
needed. Under the word-size condition of the theorem, the input and its length are words.
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
of the program. Copies, loads and stores are not checked. -/
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

/-! A program reads the length `k` of its input `x₁, …, xₖ` at `M[0]` and the input at
`M[1], …, M[k]`. A run of `k` steps follows `step` one instruction at a time; each of its steps
continues to a next state. The theorem asks for a run to a state whose next step is a `halt`, so
the run executes one more instruction, the `halt`, and then stops. Every instruction takes one
unit of time, whatever its operands and the word size.
-/

/-- The start state on input `x₁, …, xₖ`: instruction `0`, registers `0`, and memory
`k, x₁, …, xₖ` at addresses `0, 1, …, k`, then `0` everywhere. -/
def init (input : List ℕ) : State r :=
  ⟨0, fun _ => 0, fun a => (input.length :: input).getD a 0⟩

/-- `Runs w p s t k`: from state `s`, `k` steps of program `p` at word size `w` lead to state
`t`, each continuing to a next state, none halting or faulting. (`Relation.RelatesInSteps R s t k`
holds when `k` steps of the relation `R` lead from `s` to `t`: `s = t` for `k = 0`, and for
`k + 1`, `k` steps to some `u` and then `R u t`.) -/
def Runs (w : ℕ) (p : Program r) : State r → State r → ℕ → Prop :=
  Relation.RelatesInSteps fun s t => step w p s = .next t

/-! ## Main theorems -/

/-- **Dijkstra's algorithm (binary heap).** Some program `p` of the word RAM defined in the
representation details (over the exact basis), with some number `r` of registers, and some constant
`K` satisfy the following.
For every graph `G` with `n` vertices and `m` edges and largest weight `W`, every source `s`, and
every word size `w` with `8 (n + m + 2) (W + 2) < 2 ^ w`: started on the input `encode G s`, the
program runs for `steps` steps to a state `t` whose next instruction is `halt`, executes
`steps + 1 ≤ K (m + 1) (Nat.log 2 n + 1)` instructions in all, and then holds at `outAddr G v`
the encoded distance from `s` to `v`, for every vertex `v`. Here `Nat.log 2 n` is the integer part
of `log₂ n` (and `0` for `n = 0`). The output of `halt` is not part of the result. -/
theorem dijkstra_logLinear :
    ∃ r, ∃ p : Program r, ∃ K, ∀ (n : ℕ) (G : Graph n) (s : Fin n) (w : ℕ),
      8 * (n + numEdges G + 2) * (maxWeight G + 2) < 2 ^ w →
      ∃ t steps, Runs w p (init (encode G s)) t steps ∧
        (∃ v, step w p t = .halt v) ∧
        steps + 1 ≤ K * (numEdges G + 1) * (Nat.log 2 n + 1) ∧
        ∀ v : Fin n, t.mem (outAddr G v) = encodeDist (dist G s v) :=
  -- the bridge's halting runs and agreeing outcomes are unused here: `OutcomeAgrees` is `True`
  DijkstraBridge.logLinear
    ⟨AluOp, .add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr, @AluOp.rec, AluOp.eval,
      Instr, .const, .copy, .alu, .width, .load, .store, .jump, .branchEq, .branchLt, .halt,
      @Instr.rec, State, .mk, Outcome, .next, .halt, .fault, step,
      ComplexityTests.Abstracts.WordRAMBridge.haltsVia Instr State Outcome step
        fun f g a o => o.rec f g a, fun _ _ => True⟩
    (by constructor <;>
      simp_all [step, ComplexityTests.Abstracts.WordRAMBridge.haltsVia, AluOp.eval])
    State.mem (fun _ _ _ => rfl) (W := @IsWalk) ⟨fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl⟩

/-- **Dijkstra's algorithm (Fibonacci heap).** Some program `p` of the word RAM defined in the
representation details (over the exact basis), with some number `r` of registers, and some constant
`K` satisfy the following.
For every graph `G` with `n` vertices and `m` edges and largest weight `W`, every source `s`, and
every word size `w` with `8 (n + m + 2) (W + 2) < 2 ^ w`: started on the input `encode G s`, the
program runs for `steps` steps to a state `t` whose next instruction is `halt`, executes
`steps + 1 ≤ K (m + n (Nat.log 2 n + 1))` instructions in all, and then holds at `outAddr G v`
the encoded distance from `s` to `v`, for every vertex `v`. -/
theorem dijkstra_fibonacci :
    ∃ r, ∃ p : Program r, ∃ K, ∀ (n : ℕ) (G : Graph n) (s : Fin n) (w : ℕ),
      8 * (n + numEdges G + 2) * (maxWeight G + 2) < 2 ^ w →
      ∃ t steps, Runs w p (init (encode G s)) t steps ∧
        (∃ v, step w p t = .halt v) ∧
        steps + 1 ≤ K * (numEdges G + n * (Nat.log 2 n + 1)) ∧
        ∀ v : Fin n, t.mem (outAddr G v) = encodeDist (dist G s v) :=
  DijkstraBridge.fibonacci
    ⟨AluOp, .add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr, @AluOp.rec, AluOp.eval,
      Instr, .const, .copy, .alu, .width, .load, .store, .jump, .branchEq, .branchLt, .halt,
      @Instr.rec, State, .mk, Outcome, .next, .halt, .fault, step,
      ComplexityTests.Abstracts.WordRAMBridge.haltsVia Instr State Outcome step
        fun f g a o => o.rec f g a, fun _ _ => True⟩
    (by constructor <;>
      simp_all [step, ComplexityTests.Abstracts.WordRAMBridge.haltsVia, AluOp.eval])
    State.mem (fun _ _ _ => rfl) (W := @IsWalk) ⟨fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl⟩

/--
info: abstract audit passed for `ComplexityAbstracts.DijkstraAbstract`: 219 root
declarations, 229 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.DijkstraAbstract

end ComplexityAbstracts.DijkstraAbstract
