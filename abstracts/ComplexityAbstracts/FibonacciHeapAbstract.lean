/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.FibonacciHeapBridge

/-! # Fibonacci heaps: amortized priority queues on the word RAM

An indexed min-priority queue maintains a subset of the handles `0, …, n - 1` (the type `Fin n`),
each associated with a natural-number key at most `K_max`. It supports membership/key queries
(`isEmpty`, `getKey`), inserting an absent handle (`insert`), lowering the key of a present handle
(`decreaseKey`), and removing the present `(handle, key)` pair of minimum key (`extractMin`),
breaking equal-key ties by smallest handle index. Fredman and Tarjan's Fibonacci heap supports
queries in `O(1)` time, `insert` and `decreaseKey` in `O(1)` amortized time, and `extractMin` in
`O(log n)` amortized time.

The theorems below state this guarantee on the word RAM over the exact basis of operations, inside a
caller-chosen contiguous block `[base, base + 9 n + 1)` of `9 n + 1` words:

* `fibonacciHeap_amortized` initializes an empty heap on zeroed `[base, base + 9 n + 1)` in `O(1)`
  instructions and executes any valid sequence of `m_q` queries, `m_ins` insertions, `m_dec` key
  decreases, and `m_ext` minimum extractions in
  `O(m_q + m_ins + m_dec + m_ext (log n + 1))` total instructions;
* `fibonacciHeap_amortized_reusable` initializes an empty heap on arbitrary `w`-bit memory in
  `O(n + 1)` instructions and achieves the same amortized operation bound.

In both theorems, neither initialization nor any operation modifies memory outside
`[base, base + 9 n + 1)`. Every concept in the statements—the priority queue, its tie-breaking
minimum, admissible operation sequences, the exact word RAM, the register calling convention and
memory confinement—is defined from scratch in this file. Lean checks the proofs through
`FibonacciHeapBridge`, and `#check_abstract` verifies mechanically that no definition or theorem
statement here depends on implementation modules.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci heaps and their uses in improved network optimization
  algorithms*][FredmanTarjan1987], Section 2, p. 604 (the potential defined before Theorem 1) and
  Theorem 1.
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 19.1, eq. (19.1), and Sections 19.2–19.4.
-/

namespace ComplexityAbstracts.FibonacciHeapAbstract

/-! ## Indexed priority queues

A priority-queue state `q : Queue n` maps each handle `v : Fin n` to `none` when `v` is absent and
to `some k` when `v` is present with key `k`. To make `extractMin` a deterministic function of `q`
alone (independent of insertion history), `PrioLE` orders `(handle, key)` pairs lexicographically by
`(key, handle)`. An operation sequence is admissible (`ValidSeq K_max`) when every `insert v k` acts
on an absent handle with `k ≤ K_max` and every `decreaseKey v k` lowers the current key of a present
handle with `k ≤ K_max`.
-/

/-- Operations on an indexed min-priority queue over handles `Fin n` and natural-number keys. -/
inductive Op (n : ℕ)
  | isEmpty
  | getKey (v : Fin n)
  | insert (v : Fin n) (k : ℕ)
  | decreaseKey (v : Fin n) (k : ℕ)
  | extractMin

/-- Abstract state of an indexed min-priority queue on `Fin n`: `none` when absent, `some k` when
present with key `k`. -/
abbrev Queue (n : ℕ) := Fin n → Option ℕ

/-- The empty priority queue on `Fin n`. -/
def emptyQueue (n : ℕ) : Queue n := fun _ => none

/-- Lexicographic priority order on `(handle, key)` pairs: smaller key first, breaking equal-key
ties by smaller handle index. -/
abbrev PrioLE {n : ℕ} (a b : Fin n × ℕ) : Prop :=
  a.2 < b.2 ∨ (a.2 = b.2 ∧ (a.1 : ℕ) ≤ (b.1 : ℕ))

/-- Smaller of two `(handle, key)` pairs under `PrioLE`. -/
def chooseMin {n : ℕ} (a b : Fin n × ℕ) : Fin n × ℕ :=
  if PrioLE a b then a else b

/-- Minimum `(handle, key)` pair in a list under `PrioLE`, or `none` on the empty list. -/
def foldMin {n : ℕ} : List (Fin n × ℕ) → Option (Fin n × ℕ)
  | [] => none
  | a :: l =>
    match foldMin l with
    | none => some a
    | some b => some (chooseMin a b)

/-- Present `(handle, key)` pair minimizing `(key, handle)` in `q`, or `none` when `q` is empty. -/
def findMin {n : ℕ} (q : Queue n) : Option (Fin n × ℕ) :=
  foldMin ((List.finRange n).filterMap fun v => (q v).map (v, ·))

/-- Return type of each priority-queue operation. -/
def OpResult {n : ℕ} : Op n → Type
  | .isEmpty => Bool
  | .getKey _ => Option ℕ
  | .insert _ _ => Unit
  | .decreaseKey _ _ => Unit
  | .extractMin => Option (Fin n × ℕ)

/-- Abstract state transition and return value of operation `o` on queue `q`. -/
def stepOp {n : ℕ} (q : Queue n) : (o : Op n) → Queue n × OpResult o
  | .isEmpty => (q, decide (∀ v, q v = none))
  | .getKey v => (q, q v)
  | .insert v k => (Function.update q v (some k), ())
  | .decreaseKey v k => (Function.update q v (some k), ())
  | .extractMin =>
    match findMin q with
    | none => (q, none)
    | some (u, k) => (Function.update q u none, some (u, k))

/-- Precondition for a single operation under key bound `K_max`: `insert` requires an absent handle
and `k ≤ K_max`; `decreaseKey` requires a present handle whose key does not increase and
`k ≤ K_max`. -/
def ValidOp {n : ℕ} (K_max : ℕ) (q : Queue n) : Op n → Prop
  | .isEmpty | .getKey _ | .extractMin => True
  | .insert v k => q v = none ∧ k ≤ K_max
  | .decreaseKey v k => (∃ k₀, q v = some k₀ ∧ k ≤ k₀) ∧ k ≤ K_max

/-- Sequential admissibility of an operation list starting from queue `q`. -/
def ValidSeq {n : ℕ} (K_max : ℕ) : Queue n → List (Op n) → Prop
  | _, [] => True
  | q, o :: ops => ValidOp K_max q o ∧ ValidSeq K_max (stepOp q o).1 ops

/-- Number of `isEmpty` and `getKey` queries in `ops`. -/
def numQueries {n : ℕ} : List (Op n) → ℕ
  | [] => 0
  | .isEmpty :: ops => 1 + numQueries ops
  | .getKey _ :: ops => 1 + numQueries ops
  | .insert _ _ :: ops => numQueries ops
  | .decreaseKey _ _ :: ops => numQueries ops
  | .extractMin :: ops => numQueries ops

/-- Number of `insert` operations in `ops`. -/
def numInserts {n : ℕ} : List (Op n) → ℕ
  | [] => 0
  | .isEmpty :: ops => numInserts ops
  | .getKey _ :: ops => numInserts ops
  | .insert _ _ :: ops => 1 + numInserts ops
  | .decreaseKey _ _ :: ops => numInserts ops
  | .extractMin :: ops => numInserts ops

/-- Number of `decreaseKey` operations in `ops`. -/
def numDecreaseKeys {n : ℕ} : List (Op n) → ℕ
  | [] => 0
  | .isEmpty :: ops => numDecreaseKeys ops
  | .getKey _ :: ops => numDecreaseKeys ops
  | .insert _ _ :: ops => numDecreaseKeys ops
  | .decreaseKey _ _ :: ops => 1 + numDecreaseKeys ops
  | .extractMin :: ops => numDecreaseKeys ops

/-- Number of `extractMin` operations in `ops`. -/
def numExtractMins {n : ℕ} : List (Op n) → ℕ
  | [] => 0
  | .isEmpty :: ops => numExtractMins ops
  | .getKey _ :: ops => numExtractMins ops
  | .insert _ _ :: ops => numExtractMins ops
  | .decreaseKey _ _ :: ops => numExtractMins ops
  | .extractMin :: ops => 1 + numExtractMins ops

/-! ## Memory layout, calling convention and cost

The data structure occupies `9 n + 1` words at addresses `[base, base + 9 n + 1)`, assuming
`base + (9 n + 1) < 2 ^ w`, `K_max < 2 ^ w`, and every initial memory cell holds a `w`-bit word
(`< 2 ^ w`). Initialization (`p_init`) starts at `pc = 0` with `R[0] = n`, `R[1] = base`, and `0` in
all other registers (`initRegs`). Each subsequent operation call (`p_op`) starts at `pc = 0` after
writing the 3-bit operation tag and `(handle, key)` arguments into `R[17..21]` while leaving all
other registers unchanged (`prepareRegs`), runs to a `halt` instruction, and returns its observation
in `R[22..24]` (`decodeResult`), leaving every memory cell outside `[base, base + 9 n + 1)`
unchanged (`UnchangedOutside`). Every instruction costs one unit of time, each `halt` included. The
appendix defines the exact word RAM (`Program`, `State`, `step`, `Runs`) and the register and memory
conventions.
-/

/-! ## Representation details

**The machine.** The word RAM over the exact basis, as in `WordRAMAbstract`. At word size `w`, a
*word* is a natural number below `2 ^ w`. A machine has `r` registers `R[0], …, R[r - 1]` and an
unbounded memory `M : ℕ → ℕ`. Each binary operation computes its exact natural-number value; an
instruction faults on `x - y` with `y > x`, on `x / 0` or `x % 0`, on a constant or operation value
at least `2 ^ w`, or on jumping out of the program.
-/

variable {r : ℕ}

/-- Exact binary ALU operations. -/
inductive AluOp
  | add | sub | mul | div | mod | and | or | xor | shl | shr

/-- Exact natural-number evaluation of `AluOp`, or `none` on underflow / division by zero. -/
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

/-- Instructions over `r` registers; jump targets are instruction indices. -/
inductive Instr (r : ℕ)
  | const (d : Fin r) (x : ℕ)
  | copy (d i : Fin r)
  | alu (f : AluOp) (d i j : Fin r)
  | width (d : Fin r)
  | load (d a : Fin r)
  | store (a i : Fin r)
  | jump (t : ℕ)
  | branchEq (i j : Fin r) (t : ℕ)
  | branchLt (i j : Fin r) (t : ℕ)
  | halt (i : Fin r)

/-- A flat program is a list of instructions indexed from `0`. -/
abbrev Program (r : ℕ) := List (Instr r)

/-- Machine state: next instruction index `pc`, registers `reg`, and memory `mem`. -/
structure State (r : ℕ) where
  /-- Index of the next instruction. -/
  pc : ℕ
  /-- Register file `R[0..r - 1]`. -/
  reg : Fin r → ℕ
  /-- Unbounded word-addressed memory `M`. -/
  mem : ℕ → ℕ

/-- Outcome of one step: continue in a new state, halt with an output word, or fault. -/
inductive Outcome (r : ℕ)
  | next (s : State r)
  | halt (v : ℕ)
  | fault

/-- Single-step transition of program `p` at word size `w`. -/
def step (w : ℕ) (p : Program r) (s : State r) : Outcome r :=
  let set (d : Fin r) (x : ℕ) : Outcome r :=
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
  | some (.width d) => set d w
  | some (.load d a) => set d (s.mem (s.reg a))
  | some (.store a i) =>
    .next { s with pc := s.pc + 1, mem := Function.update s.mem (s.reg a) (s.reg i) }
  | some (.jump t) => .next { s with pc := t }
  | some (.branchEq i j t) => .next { s with pc := if s.reg i = s.reg j then t else s.pc + 1 }
  | some (.branchLt i j t) => .next { s with pc := if s.reg i < s.reg j then t else s.pc + 1 }
  | some (.halt i) => .halt (s.reg i)

/-- `Runs w p s t k`: `k` non-halting, non-faulting steps of `p` at word size `w` from `s` to `t`.
-/
def Runs (w : ℕ) (p : Program r) : State r → State r → ℕ → Prop :=
  Relation.RelatesInSteps fun s t => step w p s = .next t

/-! **Calling convention and memory confinement.** Registers `R[0..16]` hold persistent heap state
across calls (`p_init` reads `n` in `R[0]` and `base` in `R[1]`), `R[17..21]` carry each operation's
3-bit tag and `(handle, key)` arguments, `R[22..24]` return its result, and `R[25..]` are scratch
registers. -/

/-- Initial register assignment for `p_init`: `R[0] = n`, `R[1] = base`, and `0` elsewhere. -/
def initRegs (n base : ℕ) (i : Fin r) : ℕ :=
  if (i : ℕ) = 0 then n else if (i : ℕ) = 1 then base else 0

/-- Write `(t₂, t₁, t₀, a, b)` into `R[17..21]`, leaving every other register unchanged. -/
def setArgs (t₂ t₁ t₀ a b : ℕ) (reg : Fin r → ℕ) (i : Fin r) : ℕ :=
  if (i : ℕ) = 17 then t₂
  else if (i : ℕ) = 18 then t₁
  else if (i : ℕ) = 19 then t₀
  else if (i : ℕ) = 20 then a
  else if (i : ℕ) = 21 then b
  else reg i

/-- Prepare registers before calling `p_op`: write operation `o`'s tag and arguments into
`R[17..21]` and leave all other registers intact. -/
def prepareRegs {n : ℕ} : Op n → (Fin r → ℕ) → Fin r → ℕ
  | .isEmpty, reg => setArgs 0 0 0 0 0 reg
  | .getKey v, reg => setArgs 0 0 1 v 0 reg
  | .insert v k, reg => setArgs 0 1 0 v k reg
  | .decreaseKey v k, reg => setArgs 0 1 1 v k reg
  | .extractMin, reg => setArgs 1 0 0 0 0 reg

/-- Read register `idx`, or `0` when `r ≤ idx`. -/
def regAt (reg : Fin r → ℕ) (idx : ℕ) : ℕ :=
  if h : idx < r then reg ⟨idx, h⟩ else 0

/-- Decode operation `o`'s return value from `R[22..24]`: `R[22]` is the boolean result for
`isEmpty` and the presence flag for `getKey`/`extractMin`, `R[23]` is the extracted handle index,
and `R[24]` is the queried or extracted key. -/
def decodeResult {n : ℕ} : (o : Op n) → (Fin r → ℕ) → Option (OpResult o)
  | .isEmpty, reg => some (decide (regAt reg 22 ≠ 0))
  | .getKey _, reg =>
    if regAt reg 22 = 0 then some none else some (some (regAt reg 24))
  | .insert _ _, _ => some ()
  | .decreaseKey _ _, _ => some ()
  | .extractMin, reg =>
    if regAt reg 22 = 0 then some none
    else if h : regAt reg 23 < n then some (some (⟨regAt reg 23, h⟩, regAt reg 24))
    else none

/-- Every memory address outside `[base, base + len)` retains its previous value. -/
def UnchangedOutside (base len : ℕ) (m m' : ℕ → ℕ) : Prop :=
  ∀ a, a < base ∨ base + len ≤ a → m' a = m a

/-! ## Multi-operation execution and main theorems -/

/-- `RunsOps w p base len q reg mem ops reg' mem' total`: starting from abstract queue `q`,
registers `reg`, and memory `mem`, executing `ops` sequentially by preparing `R[17..21]`
(`prepareRegs`), running `p` from `pc = 0` to `halt`, decoding the exact `stepOp` return value
(`decodeResult`), and modifying memory only within `[base, base + len)` (`UnchangedOutside`) reaches
registers `reg'` and memory `mem'` in `total` instructions (each operation's `halt` included). -/
inductive RunsOps {n : ℕ} (w : ℕ) (p : Program r) (base len : ℕ) :
    Queue n → (Fin r → ℕ) → (ℕ → ℕ) → List (Op n) → (Fin r → ℕ) → (ℕ → ℕ) → ℕ → Prop
  | nil {q reg mem} : RunsOps w p base len q reg mem [] reg mem 0
  | cons {q reg mem o ops t reg' mem' steps rest} :
      Runs w p ⟨0, prepareRegs o reg, mem⟩ t steps →
      (∃ out, step w p t = .halt out) →
      decodeResult o t.reg = some (stepOp q o).2 →
      UnchangedOutside base len mem t.mem →
      RunsOps w p base len (stepOp q o).1 t.reg t.mem ops reg' mem' rest →
      RunsOps w p base len q reg mem (o :: ops) reg' mem' ((steps + 1) + rest)

/-- **Fibonacci heap (`O(1)` fresh initialization).** There exist a register count `r`, flat
programs `p_init` and `p_op` over `r` registers on the exact word RAM, and a constant `K` such that
for all `n`, `K_max`, `base`, `w`, `w`-bit memory `mem₀` zeroed on `[base, base + 9 n + 1)` with
`base + (9 n + 1) < 2 ^ w` and `K_max < 2 ^ w`, and every admissible sequence `ops` starting from
`emptyQueue n`: `p_init` halts in `t_init + 1 ≤ K` instructions without modifying memory outside
`[base, base + 9 n + 1)`, and `p_op` executes `ops` (with `m_q = numQueries ops`,
`m_ins = numInserts ops`, `m_dec = numDecreaseKeys ops`, and `m_ext = numExtractMins ops`) in
`t_ops ≤ K (m_q + m_ins + m_dec + m_ext (Nat.log 2 n + 1))` total instructions while producing every
exact `stepOp` result and leaving memory outside `[base, base + 9 n + 1)` unchanged. -/
theorem fibonacciHeap_amortized :
    ∃ r, ∃ p_init p_op : Program r, ∃ K,
      ∀ (n K_max base w : ℕ) (mem₀ : ℕ → ℕ) (ops : List (Op n)),
        base + (9 * n + 1) < 2 ^ w →
        K_max < 2 ^ w →
        (∀ a, mem₀ a < 2 ^ w) →
        (∀ a, base ≤ a → a < base + (9 * n + 1) → mem₀ a = 0) →
        ValidSeq K_max (emptyQueue n) ops →
        ∃ t₀ t_init reg_f mem_f t_ops,
          Runs w p_init ⟨0, initRegs n base, mem₀⟩ t₀ t_init ∧
          (∃ out, step w p_init t₀ = .halt out) ∧
          UnchangedOutside base (9 * n + 1) mem₀ t₀.mem ∧
          RunsOps w p_op base (9 * n + 1) (emptyQueue n) t₀.reg t₀.mem ops reg_f mem_f t_ops ∧
          t_init + 1 ≤ K ∧
          t_ops ≤
            K * (numQueries ops + numInserts ops + numDecreaseKeys ops +
              numExtractMins ops * (Nat.log 2 n + 1)) :=
  FibonacciHeapBridge.amortized_fresh
    ⟨AluOp, .add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr, @AluOp.rec, AluOp.eval,
      Instr, .const, .copy, .alu, .width, .load, .store, .jump, .branchEq, .branchLt, .halt,
      @Instr.rec, State, .mk, Outcome, .next, .halt, .fault, step,
      ComplexityTests.Abstracts.WordRAMBridge.haltsVia Instr State Outcome step
        fun f g a o => o.rec f g a,
      fun _ _ => True⟩
    (by constructor <;>
      simp_all [step, ComplexityTests.Abstracts.WordRAMBridge.haltsVia, AluOp.eval])
    ⟨Op, .isEmpty, .getKey, .insert, .decreaseKey, .extractMin, @Op.rec, @chooseMin, @foldMin,
      @findMin, fun q o => (stepOp q o).1, fun q o reg => decodeResult o reg = some (stepOp q o).2,
      @ValidOp, @ValidSeq, @numQueries, @numInserts, @numDecreaseKeys, @numExtractMins, @initRegs,
      @prepareRegs 42, @State.reg, @State.mem, @RunsOps⟩
    ⟨fun _ _ => ⟨fun h => by simp [chooseMin, h], fun h => by simp [chooseMin, h]⟩,
      rfl, fun _ _ => rfl, fun _ => rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun q => by simp only [stepOp]; cases findMin q <;> rfl,
      fun _ _ h => congrArg some (decide_eq_decide.mpr h),
      fun _ _ _ h => h, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
      fun q _ h => h.trans (congrArg some (by simp only [stepOp]; cases findMin q <;> rfl)),
      fun _ _ _ h => h, fun _ _ _ h => h, fun _ _ _ h => h,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      RunsOps.nil, RunsOps.cons⟩

/-- **Fibonacci heap (`O(n)` reusable initialization on arbitrary memory).** Under the same
word-size conditions (`base + (9 n + 1) < 2 ^ w`, `K_max < 2 ^ w`, and every cell of `mem₀` below
`2 ^ w`), without assuming `[base, base + 9 n + 1)` is initially zeroed, `p_init` clears the block
and initializes an empty heap in `t_init + 1 ≤ K (n + 1)` instructions, and `p_op` executes `ops` in
`t_ops ≤ K (numQueries ops + numInserts ops + numDecreaseKeys ops +
numExtractMins ops * (Nat.log 2 n + 1))` instructions while preserving memory
outside `[base, base + 9 n + 1)`. -/
theorem fibonacciHeap_amortized_reusable :
    ∃ r, ∃ p_init p_op : Program r, ∃ K,
      ∀ (n K_max base w : ℕ) (mem₀ : ℕ → ℕ) (ops : List (Op n)),
        base + (9 * n + 1) < 2 ^ w →
        K_max < 2 ^ w →
        (∀ a, mem₀ a < 2 ^ w) →
        ValidSeq K_max (emptyQueue n) ops →
        ∃ t₀ t_init reg_f mem_f t_ops,
          Runs w p_init ⟨0, initRegs n base, mem₀⟩ t₀ t_init ∧
          (∃ out, step w p_init t₀ = .halt out) ∧
          UnchangedOutside base (9 * n + 1) mem₀ t₀.mem ∧
          RunsOps w p_op base (9 * n + 1) (emptyQueue n) t₀.reg t₀.mem ops reg_f mem_f t_ops ∧
          t_init + 1 ≤ K * (n + 1) ∧
          t_ops ≤
            K * (numQueries ops + numInserts ops + numDecreaseKeys ops +
              numExtractMins ops * (Nat.log 2 n + 1)) :=
  FibonacciHeapBridge.amortized_reusable
    ⟨AluOp, .add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr, @AluOp.rec, AluOp.eval,
      Instr, .const, .copy, .alu, .width, .load, .store, .jump, .branchEq, .branchLt, .halt,
      @Instr.rec, State, .mk, Outcome, .next, .halt, .fault, step,
      ComplexityTests.Abstracts.WordRAMBridge.haltsVia Instr State Outcome step
        fun f g a o => o.rec f g a,
      fun _ _ => True⟩
    (by constructor <;>
      simp_all [step, ComplexityTests.Abstracts.WordRAMBridge.haltsVia, AluOp.eval])
    ⟨Op, .isEmpty, .getKey, .insert, .decreaseKey, .extractMin, @Op.rec, @chooseMin, @foldMin,
      @findMin, fun q o => (stepOp q o).1, fun q o reg => decodeResult o reg = some (stepOp q o).2,
      @ValidOp, @ValidSeq, @numQueries, @numInserts, @numDecreaseKeys, @numExtractMins, @initRegs,
      @prepareRegs 42, @State.reg, @State.mem, @RunsOps⟩
    ⟨fun _ _ => ⟨fun h => by simp [chooseMin, h], fun h => by simp [chooseMin, h]⟩,
      rfl, fun _ _ => rfl, fun _ => rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun q => by simp only [stepOp]; cases findMin q <;> rfl,
      fun _ _ h => congrArg some (decide_eq_decide.mpr h),
      fun _ _ _ h => h, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
      fun q _ h => h.trans (congrArg some (by simp only [stepOp]; cases findMin q <;> rfl)),
      fun _ _ _ h => h, fun _ _ _ h => h, fun _ _ _ h => h,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      RunsOps.nil, RunsOps.cons⟩

/--
info: abstract audit passed for `ComplexityAbstracts.FibonacciHeapAbstract`: 308 root
declarations, 259 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.FibonacciHeapAbstract

end ComplexityAbstracts.FibonacciHeapAbstract
