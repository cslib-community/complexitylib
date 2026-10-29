/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.FibonacciHeapBridge

/-! # Fibonacci heaps: amortized priority queues on the word RAM

A min-priority queue with capacity `n_max`, key bound `U`, and value bound `V` maintains at most
`n_max` elements, where each stored element is a key–value pair `(u, v)` with `u < U` and `v < V`
identified by a handle `h : Fin n_max` allocated by the data structure. It supports emptiness and
handle-lookup queries (`isEmpty`, `get h`), inserting a new `(key, value)` pair (`insert u v`, which
allocates and returns an unused handle `h : Fin n_max`), lowering the key of a currently stored
handle (`decreaseKey h u'`), and removing a stored element of minimum key (`extractMin`, which
returns `some (u, v, h)` or `none` when empty). Fredman and Tarjan's Fibonacci heap supports queries
in `O(1)` time, `insert` and `decreaseKey` in `O(1)` amortized time, and `extractMin` in
`O(log n + 1)` amortized time, where `n` is the current number of stored elements.

The theorems below state this guarantee on the word RAM over the exact basis of operations, inside a
caller-chosen contiguous block `[base, base + 11 * n_max + 1)` of `11 * n_max + 1` words:

* `fibonacciHeap_amortized` initializes an empty heap on zeroed `[base, base + 11 * n_max + 1)` in
  `O(1)` instructions and executes any admissible sequence `ops` of `m_q` queries, `m_ins`
  insertions, `m_dec` key decreases, and `m_ext` minimum extractions in
  `O(m_q + m_ins + m_dec + ∑ (log n_t + 1))` total instructions, where `n_t = size q_t` is the
  number of stored elements immediately before the `t`-th `extractMin` (bounded in turn by
  `m_ext * (log n_max + 1)`);
* `fibonacciHeap_amortized_reusable` initializes an empty heap on arbitrary `w`-bit memory in
  `O(n_max + 1)` instructions and achieves the same amortized operation bound.

In both theorems, neither initialization nor any operation modifies memory outside
`[base, base + 11 * n_max + 1)`. Every concept in the statements—the priority queue, its relational
transition specification, admissible operation sequences, the exact word RAM, the register calling
convention and memory confinement—is defined from scratch in this file. Lean checks the proofs
through `FibonacciHeapBridge`, and `#check_abstract` verifies mechanically that no definition or
theorem statement here depends on implementation modules.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci heaps and their uses in improved network optimization
  algorithms*][FredmanTarjan1987], Section 2, p. 604 (the potential defined before Theorem 1) and
  Theorem 1.
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 19.1, eq. (19.1), and Sections 19.2–19.4.
-/

namespace ComplexityAbstracts.FibonacciHeapAbstract

/-! ## Priority queues with handles

A priority-queue state `q : Queue n_max` maps each handle `h : Fin n_max` to `none` when `h` is
currently unused and to `some (u, v)` when `h` is present with key `u` and satellite value `v`. The
current number of stored elements is `size q`. Because the data structure chooses which unused
handle to allocate on `insert u v` and which minimum-key entry to remove on `extractMin` when keys
tie, transitions are specified relationally by `StepRel`. An operation sequence is admissible
(`ValidSeq U V`) when every operation is valid in the current state and the remaining suffix is
admissible after every valid relational outcome.
-/

/-- Operations on a min-priority queue with capacity `n_max`, natural-number keys, and
natural-number satellite values. -/
inductive Op (n_max : ℕ)
  | isEmpty
  | get (h : Fin n_max)
  | insert (u v : ℕ)
  | decreaseKey (h : Fin n_max) (u' : ℕ)
  | extractMin

/-- Abstract state of a min-priority queue with capacity `n_max`: `none` when handle `h` is unused,
`some (u, v)` when `h` stores key `u` and satellite value `v`. -/
abbrev Queue (n_max : ℕ) := Fin n_max → Option (ℕ × ℕ)

/-- The empty priority queue of capacity `n_max`. -/
def emptyQueue (n_max : ℕ) : Queue n_max := fun _ => none

/-- Current number of elements stored in `q`. -/
def size {n_max : ℕ} (q : Queue n_max) : ℕ :=
  (Finset.univ.filter fun h => (q h).isSome).card

/-- Handle `h` is present in `q` with `(u, v)` and `u` is a minimum key among all stored elements.
-/
def IsMinEntry {n_max : ℕ} (q : Queue n_max) (h : Fin n_max) (u v : ℕ) : Prop :=
  q h = some (u, v) ∧ ∀ h' u' v', q h' = some (u', v') → u ≤ u'

/-- Return type of each priority-queue operation. -/
def OpResult {n_max : ℕ} : Op n_max → Type
  | .isEmpty => Bool
  | .get _ => Option (ℕ × ℕ)
  | .insert _ _ => Option (Fin n_max)
  | .decreaseKey _ _ => Unit
  | .extractMin => Option (ℕ × ℕ × Fin n_max)

/-- Relational transition and return value of operation `o` on queue `q`: `insert u v` allocates any
currently unused handle `h : Fin n_max` and stores `(u, v)` at `h`; `extractMin` removes and returns
any stored entry `(u, v, h)` of minimum key `u` (or `none` when `q` is empty). -/
def StepRel {n_max : ℕ} (q : Queue n_max) : (o : Op n_max) → Queue n_max → OpResult o → Prop
  | .isEmpty, q', res => q' = q ∧ res = decide (∀ h, q h = none)
  | .get h, q', res => q' = q ∧ res = q h
  | .insert u v, q', res =>
    ∃ h : Fin n_max, q h = none ∧ q' = Function.update q h (some (u, v)) ∧ res = some h
  | .decreaseKey h u', q', res =>
    (∃ u₀ v, q h = some (u₀, v) ∧ q' = Function.update q h (some (u', v))) ∧ res = ()
  | .extractMin, q', res =>
    ((∀ h, q h = none) ∧ q' = q ∧ res = none) ∨
    (∃ h u v, IsMinEntry q h u v ∧ q' = Function.update q h none ∧ res = some (u, v, h))

/-- Precondition for a single operation under key bound `U` and value bound `V`: `insert u v`
requires `size q < n_max`, `u < U`, and `v < V`; `decreaseKey h u'` requires `h` to be present with
some current key `u₀ ≥ u'`. -/
def ValidOp {n_max : ℕ} (U V : ℕ) (q : Queue n_max) : Op n_max → Prop
  | .isEmpty | .get _ | .extractMin => True
  | .insert u v => size q < n_max ∧ u < U ∧ v < V
  | .decreaseKey h u' => ∃ u₀ v, q h = some (u₀, v) ∧ u' ≤ u₀

/-- Sequential admissibility of an operation list starting from queue `q`: each operation is valid
in the current state, and the remaining suffix is valid after every relational transition `StepRel`
that the operation may take. -/
def ValidSeq {n_max : ℕ} (U V : ℕ) : Queue n_max → List (Op n_max) → Prop
  | _, [] => True
  | q, o :: ops => ValidOp U V q o ∧ ∀ q' res, StepRel q o q' res → ValidSeq U V q' ops

/-- Number of `isEmpty` and `get` queries in `ops`. -/
def numQueries {n_max : ℕ} : List (Op n_max) → ℕ
  | [] => 0
  | .isEmpty :: ops => 1 + numQueries ops
  | .get _ :: ops => 1 + numQueries ops
  | .insert _ _ :: ops => numQueries ops
  | .decreaseKey _ _ :: ops => numQueries ops
  | .extractMin :: ops => numQueries ops

/-- Number of `insert` operations in `ops`. -/
def numInserts {n_max : ℕ} : List (Op n_max) → ℕ
  | [] => 0
  | .isEmpty :: ops => numInserts ops
  | .get _ :: ops => numInserts ops
  | .insert _ _ :: ops => 1 + numInserts ops
  | .decreaseKey _ _ :: ops => numInserts ops
  | .extractMin :: ops => numInserts ops

/-- Number of `decreaseKey` operations in `ops`. -/
def numDecreaseKeys {n_max : ℕ} : List (Op n_max) → ℕ
  | [] => 0
  | .isEmpty :: ops => numDecreaseKeys ops
  | .get _ :: ops => numDecreaseKeys ops
  | .insert _ _ :: ops => numDecreaseKeys ops
  | .decreaseKey _ _ :: ops => 1 + numDecreaseKeys ops
  | .extractMin :: ops => numDecreaseKeys ops

/-- Number of `extractMin` operations in `ops`. -/
def numExtractMins {n_max : ℕ} : List (Op n_max) → ℕ
  | [] => 0
  | .isEmpty :: ops => numExtractMins ops
  | .get _ :: ops => numExtractMins ops
  | .insert _ _ :: ops => numExtractMins ops
  | .decreaseKey _ _ :: ops => numExtractMins ops
  | .extractMin :: ops => 1 + numExtractMins ops

/-- Logarithmic cost factor `Nat.log 2 n + 1` in the current number of stored elements `n = size q`
for an `extractMin` step from queue `q`, and `0` for all other operations. -/
def extractStepLog {n_max : ℕ} (q : Queue n_max) : Op n_max → ℕ
  | .extractMin => Nat.log 2 (size q) + 1
  | _ => 0

/-! ## Memory layout, calling convention and cost

The data structure occupies `11 * n_max + 1` words at addresses `[base, base + 11 * n_max + 1)`,
assuming `base + (11 * n_max + 1) < 2 ^ w`, `U < 2 ^ w`, `V < 2 ^ w`, and every initial memory cell
holds a `w`-bit word (`< 2 ^ w`). Initialization (`p_init`) starts at `pc = 0` with `R[0] = n_max`,
`R[1] = base`, and `0` in all other registers (`initRegs`). Each subsequent operation call (`p_op`)
starts at `pc = 0` after writing the 3-bit operation tag, handle/key arguments into `R[17..21]`, and
satellite value argument into `R[46]` while leaving all other registers unchanged (`prepareRegs`),
runs to a `halt` instruction, and returns its observation in `R[22..24]` and `R[47]`
(`decodeResult`), leaving every memory cell outside `[base, base + 11 * n_max + 1)` unchanged
(`UnchangedOutside`). Every instruction costs one unit of time, each `halt` included. The appendix
defines the exact word RAM (`Program`, `State`, `step`, `Runs`) and the register and memory
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

/-! **Calling convention and memory confinement.** Registers `R[0..16]` and `R[42..45]` hold
persistent heap and allocator state across calls (`p_init` reads `n_max` in `R[0]` and `base` in
`R[1]`), `R[17..21]` and `R[46]` carry each operation's 3-bit tag and `(handle, key, value)`
arguments, `R[22..24]` and `R[47]` return its result, and the remaining registers are scratch
registers. -/

/-- Initial register assignment for `p_init`: `R[0] = n_max`, `R[1] = base`, and `0` elsewhere. -/
def initRegs (n_max base : ℕ) (i : Fin r) : ℕ :=
  if (i : ℕ) = 0 then n_max else if (i : ℕ) = 1 then base else 0

/-- Write `(t₂, t₁, t₀, a, b)` into `R[17..21]` and `val` into `R[46]`, leaving every other register
unchanged. -/
def setArgs (t₂ t₁ t₀ a b val : ℕ) (reg : Fin r → ℕ) (i : Fin r) : ℕ :=
  if (i : ℕ) = 17 then t₂
  else if (i : ℕ) = 18 then t₁
  else if (i : ℕ) = 19 then t₀
  else if (i : ℕ) = 20 then a
  else if (i : ℕ) = 21 then b
  else if (i : ℕ) = 46 then val
  else reg i

/-- Prepare registers before calling `p_op`: write operation `o`'s tag and arguments into
`R[17..21]` and `R[46]`, leaving all other registers intact. -/
def prepareRegs {n_max : ℕ} : Op n_max → (Fin r → ℕ) → Fin r → ℕ
  | .isEmpty, reg => setArgs 0 0 0 0 0 0 reg
  | .get h, reg => setArgs 0 0 1 h 0 0 reg
  | .insert u v, reg => setArgs 0 1 0 0 u v reg
  | .decreaseKey h u', reg => setArgs 0 1 1 h u' 0 reg
  | .extractMin, reg => setArgs 1 0 0 0 0 0 reg

/-- Read register `idx`, or `0` when `r ≤ idx`. -/
def regAt (reg : Fin r → ℕ) (idx : ℕ) : ℕ :=
  if h : idx < r then reg ⟨idx, h⟩ else 0

/-- Decode operation `o`'s return value from `R[22..24]` and `R[47]`: `R[22]` is the boolean result
for `isEmpty` and the presence flag for `get` and `extractMin`, `R[23]` is the allocated or
extracted handle index, `R[24]` is the queried or extracted key, and `R[47]` is the queried or
extracted satellite value. -/
def decodeResult {n_max : ℕ} : (o : Op n_max) → (Fin r → ℕ) → Option (OpResult o)
  | .isEmpty, reg => some (decide (regAt reg 22 ≠ 0))
  | .get _, reg =>
    if regAt reg 22 = 0 then some none else some (some (regAt reg 24, regAt reg 47))
  | .insert _ _, reg =>
    if h : regAt reg 23 < n_max then some (some ⟨regAt reg 23, h⟩) else none
  | .decreaseKey _ _, _ => some ()
  | .extractMin, reg =>
    if regAt reg 22 = 0 then some none
    else if h : regAt reg 23 < n_max then
      some (some (regAt reg 24, regAt reg 47, ⟨regAt reg 23, h⟩))
    else none

/-- Every memory address outside `[base, base + len)` retains its previous value. -/
def UnchangedOutside (base len : ℕ) (m m' : ℕ → ℕ) : Prop :=
  ∀ a, a < base ∨ base + len ≤ a → m' a = m a

/-! ## Multi-operation execution and main theorems -/

/-- `RunsOps w p base len q reg mem ops q' reg' mem' total extLog`: starting from abstract queue
`q`, registers `reg`, and memory `mem`, executing `ops` sequentially by preparing `R[17..21]` and
`R[46]` (`prepareRegs`), running `p` from `pc = 0` to `halt`, advancing `q` to some next queue state
`q₁` with return value `res` satisfying `StepRel q o q₁ res` and `decodeResult o t.reg = some res`,
and modifying memory only within `[base, base + len)` (`UnchangedOutside`) reaches final queue `q'`,
registers `reg'`, and memory `mem'` in `total` instructions (each operation's `halt` included) with
cumulative extraction log cost `extLog` (the sum of `Nat.log 2 (size q_t) + 1` over all `extractMin`
steps along the execution). -/
inductive RunsOps {n_max : ℕ} (w : ℕ) (p : Program r) (base len : ℕ) :
    Queue n_max → (Fin r → ℕ) → (ℕ → ℕ) → List (Op n_max) →
      Queue n_max → (Fin r → ℕ) → (ℕ → ℕ) → ℕ → ℕ → Prop
  | nil {q reg mem} : RunsOps w p base len q reg mem [] q reg mem 0 0
  | cons {q q₁ q' reg mem o res ops t reg' mem' steps rest extRest} :
      Runs w p ⟨0, prepareRegs o reg, mem⟩ t steps →
      (∃ out, step w p t = .halt out) →
      StepRel q o q₁ res →
      decodeResult o t.reg = some res →
      UnchangedOutside base len mem t.mem →
      RunsOps w p base len q₁ t.reg t.mem ops q' reg' mem' rest extRest →
      RunsOps w p base len q reg mem (o :: ops) q' reg' mem'
        ((steps + 1) + rest) (extractStepLog q o + extRest)

/-- **Fibonacci heap (`O(1)` fresh initialization).** There exist a register count `r`, flat
programs `p_init` and `p_op` over `r` registers on the exact word RAM, and a constant `K` such that
for all `n_max`, `U`, `V`, `base`, `w`, `w`-bit memory `mem₀` zeroed on
`[base, base + 11 * n_max + 1)` with `base + (11 * n_max + 1) < 2 ^ w`, `U < 2 ^ w`, `V < 2 ^ w`,
and every admissible sequence `ops` starting from `emptyQueue n_max`: `p_init` halts in
`t_init + 1 ≤ K` instructions without modifying memory outside `[base, base + 11 * n_max + 1)`, and
`p_op` executes `ops` (with `m_q = numQueries ops`, `m_ins = numInserts ops`,
`m_dec = numDecreaseKeys ops`, and `m_ext = numExtractMins ops`) in
`t_ops ≤ K * (m_q + m_ins + m_dec + extLog)` total instructions, where `extLog` is the sum of
`Nat.log 2 (size q_t) + 1` in the current number of stored elements `size q_t` over all `extractMin`
steps (satisfying `extLog ≤ m_ext * (Nat.log 2 n_max + 1)`), while producing valid relational
`StepRel` results and leaving memory outside `[base, base + 11 * n_max + 1)` unchanged. -/
theorem fibonacciHeap_amortized :
    ∃ r, ∃ p_init p_op : Program r, ∃ K,
      ∀ (n_max U V base w : ℕ) (mem₀ : ℕ → ℕ) (ops : List (Op n_max)),
        base + (11 * n_max + 1) < 2 ^ w →
        U < 2 ^ w →
        V < 2 ^ w →
        (∀ a, mem₀ a < 2 ^ w) →
        (∀ a, base ≤ a → a < base + (11 * n_max + 1) → mem₀ a = 0) →
        ValidSeq U V (emptyQueue n_max) ops →
        ∃ t₀ t_init q_f reg_f mem_f t_ops extLog,
          Runs w p_init ⟨0, initRegs n_max base, mem₀⟩ t₀ t_init ∧
          (∃ out, step w p_init t₀ = .halt out) ∧
          UnchangedOutside base (11 * n_max + 1) mem₀ t₀.mem ∧
          RunsOps w p_op base (11 * n_max + 1) (emptyQueue n_max) t₀.reg t₀.mem ops
            q_f reg_f mem_f t_ops extLog ∧
          t_init + 1 ≤ K ∧
          t_ops ≤
            K * (numQueries ops + numInserts ops + numDecreaseKeys ops + extLog) ∧
          extLog ≤ numExtractMins ops * (Nat.log 2 n_max + 1) :=
  FibonacciHeapBridge.amortized_fresh
    ⟨AluOp, .add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr, @AluOp.rec, AluOp.eval,
      Instr, .const, .copy, .alu, .width, .load, .store, .jump, .branchEq, .branchLt, .halt,
      @Instr.rec, State, .mk, Outcome, .next, .halt, .fault, step,
      ComplexityTests.Abstracts.WordRAMBridge.haltsVia Instr State Outcome step
        fun f g a o => o.rec f g a,
      fun _ _ => True⟩
    (by constructor <;>
      simp_all [step, ComplexityTests.Abstracts.WordRAMBridge.haltsVia, AluOp.eval])
    ⟨Op, .isEmpty, .get, .insert, .decreaseKey, .extractMin, @Op.rec, @size, @extractStepLog,
      fun q o q' => ∃ res, StepRel q o q' res,
      fun q o q' reg => ∃ res, StepRel q o q' res ∧ decodeResult o reg = some res,
      @ValidOp, @ValidSeq, @numQueries, @numInserts, @numDecreaseKeys, @numExtractMins, @initRegs,
      @prepareRegs 48, @State.reg, @State.mem, @RunsOps⟩
    ⟨fun _ => rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl,
      fun _ => ⟨_, rfl, rfl⟩,
      fun _ _ => ⟨_, rfl, rfl⟩,
      fun _ _ _ h hnone => ⟨some h, h, hnone, rfl, rfl⟩,
      fun _ _ _ u₀ v hq => ⟨(), ⟨u₀, v, hq, rfl⟩, rfl⟩,
      fun _ hemp => ⟨none, Or.inl ⟨hemp, rfl, rfl⟩⟩,
      fun _ h u v hq hmin => ⟨some (u, v, h), Or.inr ⟨h, u, v, ⟨hq, hmin⟩, rfl, rfl⟩⟩,
      fun q _ h => ⟨decide (∀ h, q h = none), ⟨rfl, rfl⟩, congrArg some (decide_eq_decide.mpr h)⟩,
      fun q h _ hd => ⟨q h, ⟨rfl, rfl⟩, hd⟩,
      fun _ _ _ h _ hnone hv =>
        ⟨some h, ⟨h, hnone, rfl, rfl⟩, by
          simp only [decodeResult, regAt, show (23 : ℕ) < 48 by decide, ↓reduceDIte, hv,
            Fin.is_lt, Fin.eta]⟩,
      fun _ _ _ u₀ v _ hq => ⟨(), ⟨⟨u₀, v, hq, rfl⟩, rfl⟩, rfl⟩,
      fun _ _ hemp hflag =>
        ⟨none, Or.inl ⟨hemp, rfl, rfl⟩, by
          simp only [decodeResult, regAt, show (22 : ℕ) < 48 by decide, ↓reduceDIte, hflag,
            ↓reduceIte]⟩,
      fun _ h u v _ hq hmin hflag hv hk hval =>
        ⟨some (u, v, h), Or.inr ⟨h, u, v, ⟨hq, hmin⟩, rfl, rfl⟩, by
          simp only [decodeResult, regAt, show (22 : ℕ) < 48 by decide,
            show (23 : ℕ) < 48 by decide, show (24 : ℕ) < 48 by decide,
            show (47 : ℕ) < 48 by decide, ↓reduceDIte, hflag, ↓reduceIte,
            hv, hk, hval, Fin.is_lt, Fin.eta]⟩,
      fun _ _ _ h => h,
      fun _ _ _ h => h,
      fun _ _ _ h => ⟨h.1, fun q' hex => hex.elim fun res hstep => h.2 q' res hstep⟩,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      RunsOps.nil,
      fun hr hh hd hmod hrest => hd.elim fun _ hsd => RunsOps.cons hr hh hsd.1 hsd.2 hmod hrest⟩

/-- **Fibonacci heap (`O(n_max + 1)` reusable initialization on arbitrary memory).** Under the same
word-size conditions (`base + (11 * n_max + 1) < 2 ^ w`, `U < 2 ^ w`, `V < 2 ^ w`, and every cell of
`mem₀` below `2 ^ w`), without assuming `[base, base + 11 * n_max + 1)` is initially zeroed,
`p_init` clears the block and initializes an empty heap in `t_init + 1 ≤ K * (n_max + 1)`
instructions, and `p_op` executes `ops` in
`t_ops ≤ K * (numQueries ops + numInserts ops + numDecreaseKeys ops + extLog)` instructions with
`extLog ≤ numExtractMins ops * (Nat.log 2 n_max + 1)` while preserving memory outside
`[base, base + 11 * n_max + 1)`. -/
theorem fibonacciHeap_amortized_reusable :
    ∃ r, ∃ p_init p_op : Program r, ∃ K,
      ∀ (n_max U V base w : ℕ) (mem₀ : ℕ → ℕ) (ops : List (Op n_max)),
        base + (11 * n_max + 1) < 2 ^ w →
        U < 2 ^ w →
        V < 2 ^ w →
        (∀ a, mem₀ a < 2 ^ w) →
        ValidSeq U V (emptyQueue n_max) ops →
        ∃ t₀ t_init q_f reg_f mem_f t_ops extLog,
          Runs w p_init ⟨0, initRegs n_max base, mem₀⟩ t₀ t_init ∧
          (∃ out, step w p_init t₀ = .halt out) ∧
          UnchangedOutside base (11 * n_max + 1) mem₀ t₀.mem ∧
          RunsOps w p_op base (11 * n_max + 1) (emptyQueue n_max) t₀.reg t₀.mem ops
            q_f reg_f mem_f t_ops extLog ∧
          t_init + 1 ≤ K * (n_max + 1) ∧
          t_ops ≤
            K * (numQueries ops + numInserts ops + numDecreaseKeys ops + extLog) ∧
          extLog ≤ numExtractMins ops * (Nat.log 2 n_max + 1) :=
  FibonacciHeapBridge.amortized_reusable
    ⟨AluOp, .add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr, @AluOp.rec, AluOp.eval,
      Instr, .const, .copy, .alu, .width, .load, .store, .jump, .branchEq, .branchLt, .halt,
      @Instr.rec, State, .mk, Outcome, .next, .halt, .fault, step,
      ComplexityTests.Abstracts.WordRAMBridge.haltsVia Instr State Outcome step
        fun f g a o => o.rec f g a,
      fun _ _ => True⟩
    (by constructor <;>
      simp_all [step, ComplexityTests.Abstracts.WordRAMBridge.haltsVia, AluOp.eval])
    ⟨Op, .isEmpty, .get, .insert, .decreaseKey, .extractMin, @Op.rec, @size, @extractStepLog,
      fun q o q' => ∃ res, StepRel q o q' res,
      fun q o q' reg => ∃ res, StepRel q o q' res ∧ decodeResult o reg = some res,
      @ValidOp, @ValidSeq, @numQueries, @numInserts, @numDecreaseKeys, @numExtractMins, @initRegs,
      @prepareRegs 48, @State.reg, @State.mem, @RunsOps⟩
    ⟨fun _ => rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl,
      fun _ => ⟨_, rfl, rfl⟩,
      fun _ _ => ⟨_, rfl, rfl⟩,
      fun _ _ _ h hnone => ⟨some h, h, hnone, rfl, rfl⟩,
      fun _ _ _ u₀ v hq => ⟨(), ⟨u₀, v, hq, rfl⟩, rfl⟩,
      fun _ hemp => ⟨none, Or.inl ⟨hemp, rfl, rfl⟩⟩,
      fun _ h u v hq hmin => ⟨some (u, v, h), Or.inr ⟨h, u, v, ⟨hq, hmin⟩, rfl, rfl⟩⟩,
      fun q _ h => ⟨decide (∀ h, q h = none), ⟨rfl, rfl⟩, congrArg some (decide_eq_decide.mpr h)⟩,
      fun q h _ hd => ⟨q h, ⟨rfl, rfl⟩, hd⟩,
      fun _ _ _ h _ hnone hv =>
        ⟨some h, ⟨h, hnone, rfl, rfl⟩, by
          simp only [decodeResult, regAt, show (23 : ℕ) < 48 by decide, ↓reduceDIte, hv,
            Fin.is_lt, Fin.eta]⟩,
      fun _ _ _ u₀ v _ hq => ⟨(), ⟨⟨u₀, v, hq, rfl⟩, rfl⟩, rfl⟩,
      fun _ _ hemp hflag =>
        ⟨none, Or.inl ⟨hemp, rfl, rfl⟩, by
          simp only [decodeResult, regAt, show (22 : ℕ) < 48 by decide, ↓reduceDIte, hflag,
            ↓reduceIte]⟩,
      fun _ h u v _ hq hmin hflag hv hk hval =>
        ⟨some (u, v, h), Or.inr ⟨h, u, v, ⟨hq, hmin⟩, rfl, rfl⟩, by
          simp only [decodeResult, regAt, show (22 : ℕ) < 48 by decide,
            show (23 : ℕ) < 48 by decide, show (24 : ℕ) < 48 by decide,
            show (47 : ℕ) < 48 by decide, ↓reduceDIte, hflag, ↓reduceIte,
            hv, hk, hval, Fin.is_lt, Fin.eta]⟩,
      fun _ _ _ h => h,
      fun _ _ _ h => h,
      fun _ _ _ h => ⟨h.1, fun q' hex => hex.elim fun res hstep => h.2 q' res hstep⟩,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, rfl,
      fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      RunsOps.nil,
      fun hr hh hd hmod hrest => hd.elim fun _ hsd => RunsOps.cons hr hh hsd.1 hsd.2 hmod hrest⟩

/--
info: abstract audit passed for `ComplexityAbstracts.FibonacciHeapAbstract`: 303 root
declarations, 260 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.FibonacciHeapAbstract

end ComplexityAbstracts.FibonacciHeapAbstract
