/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.HashTablesBridge
import Cslib.Probability.PMF
import Mathlib.Data.Nat.Log

/-!
# Formal Abstract: Word-RAM Hash Tables

This self-contained file states the formal specification and expected-amortized multi-operation
theorems for the four Word-RAM dictionary hash tables in Complexitylib, specialized to the
polynomial key-universe exponent `c_exp = 4` (`U ≤ max n_max 4 ^ 4` where required):

1. **Chained hashing with multiply-shift** (`ChainedHash.seq_expected_amortized`,
   following `[CLRS2009]`, 3rd ed., Sections 11.2 and 11.3.3, Theorem 11.3 and Corollary 11.4,
   and `[DietzfelbingerHagerupKatajainenPenttonen1997]`, Lemma 2.4).
2. **Linear probing with `5`-wise independent polynomial hashing**
   (`LinearProbing.seq_expected_amortized`, following `[PaghPaghRuzic2009]`,
   *SIAM J. Comput.* 39(3):1107–1120, 2009, Section 2.3 Lemma 2.1 pp. 1110–1111 and Section 4
   Lemma 4.1, Theorem 4.3, Theorem 4.5 pp. 1114–1118; `[CLRS2009]`, 3rd ed., Section 11.4;
   `[Vadhan2012]`, Section 3.5.5; `[CarterWegman1979]`; `[WegmanCarter1981]`;
   `[LidlNiederreiter1997]`).
3. **Uniform probing via odd-stride double hashing** (`UniformProbing.seq_expected_amortized`,
   following `[CLRS2009]`, 3rd ed., Section 11.4, pp. 269–277; `[SchmidtSiegel1990]`, STOC 1990,
   pp. 224–234, and NYU Courant TR1995-687, May 1995, pp. 1–2, 4–7, 37–39; `[Thorup2013]`,
   FOCS 2013, pp. 90–99, and `arXiv:1311.3121v2`, Theorem 1(a) p. 4, Lemma 2 p. 5, and Section 2
   Eqs. (6)–(7) p. 11).
4. **Cuckoo hashing** (`CuckooHashing.cuckoo_seq_expected_amortized`, following `[PaghRodler2004]`,
   8 Dec 2003 author manuscript / *J. Algorithms* 51(2):122–144, 2004, Section 2.3 "Analysis",
   manuscript pp. 6–10: Lemma 1 p. 7, Eq. (3) p. 9, rehash analysis pp. 9–10; `[Thorup2013]`,
   FOCS 2013, pp. 90–99, and `arXiv:1311.3121v2`, Theorem 1(a) p. 4, Lemma 2 p. 5, Section 2
   Eqs. (6)–(7) p. 11, and Section 3 Theorem 7(a) and Lemmas 8–9 pp. 12–14; `[CarterWegman1979]`;
   `[WegmanCarter1981]`).

## Scope, program parameterization, and cost accounting

- **Insert-only bounded capacity:** All four tables implement `DictOp U` (`get` and `insert` with
  overwrite) up to `n_max` distinct keys (`ValidDictHistory V n_max`). Key deletion (`erase`) is
  not supported, unlike the dynamic dictionaries in `[PaghPaghRuzic2009]` and `[PaghRodler2004]`.
- **Program dependence:** In each headline theorem, the existential over the initializer and
  operation programs `∃ (p_init p_op : List (Instr r))` is placed outside the universal quantifiers
  over `V`, `w`, and `base` (and outside `U` for uniform probing and cuckoo hashing):
  - in `chainedHashing` and `linearProbing`, `p_init` and `p_op` depend on `(U, n_max)`;
  - in `uniformProbing` and `cuckooHashing`, `p_init` and `p_op` depend only on `n_max` (at fixed
    `c_exp = 4`; `cuckooHashing` also receives `n_max` and `U` in `reg₀ 3` and `reg₀ 4` at
    initialization).
  No theorem in this abstract bounds the static code length `p_init.length` or `p_op.length`; all
  time bounds count **executed instructions** (`expectedTime w p s ≤ T + 1`), excluding caller
  argument preparation (`prepareDictRegs`) and dispatch.
- **Initialization step scaling and memory confinement:** From zeroed memory in `[base, base + sp)`,
  initialization executes in `16 = O(1)` steps for `chainedHashing`,
  `lpInitSteps U n_max = O(n_max + log U)` steps for `linearProbing`,
  `upInitSteps n_max = O(n_max ^ (1 / 2))` steps for `uniformProbing`, and
  `cuckooInitSteps n_max U = O(n_max + log U)` steps for `cuckooHashing`. Every state in
  `μ_init.support` satisfies `WordBounded w`, stores `base` in `baseReg` and `base + sp` in the
  frontier register, and satisfies `UnchangedOutside base sp mem₀`.
- **Linear probing proof adaptation and calling convention:** `linearProbing` uses the library's
  simplified proof adaptation at load factor `α ≤ 1 / 8` (`lpTableSize n_max ≥ 8 * n_max`) with
  `5`-wise independent polynomial hashing over binary trinomial fields, and preserves non-argument
  registers across calls (`clearScratch = false`), whereas `chainedHashing`, `uniformProbing`, and
  `cuckooHashing` zero scratch registers except `baseReg` (`clearScratch = true`).
- **Oblivious adversary:** In every headline theorem, the initial coupled distribution
  `∃ (Seed : Type) (μ_init : PMF (CoupledState Seed r))` produced by `p_init` is quantified
  **before** `∀ ops : List (DictOp U)`, and `ops` is fixed before the random choices of `p_init`
  and `p_op`.

A reader only needs to inspect the definitions and theorem statements in this file to verify that
the formalization proves the intended mathematical claims; Lean verifies the proofs through
`ComplexityAbstracts.HashTablesBridge`, and `#check_abstract` audits the dependency boundary.
-/

namespace ComplexityAbstracts.HashTablesAbstract

open scoped ENNReal

/-! ## Randomized Word-RAM Model -/

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

/-- Instructions over `r` registers: ten deterministic instructions and bounded random sampling
`rand`. -/
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
  | rand (d i : Fin r)

/-- A program over `r` registers is a list of instructions indexed from `0`. -/
abbrev Program (r : ℕ) := List (Instr r)

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

/-- Machine state: instruction index `pc`, registers `reg`, and memory `mem`. -/
structure State (r : ℕ) where
  pc : ℕ
  reg : Fin r → ℕ
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

/-- Expected running time in `ENNReal`, as the sum over `t` of the probability of still running. -/
noncomputable def expectedTime {r : ℕ} (w : ℕ) (p : Program r)
    (s : State r) : ℝ≥0∞ :=
  ∑' t : ℕ,
    (evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = .running u}

/-! ## Bounded-Capacity Dictionary Specification -/

/-- Abstract dictionary state over key universe `Fin U` with `ℕ`-valued entries. -/
abbrev DictState (U : ℕ) : Type :=
  Fin U → Option ℕ

/-- Initial empty dictionary mapping every key in `Fin U` to `none`. -/
def emptyDict (U : ℕ) : DictState U :=
  fun _ => none

/-- Finite set of keys currently present in dictionary `s`. -/
def dictDom {U : ℕ} (s : DictState U) : Finset (Fin U) :=
  Finset.univ.filter fun u => (s u).isSome

/-- Operations on a dictionary over key universe `Fin U`:
- `get u`: look up key `u : Fin U`;
- `insert u v`: insert or overwrite key `u : Fin U` with value `v : ℕ`. -/
inductive DictOp (U : ℕ) : Type where
  | get (u : Fin U) : DictOp U
  | insert (u : Fin U) (v : ℕ) : DictOp U

/-- Apply one dictionary operation `o : DictOp U` to abstract state `s : DictState U`:
- `get u` leaves `s` unchanged;
- `insert u v` updates `s` at `u` to `some v`. -/
def stepDict {U : ℕ} (s : DictState U) : DictOp U → DictState U
  | .get _ => s
  | .insert u v => Function.update s u (some v)

/-- Admissibility of a single dictionary operation `o : DictOp U` on state `s` under value bound `V`
and capacity `n_max`:
- `get u` is always admissible;
- `insert u v` requires `v < V` and either `(dictDom s).card < n_max` (room for a new key) or
  `(s u).isSome` (overwriting an existing key). -/
def validDictOp {U : ℕ} (V n_max : ℕ) (s : DictState U) : DictOp U → Prop
  | .get _ => True
  | .insert u v => ((dictDom s).card < n_max ∨ (s u).isSome) ∧ v < V

/-- Admissibility of an oblivious operation sequence `ops : List (DictOp U)` starting from state `s`
under value bound `V` and capacity `n_max`. -/
def ValidDictHistory {U : ℕ} (V n_max : ℕ) : DictState U → List (DictOp U) → Prop
  | _, [] => True
  | s, o :: os => validDictOp V n_max s o ∧ ValidDictHistory V n_max (stepDict s o) os

/-! ## Distributional Word-RAM Execution and Calling Convention -/

/-- All registers and memory cells carry `w`-bit machine words (`< 2 ^ w`). -/
def WordBounded {r : ℕ} (w : ℕ) (reg : Fin r → ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ i, reg i < 2 ^ w) ∧ ∀ a, mem a < 2 ^ w

/-- Memory cells outside the allocated region `[base, base + sp)` are unchanged between `mem` and
`mem'`. -/
def UnchangedOutside (base sp : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  ∀ a, (a < base ∨ base + sp ≤ a) → mem' a = mem a

/-- No reachable configuration of program `p` from state `s` at word width `w` faults at any time
horizon `T`. -/
def RandFaultFree {r : ℕ} (w : ℕ) (p : Program r) (s : State r) : Prop :=
  ∀ T : ℕ, evalRand w p T s .faulted = 0

/-- Register bank and memory snapshot of an `r`-register Word-RAM. -/
structure RegMem (r : ℕ) where
  reg : Fin r → ℕ
  mem : ℕ → ℕ

/-- Machine state coupled with a latent random seed `seed : Seed`. -/
structure CoupledState (Seed : Type) (r : ℕ) where
  seed : Seed
  reg : Fin r → ℕ
  mem : ℕ → ℕ

/-- Project a coupled state to its register bank and memory snapshot. -/
def CoupledState.toRegMem {Seed : Type} {r : ℕ} (p : CoupledState Seed r) : RegMem r :=
  ⟨p.reg, p.mem⟩

/-- Executing compiled Word-RAM program `p` from `(0, reg, mem)` at word width `w` with output
register `outReg` is fault-free across all horizons, has expected instruction count at most `T + 1`
(accounting for the final `halt` instruction), and reaches each terminal state `q : RegMem r` with
limiting halting probability at least `μ q`. -/
def ExecProgramDist {r : ℕ} (w : ℕ) (p : Program r) (outReg : Fin r)
    (reg : Fin r → ℕ) (mem : ℕ → ℕ) (μ : PMF (RegMem r)) (T : ℝ≥0∞) : Prop :=
  let s : State r := ⟨0, reg, mem⟩
  RandFaultFree w p s ∧
  expectedTime w p s ≤ T + 1 ∧
  ∀ q : RegMem r,
    μ q ≤ ⨆ T_hor : ℕ, evalRand w p T_hor s (.halted (q.reg outReg) q.reg q.mem)

/-- Calling-convention register assignment for a dictionary operation `o : DictOp U` on an
`r`-register Word-RAM with scratch-clearing flag `clearScratch`, base-address register `baseReg`,
operation-tag register `tagReg`, key register `keyReg`, and value register `valReg`:
- `tagReg` receives `0` for `get u` and `1` for `insert u v`;
- `keyReg` receives `u.val`;
- `valReg` receives `v` for `insert u v` (and `0` for `get u`);
- every other register `i` is zeroed when `clearScratch && decide (i ≠ baseReg)` and preserved
  (`reg i`) otherwise. -/
def prepareDictRegs {r U : ℕ} (clearScratch : Bool) (baseReg tagReg keyReg valReg : Fin r)
    (o : DictOp U) (reg : Fin r → ℕ) (i : Fin r) : ℕ :=
  if i = tagReg then
    match o with
    | .get _ => 0
    | .insert _ _ => 1
  else if i = keyReg then
    match o with
    | .get u => u.val
    | .insert u _ => u.val
  else if i = valReg then
    match o with
    | .get _ => 0
    | .insert _ v => v
  else if clearScratch && decide (i ≠ baseReg) then
    0
  else
    reg i

/-- Decode a Word-RAM output register value `w_out : ℕ` as a dictionary lookup result `Option ℕ`:
`0` encodes `none` (key absent) and `v + 1` encodes `some v` (key present with value `v`). -/
def decodeLookup (w_out : ℕ) : Option ℕ :=
  if w_out = 0 then none else some (w_out - 1)

/-- Output correctness of a post-operation register bank `reg` for operation `o : DictOp U`
against pre-operation dictionary state `s : DictState U` with output register `outReg`:
- for `get u`, `decodeLookup (reg outReg) = s u`;
- for `insert u v`, the unit return needs no output-register check (`True`). -/
def OpOutputCorrect {r U : ℕ} (outReg : Fin r) (s : DictState U)
    (o : DictOp U) (reg : Fin r → ℕ) : Prop :=
  match o with
  | .get u => decodeLookup (reg outReg) = s u
  | .insert _ _ => True

/-- Sequential multi-operation execution of a history `ops : List (DictOp U)` by the Word-RAM
operation program `p_op : Program r` at word width `w`, with calling-convention parameters
`(clearScratch, baseReg, tagReg, keyReg, valReg, outReg)` and allocated memory region
`[base, base + sp)`:
- `nil`: the empty operation history leaves the coupled state distribution `μ` unchanged with `0`
  expected operation steps;
- `cons`: from every supported coupled state `p ∈ μ.support`, running `p_op` after loading the
  encoded arguments of `o` via `prepareDictRegs clearScratch baseReg tagReg keyReg valReg o`
  executes with distribution `(μ_step p).map CoupledState.toRegMem` and expected step budget
  `T_step p` (`ExecProgramDist`). Every resulting state `q ∈ (μ_step p).support` has `w`-bit
  bounded registers and memory, satisfies `OpOutputCorrect outReg s o q.reg` (matching the
  dictionary specification), and leaves memory outside `[base, base + sp)` unchanged. The
  remaining operations `ops` execute from `μ.bind μ_step` to `μ_final` with expected step budget
  `T_rest`, yielding total expected operation cost `(∑' p, μ p * T_step p) + T_rest`. -/
inductive ExecDictOps {Seed : Type} {r U : ℕ}
    (w : ℕ) (p_op : Program r) (clearScratch : Bool)
    (baseReg tagReg keyReg valReg outReg : Fin r) (base sp : ℕ) :
    DictState U → List (DictOp U) →
    PMF (CoupledState Seed r) → PMF (CoupledState Seed r) → ℝ≥0∞ → Prop where
  | nil (s : DictState U) (μ : PMF (CoupledState Seed r)) :
      ExecDictOps w p_op clearScratch baseReg tagReg keyReg valReg outReg base sp s [] μ μ 0
  | cons {s : DictState U} {o : DictOp U} {ops : List (DictOp U)}
      {μ μ_final : PMF (CoupledState Seed r)} {T_rest : ℝ≥0∞}
      (T_step : CoupledState Seed r → ℝ≥0∞)
      (μ_step : CoupledState Seed r → PMF (CoupledState Seed r))
      (hstep : ∀ p ∈ μ.support,
        ExecProgramDist w p_op outReg
          (prepareDictRegs clearScratch baseReg tagReg keyReg valReg o p.reg) p.mem
          ((μ_step p).map CoupledState.toRegMem) (T_step p) ∧
        ∀ q ∈ (μ_step p).support,
          WordBounded w q.reg q.mem ∧
          OpOutputCorrect outReg s o q.reg ∧
          UnchangedOutside base sp p.mem q.mem)
      (hrest : ExecDictOps w p_op clearScratch baseReg tagReg keyReg valReg outReg base sp
        (stepDict s o) ops (μ.bind μ_step) μ_final T_rest) :
      ExecDictOps w p_op clearScratch baseReg tagReg keyReg valReg outReg base sp
        s (o :: ops) μ μ_final ((∑' p, μ p * T_step p) + T_rest)

/-! ## Table 1: Chained Hashing with Multiply-Shift (`ChainedHash.lean`) -/

/-- Bucket bit-width `⌈log₂(max n_max 2)⌉` for chained hashing. -/
def chainedBucketBits (n_max : ℕ) : ℕ :=
  Nat.clog 2 (max n_max 2)

/-- Number of buckets `2 ^ chainedBucketBits n_max` for chained hashing. -/
def chainedNumBuckets (n_max : ℕ) : ℕ :=
  2 ^ chainedBucketBits n_max

/-- Multiply-shift bit-width `max (chainedBucketBits n_max) ⌈log₂(max U 2)⌉`. -/
def chainedHashBits (U n_max : ℕ) : ℕ :=
  max (chainedBucketBits n_max) (Nat.clog 2 (max U 2))

/-- Memory footprint `4 + chainedNumBuckets n_max + 3 * n_max` (in machine words) of chained
hashing: `4`-word header, `chainedNumBuckets n_max` bucket heads, and `3 * n_max` node words
(`key`, `val`, `next`). -/
def chainedSpace (n_max : ℕ) : ℕ :=
  4 + chainedNumBuckets n_max + 3 * n_max

/-- Across all capacities `n_max : ℕ`, chained hashing uses at most `8 * (n_max + 1)` words of
memory. -/
theorem chainedSpace_le (n_max : ℕ) :
    chainedSpace n_max ≤ 8 * (n_max + 1) :=
  ComplexityAbstracts.HashTablesBridge.chainedSpace_le n_max

/-- **Chained Hashing with Multiply-Shift** (`ChainedHash.seq_expected_amortized`):
For every key universe `U` and capacity `n_max`, there exist 22-register Word-RAM programs `p_init`
and `p_op` (depending on `(U, n_max)` and independent of `V`, `w`, and `base`) such that for every
value bound `V`, word width `w`, and base address `base` satisfying
`2 * chainedHashBits U n_max ≤ w`, `base + chainedSpace n_max < 2 ^ w`, and `V < 2 ^ w`, from any
word-bounded initial state `(reg₀, mem₀)` with `reg₀ 6 = base` and zeroed memory in
`[base, base + chainedSpace n_max)`, there exists an initial coupled distribution `μ_init` (chosen
before any operation sequence `ops`) such that:
- `p_init` initializes the table in `16` expected executed body instructions (`≤ 17` including
  `halt`), and every `p ∈ μ_init.support` satisfies `WordBounded w p.reg p.mem`,
  `p.reg 5 = base`, `p.reg 6 = base + chainedSpace n_max`, and
  `UnchangedOutside base (chainedSpace n_max) mem₀ p.mem`;
- for every oblivious operation history `ops : List (DictOp U)` valid for capacity `n_max` and
  value bound `V`, `p_op` executes `ops` sequentially with output register `10`, matching
  `stepDict` and `OpOutputCorrect` at every step;
- the total expected executed body instruction count satisfies
  `16 + T_ops ≤ 16 + 73 * ops.length` (`O(1)` initialization and `73 = O(1)` expected executed
  instructions per `get` or `insert`, excluding caller argument preparation and dispatch; no bound
  is stated on static code length).

References: `[CLRS2009]` (3rd ed., Sections 11.2 and 11.3.3, Theorem 11.3 and Corollary 11.4);
`[DietzfelbingerHagerupKatajainenPenttonen1997]` (Lemma 2.4). -/
theorem chainedHashing :
    ∀ (U n_max : ℕ),
      ∃ (p_init p_op : List (Instr 22)),
        ∀ (V w base : ℕ),
          2 * chainedHashBits U n_max ≤ w →
          base + chainedSpace n_max < 2 ^ w →
          V < 2 ^ w →
          ∀ (reg₀ : Fin 22 → ℕ) (mem₀ : ℕ → ℕ),
            WordBounded w reg₀ mem₀ →
            reg₀ ⟨6, by decide⟩ = base →
            (∀ a, base ≤ a → a < base + chainedSpace n_max → mem₀ a = 0) →
            ∃ (Seed : Type) (μ_init : PMF (CoupledState Seed 22)),
              ExecProgramDist w p_init ⟨10, by decide⟩ reg₀ mem₀
                (μ_init.map CoupledState.toRegMem) 16 ∧
              (∀ p ∈ μ_init.support,
                WordBounded w p.reg p.mem ∧
                p.reg ⟨5, by decide⟩ = base ∧
                p.reg ⟨6, by decide⟩ = base + chainedSpace n_max ∧
                UnchangedOutside base (chainedSpace n_max) mem₀ p.mem) ∧
              ∀ ops : List (DictOp U),
                ValidDictHistory V n_max (emptyDict U) ops →
                ∃ (μ_final : PMF (CoupledState Seed 22)) (T_ops : ℝ≥0∞),
                  ExecDictOps w p_op true
                    ⟨5, by decide⟩ ⟨7, by decide⟩ ⟨8, by decide⟩ ⟨9, by decide⟩ ⟨10, by decide⟩
                    base (chainedSpace n_max) (emptyDict U) ops
                    μ_init μ_final T_ops ∧
                  (16 : ℝ≥0∞) + T_ops ≤ ((16 + 73 * ops.length : ℕ) : ℝ≥0∞) :=
  ComplexityAbstracts.HashTablesBridge.chainedHashing
    ⟨AluOp, .add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr,
      @AluOp.rec, AluOp.eval,
      Instr, .const, .copy, .alu, .width, .load, .store, .jump,
      .branchEq, .branchLt, .halt, .rand, @Instr.rec,
      Comp, @Comp.pure, @Comp.sample, @Comp.bind, @Comp.eval,
      ComplexityAbstracts.HashFamiliesBridge.compCallsAtMost (@Comp.rec),
      State, .mk, Cfg, .running, .halted, .faulted, @stepRand, @runRand⟩
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [AluOp.eval, Comp.bind, Comp.eval,
        ComplexityAbstracts.HashFamiliesBridge.compCallsAtMost, stepRand, runRand])
    ⟨DictOp, @DictOp.get, @DictOp.insert, @DictOp.rec,
      @stepDict, @validDictOp, @ValidDictHistory,
      RegMem, @RegMem.mk, @RegMem.reg, @RegMem.mem,
      CoupledState, @CoupledState.mk, @CoupledState.seed, @CoupledState.reg, @CoupledState.mem,
      @prepareDictRegs, @OpOutputCorrect, @ExecDictOps⟩
    ⟨fun _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl,
      fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      @ExecDictOps.nil, @ExecDictOps.cons⟩

/-! ## Table 2: Linear Probing with `5`-Wise Independent Hashing (`LinearProbing.lean`) -/

/-- Four-Russians chunk bit-width `max 1 (⌊log₂(max n_max 2)⌋ / 3)` for table-accelerated binary
trinomial field multiplication. -/
def chunkBits (n_max : ℕ) : ℕ :=
  max 1 (Nat.log 2 (max n_max 2) / 3)

/-- Structural recursion helper computing the smallest `t : ℕ` with `2 * 3 ^ t ≥ B`. -/
def trinomialStepLoop (fuel : ℕ) : ℕ → ℕ :=
  Nat.rec (fun _ => 0)
    (fun _ ih B => if B ≤ 2 then 0 else ih ((B + 2) / 3) + 1)
    fuel

/-- Selected trinomial step parameter `t` such that `2 * 3 ^ t ≥ max ⌈log₂(max U 2)⌉ (max M 1)`. -/
def trinomialStep (U M : ℕ) : ℕ :=
  let B := max (Nat.clog 2 (max U 2)) (max M 1)
  trinomialStepLoop B B

/-- Degree `D = 2 * 3 ^ trinomialStep U M` of the binary trinomial field
`GF(2)[X] / (X ^ D + X ^ (D / 2) + 1)`. -/
def trinomialDeg (U M : ℕ) : ℕ :=
  2 * 3 ^ trinomialStep U M

/-- Number of `chunkBits n_max`-bit limbs `⌈trinomialDeg U M / chunkBits n_max⌉` in a field
element of `GF(2 ^ (trinomialDeg U M))`. -/
def limbCount (n_max U M : ℕ) : ℕ :=
  (trinomialDeg U M + chunkBits n_max - 1) / chunkBits n_max

/-- Memory footprint `8 + k + 2 ^ (2 * chunkBits n_max)` (in machine words) of the `k`-wise
independent polynomial hash family (`8`-word header, `k` coefficients, and the
`2 ^ (2 * chunkBits n_max)`-entry chunk-multiplication lookup table). -/
def kWiseSpace (n_max k : ℕ) : ℕ :=
  8 + k + 2 ^ (2 * chunkBits n_max)

/-- Deterministic lookup-table setup step count for `k`-wise polynomial hashing before seed
sampling. -/
def kWiseInitTableSteps (n_max U M : ℕ) : ℕ :=
  19 * 2 ^ (2 * chunkBits n_max) +
    4 * Nat.log 2 (max n_max 2) +
    5 * Nat.clog 2 (max U 2) +
    5 * trinomialStep U M + 69

/-- Deterministic instruction budget `((11 * L + 12) * L + 30) * k + 19` (where
`L = limbCount n_max U M`) for evaluating a degree-`(k - 1)` polynomial over
`GF(2 ^ (trinomialDeg U M))`. -/
def kWiseEvalSteps (n_max U M k : ℕ) : ℕ :=
  ((11 * limbCount n_max U M + 12) * limbCount n_max U M + 30) * k + 19

/-- Power-of-2 table bit-width `⌈log₂(max (8 * n_max) 8)⌉` for linear probing
(`M = 2 ^ m ≥ 8 * n_max` with load factor `α ≤ 1 / 8`). -/
def lpTableLog (n_max : ℕ) : ℕ :=
  Nat.clog 2 (max (8 * n_max) 8)

/-- Power-of-2 table size `2 ^ lpTableLog n_max` for linear probing. -/
def lpTableSize (n_max : ℕ) : ℕ :=
  2 ^ lpTableLog n_max

/-- Memory footprint `kWiseSpace n_max 5 + 3 * lpTableSize n_max` (in machine words) of linear
probing: the `5`-wise hash block plus three parallel arrays (`status`, `key`, `val`) of length
`lpTableSize n_max`. -/
def lpSpace (n_max : ℕ) : ℕ :=
  kWiseSpace n_max 5 + 3 * lpTableSize n_max

/-- Across all capacities `n_max : ℕ`, linear probing uses at most `209 * (n_max + 1)` words of
memory. -/
theorem linearProbingSpace_le (n_max : ℕ) :
    lpSpace n_max ≤ 209 * (n_max + 1) :=
  ComplexityAbstracts.HashTablesBridge.linearProbingSpace_le n_max

/-- Expected instruction count `3 + (kWiseInitTableSteps n_max U (lpTableLog n_max) + 38)` for
linear-probing initialization from zeroed memory. -/
def lpInitSteps (U n_max : ℕ) : ℕ :=
  3 + (kWiseInitTableSteps n_max U (lpTableLog n_max) + 38)

/-- Exact expected per-operation instruction charge
`kWiseEvalSteps n_max U (lpTableLog n_max) 5 + 12 * 288 + 27` for linear probing. -/
def lpOpCharge (U n_max : ℕ) : ℕ :=
  kWiseEvalSteps n_max U (lpTableLog n_max) 5 + 12 * 288 + 27

/-- Uniform `O(1)` per-operation expected instruction bound `559652` (`556169` for `5`-wise
polynomial evaluation with `L ≤ 100` limbs plus `12 * 288 + 27 = 3483` for probing) for linear
probing under a polynomial key universe `U ≤ max n_max 4 ^ 4`. -/
def lpOpChargeBound : ℕ :=
  559652

/-- Whenever `U ≤ max n_max 4 ^ 4`, the per-operation expected instruction charge
`lpOpCharge U n_max` of linear probing is at most `lpOpChargeBound = 559652`, independently of
`n_max` and `U`. -/
theorem linearProbingCharge_le {U n_max : ℕ} (hU : U ≤ max n_max 4 ^ 4) :
    lpOpCharge U n_max ≤ lpOpChargeBound :=
  ComplexityAbstracts.HashTablesBridge.linearProbingCharge_le hU

/-- **Linear Probing with `5`-Wise Independent Hashing** (`LinearProbing.seq_expected_amortized`,
specialized to `c_exp = 4`):
For every key universe `U` and capacity `n_max`, there exist 24-register Word-RAM programs `p_init`
and `p_op` (depending on `(U, n_max)` and independent of `V`, `w`, and `base`) such that for every
value bound `V`, word width `w`, and base address `base` satisfying `U ≤ max n_max 4 ^ 4`,
`2 * trinomialDeg U (lpTableLog n_max) ≤ w`, `base + lpSpace n_max < 2 ^ w`, and `V < 2 ^ w`, from
any word-bounded initial state `(reg₀, mem₀)` with `reg₀ 18 = base` and zeroed memory in
`[base, base + lpSpace n_max)`, there exists an initial coupled distribution `μ_init` (chosen before
any operation sequence `ops`) such that:
- `p_init` initializes the table in `lpInitSteps U n_max` expected executed body instructions, and
  every `p ∈ μ_init.support` satisfies `WordBounded w p.reg p.mem`, `p.reg 0 = base`,
  `p.reg 18 = base + lpSpace n_max`, and `UnchangedOutside base (lpSpace n_max) mem₀ p.mem`;
- for every oblivious operation history `ops : List (DictOp U)` valid for capacity `n_max` and
  value bound `V`, `p_op` executes `ops` sequentially with output register `2` (`clearScratch =
  false`, preserving non-argument registers), matching `stepDict` and `OpOutputCorrect` at every
  step;
- the total expected executed body instruction count satisfies both
  `lpInitSteps U n_max + T_ops ≤ lpInitSteps U n_max + ops.length * lpOpCharge U n_max` and the
  uniform `O(1)` per-operation bound
  `lpInitSteps U n_max + T_ops ≤ lpInitSteps U n_max + ops.length * 559652`
  (independent of `n_max` and `U`, excluding caller argument preparation and dispatch; no bound is
  stated on static code length).

References: `[PaghPaghRuzic2009]` (*SIAM J. Comput.* 39(3):1107–1120, 2009, Section 2.3 Lemma 2.1
pp. 1110–1111 and Section 4 Lemma 4.1, Theorem 4.3, Theorem 4.5 pp. 1114–1118); `[CLRS2009]`
(3rd ed., Section 11.4); `[Vadhan2012]` (Section 3.5.5); `[CarterWegman1979]`;
`[WegmanCarter1981]`; `[LidlNiederreiter1997]`. -/
theorem linearProbing :
    ∀ (U n_max : ℕ),
      ∃ (p_init p_op : List (Instr 24)),
        ∀ (V w base : ℕ),
          U ≤ max n_max 4 ^ 4 →
          2 * trinomialDeg U (lpTableLog n_max) ≤ w →
          base + lpSpace n_max < 2 ^ w →
          V < 2 ^ w →
          ∀ (reg₀ : Fin 24 → ℕ) (mem₀ : ℕ → ℕ),
            WordBounded w reg₀ mem₀ →
            reg₀ ⟨18, by decide⟩ = base →
            (∀ a, base ≤ a → a < base + lpSpace n_max → mem₀ a = 0) →
            ∃ (Seed : Type) (μ_init : PMF (CoupledState Seed 24)),
              ExecProgramDist w p_init ⟨2, by decide⟩ reg₀ mem₀
                (μ_init.map CoupledState.toRegMem) (lpInitSteps U n_max) ∧
              (∀ p ∈ μ_init.support,
                WordBounded w p.reg p.mem ∧
                p.reg ⟨0, by decide⟩ = base ∧
                p.reg ⟨18, by decide⟩ = base + lpSpace n_max ∧
                UnchangedOutside base (lpSpace n_max) mem₀ p.mem) ∧
              ∀ ops : List (DictOp U),
                ValidDictHistory V n_max (emptyDict U) ops →
                ∃ (μ_final : PMF (CoupledState Seed 24)) (T_ops : ℝ≥0∞),
                  ExecDictOps w p_op false
                    ⟨0, by decide⟩ ⟨22, by decide⟩ ⟨1, by decide⟩ ⟨23, by decide⟩ ⟨2, by decide⟩
                    base (lpSpace n_max) (emptyDict U) ops
                    μ_init μ_final T_ops ∧
                  (lpInitSteps U n_max : ℝ≥0∞) + T_ops ≤
                    ((lpInitSteps U n_max + ops.length * lpOpCharge U n_max : ℕ) : ℝ≥0∞) ∧
                  (lpInitSteps U n_max : ℝ≥0∞) + T_ops ≤
                    ((lpInitSteps U n_max + ops.length * lpOpChargeBound : ℕ) : ℝ≥0∞) :=
  ComplexityAbstracts.HashTablesBridge.linearProbing
    ⟨AluOp, .add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr,
      @AluOp.rec, AluOp.eval,
      Instr, .const, .copy, .alu, .width, .load, .store, .jump,
      .branchEq, .branchLt, .halt, .rand, @Instr.rec,
      Comp, @Comp.pure, @Comp.sample, @Comp.bind, @Comp.eval,
      ComplexityAbstracts.HashFamiliesBridge.compCallsAtMost (@Comp.rec),
      State, .mk, Cfg, .running, .halted, .faulted, @stepRand, @runRand⟩
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [AluOp.eval, Comp.bind, Comp.eval,
        ComplexityAbstracts.HashFamiliesBridge.compCallsAtMost, stepRand, runRand])
    ⟨DictOp, @DictOp.get, @DictOp.insert, @DictOp.rec,
      @stepDict, @validDictOp, @ValidDictHistory,
      RegMem, @RegMem.mk, @RegMem.reg, @RegMem.mem,
      CoupledState, @CoupledState.mk, @CoupledState.seed, @CoupledState.reg, @CoupledState.mem,
      @prepareDictRegs, @OpOutputCorrect, @ExecDictOps⟩
    ⟨fun _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl,
      fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      @ExecDictOps.nil, @ExecDictOps.cons⟩

/-! ## Table 3: Uniform Probing via Odd-Stride Double Hashing (`UniformProbing.lean`) -/

/-- Double-tabulation threshold `2 ^ 320000` (`doubleTabThreshold 4`) at `c_exp = 4`, corresponding
to character bit-width `charBits n_max ≥ 4 * (8 + 48 * 4) ^ 2 = 160000`. Note that constants
derived from `regimeThreshold` in uniform probing and cuckoo hashing are astronomically large. -/
def regimeThreshold : ℕ :=
  2 ^ 320000

/-- Double-tabulation character bit-width `⌊(1 + ⌈log₂(max n_max 4)⌉) / 2⌋`. -/
def charBits (n_max : ℕ) : ℕ :=
  (1 + Nat.clog 2 (max n_max 4)) / 2

/-- Power-of-2 table bit-width `⌈log₂(32 * max n_max 4)⌉` (`≥ 7`). -/
def tableBits32 (n_max : ℕ) : ℕ :=
  Nat.clog 2 (32 * max n_max 4)

/-- Power-of-2 table size `2 ^ tableBits32 n_max` (`≥ 32 * max n_max 4`). -/
def tableSize32 (n_max : ℕ) : ℕ :=
  2 ^ tableBits32 n_max

/-- Memory footprint `(c + 1) * d * 2 ^ b` (in machine words) of a single Double Tabulation
instance with `c` characters, intermediate tuple length `d`, and `b`-bit characters. -/
def doubleTabSpace (c d b : ℕ) : ℕ :=
  (c + 1) * d * 2 ^ b

/-- Exact instruction count `5 * doubleTabSpace c d b + 13` for resampling a Double Tabulation
instance. -/
def doubleTabResampleSteps (c d b : ℕ) : ℕ :=
  5 * doubleTabSpace c d b + 13

/-- Exact deterministic instruction count `(12 * c + 11) * d + 10` for evaluating a Double
Tabulation instance. -/
def doubleTabEvalSteps (c d : ℕ) : ℕ :=
  (12 * c + 11) * d + 10

/-- Memory footprint `doubleTabSpace 8 64 (charBits n_max) = 576 * 2 ^ charBits n_max` of one
Double Tabulation table at `c_exp = 4` (`c = 8`, `d = 64`). -/
def upSingleTabSpace (n_max : ℕ) : ℕ :=
  doubleTabSpace 8 64 (charBits n_max)

/-- Total memory footprint `2 * upSingleTabSpace n_max + 3 * tableSize32 n_max` (in machine words)
of uniform probing at `c_exp = 4`: primary and odd-stride Double Tabulation tables plus three
parallel slot arrays (`used`, `key`, `val`) of length `tableSize32 n_max`. -/
def upSpace (n_max : ℕ) : ℕ :=
  2 * upSingleTabSpace n_max + 3 * tableSize32 n_max

/-- Linear-space factor `32 * (8 + 1) * 64 + 768 = 19200` for uniform probing at `c_exp = 4`. -/
def upSpaceFactor : ℕ :=
  32 * (8 + 1) * 64 + 768

/-- Across all capacities `n_max : ℕ`, uniform probing uses at most
`upSpaceFactor * (n_max + 1) = 19200 * (n_max + 1)` words of memory. -/
theorem uniformProbingSpace_le (n_max : ℕ) :
    upSpace n_max ≤ upSpaceFactor * (n_max + 1) :=
  ComplexityAbstracts.HashTablesBridge.uniformProbingSpace_le n_max

/-- Expected instruction count `3 + (2 * doubleTabResampleSteps 8 64 (charBits n_max) + 4)` for
uniform-probing initialization from zeroed memory at `c_exp = 4`. -/
def upInitSteps (n_max : ℕ) : ℕ :=
  3 + (2 * doubleTabResampleSteps 8 64 (charBits n_max) + 4)

/-- Deterministic instruction count `2 * doubleTabEvalSteps 8 64 + 15 = 13731` for evaluating the
primary and odd-stride Double Tabulation hashes at `c_exp = 4`. -/
def upHashEvalSteps : ℕ :=
  2 * doubleTabEvalSteps 8 64 + 15

/-- Uniform `O(1)` expected per-operation instruction charge
`13 * regimeThreshold + upHashEvalSteps + 8 = 13 * 2 ^ 320000 + 13739` for uniform probing at
`c_exp = 4` (independent of `n_max` and `U`; astronomically large because the unconditional
all-`n_max` probe bound uses `regimeThreshold = 2 ^ 320000` below the double-tabulation
threshold). -/
def upOpCharge : ℕ :=
  13 * regimeThreshold + upHashEvalSteps + 8

/-- **Uniform Probing via Odd-Stride Double Hashing** (`UniformProbing.seq_expected_amortized`,
specialized to `c_exp = 4`):
For every capacity `n_max`, there exist 16-register Word-RAM programs `p_init` and `p_op`
(depending only on `n_max` at fixed `c_exp = 4` and independent of `U`, `V`, `w`, and `base`) such
that for every key universe `U`, value bound `V`, word width `w`, and base address `base` satisfying
`U ≤ max n_max 4 ^ 4`, `base + upSpace n_max < 2 ^ w`, `∀ u : Fin U, u.val < 2 ^ w`, and
`V < 2 ^ w`, from any word-bounded initial state `(reg₀, mem₀)` with `reg₀ 14 = base` and zeroed
memory in `[base, base + upSpace n_max)`, there exists an initial coupled distribution `μ_init`
(chosen before any operation sequence `ops`) such that:
- `p_init` initializes the table in `upInitSteps n_max` expected executed body instructions, and
  every `p ∈ μ_init.support` satisfies `WordBounded w p.reg p.mem`, `p.reg 0 = base`,
  `p.reg 14 = base + upSpace n_max`, and `UnchangedOutside base (upSpace n_max) mem₀ p.mem`;
- for every oblivious operation history `ops : List (DictOp U)` valid for capacity `n_max` and
  value bound `V`, `p_op` executes `ops` sequentially with output register `12`, matching
  `stepDict` and `OpOutputCorrect` at every step;
- the total expected executed body instruction count satisfies
  `upInitSteps n_max + T_ops ≤ upInitSteps n_max + ops.length * upOpCharge`
  (`upOpCharge = 13 * 2 ^ 320000 + 13739 = O(1)` expected executed instructions per `get` or
  `insert`, independent of `n_max` and `U`, excluding caller argument preparation and dispatch; no
  bound is stated on static code length).

References: `[CLRS2009]` (3rd ed., Section 11.4, pp. 269–277); `[SchmidtSiegel1990]` (STOC 1990,
pp. 224–234; NYU Courant Technical Report `TR1995-687`, May 1995, pp. 1–2, 4–7, 37–39);
`[Thorup2013]` (FOCS 2013, pp. 90–99; `arXiv:1311.3121v2`, Theorem 1(a) p. 4, Lemma 2 p. 5, and
Section 2 Eqs. (6)–(7) p. 11). -/
theorem uniformProbing :
    ∀ (n_max : ℕ),
      ∃ (p_init p_op : List (Instr 16)),
        ∀ (U V w base : ℕ),
          U ≤ max n_max 4 ^ 4 →
          base + upSpace n_max < 2 ^ w →
          (∀ u : Fin U, u.val < 2 ^ w) →
          V < 2 ^ w →
          ∀ (reg₀ : Fin 16 → ℕ) (mem₀ : ℕ → ℕ),
            WordBounded w reg₀ mem₀ →
            reg₀ ⟨14, by decide⟩ = base →
            (∀ a, base ≤ a → a < base + upSpace n_max → mem₀ a = 0) →
            ∃ (Seed : Type) (μ_init : PMF (CoupledState Seed 16)),
              ExecProgramDist w p_init ⟨12, by decide⟩ reg₀ mem₀
                (μ_init.map CoupledState.toRegMem) (upInitSteps n_max) ∧
              (∀ p ∈ μ_init.support,
                WordBounded w p.reg p.mem ∧
                p.reg ⟨0, by decide⟩ = base ∧
                p.reg ⟨14, by decide⟩ = base + upSpace n_max ∧
                UnchangedOutside base (upSpace n_max) mem₀ p.mem) ∧
              ∀ ops : List (DictOp U),
                ValidDictHistory V n_max (emptyDict U) ops →
                ∃ (μ_final : PMF (CoupledState Seed 16)) (T_ops : ℝ≥0∞),
                  ExecDictOps w p_op true
                    ⟨0, by decide⟩ ⟨12, by decide⟩ ⟨13, by decide⟩ ⟨14, by decide⟩ ⟨12, by decide⟩
                    base (upSpace n_max) (emptyDict U) ops
                    μ_init μ_final T_ops ∧
                  (upInitSteps n_max : ℝ≥0∞) + T_ops ≤
                    ((upInitSteps n_max + ops.length * upOpCharge : ℕ) : ℝ≥0∞) :=
  ComplexityAbstracts.HashTablesBridge.uniformProbing
    ⟨AluOp, .add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr,
      @AluOp.rec, AluOp.eval,
      Instr, .const, .copy, .alu, .width, .load, .store, .jump,
      .branchEq, .branchLt, .halt, .rand, @Instr.rec,
      Comp, @Comp.pure, @Comp.sample, @Comp.bind, @Comp.eval,
      ComplexityAbstracts.HashFamiliesBridge.compCallsAtMost (@Comp.rec),
      State, .mk, Cfg, .running, .halted, .faulted, @stepRand, @runRand⟩
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [AluOp.eval, Comp.bind, Comp.eval,
        ComplexityAbstracts.HashFamiliesBridge.compCallsAtMost, stepRand, runRand])
    ⟨DictOp, @DictOp.get, @DictOp.insert, @DictOp.rec,
      @stepDict, @validDictOp, @ValidDictHistory,
      RegMem, @RegMem.mk, @RegMem.reg, @RegMem.mem,
      CoupledState, @CoupledState.mk, @CoupledState.seed, @CoupledState.reg, @CoupledState.mem,
      @prepareDictRegs, @OpOutputCorrect, @ExecDictOps⟩
    ⟨fun _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl,
      fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      @ExecDictOps.nil, @ExecDictOps.cons⟩
    regimeThreshold upHashEvalSteps upOpCharge rfl rfl rfl

/-! ## Table 4: Pagh–Rodler Cuckoo Hashing (`CuckooHashing.lean`) -/

/-- Maximum number of two-table cuckoo displacement rounds `6 * (⌈log₂(max n_max 2)⌉ + 2)` before
triggering a full-table rehash. -/
def cuckooMaxEvictions (n_max : ℕ) : ℕ :=
  6 * (Nat.clog 2 (max n_max 2) + 2)

/-- Polynomial-hash independence degree `2 * cuckooMaxEvictions n_max + 2` required by the
two-table cuckoo displacement analysis below `regimeThreshold`. -/
def cuckooK (n_max : ℕ) : ℕ :=
  2 * cuckooMaxEvictions n_max + 2

/-- Uniform upper bound `24 * 160000 + 26 = 3840026` on `cuckooK n_max` across the small-`n_max`
regime `n_max < regimeThreshold` at `c_exp = 4`. -/
def cuckooKBound : ℕ :=
  24 * 160000 + 26

/-- Memory footprint (in machine words) of one regime-switched hash block (`h₁` or `h₂`) in cuckoo
hashing at `c_exp = 4`: `kWiseSpace n_max (cuckooK n_max)` below `regimeThreshold`, and
`doubleTabSpace 8 64 (charBits n_max)` at or above `regimeThreshold`. -/
def cuckooSingleHashSpace (n_max : ℕ) : ℕ :=
  if n_max < regimeThreshold then
    kWiseSpace n_max (cuckooK n_max)
  else
    doubleTabSpace 8 64 (charBits n_max)

/-- Memory footprint `2 * cuckooSingleHashSpace n_max` of the two-block cuckoo hash pair
`(h₁, h₂)` at `c_exp = 4`. -/
def cuckooHashPairSpace (n_max : ℕ) : ℕ :=
  2 * cuckooSingleHashSpace n_max

/-- Total memory footprint `20 + cuckooHashPairSpace n_max + 2 * tableSize32 n_max + 2 * n_max`
(in machine words) of cuckoo hashing at `c_exp = 4`: `20`-word header, two-block hash pair, two
cuckoo sub-tables `T₁` and `T₂` of size `tableSize32 n_max` each, and insertion-order key and value
arrays `insKeys` and `insVals` of length `n_max` each. -/
def cuckooSpace (n_max : ℕ) : ℕ :=
  20 + cuckooHashPairSpace n_max + 2 * tableSize32 n_max + 2 * n_max

/-- Linear-space factor `20 + 2 * (16 + cuckooKBound + 16 * (8 + 1) * 64) + 514 = 7699050` for
cuckoo hashing at `c_exp = 4` (dominated by `2 * cuckooKBound = 7680052` from the small-regime
independence bound `cuckooKBound = 3840026`). -/
def cuckooSpaceFactor : ℕ :=
  20 + 2 * (16 + cuckooKBound + 16 * (8 + 1) * 64) + 514

/-- Across all capacities `n_max : ℕ`, cuckoo hashing at `c_exp = 4` uses at most
`cuckooSpaceFactor * (n_max + 1) = 7699050 * (n_max + 1)` words of memory. -/
theorem cuckooSpace_le (n_max : ℕ) :
    cuckooSpace n_max ≤ cuckooSpaceFactor * (n_max + 1) :=
  ComplexityAbstracts.HashTablesBridge.cuckooSpace_le
    regimeThreshold charBits tableBits32 tableSize32 cuckooMaxEvictions cuckooK
    kWiseSpace doubleTabSpace cuckooKBound
    cuckooSingleHashSpace cuckooHashPairSpace cuckooSpace cuckooSpaceFactor
    rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) rfl
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl
    n_max

/-- Instruction count for resampling one regime-switched hash block (`h₁` or `h₂`) in cuckoo
hashing at `c_exp = 4`. -/
def cuckooResampleSingleSteps (n_max : ℕ) : ℕ :=
  if n_max < regimeThreshold then
    5 * cuckooK n_max + 10
  else
    doubleTabResampleSteps 8 64 (charBits n_max)

/-- Expected instruction count for initializing cuckoo hashing from zeroed memory at `c_exp = 4`
(`8` span-allocation steps plus header setup, hash-table lookup initialization, and initial seed
pair sampling). -/
def cuckooInitSteps (n_max U : ℕ) : ℕ :=
  8 + (6 + 35 +
    (kWiseInitTableSteps n_max U (tableBits32 n_max) + 6 * cuckooSingleHashSpace n_max + 8) +
    (2 * cuckooResampleSingleSteps n_max + 4) + 5)

/-- Uniform `O(1)` instruction bound `427126092003` for evaluating one regime-switched cuckoo hash
function (`h₁` or `h₂`) at `c_exp = 4` under `U ≤ max n_max 4 ^ 4` (with `L ≤ 100` limbs and
`cuckooK n_max ≤ cuckooKBound = 3840026`). -/
def cuckooEvalHashBound : ℕ :=
  max (((11 * 100 + 12) * 100 + 30) * cuckooKBound + 19) (doubleTabEvalSteps 8 64) + 4

/-- Worst-case deterministic instruction bound `2 * (cuckooEvalHashBound + 36) + 31 = 854252184109`
for the two-probe `get` subprogram at `c_exp = 4`. -/
def cuckooGetStepsBound : ℕ :=
  2 * (cuckooEvalHashBound + 36) + 31

/-- Worst-case deterministic instruction bound `cuckooGetStepsBound + 2 = 854252184111` for a
`get` operation via `p_op` at `c_exp = 4`. -/
def cuckooGetCharge : ℕ :=
  cuckooGetStepsBound + 2

/-- Worst-case deterministic instruction bound `2 * (cuckooEvalHashBound + 54) + 59 = 854252184173`
for a single two-table cuckoo displacement round at `c_exp = 4`. -/
def cuckooEvictIterBound : ℕ :=
  2 * (cuckooEvalHashBound + 54) + 59

/-- Base instruction bound `2 * (cuckooEvalHashBound + 35) + 78 = 854252184154` for `insert`
before displacement rounds at `c_exp = 4`. -/
def cuckooInsertBaseBound : ℕ :=
  2 * (cuckooEvalHashBound + 35) + 78

/-- Amortized seed-resampling factor `max (10 * cuckooKBound + 35) (80 * ((8 + 1) * 64) + 63) =
38400295` per unit of `max n_max 1 * max (cuckooMaxEvictions n_max) 1` during full-table rehashes
at `c_exp = 4`. -/
def cuckooResampleAtBaseFactor : ℕ :=
  max (10 * cuckooKBound + 35) (80 * ((8 + 1) * 64) + 63)

/-- Amortized full-table rehash instruction bound
`3 * cuckooEvictIterBound + 2 * cuckooResampleAtBaseFactor + 4290 + 1 = 2562833357400` per
insertion at `c_exp = 4`. -/
def cuckooRehashAmortizedBound : ℕ :=
  3 * cuckooEvictIterBound + 2 * cuckooResampleAtBaseFactor + 4290 + 1

/-- Uniform `O(1)` expected-amortized instruction charge
`2 * (cuckooInsertBaseBound + 3 + 3 * cuckooEvictIterBound + 4 * cuckooRehashAmortizedBound) =
27336684332552` for an `insert` operation at `c_exp = 4` (with `C_walk = 3`, `C_reh = 4`, and
conditional-uniform seed slack `2`). -/
def cuckooInsertCharge : ℕ :=
  2 * (cuckooInsertBaseBound + 3 + 3 * cuckooEvictIterBound + 4 * cuckooRehashAmortizedBound)

/-- Per-operation expected instruction charge for cuckoo hashing at `c_exp = 4`:
`cuckooGetCharge` (`854252184111`) for `get` and `cuckooInsertCharge` (`27336684332552`) for
`insert`, both independent of `n_max` and `U`. -/
def cuckooOpCharge {U : ℕ} : DictOp U → ℕ
  | .get _ => cuckooGetCharge
  | .insert _ _ => cuckooInsertCharge

/-- For every dictionary operation `o : DictOp U`, `cuckooOpCharge o ≤ cuckooInsertCharge`. -/
theorem cuckooOpCharge_le {U : ℕ} (o : DictOp U) :
    cuckooOpCharge o ≤ cuckooInsertCharge :=
  ComplexityAbstracts.HashTablesBridge.cuckooOpCharge_le
    DictOp @DictOp.get @DictOp.insert @DictOp.rec
    cuckooEvalHashBound cuckooGetStepsBound cuckooGetCharge
    cuckooEvictIterBound cuckooInsertBaseBound cuckooRehashAmortizedBound
    cuckooInsertCharge
    rfl rfl rfl rfl
    @cuckooOpCharge (fun _ => rfl) (fun _ _ => rfl) o

/-- **Pagh–Rodler Cuckoo Hashing** (`CuckooHashing.cuckoo_seq_expected_amortized`,
specialized to `c_exp = 4`):
For every capacity `n_max`, there exist 19-register Word-RAM programs `p_init` and `p_op`
(depending only on `n_max` at fixed `c_exp = 4` and independent of `U`, `V`, `w`, and `base`) such
that for every key universe `U`, value bound `V`, word width `w`, and base address `base` satisfying
`U ≤ max n_max 4 ^ 4`, `2 * trinomialDeg U (tableBits32 n_max) ≤ w`,
`base + cuckooSpace n_max < 2 ^ w`, `cuckooMaxEvictions n_max < 2 ^ w`, `max U 2 + 1 < 2 ^ w`, and
`V < 2 ^ w`, from any word-bounded initial state `(reg₀, mem₀)` with `reg₀ 1 = base`,
`reg₀ 3 = n_max`, `reg₀ 4 = U`, and zeroed memory in `[base, base + cuckooSpace n_max)`, there
exists an initial coupled distribution `μ_init` (chosen before any operation sequence `ops`) such
that:
- `p_init` initializes the table in `cuckooInitSteps n_max U` expected executed body instructions,
  and every `p ∈ μ_init.support` satisfies `WordBounded w p.reg p.mem`, `p.reg 0 = base`,
  `p.reg 1 = base + cuckooSpace n_max`, and `UnchangedOutside base (cuckooSpace n_max) mem₀ p.mem`;
- for every oblivious operation history `ops : List (DictOp U)` valid for capacity `n_max` and
  value bound `V`, `p_op` executes `ops` sequentially with output register `2`, matching
  `stepDict` and `OpOutputCorrect` at every step;
- the total expected executed body instruction count satisfies both the operation-sensitive bound
  `cuckooInitSteps n_max U + T_ops ≤ cuckooInitSteps n_max U + (ops.map cuckooOpCharge).sum`
  (`cuckooGetCharge = 854252184111` per `get`, `cuckooInsertCharge = 27336684332552` per `insert`)
  and the uniform per-operation bound
  `cuckooInitSteps n_max U + T_ops ≤ cuckooInitSteps n_max U + ops.length * cuckooInsertCharge`
  (independent of `n_max` and `U`, excluding caller argument preparation and dispatch; no bound is
  stated on static code length; constants reflect `cuckooKBound = 3840026` from the
  double-tabulation threshold `regimeThreshold = 2 ^ 320000`).

References: `[PaghRodler2004]` (8 Dec 2003 author manuscript / *J. Algorithms* 51(2):122–144, 2004,
Section 2.3 "Analysis", manuscript pp. 6–10: Lemma 1 p. 7, Eq. (3) p. 9, rehash analysis pp. 9–10);
`[Thorup2013]` (FOCS 2013, pp. 90–99; `arXiv:1311.3121v2`, Theorem 1(a) p. 4, Lemma 2 p. 5,
Section 2 Eqs. (6)–(7) p. 11, and Section 3 Theorem 7(a) and Lemmas 8–9 pp. 12–14);
`[CarterWegman1979]`; `[WegmanCarter1981]`. -/
theorem cuckooHashing :
    ∀ (n_max : ℕ),
      ∃ (p_init p_op : List (Instr 19)),
        ∀ (U V w base : ℕ),
          U ≤ max n_max 4 ^ 4 →
          2 * trinomialDeg U (tableBits32 n_max) ≤ w →
          base + cuckooSpace n_max < 2 ^ w →
          cuckooMaxEvictions n_max < 2 ^ w →
          max U 2 + 1 < 2 ^ w →
          V < 2 ^ w →
          ∀ (reg₀ : Fin 19 → ℕ) (mem₀ : ℕ → ℕ),
            WordBounded w reg₀ mem₀ →
            reg₀ ⟨1, by decide⟩ = base →
            reg₀ ⟨3, by decide⟩ = n_max →
            reg₀ ⟨4, by decide⟩ = U →
            (∀ a, base ≤ a → a < base + cuckooSpace n_max → mem₀ a = 0) →
            ∃ (Seed : Type) (μ_init : PMF (CoupledState Seed 19)),
              ExecProgramDist w p_init ⟨2, by decide⟩ reg₀ mem₀
                (μ_init.map CoupledState.toRegMem) (cuckooInitSteps n_max U) ∧
              (∀ p ∈ μ_init.support,
                WordBounded w p.reg p.mem ∧
                p.reg ⟨0, by decide⟩ = base ∧
                p.reg ⟨1, by decide⟩ = base + cuckooSpace n_max ∧
                UnchangedOutside base (cuckooSpace n_max) mem₀ p.mem) ∧
              ∀ ops : List (DictOp U),
                ValidDictHistory V n_max (emptyDict U) ops →
                ∃ (μ_final : PMF (CoupledState Seed 19)) (T_ops : ℝ≥0∞),
                  ExecDictOps w p_op true
                    ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩ ⟨4, by decide⟩ ⟨2, by decide⟩
                    base (cuckooSpace n_max) (emptyDict U) ops
                    μ_init μ_final T_ops ∧
                  (cuckooInitSteps n_max U : ℝ≥0∞) + T_ops ≤
                    ((cuckooInitSteps n_max U + (ops.map cuckooOpCharge).sum : ℕ) : ℝ≥0∞) ∧
                  (cuckooInitSteps n_max U : ℝ≥0∞) + T_ops ≤
                    ((cuckooInitSteps n_max U + ops.length * cuckooInsertCharge : ℕ) : ℝ≥0∞) :=
  ComplexityAbstracts.HashTablesBridge.cuckooHashing
    ⟨AluOp, .add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr,
      @AluOp.rec, AluOp.eval,
      Instr, .const, .copy, .alu, .width, .load, .store, .jump,
      .branchEq, .branchLt, .halt, .rand, @Instr.rec,
      Comp, @Comp.pure, @Comp.sample, @Comp.bind, @Comp.eval,
      ComplexityAbstracts.HashFamiliesBridge.compCallsAtMost (@Comp.rec),
      State, .mk, Cfg, .running, .halted, .faulted, @stepRand, @runRand⟩
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [AluOp.eval, Comp.bind, Comp.eval,
        ComplexityAbstracts.HashFamiliesBridge.compCallsAtMost, stepRand, runRand])
    ⟨DictOp, @DictOp.get, @DictOp.insert, @DictOp.rec,
      @stepDict, @validDictOp, @ValidDictHistory,
      RegMem, @RegMem.mk, @RegMem.reg, @RegMem.mem,
      CoupledState, @CoupledState.mk, @CoupledState.seed, @CoupledState.reg, @CoupledState.mem,
      @prepareDictRegs, @OpOutputCorrect, @ExecDictOps⟩
    ⟨fun _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl,
      fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      @ExecDictOps.nil, @ExecDictOps.cons⟩
    regimeThreshold
    charBits tableBits32 tableSize32
    kWiseSpace kWiseInitTableSteps
    doubleTabSpace doubleTabResampleSteps doubleTabEvalSteps
    cuckooMaxEvictions cuckooK cuckooKBound
    cuckooSingleHashSpace cuckooHashPairSpace cuckooSpace cuckooSpaceFactor
    cuckooResampleSingleSteps cuckooInitSteps
    cuckooEvalHashBound cuckooGetStepsBound cuckooGetCharge
    cuckooEvictIterBound cuckooInsertBaseBound cuckooResampleAtBaseFactor
    cuckooRehashAmortizedBound cuckooInsertCharge
    rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) rfl
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl
    (fun _ => rfl) (fun _ _ => rfl)
    rfl rfl rfl rfl rfl rfl rfl rfl
    @cuckooOpCharge (fun _ => rfl) (fun _ _ => rfl)

/-- info: abstract audit passed for `ComplexityAbstracts.HashTablesAbstract`: 416 root declarations -/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.HashTablesAbstract

end ComplexityAbstracts.HashTablesAbstract
