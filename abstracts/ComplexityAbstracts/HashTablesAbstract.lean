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

1. **Chained hashing with multiply-shift** (`ChainedHash.lean:1983` `seq_expected_amortized`,
   following `[CLRS2009]`, 3rd ed., Sections 11.2 and 11.3.3, Theorem 11.3 and Corollary 11.4,
   pp. 256–268, and `[DietzfelbingerHagerupKatajainenPenttonen1997]`, Lemma 2.4).
2. **Linear probing with `5`-wise independent polynomial hashing** (`LinearProbing.lean:2263`
   `seq_expected_amortized`, following `[PaghPaghRuzic2009]`, *SIAM J. Comput.* 39(3):1107–1120,
   2009, Section 2.3 Lemma 2.1 pp. 1110–1111 and Section 4 Lemma 4.1, Theorem 4.3, Theorem 4.5
   pp. 1114–1118; `[CLRS2009]`, 3rd ed., Section 11.4; `[Vadhan2012]`, Section 3.5.5;
   `[CarterWegman1979]`; `[WegmanCarter1981]`; `[LidlNiederreiter1997]`).
3. **Uniform probing via odd-stride double hashing** (`UniformProbing.lean:2362`
   `seq_expected_amortized`, following `[CLRS2009]`, 3rd ed., Section 11.4, pp. 269–277;
   `[SchmidtSiegel1990]`, STOC 1990, pp. 224–234, and NYU Courant TR1995-687, May 1995,
   pp. 1–2, 4–7, 37–39; `[Thorup2013]`, FOCS 2013, pp. 90–99, and `arXiv:1311.3121v2`,
   Theorem 1(a) and Lemma 2, pp. 4–5, 11–13).
4. **Cuckoo hashing** (`CuckooHashing.lean:6372` `cuckoo_seq_expected_amortized`, following
   `[PaghRodler2004]`, 8 Dec 2003 author manuscript / *J. Algorithms* 51(2):122–144, 2004,
   Section 2.3 "Analysis", manuscript pp. 6–10: Lemma 1 p. 7, Eq. (3) p. 9, rehash analysis
   pp. 9–10; `[Thorup2013]`, FOCS 2013, pp. 90–99, and `arXiv:1311.3121v2`, Sections 1.3 and 3,
   pp. 4–5, 11–13; `[CarterWegman1979]`; `[WegmanCarter1981]`).
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

/-- Every branch of `m` performs at most `R` random draws. -/
def Comp.CallsAtMost {α : Type} : Comp α → ℕ → Prop
  | .pure _, _ => True
  | .sample _ _, 0 => False
  | .sample _ next, R + 1 => ∀ k, (next k).CallsAtMost R

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
`r`-register Word-RAM with base-address register `baseReg`, operation-tag register `tagReg`,
key register `keyReg`, and value register `valReg`:
- `baseReg` is preserved (`reg baseReg`);
- `tagReg` receives `0` for `get u` and `1` for `insert u v`;
- `keyReg` receives `u.val`;
- `valReg` receives `v` for `insert u v` (and `0` for `get u`);
- all other registers are zeroed. -/
def prepareDictRegs {r U : ℕ} (baseReg tagReg keyReg valReg : Fin r)
    (o : DictOp U) (reg : Fin r → ℕ) (i : Fin r) : ℕ :=
  if decide (i ≠ baseReg) then
    match o with
    | .get u =>
        if i = tagReg then 0
        else if i = keyReg then u.val
        else 0
    | .insert u v =>
        if i = tagReg then 1
        else if i = keyReg then u.val
        else if i = valReg then v
        else 0
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
operation program `p_op : Program r` at word width `w`, with calling-convention registers
`(baseReg, tagReg, keyReg, valReg, outReg)` and allocated memory region `[base, base + sp)`:
- `nil`: the empty operation history leaves the coupled state distribution `μ` unchanged with `0`
  expected operation steps;
- `cons`: from every supported coupled state `p ∈ μ.support`, running `p_op` after loading the
  encoded arguments of `o` via `prepareDictRegs baseReg tagReg keyReg valReg o` executes with
  distribution `(μ_step p).map CoupledState.toRegMem` and expected step budget `T_step p`
  (`ExecProgramDist`), every resulting state `q ∈ (μ_step p).support` has `w`-bit bounded
  registers and memory, satisfies `OpOutputCorrect outReg s o q.reg` (matching the dictionary
  specification), and leaves memory outside `[base, base + sp)` unchanged, and the remaining
  operations `ops` execute from `μ.bind μ_step` to `μ_final` with expected step budget `T_rest`,
  yielding total expected operation cost `(∑' p, μ p * T_step p) + T_rest`. -/
inductive ExecDictOps {Seed : Type} {r U : ℕ}
    (w : ℕ) (p_op : Program r)
    (baseReg tagReg keyReg valReg outReg : Fin r) (base sp : ℕ) :
    DictState U → List (DictOp U) →
    PMF (CoupledState Seed r) → PMF (CoupledState Seed r) → ℝ≥0∞ → Prop where
  | nil (s : DictState U) (μ : PMF (CoupledState Seed r)) :
      ExecDictOps w p_op baseReg tagReg keyReg valReg outReg base sp s [] μ μ 0
  | cons {s : DictState U} {o : DictOp U} {ops : List (DictOp U)}
      {μ μ_final : PMF (CoupledState Seed r)} {T_rest : ℝ≥0∞}
      (T_step : CoupledState Seed r → ℝ≥0∞)
      (μ_step : CoupledState Seed r → PMF (CoupledState Seed r))
      (hstep : ∀ p ∈ μ.support,
        ExecProgramDist w p_op outReg
          (prepareDictRegs baseReg tagReg keyReg valReg o p.reg) p.mem
          ((μ_step p).map CoupledState.toRegMem) (T_step p) ∧
        ∀ q ∈ (μ_step p).support,
          WordBounded w q.reg q.mem ∧
          OpOutputCorrect outReg s o q.reg ∧
          UnchangedOutside base sp p.mem q.mem)
      (hrest : ExecDictOps w p_op baseReg tagReg keyReg valReg outReg base sp
        (stepDict s o) ops (μ.bind μ_step) μ_final T_rest) :
      ExecDictOps w p_op baseReg tagReg keyReg valReg outReg base sp
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

/-- **Chained Hashing with Multiply-Shift** (`ChainedHash.lean:1983` `seq_expected_amortized`):
For every key universe `U`, value bound `V < 2 ^ w`, capacity `n_max`, word width
`w ≥ 2 * chainedHashBits U n_max`, and base address `base` with `base + chainedSpace n_max < 2 ^ w`,
there exist 22-register Word-RAM programs `p_init` and `p_op` such that from any word-bounded
initial state `(reg₀, mem₀)` with `reg₀ 6 = base` and zeroed memory in
`[base, base + chainedSpace n_max)`, for every oblivious operation history `ops : List (DictOp U)`
valid for capacity `n_max` and value bound `V`:
- `p_init` initializes the table in `16` expected body instructions (`≤ 17` including `halt`);
- `p_op` executes `ops` sequentially with output register `10`, matching `stepDict` and
  `OpOutputCorrect` at every step;
- the total expected body instruction count satisfies `16 + T_ops ≤ 16 + 73 * ops.length`
  (`O(1)` initialization and `73 = O(1)` expected instructions per `get` or `insert`, excluding
  caller argument preparation and dispatch).

References: `[CLRS2009]` (3rd ed., Sections 11.2 and 11.3.3, Theorem 11.3 and Corollary 11.4,
pp. 256–268); `[DietzfelbingerHagerupKatajainenPenttonen1997]` (Lemma 2.4). -/
theorem chainedHashing :
    ∀ (U V n_max w base : ℕ),
      2 * chainedHashBits U n_max ≤ w →
      base + chainedSpace n_max < 2 ^ w →
      V < 2 ^ w →
      ∃ (p_init p_op : List (Instr 22)),
        ∀ (reg₀ : Fin 22 → ℕ) (mem₀ : ℕ → ℕ),
          WordBounded w reg₀ mem₀ →
          reg₀ ⟨6, by decide⟩ = base →
          (∀ a, base ≤ a → a < base + chainedSpace n_max → mem₀ a = 0) →
          ∀ ops : List (DictOp U),
            ValidDictHistory V n_max (emptyDict U) ops →
            ∃ (Seed : Type) (T_ops : ℝ≥0∞) (μ_init μ_final : PMF (CoupledState Seed 22)),
              ExecProgramDist w p_init ⟨10, by decide⟩ reg₀ mem₀
                (μ_init.map CoupledState.toRegMem) 16 ∧
              ExecDictOps w p_op
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
      @Comp.CallsAtMost,
      State, .mk, Cfg, .running, .halted, .faulted, @stepRand, @runRand⟩
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [AluOp.eval, Comp.bind, Comp.eval, Comp.CallsAtMost,
        stepRand, runRand])
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
      fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      @ExecDictOps.nil, @ExecDictOps.cons⟩

#check_abstract ComplexityAbstracts.HashTablesAbstract

end ComplexityAbstracts.HashTablesAbstract
