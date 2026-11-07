/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.SuccinctDictionaryBridge
import Cslib.Probability.PMF
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log

/-!
# Formal Abstract: Fixed-Capacity Succinct Dynamic Dictionary with Deletions

This self-contained file states the formal specification and the multi-operation correctness,
succinct space, and initialization-time theorems for the fixed-capacity succinct dynamic dictionary
with deletions on the randomized Word-RAM (`Succinct.impl` with `initFresh_exec` and
`steps_expected_amortized_ofFn`, `Succinct.initSteps_le`, and `Succinct.space_le_succinctWords`),
following `[BenderFarachColtonKuszmaulKuszmaul2024]` (SOSA 2024, Sections 3–4),
`[ArbitmanNaorSegev2010]` (FOCS 2010, Claim 5.7),
`[BenderConwayFarachColtonKuszmaulTagliavini2023]` (*J. ACM* 70(6):40, 2023;
`arXiv:2109.04548`, Section 7, pp. 31–33), and `[BenderFarachColtonKuszmaulKuszmaulLiu2022]`
(STOC 2022; `arXiv:2111.00602`, Sections 5.2 and 6.1, Lemma 24), combined with two-stage
universe-reduced `3`-wise independent polynomial hashing with a bit-packed Four-Russians
multiplication table (`ReducedKWise.impl`; `[CarterWegman1979]`, `[WegmanCarter1981]`,
`[PaghPaghRuzic2009]`, `[Vadhan2012]`, `[LidlNiederreiter1997]`, and
`[DietzfelbingerHagerupKatajainenPenttonen1997]`).

## Scope, operation semantics, and cost accounting

- **Dynamic dictionary with deletions (`DynDictOp U`) and material differences from SOSA 2024:**
  Supports `query u` (returning `s u`), `insert u v` (inserting or overwriting `u : Fin U` with
  `v : ℕ` when `v < V` and either fewer than `n_max` keys are currently present or `u` is already
  present), and `delete u` (removing `u` or leaving `s` unchanged if `u` is absent) across
  oblivious operation sequences `ops : List (DynDictOp U)` of any length
  (`ValidDynDictHistory V n_max`). Material differences from
  `[BenderFarachColtonKuszmaulKuszmaul2024]`: the capacity `n_max` is fixed (no table resizing),
  and operations run in `O(1)` expected amortized time for oblivious operation sequences fixed
  before initialization (whereas SOSA 2024 Sections 5–6 prove with-high-probability bounds and
  support resizing).
- **Why `n_max ≤ U` is assumed and `optBits` rounding:** Distinct active keys are drawn from
  `Fin U`, so at most `U` keys can coexist (`(dictDom s).card ≤ U`), and the binomial coefficient
  `U.choose n_max` inside `optBits U V n_max = ⌈log₂ C(U, n_max)⌉ + n_max * ⌈log₂ V⌉` is zero
  whenever `n_max > U`. Note that `optBits U V n_max` equals the exact information-theoretic
  minimum `⌈log₂(C(U, n_max) · V ^ n_max)⌉` when `V` is a power of two (and is within `< n_max`
  bits otherwise, since `⌈log₂ V⌉` rounds the per-value bit-length to an integer).
- **Single seed and per-bucket probe/hysteresis accounting:** A single quotient-hash seed is
  sampled once at initialization (`seedSlack = 1`, no rehash), and no persistent flag is kept to
  latch hash or overflow failures across operations. Each bucket's item count and expected extra
  collision or overflow probes (`probeExcess`) per operation depend only on the current active key
  set. The physical chain order and the division of a bucket's items between fixed-size full slabs
  and the shared tail pool under lazy promotion and demotion thresholds depend on operation history.
  In the `Memory.Prog` model (`SuccinctHash`), `queryWithHashProg_dict_spec`,
  `insertWithHashProg_dict_spec`, and `deleteWithHashProg_dict_spec` prove per-seed **amortized**
  `memoryCost` bounds of `26 + 8 * probeExcess`, `184 + 8 * probeExcess`, and
  `270 + 8 * probeExcess` with potential `66 * slotPotential`. In turn,
  `tsum_uniform_probeExcess_reducedPolyHash_le_five` bounds expected `probeExcess` by `5`.
- **Program parameterization and parameter-uniform `O(1)` operation charge:** The five generic
  `Memory.Prog` subroutines (`extractQuotGenProg`, `queryWithHashGenProg`, `insertWithHashGenProg`,
  `deletePrepWithHashGenProg`, `deleteFinishWithHashGenProg`) do not depend on `(U, V, w, n_max)`.
  The full program `subroutineCode U V w n_max` depends on `(U, V, w, n_max)` only through the
  `space` constant in `allocSpan`, the 36-instruction `loadParamsCode` prefix, and the hash code.
  Consequently, both the register budget `r ≥ 292` (`Succinct.rSuccinct`) and the per-operation
  charge `C_op` (`Succinct.chargeVal = 313 * Succinct.opFactor + 284725`) are universal `O(1)`
  constants existentially quantified **outside** `∀ (U V w n_max : ℕ)`, independent of
  `(U, V, w, n_max)`, `base`, and `ops.length`. For each `(U, V, w, n_max)`, the compiled
  `r`-register Word-RAM programs `p_init` and `p_op` depend on `(U, V, w, n_max)` and do not depend
  on `base`, the initial state `(reg₀, mem₀)`, or `ops`. No theorem in this abstract bounds the
  static code length `p_init.length` or `p_op.length`. All instruction counts
  (`expectedTime w p s ≤ T + 1`) exclude caller argument preparation (`prepareDynDictRegs`) and
  dispatch.
- **Initialization step bound and succinct space:** Initialization from zeroed memory on
  `[base, base + sp)` executes in at most `initBudget ≤ 31 * n_max + 1092` expected body
  instructions. The single contiguous memory block of `sp` machine words holds all hash seeds, the
  bit-packed multiplication table, and the four bit-packed dictionary arrays. It satisfies
  `sp ≤ succinctWords 81 213 U V w n_max =
  ⌈(optBits U V n_max + 81 * n_max * logLogFactor n_max) / w⌉ + 213` for every `w > 0` and
  `n_max ≤ U` with `U < 2 ^ w`, without any polynomial universe restriction
  `U ≤ poly(n_max)`.

A reader only needs to inspect the definitions and theorem statements in this file to verify that
the formalization proves the intended mathematical claims; Lean verifies the proofs through
`ComplexityAbstracts.SuccinctDictionaryBridge`, and `#check_abstract` audits the dependency
boundary.
-/

namespace ComplexityAbstracts.SuccinctDictionaryAbstract

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

/-! ## Bounded-Capacity Dynamic Dictionary Specification -/

/-- Abstract dictionary state over key universe `Fin U` with `ℕ`-valued entries. -/
abbrev DictState (U : ℕ) : Type :=
  Fin U → Option ℕ

/-- Initial empty dictionary mapping every key in `Fin U` to `none`. -/
def emptyDict (U : ℕ) : DictState U :=
  fun _ => none

/-- Finite set of keys currently present in dictionary `s`. -/
def dictDom {U : ℕ} (s : DictState U) : Finset (Fin U) :=
  Finset.univ.filter fun u => (s u).isSome

/-- Operations on a dynamic dictionary over key universe `Fin U`:
- `query u`: look up key `u : Fin U`;
- `insert u v`: insert or overwrite key `u : Fin U` with value `v : ℕ`;
- `delete u`: remove key `u : Fin U` (or no-op if `u` is absent). -/
inductive DynDictOp (U : ℕ) : Type where
  | query (u : Fin U) : DynDictOp U
  | insert (u : Fin U) (v : ℕ) : DynDictOp U
  | delete (u : Fin U) : DynDictOp U

/-- Apply one dynamic dictionary operation `o : DynDictOp U` to abstract state `s : DictState U`:
- `query u` leaves `s` unchanged;
- `insert u v` updates `s` at `u` to `some v`;
- `delete u` updates `s` at `u` to `none`. -/
def stepDynDict {U : ℕ} (s : DictState U) : DynDictOp U → DictState U
  | .query _ => s
  | .insert u v => Function.update s u (some v)
  | .delete u => Function.update s u none

/-- Admissibility of a single dynamic dictionary operation `o : DynDictOp U` on state `s` under
value bound `V` and capacity `n_max`:
- `query u` and `delete u` are always admissible;
- `insert u v` requires `v < V` and either `(dictDom s).card < n_max` (room for a new key) or
  `(s u).isSome` (overwriting an existing key). -/
def validDynDictOp {U : ℕ} (V n_max : ℕ) (s : DictState U) : DynDictOp U → Prop
  | .query _ => True
  | .insert u v => ((dictDom s).card < n_max ∨ (s u).isSome) ∧ v < V
  | .delete _ => True

/-- Admissibility of an oblivious operation sequence `ops : List (DynDictOp U)` starting from state
`s` under value bound `V` and capacity `n_max`. -/
def ValidDynDictHistory {U : ℕ} (V n_max : ℕ) : DictState U → List (DynDictOp U) → Prop
  | _, [] => True
  | s, o :: os => validDynDictOp V n_max s o ∧ ValidDynDictHistory V n_max (stepDynDict s o) os

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

/-- Calling-convention register assignment for a dynamic dictionary operation `o : DynDictOp U` on
an `r`-register Word-RAM with operation-tag register `tagReg`, key register `keyReg`, and value
register `valReg`:
- `tagReg` receives `0` for `query u`, `1` for `insert u v`, and `2` for `delete u`;
- `keyReg` receives `u.val`;
- `valReg` receives `v` for `insert u v` (and `0` for `query u` and `delete u`);
- every other register `i` is preserved (`reg i`). -/
def prepareDynDictRegs {r U : ℕ} (tagReg keyReg valReg : Fin r)
    (o : DynDictOp U) (reg : Fin r → ℕ) (i : Fin r) : ℕ :=
  if i = tagReg then
    match o with
    | .query _ => 0
    | .insert _ _ => 1
    | .delete _ => 2
  else if i = keyReg then
    match o with
    | .query u => u.val
    | .insert u _ => u.val
    | .delete u => u.val
  else if i = valReg then
    match o with
    | .query _ => 0
    | .insert _ v => v
    | .delete _ => 0
  else
    reg i

/-- Decode a two-register `Option ℕ` query response from `(reg resTagReg, reg resValReg)`:
`reg resTagReg = 0` encodes `none` (key absent), and `reg resTagReg ≠ 0` encodes
`some (reg resValReg)` (key present with value `reg resValReg`). -/
def decodeOptionRegs {r : ℕ} (resTagReg resValReg : Fin r) (reg : Fin r → ℕ) : Option ℕ :=
  if reg resTagReg = 0 then none else some (reg resValReg)

/-- Output correctness of a post-operation register bank `reg` for operation `o : DynDictOp U`
against pre-operation dictionary state `s : DictState U` with result registers
`(resTagReg, resValReg)`:
- for `query u`, `decodeOptionRegs resTagReg resValReg reg = s u`;
- for `insert u v` and `delete u`, the unit return needs no output-register check (`True`). -/
def OpOutputCorrect {r U : ℕ} (resTagReg resValReg : Fin r) (s : DictState U)
    (o : DynDictOp U) (reg : Fin r → ℕ) : Prop :=
  match o with
  | .query u => decodeOptionRegs resTagReg resValReg reg = s u
  | .insert _ _ => True
  | .delete _ => True

/-- Sequential multi-operation execution of a history `ops : List (DynDictOp U)` by the Word-RAM
operation program `p_op : Program r` at word width `w`, with calling-convention registers
`(tagReg, keyReg, valReg, outReg, resTagReg, resValReg)` and allocated memory region
`[base, base + sp)`:
- `nil`: the empty operation history leaves the coupled state distribution `μ` unchanged with `0`
  expected operation steps;
- `cons`: from every supported coupled state `p ∈ μ.support`, running `p_op` after loading the
  encoded arguments of `o` via `prepareDynDictRegs tagReg keyReg valReg o` executes with
  distribution `(μ_step p).map CoupledState.toRegMem` and expected step budget `T_step p`
  (`ExecProgramDist`). Every resulting state `q ∈ (μ_step p).support` has `w`-bit bounded registers
  and memory, satisfies `OpOutputCorrect resTagReg resValReg s o q.reg` (matching the dynamic
  dictionary specification), and leaves memory outside `[base, base + sp)` unchanged. The remaining
  operations `ops` execute from `μ.bind μ_step` to `μ_final` with expected step budget `T_rest`,
  yielding total expected operation cost `(∑' p, μ p * T_step p) + T_rest`. -/
inductive ExecDynDictOps {Seed : Type} {r U : ℕ}
    (w : ℕ) (p_op : Program r)
    (tagReg keyReg valReg outReg resTagReg resValReg : Fin r) (base sp : ℕ) :
    DictState U → List (DynDictOp U) →
    PMF (CoupledState Seed r) → PMF (CoupledState Seed r) → ℝ≥0∞ → Prop where
  | nil (s : DictState U) (μ : PMF (CoupledState Seed r)) :
      ExecDynDictOps w p_op tagReg keyReg valReg outReg resTagReg resValReg base sp s [] μ μ 0
  | cons {s : DictState U} {o : DynDictOp U} {ops : List (DynDictOp U)}
      {μ μ_final : PMF (CoupledState Seed r)} {T_rest : ℝ≥0∞}
      (T_step : CoupledState Seed r → ℝ≥0∞)
      (μ_step : CoupledState Seed r → PMF (CoupledState Seed r))
      (hstep : ∀ p ∈ μ.support,
        ExecProgramDist w p_op outReg
          (prepareDynDictRegs tagReg keyReg valReg o p.reg) p.mem
          ((μ_step p).map CoupledState.toRegMem) (T_step p) ∧
        ∀ q ∈ (μ_step p).support,
          WordBounded w q.reg q.mem ∧
          OpOutputCorrect resTagReg resValReg s o q.reg ∧
          UnchangedOutside base sp p.mem q.mem)
      (hrest : ExecDynDictOps w p_op tagReg keyReg valReg outReg resTagReg resValReg base sp
        (stepDynDict s o) ops (μ.bind μ_step) μ_final T_rest) :
      ExecDynDictOps w p_op tagReg keyReg valReg outReg resTagReg resValReg base sp
        s (o :: ops) μ μ_final ((∑' p, μ p * T_step p) + T_rest)

/-! ## Succinct Space Accounting and Headline Expected-Amortized Theorem -/

/-- Information-theoretic baseline bit-length `⌈log₂ C(U, n_max)⌉ + n_max * ⌈log₂ V⌉` required to
represent `n_max` distinct keys from `Fin U` with associated `⌈log₂ V⌉`-bit values in `Fin V`
(equal to the exact information-theoretic minimum `⌈log₂(C(U, n_max) · V ^ n_max)⌉` when `V` is a
power of two, and within `< n_max` bits otherwise). -/
def optBits (U V n_max : ℕ) : ℕ :=
  Nat.clog 2 (U.choose n_max) + n_max * Nat.clog 2 V

/-- Doubly-logarithmic additive per-item bit factor `⌈log₂ ⌈log₂ (max n_max 4)⌉⌉ =
O(log log n_max)`. -/
def logLogFactor (n_max : ℕ) : ℕ :=
  Nat.clog 2 (Nat.clog 2 (max n_max 4))

/-- Succinct word-space upper bound
`⌈(optBits U V n_max + C * n_max * logLogFactor n_max) / w⌉ + C₀` (in `w`-bit machine words)
with per-item doubly-logarithmic bit slack constant `C` and constant word overhead `C₀`. -/
def succinctWords (C C₀ U V w n_max : ℕ) : ℕ :=
  (optBits U V n_max + C * n_max * logLogFactor n_max + w - 1) / w + C₀

/-- **Fixed-Capacity Succinct Dynamic Dictionary with Deletions**
(`Succinct.impl` with `initFresh_exec` and `steps_expected_amortized_ofFn`,
`Succinct.initSteps_le`, and `Succinct.space_le_succinctWords`):
Certifies multi-operation distributional correctness, succinct space, linear initialization cost,
and universal `O(1)` expected amortized operation time on the Word-RAM. There exist universal
constants `r ≥ 292` (`Succinct.rSuccinct`) and `C_op : ℕ` (`Succinct.chargeVal = 313 *
Succinct.opFactor + 284725`, independent of `U`, `V`, `w`, `n_max`, `base`, and `ops.length`) such
that for every key universe `U`, value bound `V`, word width `w`, and capacity `n_max`, there exist
allocated block size `sp : ℕ`, initialization instruction budget `initBudget : ℕ`, and compiled
`r`-register Word-RAM programs `p_init` and `p_op` (depending on `(U, V, w, n_max)` and independent
of `base`, with no static code-size bound) such that:
- `initBudget ≤ 31 * n_max + 1092`;
- whenever `0 < w`, `n_max ≤ U` (since distinct keys lie in `Fin U` and `U.choose n_max = 0` for
  `n_max > U`), and `U < 2 ^ w`, the total word footprint `sp` satisfies the succinct bound
  `sp ≤ succinctWords 81 213 U V w n_max` (with no polynomial restriction `U ≤ poly(n_max)`);
- for every base address `base` with `0 < w`, `n_max ≤ U`, `U < 2 ^ w`, `V < 2 ^ w`, and
  `base + sp < 2 ^ w`, from any word-bounded initial state `(reg₀, mem₀)` with `reg₀ 240 = base`
  and zeroed memory in `[base, base + sp)`, there exists an initial coupled distribution `μ_init`
  (chosen before any operation sequence `ops`) such that:
  1. `p_init` initializes the dictionary in `initBudget ≤ 31 * n_max + 1092` expected executed body
     instructions, and every `p ∈ μ_init.support` satisfies `WordBounded w p.reg p.mem`,
     `p.reg 0 = base`, `p.reg 240 = base + sp`, and `UnchangedOutside base sp mem₀ p.mem`;
  2. for every oblivious operation history `ops : List (DynDictOp U)` of any length valid for
     capacity `n_max` and value bound `V` (`ValidDynDictHistory V n_max (emptyDict U) ops`), `p_op`
     executes `ops` sequentially (`ExecDynDictOps`), matching `stepDynDict` and `OpOutputCorrect`
     at every step;
  3. the expected executed body instruction count `T_ops` across `ops` satisfies the expected
     amortized bound `T_ops ≤ ops.length * C_op` for the universal constant `C_op`.

References: `[BenderFarachColtonKuszmaulKuszmaul2024]` (SOSA 2024, Sections 3–4);
`[ArbitmanNaorSegev2010]` (FOCS 2010, Claim 5.7);
`[BenderConwayFarachColtonKuszmaulTagliavini2023]` (*J. ACM* 70(6):40, 2023;
`arXiv:2109.04548`, Section 7, pp. 31–33); `[BenderFarachColtonKuszmaulKuszmaulLiu2022]`
(STOC 2022; `arXiv:2111.00602`, Sections 5.2 and 6.1, Lemma 24); `[PaghPaghRuzic2009]`;
`[DietzfelbingerHagerupKatajainenPenttonen1997]`; `[CarterWegman1979]`; `[WegmanCarter1981]`;
`[Vadhan2012]`; `[LidlNiederreiter1997]`. -/
theorem succinctDynamicDictionary :
    ∃ (r C_op : ℕ) (hr : 292 ≤ r),
      ∀ (U V w n_max : ℕ),
        ∃ (sp initBudget : ℕ) (p_init p_op : List (Instr r)),
          initBudget ≤ 31 * n_max + 1092 ∧
          (0 < w → n_max ≤ U → U < 2 ^ w →
            sp ≤ succinctWords 81 213 U V w n_max) ∧
          ∀ (base : ℕ),
            0 < w →
            n_max ≤ U →
            U < 2 ^ w →
            V < 2 ^ w →
            base + sp < 2 ^ w →
            ∀ (reg₀ : Fin r → ℕ) (mem₀ : ℕ → ℕ),
              WordBounded w reg₀ mem₀ →
              reg₀ ⟨240, by omega⟩ = base →
              (∀ a, base ≤ a → a < base + sp → mem₀ a = 0) →
              ∃ (Seed : Type) (μ_init : PMF (CoupledState Seed r)),
                ExecProgramDist w p_init ⟨247, by omega⟩ reg₀ mem₀
                  (μ_init.map CoupledState.toRegMem) initBudget ∧
                (∀ p ∈ μ_init.support,
                  WordBounded w p.reg p.mem ∧
                  p.reg ⟨0, by omega⟩ = base ∧
                  p.reg ⟨240, by omega⟩ = base + sp ∧
                  UnchangedOutside base sp mem₀ p.mem) ∧
                ∀ ops : List (DynDictOp U),
                  ValidDynDictHistory V n_max (emptyDict U) ops →
                  ∃ (μ_final : PMF (CoupledState Seed r)) (T_ops : ℝ≥0∞),
                    ExecDynDictOps w p_op
                      ⟨244, by omega⟩ ⟨245, by omega⟩ ⟨246, by omega⟩
                      ⟨247, by omega⟩ ⟨252, by omega⟩ ⟨253, by omega⟩
                      base sp (emptyDict U) ops
                      μ_init μ_final T_ops ∧
                    T_ops ≤ ((ops.length * C_op : ℕ) : ℝ≥0∞) :=
  ComplexityAbstracts.SuccinctDictionaryBridge.succinctDynamicDictionary
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
    ⟨DynDictOp, @DynDictOp.query, @DynDictOp.insert, @DynDictOp.delete, @DynDictOp.rec,
      @stepDynDict, @validDynDictOp, @ValidDynDictHistory,
      RegMem, @RegMem.mk, @RegMem.reg, @RegMem.mem,
      CoupledState, @CoupledState.mk, @CoupledState.seed, @CoupledState.reg, @CoupledState.mem,
      @prepareDynDictRegs, @OpOutputCorrect, @ExecDynDictOps⟩
    ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl,
      fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl,
      fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      @ExecDynDictOps.nil, @ExecDynDictOps.cons⟩

/--
info: abstract audit passed for `ComplexityAbstracts.SuccinctDictionaryAbstract`: 375 root
declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.SuccinctDictionaryAbstract

end ComplexityAbstracts.SuccinctDictionaryAbstract
