/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.HashFamiliesBridge
import Cslib.Probability.PMF
import Mathlib.Data.Nat.Log

/-!
# Formal Abstract: High-Independence Word-RAM Hash Family

This self-contained file states the formal specification and headline theorems for the
all-capacity, high-independence Word-RAM hash family in Complexitylib (`provableImpl` and
`provableObliviousSequenceImpl` in
`Complexity/DataStructure/HashFamily/WordRAM/DoubleTabulation.lean`),
specialized to the polynomial key-universe exponent `c_exp = 4` (`U ≤ max n_max 4 ^ 4`).

## Regime-Switched Construction and Resource Bounds

Given a target independence parameter `k : ℕ`, a capacity parameter `n_max : ℕ`, a key universe
`Fin U` with `U ≤ max n_max 4 ^ 4`, and an output bit-width `M ≤ 4 * Nat.clog 2 (max n_max 4) + 5`
(hash codomain `Fin (2 ^ M)`), the construction switches at the explicit capacity threshold
`regimeThreshold = 2 ^ 320000` (`doubleTabThreshold 4`, derived from `b ≥ 4 * (8 + 48 * 4) ^ 2 =
160000`):

1. **Small-capacity regime (`n_max < 2 ^ 320000`)**:
   Evaluates a degree-`(k - 1)` polynomial over a binary trinomial extension field `GF(2 ^ D)` of
   degree `D = trinomialDeg U M = 2 * 3 ^ t` (where `t = trinomialStep U M` satisfies
   `2 * 3 ^ t ≥ max (Nat.clog 2 (max U 2)) (max M 1)` in
   `GF(2)[X] / (X ^ D + X ^ (D / 2) + 1)`),
   accelerated by a precomputed four-Russians multiplication lookup table of size
   `2 ^ (2 * chunkBits n_max)` words (`chunkBits n_max = max 1 (Nat.log 2 (max n_max 2) / 3)`).
   Every seed is **exact** `k`-wise independent (`failureProbBound k n_max = 0`), `.eval u` runs in
   `evalTimeBound k = max (111230 * k + 19) 6858 + 4` instructions (`O_k(1)`), and `.resample` draws
   `k` random words in `5 * k + 13` instructions (`O_k(1)`).
2. **Large-capacity regime (`n_max ≥ 2 ^ 320000`)**:
   Uses Thorup's double-tabulation construction `[Thorup2013]` (FOCS 2013, pp. 90–99;
   `arXiv:1311.3121v2`, Theorem 1(a) p. 4, Lemma 2 p. 5, and Section 2 Eqs. (6)–(7) p. 11) with
   character bit-width `b = charBits n_max = (1 + Nat.clog 2 (max n_max 4)) / 2`, input alphabet
   `Σ = Fin (2 ^ b)`, top position count `c = 8`, intermediate position count `d = 64`, counting
   parameter `q = 4` (`d = 2 * q * c`), and `576 * 2 ^ b` words of table storage
   (`(c + 1) * d * |Σ|`).
   Each `.eval u` performs `c + d` table lookups in `evalTimeBound k` instructions (`O_k(1)`), and
   `.resample` refreshes all `576 * 2 ^ b` table entries in `2880 * 2 ^ b + 16` instructions
   (`O(n_max)`). Whereas `[Thorup2013]` Theorem 1(a) states failure probability
   `o(|Φ| ^ 2 / |Ψ| ^ (d / (2 * c)))` for `k = |Ψ| ^ (1 / (5 * c))`, the library's fixed-`k` proof
   adaptation bounds each resampling epoch's failure probability by `failureProbBound k n_max`:
   whenever `2 * codeBound k ≤ 2 ^ (3 * b)` (where `codeBound k = 8 * ((8 * k) ^ 16 * 64) ^ 4 =
   2 ^ 219 * k ^ 64` from Section 2, Eqs. (6)–(7), p. 11 at `c = 8, d = 64, q = 4`),
   `failureProbBound k n_max = 2 * (codeBound k) ^ 2 / 2 ^ (6 * b) ≤
   2 * (codeBound k) ^ 2 / max n_max 4 ^ 3`.

Across all `n_max : ℕ`, the memory footprint satisfies `space k n_max ≤ (k + 9232) * (n_max + 1)`
words (`space_le`), `.eval u` halts within `evalTimeBound k ≤ 111230 * k + 6862` instructions
(`evalTimeBound_le`), and `.resample` halts within
`resampleTime k n_max ≤ (5 * k + 46096) * (n_max + 1)` instructions (`resampleTime_le`).

## Multi-Operation Execution and High-Probability `k`-Wise Independence Contract

The headline theorems `highIndependenceHashFamily_fresh` (for fresh zeroed memory in
`[base, base + space k n_max)`) and `highIndependenceHashFamily_clear` (for arbitrary initial
memory, including an explicit zero-fill pass) package:

- **Initialization (`p_init` / `p_initClear`)**: halts within `initFreshTime k n_max U M` (resp.
  `initClearTime k n_max U M`) instructions on every execution branch (`HaltsWithin` and bounded
  `expectedTime`), modifies memory only inside `[base, base + space k n_max)`, sets register `0` to
  `base` and register `22` to `base + space k n_max`, and produces an initial state distribution
  `ν₀` with empty transcript `[]`.
- **Sequential multi-operation execution (`RunsOps`)**: for every oblivious operation sequence
  `ops : List (Op U)` of `.resample` and `.eval u` calls, running `p_op` sequentially from `ν₀`
  halts within `evalTimeBound k` steps on each `.eval u` (deterministically and without modifying
  memory) and within `resampleTime k n_max` steps on each `.resample` (modifying memory only inside
  `[base, base + space k n_max)`), producing a final state distribution `ν_final`.
- **High-probability `k`-wise independence (`WhpKWiseContract`)**: whenever every resampling epoch
  in `ops` queries at most `k` distinct keys (`BoundedEpochKeys k ops`), the transcript marginal
  `ν_final.map SeqState.transcript` matches `ops` and is coupled (`CoupledWithin`) to the ideal
  random-oracle transcript distribution `idealTranscriptPMF ops` within total variation / coupling
  disagreement at most `epochCount ops * failureProbBound k n_max`.
-/

namespace ComplexityAbstracts.HashFamiliesAbstract

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

/-- Every positive-probability outcome after `T` steps from `s` has halted cleanly. -/
def HaltsWithin {r : ℕ} (w : ℕ) (p : Program r) (s : State r) (T : ℕ) : Prop :=
  ∀ cfg ∈ (evalRand w p T s).support, ∃ v reg mem, cfg = .halted v reg mem

/-- Expected running time in `ENNReal`, as the sum over `t` of the probability of still running. -/
noncomputable def expectedTime {r : ℕ} (w : ℕ) (p : Program r)
    (s : State r) : ℝ≥0∞ :=
  ∑' t : ℕ,
    (evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = .running u}

/-! ## Operations, Transcripts, and Epochs -/

/-- Operations supported by a dynamic hash-function family over key universe `Fin U`:
- `resample`: draw a fresh hash seed, starting a new resampling epoch;
- `eval u`: evaluate the current hash function at key `u : Fin U`. -/
inductive Op (U : ℕ) where
  | resample : Op U
  | eval (u : Fin U) : Op U

/-- A transcript entry recording one completed operation over key universe `Fin U` and hash
codomain `Fin m`:
- `resample`: a completed `.resample` step (returning unit);
- `eval u y`: a completed `.eval u` step returning hash value `y : Fin m`. -/
inductive Label (U m : ℕ) where
  | resample : Label U m
  | eval (u : Fin U) (y : Fin m) : Label U m

/-- Underlying operation recorded by a transcript label. -/
def Label.op {U m : ℕ} : Label U m → Op U
  | .resample => .resample
  | .eval u _ => .eval u

/-- Partition an operation sequence `ops` into the sets of distinct keys queried in each resampling
epoch (separated by `.resample` operations, starting with an initial epoch). -/
def epochKeys {U : ℕ} : List (Op U) → List (Finset (Fin U))
  | [] => [∅]
  | .resample :: ops => ∅ :: epochKeys ops
  | .eval u :: ops =>
      match epochKeys ops with
      | [] => [{u}]
      | E :: rest => insert u E :: rest

/-- Every resampling epoch in `ops` queries at most `k` distinct keys. -/
def BoundedEpochKeys {U : ℕ} (k : ℕ) (ops : List (Op U)) : Prop :=
  ∀ E ∈ epochKeys ops, E.card ≤ k

/-- Total number of resampling epochs in `ops` (`1` plus the number of `.resample` operations). -/
def epochCount {U : ℕ} : List (Op U) → ℕ
  | [] => 1
  | .resample :: ops => epochCount ops + 1
  | .eval _ :: ops => epochCount ops

/-! ## Ideal Random-Oracle Transcript and High-Probability `k`-Wise Independence Contract -/

/-- Transcript distribution of `ops` starting from an active hash function `f : Fin U → Fin m`,
drawing a fresh independent uniform random function `f' ← PMF.uniformOfFintype (Fin U → Fin m)` at
each `.resample` operation. -/
noncomputable def idealTranscriptFrom {U m : ℕ} [NeZero m] (f : Fin U → Fin m) :
    List (Op U) → PMF (List (Label U m))
  | [] => PMF.pure []
  | .eval u :: ops =>
      (idealTranscriptFrom f ops).map fun rest => .eval u (f u) :: rest
  | .resample :: ops =>
      (Cslib.Probability.PMF.uniformOfFintype (Fin U → Fin m)).bind fun f' =>
        (idealTranscriptFrom f' ops).map fun rest => .resample :: rest

/-- Ideal multi-epoch uniform random-function transcript distribution on `ops`: draws an initial
uniform random function `f₀ ← PMF.uniformOfFintype (Fin U → Fin m)` and evaluates `ops` via
`idealTranscriptFrom`. -/
noncomputable def idealTranscriptPMF {U m : ℕ} [NeZero m] (ops : List (Op U)) :
    PMF (List (Label U m)) :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin U → Fin m)).bind fun f₀ =>
    idealTranscriptFrom f₀ ops

/-- Every transcript entry in `tr` records the corresponding operation in `ops`. -/
def TranscriptMatches {U m : ℕ} (ops : List (Op U)) (tr : List (Label U m)) : Prop :=
  tr.map Label.op = ops

/-- Two distributions `μ, ν : PMF α` admit a coupling `γ : PMF (α × α)` with marginals `μ` and `ν`
whose disagreement event `{p | p.1 ≠ p.2}` has probability at most `ε`. -/
def CoupledWithin {α : Type} (μ ν : PMF α) (ε : ℝ≥0∞) : Prop :=
  ∃ γ : PMF (α × α),
    γ.map Prod.fst = μ ∧
    γ.map Prod.snd = ν ∧
    γ.toOuterMeasure {p : α × α | p.1 ≠ p.2} ≤ ε

/-- High-probability `k`-wise independence contract with per-epoch failure probability `δ`:
every supported transcript matches `ops`, and the transcript distribution `μ` can be coupled to the
ideal random-oracle transcript distribution `idealTranscriptPMF ops` with disagreement probability
at most `epochCount ops * δ`. -/
def WhpKWiseContract {U m : ℕ} [NeZero m] (δ : ℝ≥0∞)
    (ops : List (Op U)) (μ : PMF (List (Label U m))) : Prop :=
  (∀ tr ∈ μ.support, TranscriptMatches ops tr) ∧
  CoupledWithin μ (idealTranscriptPMF (m := m) ops) ((epochCount ops : ℝ≥0∞) * δ)

/-! ## Calling Convention and Sequential Multi-Operation Word-RAM Execution -/

/-- All registers and memory cells carry `w`-bit machine words (`< 2 ^ w`). -/
def WordBounded {r : ℕ} (w : ℕ) (reg : Fin r → ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ i, reg i < 2 ^ w) ∧ ∀ a, mem a < 2 ^ w

/-- Memory cells outside the allocated region `[base, base + sp)` are unchanged between `mem` and
`mem'`. -/
def UnchangedOutside (base sp : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  ∀ a, (a < base ∨ base + sp ≤ a) → mem' a = mem a

/-- Load the operation tag and argument for `o : Op U` into the 23-register Word-RAM bank:
- register `18` receives the operation tag (`0` for `.resample`, `1` for `.eval u`);
- register `1` receives the key `u.val` for `.eval u` (and `0` for `.resample`);
- all other registers (including the base-address register `0` and allocation-frontier register
  `22`) are preserved. -/
def prepareRegs {U : ℕ} (o : Op U) (reg : Fin 23 → ℕ) (i : Fin 23) : ℕ :=
  if decide (i = ⟨18, by decide⟩ ∨ i = ⟨1, by decide⟩) then
    match o with
    | .resample => 0
    | .eval u =>
        if i = ⟨18, by decide⟩ then 1
        else if i = ⟨1, by decide⟩ then u.val
        else 0
  else
    reg i

/-- Decode the completed transcript label for `o : Op U` from the output register bank `reg`:
- `.resample` always decodes to `some .resample`;
- `.eval u` reads the hash output from register `2` (`outReg`) when `reg 2 < m`. -/
def decodeLabel {U : ℕ} (m : ℕ) (o : Op U) (reg : Fin 23 → ℕ) : Option (Label U m) :=
  match o with
  | .resample => some .resample
  | .eval u =>
      if h : reg ⟨2, by decide⟩ < m then
        some (.eval u ⟨reg ⟨2, by decide⟩, h⟩)
      else
        none

/-- Machine state paired with the accumulated transcript of completed operations. -/
structure SeqState (U m : ℕ) where
  reg : Fin 23 → ℕ
  mem : ℕ → ℕ
  transcript : List (Label U m)

/-- Result of a single operation step: post-step register bank, memory, and decoded label. -/
structure StepResult (U m : ℕ) where
  reg : Fin 23 → ℕ
  mem : ℕ → ℕ
  label : Label U m

/-- Append a completed single-operation step `q` to a sequential state `t`. -/
def SeqState.appendStep {U m : ℕ} (t : SeqState U m) (q : StepResult U m) : SeqState U m :=
  ⟨q.reg, q.mem, t.transcript ++ [q.label]⟩

/-- Per-operation worst-case instruction budget: `t_res` for `.resample` and `t_eval` for
`.eval u`. -/
def opBudget {U : ℕ} (t_eval t_res : ℕ) : Op U → ℕ
  | .resample => t_res
  | .eval _ => t_eval

/-- Sequential execution of an operation list `ops : List (Op U)` by the Word-RAM operation program
`p_op : List (Instr 23)` at word width `w`, with allocated memory region `[base, base + sp)` and
per-operation step budgets `t_eval` (for `.eval u`) and `t_res` (for `.resample`):
- `nil`: the empty operation list leaves the state distribution `ν` unchanged;
- `cons`: from every supported state `t ∈ ν.support`, running `p_op` from
  `State.mk 0 (prepareRegs o t.reg) t.mem` halts within `opBudget t_eval t_res o` steps on every
  random branch (`HaltsWithin`), produces halted states distributed according to `μ_step t` (with
  word-bounded registers/memory, valid decoded label `q.label`, and memory unchanged outside
  `[base, base + sp)`), is **deterministic and memory-preserving** whenever `o = .eval u`, and the
  remaining operations `ops` execute from the updated distribution
  `ν.bind (fun t => (μ_step t).map t.appendStep)` to `ν_final`. -/
inductive RunsOps {U m : ℕ}
    (w : ℕ) (p_op : List (Instr 23)) (base sp t_eval t_res : ℕ) :
    List (Op U) → PMF (SeqState U m) → PMF (SeqState U m) → Prop where
  | nil (ν : PMF (SeqState U m)) :
      RunsOps w p_op base sp t_eval t_res [] ν ν
  | cons {o : Op U} {ops : List (Op U)} {ν ν_final : PMF (SeqState U m)}
      (μ_step : SeqState U m → PMF (StepResult U m))
      (hstep : ∀ t ∈ ν.support,
        let s_in : State 23 := ⟨0, prepareRegs o t.reg, t.mem⟩
        let T := opBudget t_eval t_res o
        WordBounded w t.reg t.mem ∧
        HaltsWithin w p_op s_in T ∧
        evalRand w p_op T s_in =
          (μ_step t).map (fun q => .halted (q.reg ⟨2, by decide⟩) q.reg q.mem) ∧
        (∀ u, o = .eval u → ∃ q, μ_step t = PMF.pure q ∧ q.mem = t.mem) ∧
        ∀ q ∈ (μ_step t).support,
          WordBounded w q.reg q.mem ∧
          decodeLabel m o q.reg = some q.label ∧
          UnchangedOutside base sp t.mem q.mem)
      (hrest : RunsOps w p_op base sp t_eval t_res ops
        (ν.bind fun t => (μ_step t).map t.appendStep) ν_final) :
      RunsOps w p_op base sp t_eval t_res (o :: ops) ν ν_final

/-! ## Resource Functions and Failure-Probability Bounds at `c_exp = 4` -/

/-- Capacity threshold `2 ^ 320000` (`doubleTabThreshold 4`) where the construction switches from
the table-accelerated `k`-wise polynomial regime (`n_max < 2 ^ 320000`) to Thorup's
double-tabulation regime (`n_max ≥ 2 ^ 320000`), corresponding to character bit-width
`charBits n_max ≥ 4 * (8 + 48 * 4) ^ 2 = 160000`. -/
def regimeThreshold : ℕ :=
  2 ^ 320000

/-- Four-Russians chunk bit-width `max 1 (⌊log₂(max n_max 2)⌋ / 3)` in the small-capacity regime. -/
def chunkBits (n_max : ℕ) : ℕ :=
  max 1 (Nat.log 2 (max n_max 2) / 3)

/-- Double-tabulation character bit-width `⌊(1 + ⌈log₂(max n_max 4)⌉) / 2⌋` in the large-capacity
regime, so the character alphabet `Σ = Fin (2 ^ charBits n_max)` has size `O(n_max)`. -/
def charBits (n_max : ℕ) : ℕ :=
  (1 + Nat.clog 2 (max n_max 4)) / 2

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
`GF(2)[X] / (X ^ D + X ^ (D / 2) + 1)` used in the small-capacity polynomial regime. -/
def trinomialDeg (U M : ℕ) : ℕ :=
  2 * 3 ^ trinomialStep U M

/-- Memory footprint `space k n_max` (in machine words) of the regime-switched hash family at
`c_exp = 4`:
- `8 + k + 2 ^ (2 * chunkBits n_max)` words when `n_max < 2 ^ 320000` (parameter header, `k` seed
  coefficients, and the `2 ^ (2 * chunkBits n_max)`-entry chunk-multiplication lookup table);
- `576 * 2 ^ charBits n_max` words (`(8 + 1) * 64 * 2 ^ charBits n_max`) when
  `2 ^ 320000 ≤ n_max` (top table `T₁` of `8 × 2 ^ b × 64` words and bottom table `T₂` of
  `64 × 2 ^ b` words). -/
def space (k n_max : ℕ) : ℕ :=
  if n_max < regimeThreshold then
    8 + k + 2 ^ (2 * chunkBits n_max)
  else
    576 * 2 ^ charBits n_max

/-- Uniform `O_k(1)` worst-case instruction budget for `.eval u` across all capacities `n_max`,
key universes `U ≤ max n_max 4 ^ 4`, and output bit-widths `M ≤ 4 * Nat.clog 2 (max n_max 4) + 5`
(including subroutine dispatch and the final `halt` instruction). -/
def evalTimeBound (k : ℕ) : ℕ :=
  max (111230 * k + 19) 6858 + 4

/-- Worst-case instruction budget for `.resample` (including subroutine dispatch and the final
`halt` instruction):
- `5 * k + 13` instructions (`O_k(1)`) when `n_max < 2 ^ 320000`;
- `2880 * 2 ^ charBits n_max + 16` instructions (`O(n_max)`) when `2 ^ 320000 ≤ n_max`. -/
def resampleTime (k n_max : ℕ) : ℕ :=
  if n_max < regimeThreshold then
    5 * k + 13
  else
    2880 * 2 ^ charBits n_max + 16

/-- Deterministic lookup-table initialization step count before the initial seed sample. -/
def initTableSteps (n_max U M : ℕ) : ℕ :=
  if n_max < regimeThreshold then
    19 * 2 ^ (2 * chunkBits n_max) +
      4 * Nat.log 2 (max n_max 2) +
      5 * Nat.clog 2 (max U 2) +
      5 * trinomialStep U M + 69
  else
    1

/-- Worst-case instruction budget for `p_init` when `[base, base + space k n_max)` is initially
zeroed. -/
def initFreshTime (k n_max U M : ℕ) : ℕ :=
  initTableSteps n_max U M + resampleTime k n_max + 1

/-- Worst-case instruction budget for `p_initClear` on arbitrary initial memory (adding the
`4 * space k n_max + 6`-step zero-fill pass). -/
def initClearTime (k n_max U M : ℕ) : ℕ :=
  initFreshTime k n_max U M + (4 * space k n_max + 6)

/-- Per-step efficient-code counting factor `8 * ((8 * k) ^ 16 * 64) ^ 4`
(`doubleTabCodeBound 8 64 4 k = 2 ^ 219 * k ^ 64`) from `[Thorup2013]` (FOCS 2013, pp. 90–99;
`arXiv:1311.3121v2`, Section 2, Eqs. (6)–(7), p. 11) specialized to `c = 8`, `d = 64`, and
`q = 4`. -/
def codeBound (k : ℕ) : ℕ :=
  8 * ((8 * k) ^ 16 * 64) ^ 4

/-- Per-epoch failure probability bound `failureProbBound k n_max` proved by the library for the
regime-switched hash family at `c_exp = 4`:
- **Small capacities (`n_max < 2 ^ 320000`)**: `0` (every seed in the trinomial polynomial family is
  exact `k`-wise independent);
- **Large capacities (`n_max ≥ 2 ^ 320000`) with `2 * codeBound k ≤ 2 ^ (3 * charBits n_max)`**:
  `2 * (codeBound k) ^ 2 / 2 ^ (6 * charBits n_max) ≤ 2 * (codeBound k) ^ 2 / max n_max 4 ^ 3`
  (fixed-`k` proof adaptation of `[Thorup2013]`, FOCS 2013, pp. 90–99; `arXiv:1311.3121v2`,
  Theorem 1(a) p. 4, Lemma 2 p. 5, and Section 2 Eqs. (6)–(7) p. 11);
- **Large capacities when `k` exceeds the non-triviality condition
  `2 * codeBound k ≤ 2 ^ (3 * charBits n_max)`**:
  falls back to the trivial probability bound `1`. -/
noncomputable def failureProbBound (k n_max : ℕ) : ℝ≥0∞ :=
  if n_max < regimeThreshold then
    0
  else if 2 * codeBound k ≤ 2 ^ (3 * charBits n_max) then
    ((2 * (codeBound k) ^ 2 : ℕ) : ℝ≥0∞) / ((2 ^ (6 * charBits n_max) : ℕ) : ℝ≥0∞)
  else
    1

/-! ## Explicit Asymptotic and Regime Properties of the Resource and Failure Bounds -/

/-- Across all capacities `n_max` (both below and above `regimeThreshold = 2 ^ 320000`), the memory
footprint `space k n_max` is `O_k(n_max + 1)` machine words. -/
theorem space_le (k n_max : ℕ) :
    space k n_max ≤ (k + 9232) * (n_max + 1) :=
  ComplexityAbstracts.HashFamiliesBridge.space_le k n_max

/-- Every `.eval u` operation halts within `111230 * k + 6862 = O_k(1)` Word-RAM instructions,
independently of `n_max`, `U`, and `M`. -/
theorem evalTimeBound_le (k : ℕ) :
    evalTimeBound k ≤ 111230 * k + 6862 :=
  ComplexityAbstracts.HashFamiliesBridge.evalTimeBound_le k

/-- Below `regimeThreshold`, `.resample` halts in `5 * k + 13 = O_k(1)` Word-RAM instructions. -/
theorem resampleTime_eq_of_lt {k n_max : ℕ} (hlt : n_max < regimeThreshold) :
    resampleTime k n_max = 5 * k + 13 :=
  ComplexityAbstracts.HashFamiliesBridge.resampleTime_eq_of_lt hlt

/-- Across all capacities `n_max`, `.resample` halts within `(5 * k + 46096) * (n_max + 1) =
O_k(n_max + 1)` Word-RAM instructions. -/
theorem resampleTime_le (k n_max : ℕ) :
    resampleTime k n_max ≤ (5 * k + 46096) * (n_max + 1) :=
  ComplexityAbstracts.HashFamiliesBridge.resampleTime_le k n_max

/-- Below `regimeThreshold = 2 ^ 320000`, the hash family is **exact** `k`-wise independent:
the per-epoch failure probability is `0` for every `k`. -/
theorem failureProbBound_eq_zero_of_lt {k n_max : ℕ} (hlt : n_max < regimeThreshold) :
    failureProbBound k n_max = 0 :=
  ComplexityAbstracts.HashFamiliesBridge.failureProbBound_eq_zero_of_lt hlt

/-- In the double-tabulation regime (`n_max ≥ 2 ^ 320000`), whenever `k` satisfies the
non-triviality condition `2 * codeBound k ≤ 2 ^ (3 * charBits n_max)`, the per-epoch failure
probability equals `2 * (codeBound k) ^ 2 / 2 ^ (6 * charBits n_max)`. -/
theorem failureProbBound_eq_of_ge {k n_max : ℕ} (hge : regimeThreshold ≤ n_max)
    (hk : 2 * codeBound k ≤ 2 ^ (3 * charBits n_max)) :
    failureProbBound k n_max =
      ((2 * (codeBound k) ^ 2 : ℕ) : ℝ≥0∞) / ((2 ^ (6 * charBits n_max) : ℕ) : ℝ≥0∞) :=
  ComplexityAbstracts.HashFamiliesBridge.failureProbBound_eq_of_ge hge hk

/-- In the double-tabulation regime (`n_max ≥ 2 ^ 320000`) under
`2 * codeBound k ≤ 2 ^ (3 * charBits n_max)`, the per-epoch failure probability is at most
`2 * (codeBound k) ^ 2 / max n_max 4 ^ 3 = O_k(1 / n_max ^ 3)`. -/
theorem failureProbBound_le_inv_cube_of_ge {k n_max : ℕ} (hge : regimeThreshold ≤ n_max)
    (hk : 2 * codeBound k ≤ 2 ^ (3 * charBits n_max)) :
    failureProbBound k n_max ≤
      ((2 * (codeBound k) ^ 2 : ℕ) : ℝ≥0∞) / ((max n_max 4 ^ 3 : ℕ) : ℝ≥0∞) :=
  ComplexityAbstracts.HashFamiliesBridge.failureProbBound_le_inv_cube_of_ge hge hk

/-! ## Headline Theorems -/

/-- **All-Capacity High-Independence Word-RAM Hash Family (`c_exp = 4`, Fresh Zeroed Memory)**:
For every independence parameter `k`, capacity `n_max`, key universe `U ≤ max n_max 4 ^ 4`, output
bit-width `M ≤ 4 * Nat.clog 2 (max n_max 4) + 5`, word width `w ≥ 2 * trinomialDeg U M`, and base
address `base` whose `space k n_max`-word region fits in `w`-bit machine words, there exist
23-register Word-RAM programs `p_init` and `p_op` such that from any word-bounded initial state
`(reg₀, mem₀)` with `reg₀ 22 = base`, `reg₀ 1 = n_max`, `reg₀ 2 = U`, `reg₀ 3 = M`, and
`mem₀ a = 0` on `[base, base + space k n_max)`:

1. **Initialization**: `p_init` halts within `initFreshTime k n_max U M` steps on every random
   branch (and in expected time), modifies memory only inside `[base, base + space k n_max)`, sets
   `reg 0 = base` and `reg 22 = base + space k n_max`, and produces an initial state distribution
   `ν₀` with empty transcript `[]`.
2. **Multi-operation execution and `k`-wise independence**: for every oblivious operation sequence
   `ops : List (Op U)`, `p_op` executes `ops` sequentially from `ν₀` (`RunsOps`) within
   `evalTimeBound k = O_k(1)` steps per `.eval u` (deterministically and without modifying memory)
   and `resampleTime k n_max` steps per `.resample`, and whenever every resampling epoch in `ops`
   queries at most `k` distinct keys (`BoundedEpochKeys k ops`), the resulting transcript
   distribution satisfies `WhpKWiseContract (failureProbBound k n_max) ops`. -/
theorem highIndependenceHashFamily_fresh :
    ∀ (k n_max U M w base : ℕ),
      U ≤ max n_max 4 ^ 4 →
      M ≤ 4 * Nat.clog 2 (max n_max 4) + 5 →
      2 * trinomialDeg U M ≤ w →
      base + space k n_max < 2 ^ w →
      max n_max 2 < 2 ^ w →
      max U 2 + 1 < 2 ^ w →
      ∃ (p_init p_op : List (Instr 23)),
        ∀ (reg₀ : Fin 23 → ℕ) (mem₀ : ℕ → ℕ),
          WordBounded w reg₀ mem₀ →
          reg₀ ⟨22, by decide⟩ = base →
          reg₀ ⟨1, by decide⟩ = n_max →
          reg₀ ⟨2, by decide⟩ = U →
          reg₀ ⟨3, by decide⟩ = M →
          (∀ a, base ≤ a → a < base + space k n_max → mem₀ a = 0) →
          ∃ ν₀ : PMF (SeqState U (2 ^ M)),
            let s₀ : State 23 := ⟨0, reg₀, mem₀⟩
            let T_init := initFreshTime k n_max U M
            HaltsWithin w p_init s₀ T_init ∧
            expectedTime w p_init s₀ ≤ (T_init : ℝ≥0∞) ∧
            evalRand w p_init T_init s₀ =
              ν₀.map (fun t => .halted (t.reg ⟨2, by decide⟩) t.reg t.mem) ∧
            (∀ t ∈ ν₀.support,
              t.transcript = [] ∧
              WordBounded w t.reg t.mem ∧
              t.reg ⟨0, by decide⟩ = base ∧
              t.reg ⟨22, by decide⟩ = base + space k n_max ∧
              UnchangedOutside base (space k n_max) mem₀ t.mem) ∧
            ∀ ops : List (Op U),
              ∃ ν_final : PMF (SeqState U (2 ^ M)),
                RunsOps w p_op base (space k n_max) (evalTimeBound k) (resampleTime k n_max)
                  ops ν₀ ν_final ∧
                (BoundedEpochKeys k ops →
                  WhpKWiseContract (failureProbBound k n_max) ops
                    (ν_final.map SeqState.transcript)) :=
  ComplexityAbstracts.HashFamiliesBridge.highIndependenceHashFamily_fresh
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
    ⟨Op, @Op.resample, @Op.eval, @Op.rec,
      Label, @Label.resample, @Label.eval, @Label.op,
      @epochKeys, @epochCount, @idealTranscriptFrom,
      @prepareRegs, @decodeLabel,
      SeqState, @SeqState.mk, @SeqState.reg, @SeqState.mem, @SeqState.transcript,
      StepResult, @StepResult.mk, @StepResult.reg, @StepResult.mem, @StepResult.label,
      @opBudget, @RunsOps⟩
    ⟨rfl, fun _ _ => rfl, rfl, fun _ => rfl, fun _ _ => rfl,
      rfl, fun _ => rfl, fun _ _ => rfl,
      fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, fun _ _ _ => rfl,
      fun _ => rfl, fun _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ => rfl, fun _ _ _ => rfl,
      @RunsOps.nil, @RunsOps.cons⟩

/-- **All-Capacity High-Independence Word-RAM Hash Family (`c_exp = 4`, Arbitrary Initial Memory)**:
Counterpart of `highIndependenceHashFamily_fresh` using the self-clearing initializer `p_initClear`,
which first zeroes `[base, base + space k n_max)` in `4 * space k n_max + 6` steps (`initClearTime`)
and therefore requires no zeroed-memory precondition on `mem₀`. -/
theorem highIndependenceHashFamily_clear :
    ∀ (k n_max U M w base : ℕ),
      U ≤ max n_max 4 ^ 4 →
      M ≤ 4 * Nat.clog 2 (max n_max 4) + 5 →
      2 * trinomialDeg U M ≤ w →
      base + space k n_max < 2 ^ w →
      max n_max 2 < 2 ^ w →
      max U 2 + 1 < 2 ^ w →
      ∃ (p_initClear p_op : List (Instr 23)),
        ∀ (reg₀ : Fin 23 → ℕ) (mem₀ : ℕ → ℕ),
          WordBounded w reg₀ mem₀ →
          reg₀ ⟨22, by decide⟩ = base →
          reg₀ ⟨1, by decide⟩ = n_max →
          reg₀ ⟨2, by decide⟩ = U →
          reg₀ ⟨3, by decide⟩ = M →
          ∃ ν₀ : PMF (SeqState U (2 ^ M)),
            let s₀ : State 23 := ⟨0, reg₀, mem₀⟩
            let T_init := initClearTime k n_max U M
            HaltsWithin w p_initClear s₀ T_init ∧
            expectedTime w p_initClear s₀ ≤ (T_init : ℝ≥0∞) ∧
            evalRand w p_initClear T_init s₀ =
              ν₀.map (fun t => .halted (t.reg ⟨2, by decide⟩) t.reg t.mem) ∧
            (∀ t ∈ ν₀.support,
              t.transcript = [] ∧
              WordBounded w t.reg t.mem ∧
              t.reg ⟨0, by decide⟩ = base ∧
              t.reg ⟨22, by decide⟩ = base + space k n_max ∧
              UnchangedOutside base (space k n_max) mem₀ t.mem) ∧
            ∀ ops : List (Op U),
              ∃ ν_final : PMF (SeqState U (2 ^ M)),
                RunsOps w p_op base (space k n_max) (evalTimeBound k) (resampleTime k n_max)
                  ops ν₀ ν_final ∧
                (BoundedEpochKeys k ops →
                  WhpKWiseContract (failureProbBound k n_max) ops
                    (ν_final.map SeqState.transcript)) :=
  ComplexityAbstracts.HashFamiliesBridge.highIndependenceHashFamily_clear
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
    ⟨Op, @Op.resample, @Op.eval, @Op.rec,
      Label, @Label.resample, @Label.eval, @Label.op,
      @epochKeys, @epochCount, @idealTranscriptFrom,
      @prepareRegs, @decodeLabel,
      SeqState, @SeqState.mk, @SeqState.reg, @SeqState.mem, @SeqState.transcript,
      StepResult, @StepResult.mk, @StepResult.reg, @StepResult.mem, @StepResult.label,
      @opBudget, @RunsOps⟩
    ⟨rfl, fun _ _ => rfl, rfl, fun _ => rfl, fun _ _ => rfl,
      rfl, fun _ => rfl, fun _ _ => rfl,
      fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, fun _ _ _ => rfl,
      fun _ => rfl, fun _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ => rfl, fun _ _ _ => rfl,
      @RunsOps.nil, @RunsOps.cons⟩

/--
info: abstract audit passed for `ComplexityAbstracts.HashFamiliesAbstract`: 421 root
declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.HashFamiliesAbstract

end ComplexityAbstracts.HashFamiliesAbstract
