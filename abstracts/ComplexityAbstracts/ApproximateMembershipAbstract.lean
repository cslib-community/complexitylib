/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.ApproximateMembershipBridge
import ComplexityAbstracts.Check
import Cslib.Probability.PMF
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Log

/-!
# Formal Abstract: Dynamic Approximate-Membership Filter with Deletions (Quotient Filter)

This self-contained file states the formal specification and expected per-operation time and space
theorems for the dynamic approximate-membership filter with deletions implemented by a two-stage
quotient filter on the randomized Word-RAM (`QuotientFilter.implOfEps`), following
`[PaghPaghRao2005]` (SODA 2005) and `[BenderEtAl2012]` (PVLDB 5(11), 2012), combined with
two-stage multiply-shift reduction and `5`-wise independent polynomial hashing with a bit-packed
Four-Russians multiplication table (`ReducedKWise.impl`; `[CarterWegman1979]`,
`[WegmanCarter1981]`, `[PaghPaghRuzic2009]`, `[Vadhan2012]`, `[LidlNiederreiter1997]`, and
`[DietzfelbingerHagerupKatajainenPenttonen1997]`).

## Scope, operation semantics, and cost accounting

The filter supports `insert u`, `delete u`, and `query u` over key universe `Fin U` up to capacity
`n ≥ 1` active keys (`ValidFilterSeq n`) across operation sequences `ops : List (FilterOp U)` of any
length. Under strict set semantics, `insert u` is valid when `u ∉ S` and fewer than `n` keys are
currently present (`S.card < n`), adding `u` to the active set `S`; `delete u` is valid when `u` is
currently present (`u ∈ S`), removing `u` from `S`; and `query u` is always valid and leaves `S`
unchanged.

For every valid fixed operation sequence `ops` of any length, on every random branch in
`μ_final.support`, every `query u` at index `i` where `u ∈ activeSetBefore ops i` returns `true`
(`NoFalseNegatives ops`). For every index `i` and absent key `u ∉ activeSetBefore ops i` with
`ops[i]? = some (.query u)`, the probability that step `i` returns `true`
(`FalsePositiveAt ops i u`) is at most `ε` (`FilterContract ε ops`), for any `ε ≠ 0` (in particular
for all `ε ∈ (0, 1 / 2]`).

To avoid any polynomial universe restriction `log₂ U ≤ c · log₂ n`, keys `u < U ≤ 2 ^ w₀`
(`2 * w₀ ≤ w`) are first reduced to `min w₀ (3 * b)` bits
(`b = qfQuotBits w₀ n = ⌈log₂(max (8 * min n (2 ^ w₀)) 8)⌉`, so `2 ^ b = O(min n (2 ^ w₀))`) by a
`2`-universal multiply-shift hash, then mapped to a `b`-bit quotient by a degree-`4` (`5`-wise
independent) polynomial over a binary trinomial field of degree `2 * 3 ^ t` evaluated in
`L = 2 * 3 ^ min t 3 ≤ 54 = O(1)` limbs using a bit-packed multiplication table of `o(2 ^ b)` bits.
An independent multiply-shift hash produces the `min w₀ (epsLog ε + 1)`-bit remainder. Runs are
maintained in canonical sorted order so that the set of occupied slots depends only on the current
active set `S` (no amortization and no seed conditioning across deletions).

There exist universal constants `r ≥ 248` (register count) and `C_op : ℕ` (per-operation expected
instruction budget) such that the compiled `r`-register programs `p_init` and `p_op` are chosen per
`(w, w₀, n, ε)` (independent of `U` and `base`), with no static code-size bound. The instruction
bounds `qfInitSteps w₀ n` and `C_op = O(1)` count executed body instructions, excluding the final
`halt` step (accounted for as `T + 1` in `ExecProgramDist`) and caller argument delivery
(`prepareFilterRegs`). Every individual operation in `ExecFilterOps` executes in at most `C_op`
expected body instructions (`(∑' p, μ p * T_step p) ≤ C_op` at every step, not merely amortized over
the sequence). All hash seeds, the bit-packed multiplication table, and the bit-packed `(f + 3)`-bit
slot array reside in a single contiguous memory block `[base, base + qfSpaceOfEps w w₀ n ε)` of at
most `640 * ((n * epsLog ε + w - 1) / w + 1)` machine words.

A reader only needs to inspect the definitions and theorem statements in this file to verify that
the formalization proves the intended mathematical claims; Lean verifies the proofs through
`ComplexityAbstracts.ApproximateMembershipBridge`, and `#check_abstract` audits the dependency
boundary.
-/

namespace ComplexityAbstracts.ApproximateMembershipAbstract

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

/-! ## Dynamic Approximate-Membership Filter Specification -/

/-- Operations on a dynamic approximate-membership filter over key universe `Fin U`:
- `insert u`: insert key `u : Fin U` into the active set;
- `delete u`: remove key `u : Fin U` from the active set (valid when `u` is currently present);
- `query u`: test whether key `u : Fin U` is currently present. -/
inductive FilterOp (U : ℕ) : Type where
  | insert (u : Fin U) : FilterOp U
  | delete (u : Fin U) : FilterOp U
  | query (u : Fin U) : FilterOp U

/-- Underlying key `Fin U` of a filter operation `o : FilterOp U`. -/
def FilterOp.key {U : ℕ} : FilterOp U → Fin U
  | .insert u => u
  | .delete u => u
  | .query u => u

/-- Numeric operation tag (`0 = insert`, `1 = delete`, `2 = query`). -/
def FilterOp.tag {U : ℕ} : FilterOp U → ℕ
  | .insert _ => 0
  | .delete _ => 1
  | .query _ => 2

/-- Update the exact active key set `S : Finset (Fin U)` under one filter operation:
- `insert u` adds `u` (`Insert.insert u S`);
- `delete u` removes `u` (`S.erase u`);
- `query u` leaves `S` unchanged. -/
def stepSet {U : ℕ} (S : Finset (Fin U)) : FilterOp U → Finset (Fin U)
  | .insert u => Insert.insert u S
  | .delete u => S.erase u
  | .query _ => S

/-- Active key set after executing a sequence of operations `ops` starting from `S`. -/
def activeSetFrom {U : ℕ} (S : Finset (Fin U)) : List (FilterOp U) → Finset (Fin U)
  | [] => S
  | o :: os => activeSetFrom (stepSet S o) os

/-- Active key set after executing `ops` starting from the empty set `∅`. -/
def activeSet {U : ℕ} (ops : List (FilterOp U)) : Finset (Fin U) :=
  activeSetFrom ∅ ops

/-- Active key set immediately before step `i` (`0`-indexed) of `ops`. -/
def activeSetBefore {U : ℕ} (ops : List (FilterOp U)) (i : ℕ) : Finset (Fin U) :=
  activeSet (ops.take i)

/-- Admissibility of a single filter operation `o` from active set `S` under capacity `n`:
- `insert u` requires `u ∉ S ∧ S.card < n` (`u` is currently absent and fewer than `n` keys are
  present);
- `delete u` requires `u ∈ S` (only currently present keys may be deleted);
- `query u` is always admissible. -/
def ValidFilterOp {U : ℕ} (n : ℕ) (S : Finset (Fin U)) : FilterOp U → Prop
  | .insert u => u ∉ S ∧ S.card < n
  | .delete u => u ∈ S
  | .query _ => True

/-- Admissibility of an operation sequence `ops` starting from active set `S` under capacity `n`. -/
def ValidFilterSeqFrom {U : ℕ} (n : ℕ) : Finset (Fin U) → List (FilterOp U) → Prop
  | _, [] => True
  | S, o :: os => ValidFilterOp n S o ∧ ValidFilterSeqFrom n (stepSet S o) os

/-- Admissibility of an oblivious operation sequence `ops` starting from the empty filter `∅` under
capacity `n`. -/
def ValidFilterSeq {U : ℕ} (n : ℕ) (ops : List (FilterOp U)) : Prop :=
  ValidFilterSeqFrom n ∅ ops

/-- Transcript of an operation sequence: each entry `(o, ans)` records the executed operation
`o : FilterOp U` together with its Boolean observation `ans` (`false` for `insert` and `delete`,
and the query response `true` = "present" / `false` = "absent" for `query`). -/
abbrev FilterTranscript (U : ℕ) : Type :=
  List (FilterOp U × Bool)

/-- A transcript `tr` matches the operation sequence `ops` when its recorded operations equal `ops`.
-/
def TranscriptMatches {U : ℕ} (ops : List (FilterOp U)) (tr : FilterTranscript U) : Prop :=
  tr.map Prod.fst = ops

/-- Zero false negatives: for every step `i` and key `u`, if operation `i` is `query u` and `u` is
in the active set `activeSetBefore ops i`, the transcript records `true`. -/
def NoFalseNegatives {U : ℕ} (ops : List (FilterOp U)) (tr : FilterTranscript U) : Prop :=
  ∀ (i : ℕ) (u : Fin U),
    ops[i]? = some (.query u) →
    u ∈ activeSetBefore ops i →
    tr[i]? = some (.query u, true)

/-- False-positive event at step `i` for key `u`: operation `i` is `query u`, `u` is absent from
`activeSetBefore ops i`, and the transcript records `true`. -/
def FalsePositiveAt {U : ℕ} (ops : List (FilterOp U)) (i : ℕ) (u : Fin U)
    (tr : FilterTranscript U) : Prop :=
  ops[i]? = some (.query u) ∧
  u ∉ activeSetBefore ops i ∧
  tr[i]? = some (.query u, true)

/-- Distributional correctness contract for an approximate-membership filter with false-positive
rate `ε` on an oblivious operation sequence `ops`: every transcript in `μ.support` matches `ops` and
has zero false negatives, and for every step `i` and absent key `u ∉ activeSetBefore ops i` with
`ops[i]? = some (.query u)`, the probability of `FalsePositiveAt ops i u` under `μ` is at most
`ε`. -/
def FilterContract {U : ℕ} (ε : ℝ≥0∞) (ops : List (FilterOp U))
    (μ : PMF (FilterTranscript U)) : Prop :=
  (∀ tr ∈ μ.support, TranscriptMatches ops tr ∧ NoFalseNegatives ops tr) ∧
  ∀ (i : ℕ) (u : Fin U),
    ops[i]? = some (.query u) →
    u ∉ activeSetBefore ops i →
    μ.toOuterMeasure {tr | FalsePositiveAt ops i u tr} ≤ ε

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

/-- Machine state coupled with a latent random seed `seed : Seed` and the accumulated operation
transcript `transcript : FilterTranscript U`. -/
structure CoupledOutcome (Seed : Type) (U r : ℕ) where
  seed : Seed
  reg : Fin r → ℕ
  mem : ℕ → ℕ
  transcript : FilterTranscript U

/-- Project a coupled outcome to its register bank and memory snapshot. -/
def CoupledOutcome.toRegMem {Seed : Type} {U r : ℕ}
    (p : CoupledOutcome Seed U r) : RegMem r :=
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

/-- Calling-convention register assignment for a filter operation `o : FilterOp U` on an
`r`-register Word-RAM with key register `keyReg` and operation-tag register `tagReg`:
- `keyReg` receives `o.key.val`;
- `tagReg` receives `o.tag` (`0` for `insert`, `1` for `delete`, and `2` for `query`);
- every other register `i` is preserved (`reg i`). -/
def prepareFilterRegs {r U : ℕ} (keyReg tagReg : Fin r) (o : FilterOp U)
    (reg : Fin r → ℕ) (i : Fin r) : ℕ :=
  if i = keyReg then
    o.key.val
  else if i = tagReg then
    o.tag
  else
    reg i

/-- Decode the post-operation register bank `reg` for operation `o : FilterOp U` with output
register `outReg` into a transcript entry `FilterOp U × Bool`:
- `(insert u, false)` for `insert u`;
- `(delete u, false)` for `delete u`;
- `(query u, decide (reg outReg = 1))` for `query u`. -/
def decodeFilterEntry {r U : ℕ} (outReg : Fin r) (o : FilterOp U)
    (reg : Fin r → ℕ) : FilterOp U × Bool :=
  match o with
  | .insert u => (.insert u, false)
  | .delete u => (.delete u, false)
  | .query u => (.query u, decide (reg outReg = 1))

/-- Sequential multi-operation execution of `ops : List (FilterOp U)` by the Word-RAM operation
program `p_op : Program r` at word width `w`, with calling-convention registers
`(keyReg, tagReg, outReg)`, allocated memory block `[base, base + sp)`, and per-operation expected
body-instruction bound `opCharge`. The `nil` case leaves `μ` unchanged with `0` expected operation
steps. In the `cons` case, from every supported coupled state `p ∈ μ.support`, running `p_op` after
preparing `prepareFilterRegs keyReg tagReg o p.reg` executes with distribution
`(μ_step p).map CoupledOutcome.toRegMem` and expected body-instruction count `T_step p`
(`ExecProgramDist`), every resulting state `q ∈ (μ_step p).support` is `w`-bit word-bounded,
appends `decodeFilterEntry outReg o q.reg` to `p.transcript`, and leaves memory outside
`[base, base + sp)` unchanged, and the expected body-instruction count of this single operation
satisfies `(∑' p, μ p * T_step p) ≤ (opCharge : ℝ≥0∞)` (per-operation expected time, not
amortized). -/
inductive ExecFilterOps {Seed : Type} {r U : ℕ}
    (w : ℕ) (p_op : Program r) (keyReg tagReg outReg : Fin r) (base sp opCharge : ℕ) :
    List (FilterOp U) →
    PMF (CoupledOutcome Seed U r) → PMF (CoupledOutcome Seed U r) → ℝ≥0∞ → Prop where
  | nil (μ : PMF (CoupledOutcome Seed U r)) :
      ExecFilterOps w p_op keyReg tagReg outReg base sp opCharge [] μ μ 0
  | cons {o : FilterOp U} {ops : List (FilterOp U)}
      {μ μ_final : PMF (CoupledOutcome Seed U r)} {T_rest : ℝ≥0∞}
      (T_step : CoupledOutcome Seed U r → ℝ≥0∞)
      (μ_step : CoupledOutcome Seed U r → PMF (CoupledOutcome Seed U r))
      (hstep : ∀ p ∈ μ.support,
        ExecProgramDist w p_op outReg
          (prepareFilterRegs keyReg tagReg o p.reg) p.mem
          ((μ_step p).map CoupledOutcome.toRegMem) (T_step p) ∧
        ∀ q ∈ (μ_step p).support,
          WordBounded w q.reg q.mem ∧
          q.transcript = p.transcript ++ [decodeFilterEntry outReg o q.reg] ∧
          UnchangedOutside base sp p.mem q.mem)
      (hcharge : (∑' p, μ p * T_step p) ≤ (opCharge : ℝ≥0∞))
      (hrest : ExecFilterOps w p_op keyReg tagReg outReg base sp opCharge
        ops (μ.bind μ_step) μ_final T_rest) :
      ExecFilterOps w p_op keyReg tagReg outReg base sp opCharge
        (o :: ops) μ μ_final ((∑' p, μ p * T_step p) + T_rest)

/-! ## Two-Stage Quotient Filter Parameters and Headline Theorems -/

/-- Structural recursion helper computing the smallest `t : ℕ` with `2 * 3 ^ t ≥ B`. -/
def trinomialStepLoop (fuel : ℕ) : ℕ → ℕ :=
  Nat.rec (fun _ => 0)
    (fun _ ih B => if B ≤ 2 then 0 else ih ((B + 2) / 3) + 1)
    fuel

/-- Effective capacity `min n (2 ^ w₀)`. -/
def qfEffCap (w₀ n : ℕ) : ℕ :=
  min n (2 ^ w₀)

/-- Quotient bit-width `b = ⌈log₂(max (8 * min n (2 ^ w₀)) 8)⌉`: chooses `2 ^ b = O(min n (2 ^ w₀))`
slots at load factor `α ≤ 1 / 8`. -/
def qfQuotBits (w₀ n : ℕ) : ℕ :=
  Nat.clog 2 (max (8 * qfEffCap w₀ n) 8)

/-- Remainder bit-width `f = min w₀ (k + 1)` for error exponent `k` (`k + 1` bits, capped at the
key bit-width `w₀` when storing keys exactly). -/
def qfRemBits (w₀ k : ℕ) : ℕ :=
  min w₀ (k + 1)

/-- Log₂ of the number of `d`-bit entries packed per `w`-bit word in a `2 ^ b`-slot array. -/
def qfSlotPackShift (b d w : ℕ) : ℕ :=
  min b (Nat.log 2 (w / (2 * d)))

/-- Number of `w`-bit words `2 ^ (b - qfSlotPackShift b d w)` used by a `2 ^ b`-slot packed array
of `d`-bit entries. -/
def qfPackedWords (b d w : ℕ) : ℕ :=
  2 ^ (b - qfSlotPackShift b d w)

/-- Target bit-width `max (min w₀ (3 * b)) (max b' 1)` for the second-stage trinomial field. -/
def qfReducedTargetBits (w₀ b b' : ℕ) : ℕ :=
  max (min w₀ (3 * b)) (max b' 1)

/-- Trinomial step parameter `t` for reduced `min w₀ (3 * b)`-bit keys and `b'`-bit outputs. -/
def qfReducedStep (w₀ b b' : ℕ) : ℕ :=
  let B := qfReducedTargetBits w₀ b b'
  trinomialStepLoop B B

/-- Limb bit-width `c = 3 ^ (t - 3)` for trinomial step parameter `t`. -/
def qfReducedChunkBits (t : ℕ) : ℕ :=
  3 ^ (t - 3)

/-- Full-field limb count `L = 2 * 3 ^ min t 3 ≤ 54` for trinomial step parameter `t`. -/
def qfReducedLimbCount (t : ℕ) : ℕ :=
  2 * 3 ^ min t 3

/-- Log₂ of the number of `2 * c`-bit entries packed into each `w`-bit word. -/
def qfReducedPackShift (t w : ℕ) : ℕ :=
  min (2 * qfReducedChunkBits t) (Nat.log 2 (w / (2 * qfReducedChunkBits t)))

/-- Number of machine words `2 ^ (2 * c - p)` occupied by the bit-packed Four-Russians table. -/
def qfReducedTableWords (t w : ℕ) : ℕ :=
  2 ^ (2 * qfReducedChunkBits t - qfReducedPackShift t w)

/-- Number of seed words `1 + k * L` (`1` word for the multiply-shift reduction seed plus `k * L`
words for the `c`-bit limbs of the `k` polynomial coefficients). -/
def qfReducedSeedWords (w₀ b b' k : ℕ) : ℕ :=
  1 + k * qfReducedLimbCount (qfReducedStep w₀ b b')

/-- Memory footprint (in machine words) of the two-stage `k`-wise polynomial hash block. -/
def qfReducedKWiseSpace (w w₀ b b' k : ℕ) : ℕ :=
  qfReducedSeedWords w₀ b b' k + qfReducedTableWords (qfReducedStep w₀ b b') w

/-- Total memory footprint (in machine words) of the two-stage quotient filter with error exponent
`k`: the two-stage `5`-wise quotient hash block, `1` word for the independent multiply-shift
remainder seed, three `1`-bit packed slot arrays (`isFull`, `isOcc`, `isRunStart`), and one
`f`-bit packed remainder array (`remAt`). -/
def qfSpace (w w₀ n k : ℕ) : ℕ :=
  let b := qfQuotBits w₀ n
  let f := qfRemBits w₀ k
  qfReducedKWiseSpace w w₀ b b 5 + 1 + 3 * qfPackedWords b 1 w + qfPackedWords b f w

/-- Error-exponent selector `k = max 1 ⌈log₂ ⌈ε⁻¹.toNNReal⌉₊⌉` for false-positive target
`ε : ℝ≥0∞`, satisfying `(1 / 2 : ℝ≥0∞) ^ epsLog ε ≤ ε` for every `ε ≠ 0`. -/
noncomputable def epsLog (ε : ℝ≥0∞) : ℕ :=
  max 1 (Nat.clog 2 ⌈ε⁻¹.toNNReal⌉₊)

/-- Total memory footprint `qfSpace w w₀ n (epsLog ε)` (in machine words) of the two-stage
quotient filter for false-positive target `ε`. -/
noncomputable def qfSpaceOfEps (w w₀ n : ℕ) (ε : ℝ≥0∞) : ℕ :=
  qfSpace w w₀ n (epsLog ε)

/-- Across all capacities `n ≥ 1`, error exponents `k ≥ 1`, key bit-widths `w₀ ≥ 1`, and word
widths `w ≥ 2 * w₀` with `qfQuotBits w₀ n ≤ w`, the two-stage quotient filter uses at most
`640 * ((n * k + w - 1) / w + 1) = O(⌈n · k / w⌉ + 1)` machine words including all hash seeds and
lookup tables. -/
theorem qfSpace_le {w w₀ n k : ℕ}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hb : qfQuotBits w₀ n ≤ w)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    qfSpace w w₀ n k ≤ 640 * ((n * k + w - 1) / w + 1) :=
  ComplexityAbstracts.ApproximateMembershipBridge.qfSpace_le hw₀_pos hw hb hn hk

/-- Across all capacities `n ≥ 1`, false-positive targets `ε : ℝ≥0∞`, key bit-widths `w₀ ≥ 1`, and
word widths `w ≥ 2 * w₀` with `qfQuotBits w₀ n ≤ w`, the two-stage quotient filter uses at most
`640 * ((n * epsLog ε + w - 1) / w + 1) = O(⌈n · log₂(1 / ε) / w⌉ + 1)` machine words including all
hash seeds and lookup tables. -/
theorem qfSpaceOfEps_le {w w₀ n : ℕ} {ε : ℝ≥0∞}
    (hw₀_pos : 0 < w₀) (hw : 2 * w₀ ≤ w) (hb : qfQuotBits w₀ n ≤ w)
    (hn : 1 ≤ n) :
    qfSpaceOfEps w w₀ n ε ≤ 640 * ((n * epsLog ε + w - 1) / w + 1) :=
  ComplexityAbstracts.ApproximateMembershipBridge.qfSpaceOfEps_le hw₀_pos hw hb hn

/-- Deterministic instruction budget for initializing the bit-packed Four-Russians multiplication
table of the two-stage `k`-wise hash. -/
def qfReducedInitTableSteps (w₀ b b' : ℕ) : ℕ :=
  31 * 2 ^ (2 * qfReducedChunkBits (qfReducedStep w₀ b b')) + 13

/-- Expected instruction count for initializing the two-stage quotient filter from zeroed memory. -/
def qfInitSteps (w₀ n : ℕ) : ℕ :=
  let b := qfQuotBits w₀ n
  3 + (qfReducedInitTableSteps w₀ b b + (5 * qfReducedSeedWords w₀ b b 5 + 13 + 5))

/-- Two-Stage Quotient Filter with Deletions (`QuotientFilter.implOfEps` and
`QuotientFilter.implOfEps_space_le`). There exist universal constants `r ≥ 248` (register count)
and `C_op : ℕ` (per-operation expected instruction budget) such that for every word width `w`, key
bit-width `w₀`, capacity `n`, and false-positive target `ε : ℝ≥0∞`, there exist `r`-register
Word-RAM programs `p_init` and `p_op` chosen per `(w, w₀, n, ε)` (independent of `U` and `base`,
with no static code-size bound) such that for every key universe `U` and base address `base`
satisfying `ε ≠ 0` (including all `ε ∈ (0, 1 / 2]`), `1 ≤ n`, `0 < w₀`, `2 * w₀ ≤ w`,
`U ≤ 2 ^ w₀`, and `base + qfSpaceOfEps w w₀ n ε < 2 ^ w`:

The single allocated memory block of `qfSpaceOfEps w w₀ n ε` words (holding all hash seeds, the
bit-packed multiplication table, and the bit-packed slot array) uses at most
`640 * ((n * epsLog ε + w - 1) / w + 1)` machine words. From any word-bounded initial state
`(reg₀, mem₀)` with `reg₀ 240 = base` and zeroed memory in `[base, base + qfSpaceOfEps w w₀ n ε)`,
there exists an initial coupled distribution `μ_init` (chosen before any operation sequence `ops`)
initialized in `qfInitSteps w₀ n` expected executed body instructions, with `p.reg 0 = base`,
`p.reg 240 = base + qfSpaceOfEps w w₀ n ε`, `p.transcript = []`, and memory outside
`[base, base + qfSpaceOfEps w w₀ n ε)` unchanged.

For every oblivious operation sequence `ops : List (FilterOp U)` of any length satisfying
`ValidFilterSeq n ops`, `p_op` executes `ops` sequentially (`ExecFilterOps`) with expected executed
body-instruction count at most `C_op = O(1)` for every individual operation in `ops` (and total
expected body instructions `T_ops ≤ ops.length * C_op`, excluding final `halt` and caller argument
delivery), zero false negatives on every branch (`NoFalseNegatives ops`), and false-positive
probability at most `ε` for every query of an absent key (`FilterContract ε ops`).

References: `[PaghPaghRao2005]` (SODA 2005, pp. 823–829); `[BenderEtAl2012]` (PVLDB 5(11):1627–1637,
2012); `[PaghPaghRuzic2009]` (*SIAM J. Comput.* 39(3):1107–1120, 2009);
`[DietzfelbingerHagerupKatajainenPenttonen1997]`; `[CarterWegman1979]`; `[WegmanCarter1981]`;
`[Vadhan2012]`; `[LidlNiederreiter1997]`. -/
theorem quotientFilter :
    ∃ (r C_op : ℕ) (hr : 248 ≤ r),
      ∀ (w w₀ n : ℕ) (ε : ℝ≥0∞),
        ∃ (p_init p_op : List (Instr r)),
          ∀ (U base : ℕ),
            ε ≠ 0 →
            1 ≤ n →
            0 < w₀ →
            2 * w₀ ≤ w →
            U ≤ 2 ^ w₀ →
            base + qfSpaceOfEps w w₀ n ε < 2 ^ w →
            qfSpaceOfEps w w₀ n ε ≤ 640 * ((n * epsLog ε + w - 1) / w + 1) ∧
            ∀ (reg₀ : Fin r → ℕ) (mem₀ : ℕ → ℕ),
              WordBounded w reg₀ mem₀ →
              reg₀ ⟨240, by omega⟩ = base →
              (∀ a, base ≤ a → a < base + qfSpaceOfEps w w₀ n ε → mem₀ a = 0) →
              ∃ (Seed : Type) (μ_init : PMF (CoupledOutcome Seed U r)),
                ExecProgramDist w p_init ⟨1, by omega⟩ reg₀ mem₀
                  (μ_init.map CoupledOutcome.toRegMem) (qfInitSteps w₀ n) ∧
                (∀ p ∈ μ_init.support,
                  WordBounded w p.reg p.mem ∧
                  p.reg ⟨0, by omega⟩ = base ∧
                  p.reg ⟨240, by omega⟩ = base + qfSpaceOfEps w w₀ n ε ∧
                  p.transcript = [] ∧
                  UnchangedOutside base (qfSpaceOfEps w w₀ n ε) mem₀ p.mem) ∧
                ∀ ops : List (FilterOp U),
                  ValidFilterSeq n ops →
                  ∃ (μ_final : PMF (CoupledOutcome Seed U r)) (T_ops : ℝ≥0∞),
                    ExecFilterOps w p_op
                      ⟨1, by omega⟩ ⟨247, by omega⟩ ⟨1, by omega⟩
                      base (qfSpaceOfEps w w₀ n ε) C_op ops
                      μ_init μ_final T_ops ∧
                    FilterContract ε ops (μ_final.map CoupledOutcome.transcript) ∧
                    T_ops ≤ ((ops.length * C_op : ℕ) : ℝ≥0∞) :=
  ComplexityAbstracts.ApproximateMembershipBridge.quotientFilter
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
    ⟨FilterOp, @FilterOp.insert, @FilterOp.delete, @FilterOp.query, @FilterOp.rec,
      @FilterOp.key, @FilterOp.tag,
      @stepSet, @activeSetFrom, @ValidFilterOp, @ValidFilterSeqFrom, @FilterContract,
      RegMem, @RegMem.mk, @RegMem.reg, @RegMem.mem,
      CoupledOutcome, @CoupledOutcome.mk, @CoupledOutcome.seed, @CoupledOutcome.reg,
      @CoupledOutcome.mem, @CoupledOutcome.transcript,
      @prepareFilterRegs, @decodeFilterEntry, @ExecFilterOps⟩
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl,
      fun _ => rfl, fun _ => rfl, fun _ => rfl,
      fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
      fun _ _ _ => Iff.rfl,
      fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
      fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ _ _ => rfl, fun _ => rfl,
      fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      @ExecFilterOps.nil, @ExecFilterOps.cons⟩

/--
info: abstract audit passed for `ComplexityAbstracts.ApproximateMembershipAbstract`: 401 root
declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.ApproximateMembershipAbstract

end ComplexityAbstracts.ApproximateMembershipAbstract
