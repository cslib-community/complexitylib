/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Program
public import Complexity.Crypto.Protocols.MPC.SharedMul
public import Complexity.Foundations.Data.BitString.Block
public import Cslib.Computability.Circuit.Boolean.Basic

/-!
# Multi-Party Boolean Circuit Evaluation in the Shared-Multiplication Hybrid Model

This module formalizes the $m$-party Boolean circuit-evaluation protocol and its perfect
semi-honest privacy reduction, adapted from Goldreich's *Foundations of Cryptography, Volume 2:
Basic Applications*, Section 7.5.2.3 (Construction 7.5.10 and Proposition 7.5.11, print pp. 705–707;
generalizing the 2-party protocol of Section 7.3.4, Construction 7.3.9 and Proposition 7.3.10,
print pp. 645–648):

1. **Deterministic $m$-Party Circuit Functionality (`circuitFunctionality`):**
   packs `m` party inputs `x : (i : Fin m) → BitString n` into `BitString (m * n)` via
   `Cslib.BitString.blocksEquiv.symm`, evaluates a De Morgan circuit
   `C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k)` under `Boolean.interpretation`,
   and unpacks the `m * k` output bits into `(i : Fin m) → BitString k` via
   `Cslib.BitString.block`.
2. **GMW Circuit-Evaluation Protocol (`gmwCircuitSchedule`, `gmwCircuitProtocol`):**
   in the `sharedMulSpec m`-hybrid model (Section 7.5.2, Eqs. 7.44–7.45, print p. 701):
   - **Step 1 (Input sharing):** each party `s : Fin m` samples private coins
     `c s : Fin n → Fin (m - 1) → Bool`, forms `m` additive shares of its input `x s : BitString n`
     via `ProbComp.completeShares` (placing the completing share at party `m - 1`, i.e.,
     `⊤ : Fin m`, rather than at sender `s`), and sends party `r`'s share over a pairwise private
     `.message s r (BitString n)` round across `allPairs m` (including `(s, s)` self-messages).
   - **Step 2 (Gate-by-gate circuit emulation):** evaluates `C.program` gate by gate, preserving
     the invariant that the sum of all `m` parties' shares of every wire equals the true wire
     value in `C.program.trace Boolean.interpretation (BitString.blocksEquiv.symm x)`. Whereas
     Construction 7.5.10 is stated for arithmetic circuits over $\mathrm{GF}(2)$ with addition and
     multiplication gates, `Cslib.Circuits.Circuit Boolean.signature` uses the De Morgan basis
     (`const`, `not`, `and`, `or`): constant and negation gates are evaluated locally (with
     party `0` holding the constant offset via `constShare`), while conjunction (`.and`) and
     disjunction (`.or`, via $a \lor b = a + b + a \cdot b$ over $\mathrm{GF}(2)$) invoke
     `sharedMulSpec m`.
   - **Step 3 (Output share refresh and reconstruction — adaptation of Construction 7.5.10
     Step 3):** in Goldreich's Construction 7.5.10 Step 3 (print p. 706), parties exchange their
     output-wire shares directly via `.message` rounds under the circuit convention (print p. 705)
     that the output wires are the last, distinct gate wires of the circuit. Because
     `Cslib.Circuits.Circuit.outputs : Fin (m * k) → Wire (m * n) C.size` allows arbitrary wire
     references (including input wires, negated wires, or wires reused across multiple outputs),
     `singleCoordSteps` / `outputSteps` first refreshes the shares of each output coordinate
     `(r, j) : Fin m × Fin k` via one `sharedMulSpec m` call (multiplying by `constShare true`)
     before sending all `m` refreshed shares to recipient party `r` via `.message s r Bool` rounds
     (including `s = r`) so party `r` reconstructs `circuitFunctionality m n k C x r`.
3. **Perfect Semi-Honest Privacy (`gmwCircuitSim`, `perfectSemiHonestPrivate_gmwCircuit`):**
   proves Proposition 7.5.11 (print pp. 706–707), adapted to include the Step 3 share refresh so
   that `gmwCircuitProtocol m n k C` perfectly and privately computes
   `Functionality.ofDeterministic (circuitFunctionality m n k C)` in `sharedMulWorld m` against
   every static coalition `I : Finset (Fin m)` for every circuit `C` without syntactic restrictions
   on `C.outputs`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.circuitFunctionality`: deterministic $m$-party functionality computed
  by a Boolean circuit `C`.
* `Cslib.Crypto.Protocols.MPC.gmwCircuitSchedule`,
  `Cslib.Crypto.Protocols.MPC.gmwCircuitProtocol`: Construction 7.5.10 (print p. 706), adapted to
  De Morgan gates and arbitrary `Circuit.outputs` via Step 3 share refresh.
* `Cslib.Crypto.Protocols.MPC.gmwCircuitSim`: coalition simulator for `gmwCircuitProtocol`.

## Main results

* `Cslib.Crypto.Protocols.MPC.snd_eq_circuitFunctionality_of_mem_support_evalWith`: perfect output
  correctness of `gmwCircuitProtocol m n k C` in `sharedMulWorld m`.
* `Cslib.Crypto.Protocols.MPC.perfectSemiHonestPrivate_gmwCircuit`: Proposition 7.5.11 (print
  pp. 706–707), perfect semi-honest privacy of `gmwCircuitProtocol m n k C` in `sharedMulWorld m`
  against every static coalition `I : Finset (Fin m)`.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.3.4 (Construction 7.3.9, Proposition 7.3.10, pp. 645–649), Section 7.5.1.2
  (Definition 7.5.1, Eqs. 7.39–7.40, p. 696), Section 7.5.2 (Eqs. 7.44–7.45, p. 701), and
  Section 7.5.2.3 (Construction 7.5.10, Proposition 7.5.11, pp. 705–707).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp Cslib.Circuits

/-! ### Deterministic multi-party circuit functionality -/

/-- Deterministic `m`-party Boolean circuit functionality (Goldreich Section 7.5.2.3, p. 705;
cf. Section 7.3.4, pp. 645–646): packs the `m` party inputs `x : (i : Fin m) → BitString n` into
`BitString (m * n)` via `BitString.blocksEquiv.symm`, evaluates `C` under `Boolean.interpretation`,
and unpacks the `m * k` output bits into `(i : Fin m) → BitString k` via `BitString.block`. -/
@[expose] def circuitFunctionality (m n k : ℕ)
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k))
    (x : (i : Fin m) → BitString n) : (i : Fin m) → BitString k :=
  fun i => BitString.block (C.eval Boolean.interpretation (BitString.blocksEquiv.symm x)) i

namespace GMWCircuit

/-! ### Step 1: Input sharing via all-to-all point-to-point messages -/

/-- All ordered sender-receiver pairs `(s, r) : Fin m × Fin m` (including `(s, s)` self-pairs). -/
@[expose] def allPairs (m : ℕ) : List (Fin m × Fin m) :=
  (List.finRange m).flatMap fun s => (List.finRange m).map fun r => (s, r)

/-- Point-to-point message round from `p.1` to `p.2` carrying `Msg`. -/
@[expose, reducible] def msgRound {m : ℕ} {spec : MultiOracleSpec} (Msg : Type)
    (p : Fin m × Fin m) : Round m spec :=
  .message p.1 p.2 Msg

/-- Schedule of point-to-point message rounds along `L : List (Fin m × Fin m)`. -/
@[expose, reducible] def msgSchedule {m : ℕ} {spec : MultiOracleSpec} (Msg : Type)
    (L : List (Fin m × Fin m)) : Schedule m spec :=
  L.map (msgRound Msg)

/-- Schedule of all-to-all point-to-point messages of type `Msg`. -/
@[expose, reducible] def allToAllSchedule (m : ℕ) {spec : MultiOracleSpec} (Msg : Type) :
    Schedule m spec :=
  msgSchedule Msg (allPairs m)

/-- Extract party `i`'s inbox update from message round `p = (s, r)`. -/
@[expose] def extractMsg {m : ℕ} {spec : MultiOracleSpec} {Msg : Type} [Zero Msg]
    (p : Fin m × Fin m) (i : Fin m)
    (recv : (msgRound (spec := spec) Msg p).Received i) : Fin m → Msg :=
  if h : i = p.2 then Pi.single p.1 (recv h) else 0

/-- Execute point-to-point message rounds along `L`, accumulating received messages into `st.2`
and applying `finish` at `.done`. -/
@[expose] def msgStepsWith {m : ℕ} {spec : MultiOracleSpec} {Msg : Type} [AddCommMonoid Msg]
    {Out : Fin m → Type} (finish : (i : Fin m) → (Fin m → Msg) → Out i) :
    (L : List (Fin m × Fin m)) →
      Steps (fun _ : Fin m => (Fin m → Msg) × (Fin m → Msg))
        Out (msgSchedule (spec := spec) Msg L)
  | [] => .done (fun i st => finish i st.2)
  | p :: L =>
    .message (sender := p.1) (receiver := p.2)
      (fun st => st.1 p.2)
      ((msgStepsWith finish L).mapState fun i st =>
        (st.1.1, st.1.2 + extractMsg p i st.2))

/-- All-to-all message exchange: party `s` sends `toSend s r` to party `r`, and party `i` applies
`finish i` to the vector `fun s => toSend s i` of received messages. -/
@[expose] def allToAllStepsWith (m : ℕ) {spec : MultiOracleSpec} {Msg : Type} [AddCommMonoid Msg]
    {Out : Fin m → Type} (finish : (i : Fin m) → (Fin m → Msg) → Out i) :
    Steps (fun _ : Fin m => Fin m → Msg) Out (allToAllSchedule m (spec := spec) Msg) :=
  (msgStepsWith finish (allPairs m)).mapState (fun _ toSend => (toSend, 0))

/-- Sum of party `i`'s received message updates along `L`. -/
private def sumReceivedMsgs {m : ℕ} {spec : MultiOracleSpec} {Msg : Type} [AddCommMonoid Msg] :
    (L : List (Fin m × Fin m)) → (i : Fin m) →
      (msgSchedule (spec := spec) Msg L).Received i → Fin m → Msg
  | [], _, _ => 0
  | p :: L, i, r => extractMsg p i r.1 + sumReceivedMsgs L i r.2

@[simp] private theorem outputAt_msgStepsWith {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {Out : Fin m → Type}
    (finish : (i : Fin m) → (Fin m → Msg) → Out i)
    (L : List (Fin m × Fin m)) (i : Fin m)
    (st_i : (Fin m → Msg) × (Fin m → Msg))
    (recv_i : (msgSchedule (spec := spec) Msg L).Received i) :
    (msgStepsWith finish L).outputAt i st_i recv_i =
      finish i (st_i.2 + sumReceivedMsgs L i recv_i) := by
  induction L generalizing st_i with
  | nil =>
    cases recv_i
    simp [msgStepsWith, Steps.outputAt, sumReceivedMsgs]
  | cons p L ih =>
    rcases recv_i with ⟨r_head, r_tail⟩
    simp [msgStepsWith, Steps.outputAt, ih, sumReceivedMsgs, add_assoc]

/-- Received record for party `i` in round `p = (s, r)` constructed from party `i`'s inbox
`inbox_i : Fin m → Msg`. -/
@[expose] def receivedMsgOfInbox {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    (p : Fin m × Fin m) (i : Fin m) (inbox_i : Fin m → Msg) :
    (msgRound (spec := spec) Msg p).Received i :=
  fun _ => inbox_i p.1

/-- Received transcript for party `i` along `msgSchedule Msg L` constructed from `inbox_i`. -/
@[expose] def receivedScheduleOfInbox {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    (i : Fin m) (inbox_i : Fin m → Msg) :
    (L : List (Fin m × Fin m)) → (msgSchedule (spec := spec) Msg L).Received i
  | [] => ()
  | p :: L => (receivedMsgOfInbox p i inbox_i, receivedScheduleOfInbox i inbox_i L)

theorem deliverMessage_eq_receivedMsgOfInbox {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    (toSend : (s : Fin m) → Fin m → Msg) (p : Fin m × Fin m) (i : Fin m) :
    Round.deliverMessage (spec := spec) (sender := p.1) (receiver := p.2) (toSend p.1 p.2) i =
      receivedMsgOfInbox p i (fun s => toSend s i) := by
  funext h
  subst h
  rfl

private theorem evalWith_msgStepsWith {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] {Out : Fin m → Type}
    (finish : (i : Fin m) → (Fin m → Msg) → Out i)
    (L : List (Fin m × Fin m)) (W : MultiOracleWorld spec)
    (st : (i : Fin m) → (Fin m → Msg) × (Fin m → Msg)) :
    (msgStepsWith finish L).evalWith W st =
      PMF.pure (fun i => receivedScheduleOfInbox i (fun s => (st s).1 i) L) := by
  induction L generalizing st with
  | nil => rfl
  | cons p L ih =>
    simp [msgStepsWith, ih, deliverMessage_eq_receivedMsgOfInbox (fun s => (st s).1) p,
      receivedScheduleOfInbox]

@[simp] private theorem extractMsg_receivedMsgOfInbox {m : ℕ} {spec : MultiOracleSpec} {Msg : Type}
    [AddCommMonoid Msg] (p : Fin m × Fin m) (i : Fin m) (inbox_i : Fin m → Msg) :
    extractMsg (spec := spec) p i (receivedMsgOfInbox p i inbox_i) =
      if i = p.2 then Pi.single p.1 (inbox_i p.1) else 0 := by
  by_cases h : i = p.2 <;> simp [extractMsg, receivedMsgOfInbox, h]

@[simp] private theorem sumReceivedMsgs_receivedScheduleOfInbox {m : ℕ} {spec : MultiOracleSpec}
    {Msg : Type} [AddCommMonoid Msg] (i : Fin m) (inbox_i : Fin m → Msg) :
    sumReceivedMsgs (spec := spec) (allPairs m) i
      (receivedScheduleOfInbox i inbox_i (allPairs m)) = inbox_i := by
  have hL : ∀ L : List (Fin m × Fin m),
      sumReceivedMsgs (spec := spec) L i (receivedScheduleOfInbox i inbox_i L) =
        (L.map fun p => extractMsg (spec := spec) p i (receivedMsgOfInbox p i inbox_i)).sum := by
    intro L
    induction L with
    | nil => rfl
    | cons p L ih => simp [sumReceivedMsgs, receivedScheduleOfInbox, ih]
  rw [hL]
  ext s₀
  simp [allPairs, List.flatMap_def, Function.comp_def, ← Fin.sum_univ_def,
    Finset.sum_apply, Pi.single_apply]

/-- Party `s`'s `m` additive shares of its input `x_s : BitString n` formed from its private coins
`c_s : Fin n → Fin (m - 1) → Bool` via `ProbComp.completeShares` (Construction 7.5.10, Step 1,
p. 706, with the completing share placed at `⊤ : Fin m`). -/
@[expose] def shareInputBits (m n : ℕ) (x_s : BitString n) (c_s : Fin n → Fin (m - 1) → Bool) :
    Fin m → BitString n :=
  ProbComp.completeShares m x_s (fun k j => c_s j k)

theorem shareInputBits_apply (m n : ℕ) (x_s : BitString n)
    (c_s : Fin n → Fin (m - 1) → Bool) (r : Fin m) (j : Fin n) :
    shareInputBits m n x_s c_s r j = ProbComp.completeShares m (x_s j) (c_s j) r := by
  dsimp [shareInputBits, ProbComp.completeShares]
  split_ifs
  · rfl
  · simp [Finset.sum_apply]

attribute [local simp] shareInputBits_apply

@[simp] private theorem sum_shareInputBits (m n : ℕ) [NeZero m] (x_s : BitString n)
    (c_s : Fin n → Fin (m - 1) → Bool) :
    ∑ r : Fin m, shareInputBits m n x_s c_s r = x_s :=
  ProbComp.sum_completeShares m x_s (fun k j => c_s j k)

private theorem map_shareInputBits_uniform (m n : ℕ) (x_s : BitString n) :
    (PMF.uniformOfFintype (Fin n → Fin (m - 1) → Bool)).map (shareInputBits m n x_s) =
      ProbComp.eval (ProbComp.sampleAdditiveShares m x_s) := by
  simp only [ProbComp.sampleAdditiveShares, ProbComp.eval_map, ProbComp.eval_uniform]
  rw [← PMF.uniformOfFintype_map_equiv (Equiv.piComm (fun (_ : Fin n) (_ : Fin (m - 1)) => Bool)),
    PMF.map_comp]
  rfl

private theorem map_restrict_shareInputBits_uniform (m n : ℕ) [NeZero m]
    (I : Finset (Fin m)) (hI : I ≠ Finset.univ) (x_s : BitString n) :
    (PMF.uniformOfFintype (Fin n → Fin (m - 1) → Bool)).map
        (fun c_s => I.restrict (shareInputBits m n x_s c_s)) =
      PMF.uniformOfFintype ((i : I) → BitString n) := by
  rw [← ProbComp.eval_restrict_sampleAdditiveShares I hI x_s, ← map_shareInputBits_uniform m n x_s,
    PMF.map_comp]
  rfl

/-- Schedule for Step 1 (Input Sharing): all-to-all point-to-point exchange of `BitString n`. -/
@[expose, reducible] def inputShareSchedule (m n : ℕ) : Schedule m (sharedMulSpec m) :=
  allToAllSchedule m (BitString n)

/-- Step 1 (Input Sharing) of Construction 7.5.10 (p. 706): each party `s` computes
`shareInputBits m n (x s) (c s)` and sends share `r` to party `r`; each party `i` packs the
received shares via `BitString.blocksEquiv.symm` into its initial input-wire valuation
`Fin (m * n) → Bool`. -/
@[expose] def inputShareSteps (m n : ℕ) :
    Steps (fun _ : Fin m => BitString n × (Fin n → Fin (m - 1) → Bool))
      (fun _ : Fin m => Fin (m * n) → Bool)
      (inputShareSchedule m n) :=
  (allToAllStepsWith m (fun _ inc => BitString.blocksEquiv.symm inc)).mapState
    (fun _ st => shareInputBits m n st.1 st.2)

/-- Deterministic Step 1 received transcript when party `s` has input `x s` and coins `c s`. -/
@[expose] def deliverInputShares {m n : ℕ} (x : (i : Fin m) → BitString n)
    (c : (i : Fin m) → Fin n → Fin (m - 1) → Bool) (i : Fin m) :
    (inputShareSchedule m n).Received i :=
  receivedScheduleOfInbox i (fun s => shareInputBits m n (x s) (c s) i) (allPairs m)

private theorem evalWith_inputShareSteps {m n : ℕ} (W : MultiOracleWorld (sharedMulSpec m))
    (x : (i : Fin m) → BitString n) (c : (i : Fin m) → Fin n → Fin (m - 1) → Bool) :
    (inputShareSteps m n).evalWith W (fun i => (x i, c i)) =
      PMF.pure (deliverInputShares x c) := by
  simp only [inputShareSteps, allToAllStepsWith, Steps.evalWith_mapState, evalWith_msgStepsWith]
  rfl

theorem outputAt_inputShareSteps {m n : ℕ}
    (x : (i : Fin m) → BitString n) (c : (i : Fin m) → Fin n → Fin (m - 1) → Bool) (i : Fin m) :
    (inputShareSteps m n).outputAt i (x i, c i) (deliverInputShares x c i) =
      BitString.blocksEquiv.symm (fun s => shareInputBits m n (x s) (c s) i) := by
  simp [inputShareSteps, allToAllStepsWith, deliverInputShares]

attribute [local simp] outputAt_inputShareSteps

theorem sum_outputAt_inputShareSteps {m n : ℕ} [NeZero m]
    (x : (i : Fin m) → BitString n) (c : (i : Fin m) → Fin n → Fin (m - 1) → Bool)
    (idx : Fin (m * n)) :
    (∑ i : Fin m, (inputShareSteps m n).outputAt i (x i, c i) (deliverInputShares x c i) idx) =
      BitString.blocksEquiv.symm x idx := by
  simp only [outputAt_inputShareSteps, BitString.blocksEquiv_symm_apply]
  have hsum := congrFun (sum_shareInputBits m n (x (finProdFinEquiv.symm idx).1)
    (c (finProdFinEquiv.symm idx).1)) (finProdFinEquiv.symm idx).2
  simpa only [Finset.sum_apply] using hsum

/-! ### Step 2: Gate-by-gate circuit evaluation -/

/-- Extend a wire valuation `w : Wire inputCount g → Bool` with value `lastBit` on the new gate
`Wire.gate (Fin.last g)`. -/
@[expose] def extendWire {inputCount g : ℕ} (lastBit : Bool) (w : Wire inputCount g → Bool) :
    Wire inputCount (g + 1) → Bool :=
  Wire.lastCases lastBit w

theorem extendWire_last {inputCount g : ℕ} (lastBit : Bool)
    (w : Wire inputCount g → Bool) :
    extendWire lastBit w (.gate (Fin.last g)) = lastBit := by
  simp [extendWire, Wire.lastCases]

attribute [local simp] extendWire_last

theorem extendWire_castSucc {inputCount g : ℕ} (lastBit : Bool)
    (w : Wire inputCount g → Bool) (wire : Wire inputCount g) :
    extendWire lastBit w wire.castSucc = w wire := by
  cases wire <;> simp [extendWire, Wire.lastCases]

attribute [local simp] extendWire_castSucc

/-- Canonical additive share of a public Boolean constant `b : Bool`: party `0` holds `b` and all
other parties hold `false`. -/
@[expose] def constShare {m : ℕ} [NeZero m] (b : Bool) (i : Fin m) : Bool :=
  if i = 0 then b else 0

@[simp] private theorem sum_constShare {m : ℕ} [NeZero m] (b : Bool) :
    ∑ i : Fin m, constShare b i = b := by
  simp [constShare]

private theorem bool_not_eq_add_true (a : Bool) : (!a) = a + true := by
  cases a <;> rfl

private theorem bool_and_eq_mul (a b : Bool) : (a && b) = a * b := by
  cases a <;> cases b <;> rfl

private theorem bool_or_eq_add_add_mul (a b : Bool) : (a || b) = a + b + a * b := by
  cases a <;> cases b <;> rfl

/-- Schedule for evaluating a single gate `line : Line Boolean.signature inputCount g`.
Constant and negation gates require no communication (`[]`); conjunction and disjunction gates
invoke `sharedMulSpec m` once. -/
@[expose, reducible] def lineSchedule (m : ℕ) {inputCount g : ℕ}
    (line : Line Boolean.signature inputCount g) : Schedule m (sharedMulSpec m) :=
  match line with
  | ⟨.const _, _⟩ => []
  | ⟨.not, _⟩ => []
  | ⟨.and, _⟩ => [.oracle () (Function.Embedding.refl (Fin m))]
  | ⟨.or, _⟩ => [.oracle () (Function.Embedding.refl (Fin m))]

/-- Step-by-step protocol for evaluating a single gate `line : Line Boolean.signature inputCount g`,
extending each party's wire valuation from `Wire inputCount g → Bool` to
`Wire inputCount (g + 1) → Bool`. -/
@[expose] def lineSteps (m : ℕ) [NeZero m] {inputCount g : ℕ}
    (line : Line Boolean.signature inputCount g) :
    Steps (fun _ : Fin m => Wire inputCount g → Bool)
      (fun _ : Fin m => Wire inputCount (g + 1) → Bool)
      (lineSchedule m line) :=
  match line with
  | ⟨.const b, _⟩ =>
    .done (fun i w_i => extendWire (constShare b i) w_i)
  | ⟨.not, wires⟩ =>
    .done (fun i w_i => extendWire (w_i (wires 0) + constShare true i) w_i)
  | ⟨.and, wires⟩ =>
    .oracle (spec := sharedMulSpec m) (State := fun _ : Fin m => Wire inputCount g → Bool)
      (op := ()) (parties := Function.Embedding.refl (Fin m))
      (fun _ w_s => (w_s (wires 0), w_s (wires 1)))
      (.done (fun i st_i => extendWire (st_i.2 i rfl) st_i.1))
  | ⟨.or, wires⟩ =>
    .oracle (spec := sharedMulSpec m) (State := fun _ : Fin m => Wire inputCount g → Bool)
      (op := ()) (parties := Function.Embedding.refl (Fin m))
      (fun _ w_s => (w_s (wires 0), w_s (wires 1)))
      (.done (fun i st_i =>
        extendWire (st_i.1 (wires 0) + st_i.1 (wires 1) + st_i.2 i rfl) st_i.1))

/-- Schedule for evaluating a straight-line program `prog : Program Boolean.signature inputCount g`.
-/
@[expose, reducible] def progSchedule (m : ℕ) {inputCount g : ℕ}
    (prog : Program Boolean.signature inputCount g) : Schedule m (sharedMulSpec m) :=
  match prog with
  | .empty => []
  | .gate p line => progSchedule m p ++ lineSchedule m line

/-- Step-by-step evaluation of `prog : Program Boolean.signature inputCount g` (Construction 7.5.10,
Step 2, p. 706, adapted to the De Morgan basis `Boolean.signature`). -/
@[expose] def progSteps (m : ℕ) [NeZero m] {inputCount g : ℕ}
    (prog : Program Boolean.signature inputCount g) :
    Steps (fun _ : Fin m => Fin inputCount → Bool)
      (fun _ : Fin m => Wire inputCount g → Bool)
      (progSchedule m prog) :=
  match prog with
  | .empty => .done (fun _ x_in => Wire.elim x_in Fin.elim0)
  | .gate p line => (progSteps m p).append (lineSteps m line)

/-- Deliver a single `sharedMulSpec m` oracle answer tuple `ans` as a 1-round `Schedule.Received`
transcript. -/
@[expose, reducible] def deliverMulOracle {m : ℕ} (ans : Fin m → Bool) (i : Fin m) :
    Schedule.Received (spec := sharedMulSpec m)
      [.oracle () (Function.Embedding.refl (Fin m))] i :=
  (Round.deliverOracle (spec := sharedMulSpec m) (op := ())
    (Function.Embedding.refl (Fin m)) ans i, ())

/-- Received record for party `i` in `Round.oracle () (Function.Embedding.refl (Fin m))` constructed
from party `i`'s own answer bit `b : Bool`. -/
private def deliverSelfShare {m : ℕ} (b : Bool) (i : Fin m) :
    Schedule.Received (spec := sharedMulSpec m)
      [.oracle () (Function.Embedding.refl (Fin m))] i :=
  (fun _ _ => b, ())

private theorem deliverMulOracle_eq_deliverSelfShare {m : ℕ} (ans : Fin m → Bool) (i : Fin m) :
    deliverMulOracle ans i = deliverSelfShare (ans i) i := by
  apply Prod.ext
  · funext s hs
    cases hs
    rfl
  · rfl

/-- Exact received-transcript sampler for a single gate `line` when the true wire values of `p` are
`p.trace Boolean.interpretation x_flat`. -/
@[expose] noncomputable def lineDist (m : ℕ) {inputCount g : ℕ}
    (x_flat : Fin inputCount → Bool) (p : Program Boolean.signature inputCount g)
    (line : Line Boolean.signature inputCount g) :
    ProbComp ((i : Fin m) → (lineSchedule m line).Received i) :=
  match line with
  | ⟨.const _, _⟩ => pure (fun _ => ())
  | ⟨.not, _⟩ => pure (fun _ => ())
  | ⟨.and, wires⟩ =>
    deliverMulOracle <$>
      ProbComp.sampleAdditiveShares m
        (p.trace Boolean.interpretation x_flat (wires 0) *
          p.trace Boolean.interpretation x_flat (wires 1))
  | ⟨.or, wires⟩ =>
    deliverMulOracle <$>
      ProbComp.sampleAdditiveShares m
        (p.trace Boolean.interpretation x_flat (wires 0) *
          p.trace Boolean.interpretation x_flat (wires 1))

private theorem evalWith_lineSteps {m inputCount g : ℕ} [NeZero m]
    (x_flat : Fin inputCount → Bool) (p : Program Boolean.signature inputCount g)
    (line : Line Boolean.signature inputCount g)
    (w : (i : Fin m) → Wire inputCount g → Bool)
    (hw : ∀ wire : Wire inputCount g,
      (∑ i : Fin m, w i wire) = p.trace Boolean.interpretation x_flat wire) :
    (lineSteps m line).evalWith (sharedMulWorld m) w =
      ProbComp.eval (lineDist m x_flat p line) ∧
    ∀ r_line ∈ (ProbComp.eval (lineDist m x_flat p line)).support,
      ∀ wire : Wire inputCount (g + 1),
        (∑ i : Fin m, (lineSteps m line).outputAt i (w i) (r_line i) wire) =
          (p.gate line).trace Boolean.interpretation x_flat wire := by
  rcases line with ⟨op, wires⟩
  cases op with
  | const b =>
    refine ⟨by simp [lineSteps, lineDist], ?_⟩
    intro r_line _ wire
    have hr : r_line = fun _ => () := funext fun i => by cases r_line i; rfl
    subst hr
    simp only [lineSteps, Steps.outputAt]
    refine Wire.lastCases ?_ (fun wire => ?_) wire
    · simp [Line.eval, Boolean.interpretation]
    · simp [hw wire]
  | not =>
    refine ⟨by simp [lineSteps, lineDist], ?_⟩
    intro r_line _ wire
    have hr : r_line = fun _ => () := funext fun i => by cases r_line i; rfl
    subst hr
    simp only [lineSteps, Steps.outputAt]
    refine Wire.lastCases ?_ (fun wire => ?_) wire
    · simp [Line.eval, Program.trace, Boolean.interpretation,
        Finset.sum_add_distrib, hw (wires 0), bool_not_eq_add_true]
    · simp [hw wire]
  | and =>
    constructor
    · simp [lineSteps, lineDist, sharedMulWorld, sharedMulFunctionality,
        hw (wires 0), hw (wires 1), PMF.map, Function.comp_def]
    · intro r_line hr wire
      simp only [lineDist, ProbComp.eval_map, PMF.mem_support_map_iff] at hr
      obtain ⟨ans, hans, rfl⟩ := hr
      have hsum := ProbComp.sum_sampleAdditiveShares _ hans
      simp only [lineSteps, Steps.outputAt, deliverMulOracle, Round.deliverOracle]
      refine Wire.lastCases ?_ (fun wire => ?_) wire
      · simp [hsum, Line.eval, Program.trace, Boolean.interpretation, bool_and_eq_mul]
      · simp [hw wire]
  | or =>
    constructor
    · simp [lineSteps, lineDist, sharedMulWorld, sharedMulFunctionality,
        hw (wires 0), hw (wires 1), PMF.map, Function.comp_def]
    · intro r_line hr wire
      simp only [lineDist, ProbComp.eval_map, PMF.mem_support_map_iff] at hr
      obtain ⟨ans, hans, rfl⟩ := hr
      have hsum := ProbComp.sum_sampleAdditiveShares _ hans
      simp only [lineSteps, Steps.outputAt, deliverMulOracle, Round.deliverOracle]
      refine Wire.lastCases ?_ (fun wire => ?_) wire
      · simp [Finset.sum_add_distrib, hw (wires 0), hw (wires 1), hsum,
          Line.eval, Program.trace, Boolean.interpretation, bool_or_eq_add_add_mul]
      · simp [hw wire]

/-- Exact received-transcript sampler for `prog : Program Boolean.signature inputCount g` on
flattened input `x_flat`. -/
@[expose] noncomputable def progDist (m : ℕ) {inputCount g : ℕ} (x_flat : Fin inputCount → Bool)
    (prog : Program Boolean.signature inputCount g) :
    ProbComp ((i : Fin m) → (progSchedule m prog).Received i) :=
  match prog with
  | .empty => pure (fun _ => ())
  | .gate p line => do
    let r_p ← progDist m x_flat p
    let r_line ← lineDist m x_flat p line
    return fun i => Schedule.Received.append (r_p i) (r_line i)

theorem evalWith_progSteps {m inputCount g : ℕ} [NeZero m]
    (x_flat : Fin inputCount → Bool) (prog : Program Boolean.signature inputCount g)
    (st : (i : Fin m) → Fin inputCount → Bool)
    (hst : ∀ idx : Fin inputCount, (∑ i : Fin m, st i idx) = x_flat idx) :
    (progSteps m prog).evalWith (sharedMulWorld m) st =
      ProbComp.eval (progDist m x_flat prog) ∧
    ∀ r_prog ∈ (ProbComp.eval (progDist m x_flat prog)).support,
      ∀ wire : Wire inputCount g,
        (∑ i : Fin m, (progSteps m prog).outputAt i (st i) (r_prog i) wire) =
          prog.trace Boolean.interpretation x_flat wire := by
  induction prog with
  | empty =>
    refine ⟨by simp [progSteps, progDist], ?_⟩
    intro r_prog _ wire
    have hr : r_prog = fun _ => () := funext fun i => by cases r_prog i; rfl
    subst hr
    cases wire with
    | input idx => exact hst idx
    | gate k => exact k.elim0
  | gate p line ih =>
    obtain ⟨heval_p, hsum_p⟩ := ih
    constructor
    · rw [progSteps, Steps.evalWith_append, heval_p]
      simp only [progDist, ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp]
      refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun r_p hr_p => ?_
      have hline := (evalWith_lineSteps x_flat p line
        (fun i => (progSteps m p).outputAt i (st i) (r_p i)) (hsum_p r_p hr_p)).1
      rw [hline]
    · intro r_prog hr_prog wire
      simp only [progDist, ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp,
        PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hr_prog
      obtain ⟨r_p, hr_p, r_line, hr_line, rfl⟩ := hr_prog
      have hline := (evalWith_lineSteps x_flat p line
        (fun i => (progSteps m p).outputAt i (st i) (r_p i)) (hsum_p r_p hr_p)).2 r_line hr_line
      simpa [progSteps] using hline wire

private theorem eval_lineDist_restrict_of_ne_univ {m inputCount g : ℕ} [NeZero m]
    {I : Finset (Fin m)} (hI : I ≠ Finset.univ)
    (x₁ x₂ : Fin inputCount → Bool) (p : Program Boolean.signature inputCount g)
    (line : Line Boolean.signature inputCount g) :
    (ProbComp.eval (lineDist m x₁ p line)).map I.restrict =
      (ProbComp.eval (lineDist m x₂ p line)).map I.restrict := by
  have hmul : ∀ b₁ b₂ : Bool,
      ((ProbComp.eval (ProbComp.sampleAdditiveShares m b₁)).map deliverMulOracle).map I.restrict =
        ((ProbComp.eval (ProbComp.sampleAdditiveShares m b₂)).map deliverMulOracle).map
          I.restrict := by
    intro b₁ b₂
    have hfactor : ∀ b : Bool,
        ((ProbComp.eval (ProbComp.sampleAdditiveShares m b)).map deliverMulOracle).map I.restrict =
          ((ProbComp.eval (ProbComp.sampleAdditiveShares m b)).map I.restrict).map
            (fun ansI (i : I) => deliverSelfShare (ansI i) i.1) := by
      intro b
      rw [PMF.map_comp, PMF.map_comp]
      congr 1
      funext ans ⟨i, hi⟩
      exact deliverMulOracle_eq_deliverSelfShare ans i
    rw [hfactor b₁, hfactor b₂,
      ProbComp.eval_restrict_sampleAdditiveShares I hI b₁,
      ProbComp.eval_restrict_sampleAdditiveShares I hI b₂]
  rcases line with ⟨op, wires⟩
  cases op with
  | const b => rfl
  | not => rfl
  | and =>
    simp only [lineDist, ProbComp.eval_map]
    exact hmul _ _
  | or =>
    simp only [lineDist, ProbComp.eval_map]
    exact hmul _ _

private theorem eval_progDist_restrict_of_ne_univ {m inputCount g : ℕ} [NeZero m]
    {I : Finset (Fin m)} (hI : I ≠ Finset.univ)
    (x₁ x₂ : Fin inputCount → Bool) (prog : Program Boolean.signature inputCount g) :
    (ProbComp.eval (progDist m x₁ prog)).map I.restrict =
      (ProbComp.eval (progDist m x₂ prog)).map I.restrict := by
  induction prog with
  | empty => rfl
  | gate p line ih =>
    have hfactor : ∀ x_flat : Fin inputCount → Bool,
        (ProbComp.eval (progDist m x_flat (p.gate line))).map I.restrict =
          ((ProbComp.eval (progDist m x_flat p)).map I.restrict).bind fun rI_p =>
            ((ProbComp.eval (lineDist m x_flat p line)).map I.restrict).map fun rI_line (i : I) =>
              Schedule.Received.append (rI_p i) (rI_line i) := by
      intro x_flat
      simp only [progDist, ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp,
        PMF.map_bind, PMF.bind_map, PMF.map_comp]
      rfl
    rw [hfactor x₁, hfactor x₂, ih, eval_lineDist_restrict_of_ne_univ hI x₁ x₂ p line]

/-! ### Step 3: Output share refresh and reconstruction -/

/-- All output coordinates `(r, j) : Fin m × Fin k` in lexicographic order. -/
@[expose] def outCoords (m k : ℕ) : List (Fin m × Fin k) :=
  (List.finRange m).flatMap fun r => (List.finRange k).map fun j => (r, j)

/-- Schedule for gathering `Bool` shares from every sender `s ∈ S` at receiver `r`. -/
@[expose, reducible] def gatherSchedule (m : ℕ) {spec : MultiOracleSpec} (r : Fin m)
    (S : List (Fin m)) : Schedule m spec :=
  S.map fun s => .message s r Bool

/-- Extract party `i`'s received bit in `.message s r Bool`. -/
@[expose] def extractBitFor {m : ℕ} {spec : MultiOracleSpec} (s r i : Fin m)
    (recv : (Round.message (spec := spec) s r Bool).Received i) : Bool :=
  if h : i = r then recv h else 0

/-- Gather `Bool` shares at receiver `r` from senders `S`, preserving `st.1` and `st.2.1` and
applying `finish` at `.done`. -/
@[expose] def gatherStepsWith {m : ℕ} {spec : MultiOracleSpec} {State Out : Fin m → Type}
    (r : Fin m) (finish : (i : Fin m) → State i → Bool → Out i) :
    (S : List (Fin m)) →
      Steps (fun i => State i × Bool × Bool) Out (gatherSchedule m (spec := spec) r S)
  | [] => .done (fun i st => finish i st.1 st.2.2)
  | s :: S =>
    .message (sender := s) (receiver := r)
      (fun st => st.2.1)
      ((gatherStepsWith r finish S).mapState fun i st =>
        (st.1.1, st.1.2.1, st.1.2.2 + extractBitFor s r i st.2))

/-- Sum of party `i`'s received bits along `gatherSchedule m r S`. -/
@[expose] def sumGatherBits {m : ℕ} {spec : MultiOracleSpec} (r : Fin m) :
    (S : List (Fin m)) → (i : Fin m) →
      (gatherSchedule m (spec := spec) r S).Received i → Bool
  | [], _, _ => 0
  | s :: S, i, recv => extractBitFor s r i recv.1 + sumGatherBits r S i recv.2

@[simp] private theorem outputAt_gatherStepsWith {m : ℕ} {spec : MultiOracleSpec}
    {State Out : Fin m → Type} (r : Fin m)
    (finish : (i : Fin m) → State i → Bool → Out i)
    (S : List (Fin m)) (i : Fin m) (st_i : State i × Bool × Bool)
    (recv_i : (gatherSchedule m (spec := spec) r S).Received i) :
    (gatherStepsWith r finish S).outputAt i st_i recv_i =
      finish i st_i.1 (st_i.2.2 + sumGatherBits r S i recv_i) := by
  induction S generalizing st_i with
  | nil =>
    cases recv_i
    simp [gatherStepsWith, Steps.outputAt, sumGatherBits]
  | cons s S ih =>
    rcases recv_i with ⟨r_head, r_tail⟩
    simp [gatherStepsWith, Steps.outputAt, ih, sumGatherBits, add_assoc]

/-- Deterministic received transcript along `gatherSchedule m r S` when sender `s` sends `ans s`. -/
@[expose] def deliverGather {m : ℕ} {spec : MultiOracleSpec} (r : Fin m) (ans : Fin m → Bool) :
    (S : List (Fin m)) → (i : Fin m) → (gatherSchedule m (spec := spec) r S).Received i
  | [], _ => ()
  | s :: S, i => (Round.deliverMessage (ans s) i, deliverGather r ans S i)

private theorem evalWith_gatherStepsWith {m : ℕ} {spec : MultiOracleSpec}
    {State Out : Fin m → Type} (r : Fin m)
    (finish : (i : Fin m) → State i → Bool → Out i)
    (S : List (Fin m)) (W : MultiOracleWorld spec)
    (st : (i : Fin m) → State i × Bool × Bool) :
    (gatherStepsWith r finish S).evalWith W st =
      PMF.pure (fun i => deliverGather r (fun s => (st s).2.1) S i) := by
  induction S generalizing st with
  | nil => rfl
  | cons s S ih =>
    simp [gatherStepsWith, ih, deliverGather]

@[simp] private theorem extractBitFor_deliverMessage {m : ℕ} {spec : MultiOracleSpec}
    (s r i : Fin m) (b : Bool) :
    extractBitFor (spec := spec) s r i (Round.deliverMessage b i) =
      if i = r then b else 0 := by
  by_cases h : i = r <;> simp [extractBitFor, h]

theorem sumGatherBits_deliverGather {m : ℕ} {spec : MultiOracleSpec}
    (r : Fin m) (ans : Fin m → Bool) (i : Fin m) :
    sumGatherBits (spec := spec) r (List.finRange m) i
      (deliverGather r ans (List.finRange m) i) =
      if i = r then ∑ s : Fin m, ans s else 0 := by
  have hS : ∀ S : List (Fin m),
      sumGatherBits (spec := spec) r S i (deliverGather r ans S i) =
        (S.map fun s => if i = r then ans s else 0).sum := by
    intro S
    induction S with
    | nil => rfl
    | cons s S ih => simp [sumGatherBits, deliverGather, ih]
  rw [hS, Fin.sum_univ_def]
  by_cases h : i = r
  · simp [h]
  · simp [h]

attribute [local simp] sumGatherBits_deliverGather

private theorem deliverGather_eq_of_ne {m : ℕ} {spec : MultiOracleSpec} {r i : Fin m}
    (hne : i ≠ r) (ans₁ ans₂ : Fin m → Bool) (S : List (Fin m)) :
    deliverGather (spec := spec) r ans₁ S i = deliverGather (spec := spec) r ans₂ S i := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    simp only [deliverGather, ih]
    exact Prod.ext (Round.received_message_eq_of_ne hne _ _) rfl

/-- Schedule for refreshing and reconstructing a single output bit belonging to party `r`:
one `sharedMulSpec m` oracle call (an adaptation of Goldreich Construction 7.5.10 Step 3, p. 706,
that refreshes the output wire's shares for arbitrary `Circuit.outputs`) followed by `m`
point-to-point `.message s r Bool` rounds (including `s = r`). -/
@[expose, reducible] def coordSchedule (m : ℕ) (r : Fin m) : Schedule m (sharedMulSpec m) :=
  .oracle () (Function.Embedding.refl (Fin m)) ::
    gatherSchedule m r (List.finRange m)

/-- Refresh and reconstruct a single output coordinate `coord = (r, j) : Fin m × Fin k`
(adaptation of Goldreich Construction 7.5.10 Step 3, p. 706): invokes `sharedMulSpec m` on
`(st.1 r j, constShare true s)` to obtain fresh independent additive shares `ans` before sending
`ans s` from each party `s` to party `r`, which adds `Pi.single j (∑ s, ans s)` to its output
accumulator `st.2 : BitString k`. The extra `sharedMulSpec m` refresh allows `C.outputs` to
reference arbitrary wires (including input wires, negated wires, or repeated wires). -/
@[expose] def singleCoordSteps (m k : ℕ) [NeZero m] (coord : Fin m × Fin k) :
    Steps (fun _ : Fin m => (Fin m → BitString k) × BitString k)
      (fun _ : Fin m => (Fin m → BitString k) × BitString k)
      (coordSchedule m coord.1) :=
  .oracle (spec := sharedMulSpec m)
    (State := fun _ : Fin m => (Fin m → BitString k) × BitString k)
    (op := ()) (parties := Function.Embedding.refl (Fin m))
    (fun s st => (st.1 coord.1 coord.2, constShare true s))
    ((gatherStepsWith coord.1
      (fun i (st : (Fin m → BitString k) × BitString k) sum_i =>
        (st.1, st.2 + if i = coord.1 then Pi.single coord.2 sum_i else 0))
      (List.finRange m)).mapState fun i st =>
        (st.1, st.2 i rfl, 0))

/-- Received transcript for `coordSchedule m r` when the refresh oracle returns `ans`. -/
@[expose] def deliverCoord {m : ℕ} (r : Fin m) (ans : Fin m → Bool) (i : Fin m) :
    (coordSchedule m r).Received i :=
  (Round.deliverOracle (spec := sharedMulSpec m) (op := ())
    (Function.Embedding.refl (Fin m)) ans i,
    deliverGather r ans (List.finRange m) i)

private theorem deliverCoord_eq {m : ℕ} (r : Fin m) (ans : Fin m → Bool) :
    deliverCoord r ans = fun i =>
      (Round.deliverOracle (spec := sharedMulSpec m) (op := ())
        (Function.Embedding.refl (Fin m)) ans i,
        deliverGather r ans (List.finRange m) i) := rfl

private theorem evalWith_singleCoordSteps {m k : ℕ} [NeZero m] (coord : Fin m × Fin k)
    (y : Fin m → BitString k)
    (st : (i : Fin m) → (Fin m → BitString k) × BitString k)
    (hst : (∑ i : Fin m, (st i).1 coord.1 coord.2) = y coord.1 coord.2) :
    (singleCoordSteps m k coord).evalWith (sharedMulWorld m) st =
      (ProbComp.eval (ProbComp.sampleAdditiveShares m (y coord.1 coord.2))).map
        (deliverCoord coord.1) := by
  have hmul_one : ∀ b : Bool, b * true = b := by decide
  simp [singleCoordSteps, sharedMulWorld, sharedMulFunctionality, hst, hmul_one,
    evalWith_gatherStepsWith, deliverCoord_eq, Round.deliverOracle, PMF.map, Function.comp_def]

theorem outputAt_singleCoordSteps {m k : ℕ} [NeZero m] (coord : Fin m × Fin k)
    (ans : Fin m → Bool)
    (st_i : (Fin m → BitString k) × BitString k) (i : Fin m) :
    (singleCoordSteps m k coord).outputAt i st_i (deliverCoord coord.1 ans i) =
      (st_i.1, st_i.2 + if i = coord.1 then Pi.single coord.2 (∑ s : Fin m, ans s) else 0) := by
  by_cases h : i = coord.1 <;> simp [singleCoordSteps, Steps.outputAt, deliverCoord, h]

attribute [local simp] outputAt_singleCoordSteps

/-- Schedule for refreshing and reconstructing a list `L : List (Fin m × Fin k)` of output
coordinates. -/
@[expose, reducible] def outCoordsSchedule (m : ℕ) {k : ℕ} :
    List (Fin m × Fin k) → Schedule m (sharedMulSpec m)
  | [] => []
  | coord :: L => coordSchedule m coord.1 ++ outCoordsSchedule m L

/-- Step-by-step refresh and reconstruction along `L : List (Fin m × Fin k)`. -/
@[expose] def outCoordsSteps (m k : ℕ) [NeZero m] :
    (L : List (Fin m × Fin k)) →
      Steps (fun _ : Fin m => (Fin m → BitString k) × BitString k)
        (fun _ : Fin m => BitString k)
        (outCoordsSchedule m L)
  | [] => .done (fun _ st => st.2)
  | coord :: L => (singleCoordSteps m k coord).append (outCoordsSteps m k L)

/-- Exact received-transcript sampler for `outCoordsSteps m k L` on output table `y`. -/
@[expose] noncomputable def outCoordsDist (m k : ℕ) (y : Fin m → BitString k) :
    (L : List (Fin m × Fin k)) →
      ProbComp ((i : Fin m) → (outCoordsSchedule m L).Received i)
  | [] => pure (fun _ => ())
  | coord :: L => do
    let ans ← ProbComp.sampleAdditiveShares m (y coord.1 coord.2)
    let r_tail ← outCoordsDist m k y L
    return fun i => Schedule.Received.append (deliverCoord coord.1 ans i) (r_tail i)

private theorem evalWith_outCoordsSteps {m k : ℕ} [NeZero m]
    (L : List (Fin m × Fin k)) (y : Fin m → BitString k)
    (st : (i : Fin m) → (Fin m → BitString k) × BitString k)
    (hst : ∀ r j, (∑ i : Fin m, (st i).1 r j) = y r j) :
    (outCoordsSteps m k L).evalWith (sharedMulWorld m) st =
      ProbComp.eval (outCoordsDist m k y L) ∧
    ∀ recv ∈ (ProbComp.eval (outCoordsDist m k y L)).support,
      ∀ i : Fin m,
        (outCoordsSteps m k L).outputAt i (st i) (recv i) =
          (st i).2 +
            (L.map fun coord =>
              if i = coord.1 then Pi.single coord.2 (y coord.1 coord.2) else 0).sum := by
  induction L generalizing st with
  | nil =>
    refine ⟨by simp [outCoordsSteps, outCoordsDist], ?_⟩
    intro recv _ i
    cases recv i
    simp [outCoordsSteps, Steps.outputAt]
  | cons coord L ih =>
    have hcoord := evalWith_singleCoordSteps coord y st (hst coord.1 coord.2)
    constructor
    · rw [outCoordsSteps, Steps.evalWith_append, hcoord, PMF.bind_map]
      simp only [outCoordsDist, ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp,
        Function.comp_def]
      refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun ans hans => ?_
      have hnext := (ih (fun i => (singleCoordSteps m k coord).outputAt i (st i)
        (deliverCoord coord.1 ans i)) (fun r j => by simp [hst r j])).1
      rw [hnext]
    · intro recv hrecv i
      simp only [outCoordsDist, ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp,
        PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hrecv
      obtain ⟨ans, hans, r_tail, hr_tail, rfl⟩ := hrecv
      have hsum := ProbComp.sum_sampleAdditiveShares _ hans
      have hnext := (ih (fun i => (singleCoordSteps m k coord).outputAt i (st i)
        (deliverCoord coord.1 ans i)) (fun r j => by simp [hst r j])).2 r_tail hr_tail i
      rw [outCoordsSteps, Steps.outputAt_append, hnext]
      simp [hsum, add_assoc]

private theorem sum_outCoords_single {m k : ℕ} (y : Fin m → BitString k) (i : Fin m) :
    ((outCoords m k).map fun coord =>
        if i = coord.1 then Pi.single coord.2 (y coord.1 coord.2) else 0).sum =
      y i := by
  ext j₀
  simp [outCoords, List.flatMap_def, Function.comp_def, ← Fin.sum_univ_def,
    Finset.sum_apply, apply_ite (fun f : BitString k => f j₀), Pi.single_apply]

/-- Schedule for Step 3 (Output Share Refresh and Reconstruction). -/
@[expose, reducible] def outputSchedule (m k : ℕ) : Schedule m (sharedMulSpec m) :=
  outCoordsSchedule m (outCoords m k)

/-- Step 3 of `gmwCircuitProtocol` (adapting Goldreich Construction 7.5.10 Step 3, p. 706, with a
per-coordinate `sharedMulSpec m` share refresh so `C.outputs` can reference arbitrary wires):
extracts each party's shares of the `m * k` designated output wires `C.outputs` and runs
`outCoordsSteps m k (outCoords m k)`. -/
@[expose] def outputSteps (m n k : ℕ) [NeZero m]
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k)) :
    Steps (fun _ : Fin m => Wire (m * n) C.size → Bool)
      (fun _ : Fin m => BitString k)
      (outputSchedule m k) :=
  (outCoordsSteps m k (outCoords m k)).mapState fun _ w =>
    (fun r j => w (C.outputs (finProdFinEquiv (r, j))), 0)

/-- Exact received-transcript sampler for `outputSteps m n k C` when the circuit output is `y`. -/
@[expose] noncomputable def outputDist (m k : ℕ) (y : Fin m → BitString k) :
    ProbComp ((i : Fin m) → (outputSchedule m k).Received i) :=
  outCoordsDist m k y (outCoords m k)

private theorem evalWith_outputSteps {m n k : ℕ} [NeZero m]
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k))
    (x : (i : Fin m) → BitString n)
    (w : (i : Fin m) → Wire (m * n) C.size → Bool)
    (hw : ∀ wire : Wire (m * n) C.size,
      (∑ i : Fin m, w i wire) =
        C.program.trace Boolean.interpretation (BitString.blocksEquiv.symm x) wire) :
    (outputSteps m n k C).evalWith (sharedMulWorld m) w =
      ProbComp.eval (outputDist m k (circuitFunctionality m n k C x)) ∧
    ∀ recv ∈ (ProbComp.eval (outputDist m k (circuitFunctionality m n k C x))).support,
      ∀ i : Fin m,
        (outputSteps m n k C).outputAt i (w i) (recv i) =
          circuitFunctionality m n k C x i := by
  have hout := evalWith_outCoordsSteps (outCoords m k) (circuitFunctionality m n k C x)
    (fun i => (fun r j => w i (C.outputs (finProdFinEquiv (r, j))), 0))
    (fun r j => hw (C.outputs (finProdFinEquiv (r, j))))
  refine ⟨?_, ?_⟩
  · simpa [outputSteps, outputDist] using hout.1
  · intro recv hrecv i
    have hi := hout.2 recv hrecv i
    simpa [outputSteps, sum_outCoords_single] using hi

/-! ### Coalition restriction and simulation helpers -/

/-- Extend a partial tuple `vI : (i : I) → α` on a coalition `I : Finset (Fin m)` to all `m`
parties by padding parties outside `I` with `0`. -/
@[expose] def extendByZero {m : ℕ} {α : Type} [Zero α] (I : Finset (Fin m)) (vI : (i : I) → α)
    (j : Fin m) : α :=
  if hj : j ∈ I then vI ⟨j, hj⟩ else 0

@[simp] private theorem extendByZero_of_mem {m : ℕ} {α : Type} [Zero α] (I : Finset (Fin m))
    (vI : (i : I) → α) {j : Fin m} (hj : j ∈ I) :
    extendByZero I vI j = vI ⟨j, hj⟩ := by
  simp [extendByZero, hj]

@[simp] private theorem extendByZero_univ {m : ℕ} {α : Type} [Zero α] (v : Fin m → α) :
    extendByZero Finset.univ (Finset.univ.restrict v) = v := by
  ext j
  simp [extendByZero]

/-- What sender `s : Fin m` contributes to the Step 1 view of coalition `I`: its own coins `c_s` if
`s ∈ I`, together with the shares `I.restrict (shareInputBits m n x_s c_s)` sent to `I`. -/
private def senderContribution (m n : ℕ) (I : Finset (Fin m)) (s : Fin m) (x_s : BitString n)
    (c_s : Fin n → Fin (m - 1) → Bool) :
    (s ∈ I → Fin n → Fin (m - 1) → Bool) × ((i : I) → BitString n) :=
  (fun _ => c_s, I.restrict (shareInputBits m n x_s c_s))

private theorem map_senderContribution_extendByZero (m n : ℕ) [NeZero m] (I : Finset (Fin m))
    (x : (i : Fin m) → BitString n) (s : Fin m) :
    (PMF.uniformOfFintype (Fin n → Fin (m - 1) → Bool)).map
        (senderContribution m n I s (extendByZero I (I.restrict x) s)) =
      (PMF.uniformOfFintype (Fin n → Fin (m - 1) → Bool)).map
        (senderContribution m n I s (x s)) := by
  by_cases hs : s ∈ I
  · simp [hs]
  · have hI : I ≠ Finset.univ := fun h => hs (h ▸ Finset.mem_univ s)
    have hconst : ∀ b : BitString n,
        (PMF.uniformOfFintype (Fin n → Fin (m - 1) → Bool)).map (senderContribution m n I s b) =
          (PMF.uniformOfFintype ((i : I) → BitString n)).map
            (fun sh => (fun h : s ∈ I => (hs h).elim, sh)) := by
      intro b
      rw [← map_restrict_shareInputBits_uniform m n I hI b, PMF.map_comp]
      congr 1
      funext c_s
      exact Prod.ext (funext fun h => (hs h).elim) rfl
    rw [hconst, hconst]

/-- Reconstruct each coalition member `i ∈ I`'s coins and Step 1 received transcript from the
per-sender contributions `contrib`. -/
private def assembleInputShare (m n : ℕ) (I : Finset (Fin m))
    (contrib : (s : Fin m) → (s ∈ I → Fin n → Fin (m - 1) → Bool) × ((i : I) → BitString n))
    (i : I) :
    (Fin n → Fin (m - 1) → Bool) × (inputShareSchedule m n).Received i.1 :=
  ((contrib i.1).1 i.2,
    receivedScheduleOfInbox i.1 (fun s => (contrib s).2 i) (allPairs m))

private theorem eval_inputShare_restrict (m n : ℕ) [NeZero m] (I : Finset (Fin m))
    (x : (i : Fin m) → BitString n) :
    (ProbComp.eval (OracleComp.pi (fun _ : Fin m =>
        ProbComp.uniform (Fin n → Fin (m - 1) → Bool)))).map
      (fun c (i : I) => (c i.1, deliverInputShares (extendByZero I (I.restrict x)) c i.1)) =
    (ProbComp.eval (OracleComp.pi (fun _ : Fin m =>
        ProbComp.uniform (Fin n → Fin (m - 1) → Bool)))).map
      (fun c (i : I) => (c i.1, deliverInputShares x c i.1)) := by
  have hfactor : ∀ x' : (i : Fin m) → BitString n,
      (ProbComp.eval (OracleComp.pi (fun _ : Fin m =>
          ProbComp.uniform (Fin n → Fin (m - 1) → Bool)))).map
        (fun c (i : I) => (c i.1, deliverInputShares x' c i.1)) =
      (ProbComp.eval (OracleComp.pi (fun s : Fin m =>
          senderContribution m n I s (x' s) <$>
            ProbComp.uniform (Fin n → Fin (m - 1) → Bool)))).map
        (assembleInputShare m n I) := by
    intro x'
    rw [ProbComp.eval_pi_map, PMF.map_comp]
    rfl
  rw [hfactor (extendByZero I (I.restrict x)), hfactor x]
  congr 1
  refine ProbComp.eval_pi_congr fun s => ?_
  simpa only [ProbComp.eval_map, ProbComp.eval_uniform] using
    map_senderContribution_extendByZero m n I x s

private theorem eval_progDist_restrict {m n g : ℕ} [NeZero m]
    (I : Finset (Fin m)) (x : (i : Fin m) → BitString n)
    (prog : Program Boolean.signature (m * n) g) :
    (ProbComp.eval (progDist m (BitString.blocksEquiv.symm (extendByZero I (I.restrict x)))
        prog)).map I.restrict =
      (ProbComp.eval (progDist m (BitString.blocksEquiv.symm x) prog)).map I.restrict := by
  by_cases hI : I = Finset.univ
  · subst hI
    simp
  · exact eval_progDist_restrict_of_ne_univ hI _ _ prog

/-- Received transcript for `coordSchedule m r` at a non-recipient party `i ≠ r` constructed solely
from party `i`'s own refresh oracle answer `b : Bool`. -/
private def deliverCoordNonMember {m : ℕ} (r : Fin m) (b : Bool) (i : Fin m) :
    (coordSchedule m r).Received i :=
  (fun _ _ => b, deliverGather r 0 (List.finRange m) i)

private theorem deliverCoord_eq_nonMember {m : ℕ} {r i : Fin m} (hne : i ≠ r) (ans : Fin m → Bool) :
    deliverCoord r ans i = deliverCoordNonMember r (ans i) i := by
  apply Prod.ext
  · funext s hs
    cases hs
    rfl
  · exact deliverGather_eq_of_ne hne ans 0 (List.finRange m)

private theorem map_deliverCoord_restrict {m k : ℕ} [NeZero m]
    (I : Finset (Fin m)) (y : Fin m → BitString k) (coord : Fin m × Fin k) :
    ((ProbComp.eval (ProbComp.sampleAdditiveShares m
        (extendByZero I (I.restrict y) coord.1 coord.2))).map (deliverCoord coord.1)).map
      I.restrict =
    ((ProbComp.eval (ProbComp.sampleAdditiveShares m (y coord.1 coord.2))).map
        (deliverCoord coord.1)).map I.restrict := by
  by_cases hr : coord.1 ∈ I
  · simp [hr]
  · have hI : I ≠ Finset.univ := fun h => hr (h ▸ Finset.mem_univ coord.1)
    have hfactor : ∀ b : Bool,
        ((ProbComp.eval (ProbComp.sampleAdditiveShares m b)).map (deliverCoord coord.1)).map
            I.restrict =
          ((ProbComp.eval (ProbComp.sampleAdditiveShares m b)).map I.restrict).map
            (fun ansI (i : I) => deliverCoordNonMember coord.1 (ansI i) i.1) := by
      intro b
      rw [PMF.map_comp, PMF.map_comp]
      congr 1
      funext ans ⟨i, hi⟩
      exact deliverCoord_eq_nonMember (by rintro rfl; exact hr hi) ans
    rw [hfactor, hfactor,
      ProbComp.eval_restrict_sampleAdditiveShares I hI _,
      ProbComp.eval_restrict_sampleAdditiveShares I hI _]

private theorem eval_outCoordsDist_restrict {m k : ℕ} [NeZero m]
    (I : Finset (Fin m)) (y : Fin m → BitString k) (L : List (Fin m × Fin k)) :
    (ProbComp.eval (outCoordsDist m k (extendByZero I (I.restrict y)) L)).map I.restrict =
      (ProbComp.eval (outCoordsDist m k y L)).map I.restrict := by
  induction L with
  | nil => rfl
  | cons coord L ih =>
    have hfactor : ∀ y' : Fin m → BitString k,
        (ProbComp.eval (outCoordsDist m k y' (coord :: L))).map I.restrict =
          (((ProbComp.eval (ProbComp.sampleAdditiveShares m (y' coord.1 coord.2))).map
              (deliverCoord coord.1)).map I.restrict).bind fun rI_head =>
            ((ProbComp.eval (outCoordsDist m k y' L)).map I.restrict).map
              fun rI_tail (i : I) => Schedule.Received.append (rI_head i) (rI_tail i) := by
      intro y'
      simp only [outCoordsDist, ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp,
        PMF.map_bind, PMF.bind_map, PMF.map_comp]
      rfl
    rw [hfactor (extendByZero I (I.restrict y)), hfactor y,
      map_deliverCoord_restrict I y coord, ih]

private theorem eval_outputDist_restrict {m k : ℕ} [NeZero m]
    (I : Finset (Fin m)) (y : Fin m → BitString k) :
    (ProbComp.eval (outputDist m k (extendByZero I (I.restrict y)))).map I.restrict =
      (ProbComp.eval (outputDist m k y)).map I.restrict :=
  eval_outCoordsDist_restrict I y (outCoords m k)

end GMWCircuit

open GMWCircuit

/-- Complete schedule for `gmwCircuitProtocol m n k C` (Construction 7.5.10, p. 706, with Step 3
share refresh): Step 1 (`inputShareSchedule m n`), followed by Step 2 (`progSchedule m C.program`)
and Step 3 (`outputSchedule m k`). -/
@[expose, reducible] def gmwCircuitSchedule (m n k : ℕ)
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k)) :
    Schedule m (sharedMulSpec m) :=
  inputShareSchedule m n ++ (progSchedule m C.program ++ outputSchedule m k)

/-- Construction 7.5.10 (Goldreich Section 7.5.2.3, p. 706; cf. Construction 7.3.9, pp. 646–647),
adapted to De Morgan circuits (`Boolean.signature`) and arbitrary `C.outputs`:
`m`-party Boolean circuit evaluation protocol in the `sharedMulSpec m`-hybrid model.
In Step 1, party `i` samples `Fin n → Fin (m - 1) → Bool` from `sampleCoins i`, applies
`ProbComp.completeShares m (x i j)` to form the `m` shares of bit `j`, and sends share `r` via
`.message` rounds. Step 2 evaluates `C.program` gate by gate, and Step 3 refreshes each output
coordinate via one `sharedMulSpec m` call (multiplying by `constShare true`) before exchanging the
refreshed output shares via `.message` rounds. -/
@[expose] noncomputable def gmwCircuitProtocol (m n k : ℕ) [NeZero m]
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k)) :
    Protocol m (sharedMulSpec m) (gmwCircuitSchedule m n k C)
      (fun _ => BitString n) (fun _ => Fin n → Fin (m - 1) → Bool) (fun _ => BitString k) where
  sampleCoins _ := ProbComp.uniform (Fin n → Fin (m - 1) → Bool)
  steps :=
    (inputShareSteps m n).append
      ((progSteps m C.program).append (outputSteps m n k C))

namespace GMWCircuit

/-- Type of party `i`'s view in `gmwCircuitProtocol m n k C`. -/
private abbrev GMWCircuitView (m n k : ℕ)
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k)) (i : Fin m) : Type :=
  PartyView (fun _ => BitString n) (fun _ => Fin n → Fin (m - 1) → Bool)
    (gmwCircuitSchedule m n k C) i

/-- Joint view sampler for `gmwCircuitProtocol m n k C` given full input tuple `x` and output tuple
`y`: samples Step 1 coins `c`, Step 2 gate transcripts `r_prog`, and Step 3 output transcripts
`r_out` independently. -/
@[expose] noncomputable def gmwCircuitRealViews (m n k : ℕ)
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k))
    (x : (i : Fin m) → BitString n) (y : (i : Fin m) → BitString k) :
    ProbComp ((i : Fin m) →
      PartyView (fun _ => BitString n) (fun _ => Fin n → Fin (m - 1) → Bool)
        (gmwCircuitSchedule m n k C) i) := do
  let c ← OracleComp.pi (fun _ : Fin m => ProbComp.uniform (Fin n → Fin (m - 1) → Bool))
  let r_prog ← progDist m (BitString.blocksEquiv.symm x) C.program
  let r_out ← outputDist m k y
  return fun i =>
    ⟨x i, c i,
      Schedule.Received.append (deliverInputShares x c i)
        (Schedule.Received.append (r_prog i) (r_out i))⟩

private theorem evalWith_gmwCircuitProtocol {m n k : ℕ} [NeZero m]
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k))
    (x : (i : Fin m) → BitString n) :
    (gmwCircuitProtocol m n k C).evalWith (sharedMulWorld m) x =
      (ProbComp.eval (gmwCircuitRealViews m n k C x (circuitFunctionality m n k C x))).map
        (fun v => (v, circuitFunctionality m n k C x)) := by
  rw [Protocol.evalWith_eq]
  simp only [gmwCircuitProtocol, gmwCircuitRealViews,
    ProbComp.eval_bind, ProbComp.eval_map, PMF.map_bind, PMF.map_comp, bind_pure_comp,
    Function.comp_def]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun c _ => ?_
  rw [Steps.evalWith_append, evalWith_inputShareSteps, PMF.pure_bind]
  have hprog := evalWith_progSteps (BitString.blocksEquiv.symm x) C.program
    (fun i => (inputShareSteps m n).outputAt i (x i, c i) (deliverInputShares x c i))
    (sum_outputAt_inputShareSteps x c)
  rw [Steps.evalWith_append, hprog.1, PMF.map_bind, PMF.map_bind]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun r_prog hr_prog => ?_
  have hout := evalWith_outputSteps C x
    (fun i => (progSteps m C.program).outputAt i
      ((inputShareSteps m n).outputAt i (x i, c i) (deliverInputShares x c i)) (r_prog i))
    (hprog.2 r_prog hr_prog)
  rw [hout.1, PMF.map_comp, PMF.map_comp]
  refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun r_out hr_out => ?_
  refine Prod.ext rfl (funext fun i => ?_)
  simpa [Protocol.outputOfView] using hout.2 r_out hr_out i

private theorem eval_gmwCircuitRealViews_restrict {m n k : ℕ} [NeZero m]
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k))
    (I : Finset (Fin m))
    (x : (i : Fin m) → BitString n) (y : (i : Fin m) → BitString k) :
    (ProbComp.eval (gmwCircuitRealViews m n k C
        (extendByZero I (I.restrict x)) (extendByZero I (I.restrict y)))).map I.restrict =
      (ProbComp.eval (gmwCircuitRealViews m n k C x y)).map I.restrict := by
  have hfactor : ∀ (x' : (i : Fin m) → BitString n) (y' : (i : Fin m) → BitString k)
      (hx' : ∀ i : I, x' i.1 = x i.1),
      (ProbComp.eval (gmwCircuitRealViews m n k C x' y')).map I.restrict =
        ((ProbComp.eval (OracleComp.pi (fun _ : Fin m =>
            ProbComp.uniform (Fin n → Fin (m - 1) → Bool)))).map
          (fun c (i : I) => (c i.1, deliverInputShares x' c i.1))).bind fun cI =>
          ((ProbComp.eval (progDist m (BitString.blocksEquiv.symm x') C.program)).map
              I.restrict).bind
            fun rI_prog =>
              ((ProbComp.eval (outputDist m k y')).map I.restrict).map fun rI_out (i : I) =>
                (⟨x i.1, (cI i).1,
                  Schedule.Received.append (cI i).2
                    (Schedule.Received.append (rI_prog i) (rI_out i))⟩ :
                  GMWCircuitView m n k C i.1) := by
    intro x' y' hx'
    simp only [gmwCircuitRealViews, ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp,
      PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def, I.restrict_def]
    refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun c _ => ?_
    refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun r_prog _ => ?_
    congr 1
    funext r_out i
    simp [hx' i]
  rw [hfactor (extendByZero I (I.restrict x)) (extendByZero I (I.restrict y))
      (fun i => extendByZero_of_mem I (I.restrict x) i.2),
    hfactor x y (fun _ => rfl),
    eval_inputShare_restrict m n I x,
    eval_progDist_restrict I x C.program,
    eval_outputDist_restrict I y]

end GMWCircuit

/-- Output correctness of `gmwCircuitProtocol`: every outcome in the support of
`(gmwCircuitProtocol m n k C).evalWith (sharedMulWorld m) x` produces output tuple
`circuitFunctionality m n k C x`. -/
theorem snd_eq_circuitFunctionality_of_mem_support_evalWith {m n k : ℕ} [NeZero m]
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k))
    (x : (i : Fin m) → BitString n)
    {res : ((i : Fin m) →
      PartyView (fun _ => BitString n) (fun _ => Fin n → Fin (m - 1) → Bool)
        (gmwCircuitSchedule m n k C) i) × ((i : Fin m) → BitString k)}
    (hres : res ∈ ((gmwCircuitProtocol m n k C).evalWith (sharedMulWorld m) x).support) :
    res.2 = circuitFunctionality m n k C x := by
  rw [evalWith_gmwCircuitProtocol, PMF.mem_support_map_iff] at hres
  obtain ⟨_, _, rfl⟩ := hres
  rfl

/-- Simulator for `gmwCircuitProtocol m n k C` (Proposition 7.5.11, pp. 706–707; cf.
Proposition 7.3.10, pp. 647–648): extends the coalition's inputs `xI` and outputs `yI` by padding
honest parties outside `I` with `0`, runs `gmwCircuitRealViews` on the extended tuples, and
restricts the resulting party views to `I`. -/
@[expose] noncomputable def gmwCircuitSim (m n k : ℕ)
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k))
    (I : Finset (Fin m)) :
    CoalitionSimulator (gmwCircuitSchedule m n k C)
      (fun _ => BitString n) (fun _ => Fin n → Fin (m - 1) → Bool) (fun _ => BitString k) I :=
  fun xI yI =>
    I.restrict <$> gmwCircuitRealViews m n k C (extendByZero I xI) (extendByZero I yI)

/-- Proposition 7.5.11 (Goldreich Section 7.5.2.3, pp. 706–707; cf. Proposition 7.3.10,
pp. 647–648), adapted to De Morgan circuits (`Boolean.signature`) and arbitrary `C.outputs` via
Step 3 share refresh: `gmwCircuitProtocol m n k C` perfectly and privately computes
`Functionality.ofDeterministic (circuitFunctionality m n k C)` in `sharedMulWorld m` against every
static coalition `I : Finset (Fin m)`. -/
theorem perfectSemiHonestPrivate_gmwCircuit (m n k : ℕ) [NeZero m]
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n) (m * k)) :
    PerfectSemiHonestPrivate
      (gmwCircuitProtocol m n k C) (sharedMulWorld m)
      (Functionality.ofDeterministic (circuitFunctionality m n k C))
      (gmwCircuitSim m n k C) := by
  refine perfectSemiHonestPrivate_of_deterministic _ _ _ _ (fun I x => ?_)
    (fun x _ hr => snd_eq_circuitFunctionality_of_mem_support_evalWith C x hr)
  rw [gmwCircuitSim, ProbComp.eval_map, evalWith_gmwCircuitProtocol, PMF.map_comp]
  exact eval_gmwCircuitRealViews_restrict C I x (circuitFunctionality m n k C x)

end Cslib.Crypto.Protocols.MPC
