/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle
public import Complexity.Languages.Probabilistic.Sharing

/-!
# Multi-party oracle-aided protocols and semi-honest privacy

This module defines the party-structured syntax and execution semantics of synchronous `m`-party
protocols over pairwise private authenticated point-to-point channels with `k`-ary ideal oracle
calls (`MultiOracleSpec`), together with Goldreich's joint view-and-output definition of perfect
semi-honest privacy against static coalitions (`PerfectSemiHonestPrivate`).

`PerfectSemiHonestPrivate` departs from Goldreich's Definitions 7.2.1 and 7.5.1 in two ways.
Privacy is exact equality of distributions, not computational indistinguishability. The coalition
simulators are arbitrary `ProbComp` values with no efficiency requirement, whereas Goldreich asks
for a probabilistic polynomial-time simulator. Efficient simulators for the $\text{OT}_1^4$
completeness theorem are certified separately, in `Complexity.Crypto.Protocols.MPC.PolyTime`.

Each party's view (`PartyView`) is derived from the protocol execution: it records only that
party's own input `x i`, its own private coins `r i` drawn from `proto.sampleCoins i`, the messages
addressed to `i`, and the oracle answer parts for slots assigned to `i`. In `Round.Received`,
message delivery to `receiver` has type `(i = receiver) → Msg` and oracle answer delivery has
type `(s : Fin (spec.arity op)) → (parties s = i) → spec.Answer op s`, so parties outside the
recipient set receive functions over an empty proof domain and transport under party embeddings is
definitional function composition. Each party's output (`Protocol.outputOfView`) is extracted
deterministically from its own `PartyView`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.MultiOracleSpec`,
  `Cslib.Crypto.Protocols.MPC.MultiOracleSpec.toOracleSpec`,
  `Cslib.Crypto.Protocols.MPC.MultiOracleWorld`,
  `Cslib.Crypto.Protocols.MPC.MultiOracleWorld.handler`,
  `Cslib.Crypto.Protocols.MPC.noOracleSpec`,
  `Cslib.Crypto.Protocols.MPC.noOracleWorld`: `k`-ary ideal oracle specifications and memoryless
  worlds.
* `Cslib.Crypto.Protocols.MPC.Round`, `Cslib.Crypto.Protocols.MPC.Schedule`,
  `Cslib.Crypto.Protocols.MPC.Round.Received`, `Cslib.Crypto.Protocols.MPC.Schedule.Received`,
  `Cslib.Crypto.Protocols.MPC.PartyView`: synchronous communication schedules and derived
  per-party views.
* `Cslib.Crypto.Protocols.MPC.Steps`, `Cslib.Crypto.Protocols.MPC.Protocol`,
  `Cslib.Crypto.Protocols.MPC.Protocol.outputOfView`,
  `Cslib.Crypto.Protocols.MPC.Steps.mapState`, `Cslib.Crypto.Protocols.MPC.Steps.append`,
  `Cslib.Crypto.Protocols.MPC.Steps.run`, `Cslib.Crypto.Protocols.MPC.Protocol.run`,
  `Cslib.Crypto.Protocols.MPC.Protocol.evalWith`, `Cslib.Crypto.Protocols.MPC.Protocol.realJoint`:
  local step-by-step party strategies and their real execution semantics.
* `Cslib.Crypto.Protocols.MPC.Functionality`,
  `Cslib.Crypto.Protocols.MPC.Functionality.ofDeterministic`,
  `Cslib.Crypto.Protocols.MPC.CoalitionSimulator`, `Cslib.Crypto.Protocols.MPC.idealJoint`,
  `Cslib.Crypto.Protocols.MPC.PerfectSemiHonestPrivate`,
  `Cslib.Crypto.Protocols.MPC.PerfectSemiHonestPrivateProper`: ideal joint view-and-output
  execution and perfect semi-honest privacy.

## Main results

* `Cslib.Crypto.Protocols.MPC.Schedule.Received.split_append`,
  `Cslib.Crypto.Protocols.MPC.Schedule.Received.append_split`: splitting and concatenating
  received transcripts along concatenated schedules.
* `Cslib.Crypto.Protocols.MPC.Protocol.evalWith_eq`,
  `Cslib.Crypto.Protocols.MPC.Steps.evalWith_done`,
  `Cslib.Crypto.Protocols.MPC.Steps.evalWith_message`,
  `Cslib.Crypto.Protocols.MPC.Steps.evalWith_oracle`: structural evaluation rules for protocols
  and steps.
* `Cslib.Crypto.Protocols.MPC.PerfectSemiHonestPrivate.proper`: full-coalition privacy implies
  proper-coalition privacy.
* `Cslib.Crypto.Protocols.MPC.perfectSemiHonestPrivate_of_deterministic`: for deterministic
  functionalities, matching the marginal coalition view distribution (Eq. 7.39, cf. Eqs. 7.7–7.8)
  together with output correctness on the support yields full joint view-and-output privacy
  (Eq. 7.40, cf. Eqs. 7.9–7.10).

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.2.2.1 (Definition 7.2.1, pp. 620–622), Section 7.5.1.2 (Definition 7.5.1, pp. 696–697),
  and Section 7.5.2.1 (Definitions 7.5.5–7.5.6, pp. 701–702).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.MPC

open Probability

/-! ### Multi-party oracle specifications and worlds -/

/-- Specification of `k`-ary oracle operations (Goldreich Def. 7.5.5, pp. 701–702). -/
structure MultiOracleSpec where
  /-- The type of oracle operations. -/
  Op : Type
  /-- The arity `k` of each operation. -/
  arity : Op → ℕ
  /-- The query part submitted by slot `s : Fin (arity op)`. -/
  Query : (op : Op) → Fin (arity op) → Type
  /-- The answer part returned to slot `s : Fin (arity op)`. -/
  Answer : (op : Op) → Fin (arity op) → Type

/-- Underlying `OracleSpec` of a `MultiOracleSpec`. -/
abbrev MultiOracleSpec.toOracleSpec (spec : MultiOracleSpec) :
    OracleSpec (Σ op : spec.Op, (s : Fin (spec.arity op)) → spec.Query op s) :=
  fun q => (s : Fin (spec.arity q.1)) → spec.Answer q.1 s

/-- A memoryless implementation (world) of `spec`. -/
abbrev MultiOracleWorld (spec : MultiOracleSpec) :=
  (op : spec.Op) → ((s : Fin (spec.arity op)) → spec.Query op s) →
    ProbComp ((s : Fin (spec.arity op)) → spec.Answer op s)

/-- Combined `PMF` handler for `ProbOracleComp spec.toOracleSpec` in a memoryless world `W`. -/
noncomputable def MultiOracleWorld.handler {spec : MultiOracleSpec}
    (W : MultiOracleWorld spec) :
    (q : ℕ ⊕ (Σ op : spec.Op, (s : Fin (spec.arity op)) → spec.Query op s)) →
      PMF (probOracleSpec spec.toOracleSpec q) :=
  ProbOracleComp.handler (spec := spec.toOracleSpec) ProbComp.unifOracle
    (fun q => ProbComp.eval (W q.1 q.2))

/-- The empty multi-party oracle specification (plain point-to-point channel model). -/
def noOracleSpec : MultiOracleSpec where
  Op := Empty
  arity := Empty.elim
  Query := fun op => op.elim
  Answer := fun op => op.elim

/-- The unique world for `noOracleSpec`. -/
def noOracleWorld : MultiOracleWorld noOracleSpec :=
  fun op => Empty.elim op

/-! ### Synchronous rounds, schedules, and received transcripts -/

/-- A single synchronous step in an `m`-party protocol over pairwise private point-to-point
channels and `k`-ary oracle `spec`. -/
inductive Round (m : ℕ) (spec : MultiOracleSpec) : Type 1 where
  /-- Point-to-point private message of type `Msg` from `sender` to `receiver`. -/
  | message (sender receiver : Fin m) (Msg : Type)
  /-- Joint `k`-ary oracle invocation of `op` by `k` distinct parties `parties`. -/
  | oracle (op : spec.Op) (parties : Fin (spec.arity op) ↪ Fin m)

/-- A fixed-schedule `m`-party protocol shape over `spec`. -/
abbrev Schedule (m : ℕ) (spec : MultiOracleSpec) : Type 1 := List (Round m spec)

/-- What party `i` receives in round `r`, using proof-domain functions so transport under
party embeddings is definitional function composition without `if`-casts. -/
@[reducible] def Round.Received {m : ℕ} {spec : MultiOracleSpec} :
    Round m spec → Fin m → Type
  | .message _ receiver Msg, i => (i = receiver) → Msg
  | .oracle op parties, i =>
    (s : Fin (spec.arity op)) → (parties s = i) → spec.Answer op s

/-- Deliver a point-to-point message `msg` to `receiver`; parties `i ≠ receiver` have an empty
proof domain `i = receiver`. -/
def Round.deliverMessage {m : ℕ} {spec : MultiOracleSpec}
    {sender receiver : Fin m} {Msg : Type} (msg : Msg) (i : Fin m) :
    (Round.message (spec := spec) sender receiver Msg).Received i :=
  fun _ => msg

/-- Deliver oracle answer parts `ans` to the participating `parties`; for slots `s` with
`parties s ≠ i`, the proof domain `parties s = i` is empty. -/
def Round.deliverOracle {m : ℕ} {spec : MultiOracleSpec} {op : spec.Op}
    (parties : Fin (spec.arity op) ↪ Fin m)
    (ans : (s : Fin (spec.arity op)) → spec.Answer op s) (i : Fin m) :
    (Round.oracle op parties).Received i :=
  fun s _ => ans s

@[simp] theorem Round.deliverMessage_apply {m : ℕ} {spec : MultiOracleSpec}
    {sender receiver i : Fin m} {Msg : Type} (msg : Msg) (h : i = receiver) :
    Round.deliverMessage (spec := spec) (sender := sender) msg i h = msg := rfl

@[simp] theorem Round.deliverOracle_apply {m : ℕ} {spec : MultiOracleSpec} {op : spec.Op}
    (parties : Fin (spec.arity op) ↪ Fin m)
    (ans : (s : Fin (spec.arity op)) → spec.Answer op s)
    (i : Fin m) (s : Fin (spec.arity op)) (h : parties s = i) :
    Round.deliverOracle parties ans i s h = ans s := rfl

/-- For a non-recipient `i ≠ receiver`, any two received-message records are equal. -/
theorem Round.received_message_eq_of_ne {m : ℕ} {spec : MultiOracleSpec}
    {sender receiver i : Fin m} {Msg : Type} (hne : i ≠ receiver)
    (f g : (Round.message (spec := spec) sender receiver Msg).Received i) : f = g :=
  funext fun h => (hne h).elim

/-- Two received-message records at `i` are equal if they agree when `i = receiver`. -/
theorem Round.received_message_ext {m : ℕ} {spec : MultiOracleSpec}
    {sender receiver i : Fin m} {Msg : Type}
    {f g : (Round.message (spec := spec) sender receiver Msg).Received i}
    (h : ∀ hr : i = receiver, f hr = g hr) : f = g :=
  funext h

/-- Two received-oracle records at `i` are equal if they agree on every slot assigned to `i`. -/
theorem Round.received_oracle_ext {m : ℕ} {spec : MultiOracleSpec} {op : spec.Op}
    {parties : Fin (spec.arity op) ↪ Fin m} {i : Fin m}
    {f g : (Round.oracle op parties).Received i}
    (h : ∀ (s : Fin (spec.arity op)) (hs : parties s = i), f s hs = g s hs) : f = g :=
  funext fun s => funext (h s)

/-- The sequence of values received by party `i` across all rounds of `sc`. -/
@[reducible] def Schedule.Received {m : ℕ} {spec : MultiOracleSpec} :
    Schedule m spec → Fin m → Type
  | [], _ => Unit
  | r :: sc, i => r.Received i × Schedule.Received sc i

/-- Concatenate received transcripts along `sc₁` and `sc₂` into a transcript along `sc₁ ++ sc₂`. -/
def Schedule.Received.append {m : ℕ} {spec : MultiOracleSpec}
    {sc₁ sc₂ : Schedule m spec} {i : Fin m} :
    sc₁.Received i → sc₂.Received i → (sc₁ ++ sc₂).Received i :=
  match sc₁ with
  | [] => fun _ r₂ => r₂
  | _ :: sc₁ => fun r₁ r₂ => (r₁.1, Schedule.Received.append (sc₁ := sc₁) r₁.2 r₂)

/-- Split a received transcript along `sc₁ ++ sc₂` into transcripts along `sc₁` and `sc₂`. -/
def Schedule.Received.split {m : ℕ} {spec : MultiOracleSpec}
    {sc₁ sc₂ : Schedule m spec} {i : Fin m} :
    (sc₁ ++ sc₂).Received i → sc₁.Received i × sc₂.Received i :=
  match sc₁ with
  | [] => fun r => ((), r)
  | _ :: sc₁ => fun r =>
    let p := Schedule.Received.split (sc₁ := sc₁) r.2
    ((r.1, p.1), p.2)

@[simp] theorem Schedule.Received.split_append {m : ℕ} {spec : MultiOracleSpec}
    {sc₁ sc₂ : Schedule m spec} {i : Fin m}
    (r₁ : sc₁.Received i) (r₂ : sc₂.Received i) :
    Schedule.Received.split (sc₁ := sc₁) (Schedule.Received.append r₁ r₂) = (r₁, r₂) := by
  induction sc₁ with
  | nil => rfl
  | cons _ sc₁ ih => simp [Schedule.Received.append, Schedule.Received.split, ih]

@[simp] theorem Schedule.Received.append_split {m : ℕ} {spec : MultiOracleSpec}
    {sc₁ sc₂ : Schedule m spec} {i : Fin m}
    (r : (sc₁ ++ sc₂).Received i) :
    Schedule.Received.append
      (Schedule.Received.split (sc₁ := sc₁) r).1
      (Schedule.Received.split (sc₁ := sc₁) r).2 = r := by
  induction sc₁ with
  | nil => rfl
  | cons _ sc₁ ih =>
    rcases r with ⟨r_head, r_tail⟩
    simp [Schedule.Received.append, Schedule.Received.split, ih]

/-- Party `i`'s complete view of an execution along schedule `sc` (Goldreich Def. 7.2.1, p. 620). -/
@[ext] structure PartyView {m : ℕ} {spec : MultiOracleSpec}
    (In Coins : Fin m → Type) (sc : Schedule m spec) (i : Fin m) where
  /-- Party `i`'s input. -/
  input : In i
  /-- Party `i`'s private random coins. -/
  coins : Coins i
  /-- Messages and oracle answers received by party `i` along `sc`. -/
  received : sc.Received i

/-! ### Party-structured protocols and execution semantics -/

/-- Local step-by-step party computations along schedule `sc`, with `State` and `Out` as indices
after the colon so Lean's kernel accepts the varying state type in `next`. -/
inductive Steps {m : ℕ} {spec : MultiOracleSpec} :
    (Fin m → Type) → (Fin m → Type) → Schedule m spec → Type 1 where
  /-- End of interaction: each party `i` deterministically computes its output from its local
  state. -/
  | done {State Out : Fin m → Type} (output : (i : Fin m) → State i → Out i) :
      Steps State Out []
  /-- Point-to-point message round: `sender` computes `Msg` from its local state, `receiver`
  receives it, and execution continues with each party's state augmented by its `Round.Received`
  record. -/
  | message {State Out : Fin m → Type} {sender receiver : Fin m} {Msg : Type}
      {sc : Schedule m spec} (send : State sender → Msg)
      (next :
        Steps (fun i => State i × (Round.message (spec := spec) sender receiver Msg).Received i)
          Out sc) :
      Steps State Out (.message sender receiver Msg :: sc)
  /-- Joint `k`-ary oracle round: each participating party `parties s` computes its query part
  from its own local state, the oracle returns answer parts, and execution continues with each
  party's state augmented by its `Round.Received` record. -/
  | oracle {State Out : Fin m → Type} {op : spec.Op}
      {parties : Fin (spec.arity op) ↪ Fin m} {sc : Schedule m spec}
      (query : (s : Fin (spec.arity op)) → State (parties s) → spec.Query op s)
      (next : Steps (fun i => State i × (Round.oracle op parties).Received i) Out sc) :
      Steps State Out (.oracle op parties :: sc)

/-- An `m`-party protocol along schedule `sc`. -/
structure Protocol (m : ℕ) (spec : MultiOracleSpec) (sc : Schedule m spec)
    (In Coins Out : Fin m → Type) where
  /-- Independent private coin sampler for each party `i`. -/
  sampleCoins : (i : Fin m) → ProbComp (Coins i)
  /-- Interactive step-by-step party computations starting from `(input, coins)`. -/
  steps : Steps (fun i => In i × Coins i) Out sc

/-- Extract party `i`'s output from its own current local state `st_i` and its own remaining
received transcript `recv_i` along `sc`. -/
def Steps.outputAt {m : ℕ} {spec : MultiOracleSpec} {State Out : Fin m → Type}
    {sc : Schedule m spec} (steps : Steps State Out sc) (i : Fin m)
    (st_i : State i) (recv_i : sc.Received i) : Out i :=
  match steps, recv_i with
  | .done output, () => output i st_i
  | .message _ next, (r_head, r_tail) => next.outputAt i (st_i, r_head) r_tail
  | .oracle _ next, (r_head, r_tail) => next.outputAt i (st_i, r_head) r_tail

/-- Deterministic extraction of party `i`'s output from its complete `PartyView`. -/
def Protocol.outputOfView {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec}
    {In Coins Out : Fin m → Type} (proto : Protocol m spec sc In Coins Out)
    (i : Fin m) (v : PartyView In Coins sc i) : Out i :=
  proto.steps.outputAt i (v.input, v.coins) v.received

/-- Execute `steps` in `ProbOracleComp spec.toOracleSpec` from current local states `st`,
returning each party's received transcript along `sc`. -/
def Steps.run {m : ℕ} {spec : MultiOracleSpec} {State Out : Fin m → Type}
    {sc : Schedule m spec} (steps : Steps State Out sc) (st : (i : Fin m) → State i) :
    ProbOracleComp spec.toOracleSpec ((i : Fin m) → sc.Received i) :=
  match steps with
  | .done _ => pure (fun _ => ())
  | .message (sender := sender) send next => do
    let r_head : (i : Fin m) → _ := Round.deliverMessage (send (st sender))
    let r_tail ← next.run (fun i => (st i, r_head i))
    return fun i => (r_head i, r_tail i)
  | .oracle (op := op) (parties := parties) query next => do
    let ans ← ProbOracleComp.query (spec := spec.toOracleSpec)
      ⟨op, fun s => query s (st (parties s))⟩
    let r_head : (i : Fin m) → _ := Round.deliverOracle parties ans
    let r_tail ← next.run (fun i => (st i, r_head i))
    return fun i => (r_head i, r_tail i)

/-- Pinned execution of `proto` on input tuple `x` in `ProbOracleComp spec.toOracleSpec`:
samples each party's coins independently, runs `proto.steps`, and sets outputs to
`fun i => proto.outputOfView i (views i)` by definition. -/
def Protocol.run {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec}
    {In Coins Out : Fin m → Type} (proto : Protocol m spec sc In Coins Out)
    (x : (i : Fin m) → In i) :
    ProbOracleComp spec.toOracleSpec
      (((i : Fin m) → PartyView In Coins sc i) × ((i : Fin m) → Out i)) := do
  let r ← ProbOracleComp.sample (OracleComp.pi proto.sampleCoins)
  let recv ← proto.steps.run (fun i => (x i, r i))
  let views : (i : Fin m) → PartyView In Coins sc i := fun i => ⟨x i, r i, recv i⟩
  return (views, fun i => proto.outputOfView i (views i))

/-- Evaluate `steps.run st` against `W : MultiOracleWorld spec` via `OracleComp.evalWith`. -/
noncomputable def Steps.evalWith {m : ℕ} {spec : MultiOracleSpec} {State Out : Fin m → Type}
    {sc : Schedule m spec} (steps : Steps State Out sc) (W : MultiOracleWorld spec)
    (st : (i : Fin m) → State i) : PMF ((i : Fin m) → sc.Received i) :=
  OracleComp.evalWith W.handler (steps.run st)

@[simp] theorem Steps.evalWith_done {m : ℕ} {spec : MultiOracleSpec} {State Out : Fin m → Type}
    (output : (i : Fin m) → State i → Out i) (W : MultiOracleWorld spec)
    (st : (i : Fin m) → State i) :
    (Steps.done (spec := spec) output).evalWith W st = PMF.pure (fun _ => ()) := rfl

@[simp] theorem Steps.evalWith_message {m : ℕ} {spec : MultiOracleSpec} {State Out : Fin m → Type}
    {sender receiver : Fin m} {Msg : Type} {sc : Schedule m spec}
    (send : State sender → Msg)
    (next :
      Steps (fun i => State i × (Round.message (spec := spec) sender receiver Msg).Received i)
        Out sc)
    (W : MultiOracleWorld spec) (st : (i : Fin m) → State i) :
    (Steps.message send next).evalWith W st =
      (next.evalWith W (fun i => (st i, Round.deliverMessage (send (st sender)) i))).map
        (fun r_tail i => (Round.deliverMessage (send (st sender)) i, r_tail i)) := by
  simp [Steps.evalWith, Steps.run, bind_pure_comp]

@[simp] theorem Steps.evalWith_oracle {m : ℕ} {spec : MultiOracleSpec} {State Out : Fin m → Type}
    {op : spec.Op} {parties : Fin (spec.arity op) ↪ Fin m} {sc : Schedule m spec}
    (query : (s : Fin (spec.arity op)) → State (parties s) → spec.Query op s)
    (next : Steps (fun i => State i × (Round.oracle op parties).Received i) Out sc)
    (W : MultiOracleWorld spec) (st : (i : Fin m) → State i) :
    (Steps.oracle query next).evalWith W st =
      (ProbComp.eval (W op (fun s => query s (st (parties s))))).bind fun ans =>
        (next.evalWith W (fun i => (st i, Round.deliverOracle parties ans i))).map
          (fun r_tail i => (Round.deliverOracle parties ans i, r_tail i)) := by
  simp [Steps.evalWith, Steps.run, MultiOracleWorld.handler, ProbOracleComp.query,
    ProbOracleComp.handler, bind_pure_comp]

/-- Evaluate `proto.run x` against `W : MultiOracleWorld spec` via `OracleComp.evalWith`. -/
noncomputable def Protocol.evalWith {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec}
    {In Coins Out : Fin m → Type} (proto : Protocol m spec sc In Coins Out)
    (W : MultiOracleWorld spec) (x : (i : Fin m) → In i) :
    PMF (((i : Fin m) → PartyView In Coins sc i) × ((i : Fin m) → Out i)) :=
  OracleComp.evalWith W.handler (proto.run x)

/-- Precompose a step-by-step protocol computation with a local state transformation `f`. -/
def Steps.mapState {m : ℕ} {spec : MultiOracleSpec} {A B Out : Fin m → Type}
    {sc : Schedule m spec} (f : (i : Fin m) → A i → B i)
    (steps : Steps B Out sc) : Steps A Out sc :=
  match steps with
  | .done output => .done (fun i a => output i (f i a))
  | .message (sender := sender) send next =>
    .message (fun a => send (f sender a))
      (next.mapState (fun i p => (f i p.1, p.2)))
  | .oracle (parties := parties) query next =>
    .oracle (fun s a => query s (f (parties s) a))
      (next.mapState (fun i p => (f i p.1, p.2)))

@[simp] theorem Steps.outputAt_mapState {m : ℕ} {spec : MultiOracleSpec}
    {A B Out : Fin m → Type} {sc : Schedule m spec}
    (f : (i : Fin m) → A i → B i) (steps : Steps B Out sc)
    (i : Fin m) (st_i : A i) (recv_i : sc.Received i) :
    (steps.mapState f).outputAt i st_i recv_i = steps.outputAt i (f i st_i) recv_i := by
  induction steps generalizing A with
  | done output => cases recv_i; rfl
  | message send next ih =>
    rcases recv_i with ⟨r_head, r_tail⟩
    exact ih (fun j (p : A j × _) => (f j p.1, p.2)) (st_i, r_head) r_tail
  | oracle query next ih =>
    rcases recv_i with ⟨r_head, r_tail⟩
    exact ih (fun j (p : A j × _) => (f j p.1, p.2)) (st_i, r_head) r_tail

@[simp] theorem Steps.run_mapState {m : ℕ} {spec : MultiOracleSpec}
    {A B Out : Fin m → Type} {sc : Schedule m spec}
    (f : (i : Fin m) → A i → B i) (steps : Steps B Out sc) (st : (i : Fin m) → A i) :
    (steps.mapState f).run st = steps.run (fun i => f i (st i)) := by
  induction steps generalizing A with
  | done output => rfl
  | message send next ih =>
    simp [Steps.mapState, Steps.run, ih]
  | oracle query next ih =>
    simp [Steps.mapState, Steps.run, ih]

@[simp] theorem Steps.evalWith_mapState {m : ℕ} {spec : MultiOracleSpec}
    {A B Out : Fin m → Type} {sc : Schedule m spec}
    (f : (i : Fin m) → A i → B i) (steps : Steps B Out sc)
    (W : MultiOracleWorld spec) (st : (i : Fin m) → A i) :
    (steps.mapState f).evalWith W st = steps.evalWith W (fun i => f i (st i)) := by
  simp [Steps.evalWith]

/-- Sequentially compose `steps₁ : Steps State Mid sc₁` (whose `.done` node computes each
party's intermediate state `Mid i`) with `steps₂ : Steps Mid Out sc₂` along `sc₁ ++ sc₂`. -/
def Steps.append {m : ℕ} {spec : MultiOracleSpec} {State Mid Out : Fin m → Type}
    {sc₁ sc₂ : Schedule m spec} (steps₁ : Steps State Mid sc₁)
    (steps₂ : Steps Mid Out sc₂) : Steps State Out (sc₁ ++ sc₂) :=
  match steps₁ with
  | .done mid => steps₂.mapState mid
  | .message send next => .message send (next.append steps₂)
  | .oracle query next => .oracle query (next.append steps₂)

@[simp] theorem Steps.outputAt_append {m : ℕ} {spec : MultiOracleSpec}
    {State Mid Out : Fin m → Type} {sc₁ sc₂ : Schedule m spec}
    (steps₁ : Steps State Mid sc₁) (steps₂ : Steps Mid Out sc₂)
    (i : Fin m) (st_i : State i) (r₁ : sc₁.Received i) (r₂ : sc₂.Received i) :
    (steps₁.append steps₂).outputAt i st_i (Schedule.Received.append r₁ r₂) =
      steps₂.outputAt i (steps₁.outputAt i st_i r₁) r₂ := by
  induction steps₁ with
  | done mid =>
    cases r₁
    simp [Steps.append, Steps.outputAt, Schedule.Received.append]
  | message send next ih =>
    rcases r₁ with ⟨r_head, r_tail⟩
    exact ih steps₂ (st_i, r_head) r_tail
  | oracle query next ih =>
    rcases r₁ with ⟨r_head, r_tail⟩
    exact ih steps₂ (st_i, r_head) r_tail

theorem Steps.run_append {m : ℕ} {spec : MultiOracleSpec}
    {State Mid Out : Fin m → Type} {sc₁ sc₂ : Schedule m spec}
    (steps₁ : Steps State Mid sc₁) (steps₂ : Steps Mid Out sc₂)
    (st : (i : Fin m) → State i) :
    (steps₁.append steps₂).run st = do
      let r₁ ← steps₁.run st
      let r₂ ← steps₂.run (fun i => steps₁.outputAt i (st i) (r₁ i))
      return fun i => Schedule.Received.append (r₁ i) (r₂ i) := by
  induction steps₁ with
  | done mid =>
    simp [Steps.append, Steps.run, Steps.outputAt, Schedule.Received.append]
  | message send next ih =>
    simp [Steps.append, Steps.run, ih, Steps.outputAt, Schedule.Received.append]
  | oracle query next ih =>
    simp [Steps.append, Steps.run, ih, bind_assoc, Steps.outputAt, Schedule.Received.append]

theorem Steps.evalWith_append {m : ℕ} {spec : MultiOracleSpec}
    {State Mid Out : Fin m → Type} {sc₁ sc₂ : Schedule m spec}
    (steps₁ : Steps State Mid sc₁) (steps₂ : Steps Mid Out sc₂)
    (W : MultiOracleWorld spec) (st : (i : Fin m) → State i) :
    (steps₁.append steps₂).evalWith W st =
      (steps₁.evalWith W st).bind fun r₁ =>
        (steps₂.evalWith W (fun i => steps₁.outputAt i (st i) (r₁ i))).map fun r₂ i =>
          Schedule.Received.append (r₁ i) (r₂ i) := by
  simp [Steps.evalWith, Steps.run_append, bind_pure_comp]

/-- Unfold `proto.evalWith W x` into independent coin sampling followed by
`proto.steps.evalWith W`. -/
theorem Protocol.evalWith_eq {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec}
    {In Coins Out : Fin m → Type} (proto : Protocol m spec sc In Coins Out)
    (W : MultiOracleWorld spec) (x : (i : Fin m) → In i) :
    proto.evalWith W x =
      (ProbComp.eval (OracleComp.pi proto.sampleCoins)).bind fun r =>
        (proto.steps.evalWith W (fun i => (x i, r i))).map fun recv =>
          let views : (i : Fin m) → PartyView In Coins sc i := fun i => ⟨x i, r i, recv i⟩
          (views, fun i => proto.outputOfView i (views i)) := by
  simp [Protocol.evalWith, Protocol.run, Steps.evalWith, MultiOracleWorld.handler,
    ProbOracleComp.handler_eq_sumHandler, ProbOracleComp.sample_eq_liftLeft,
    ProbComp.eval_eq_evalWith, bind_pure_comp]

/-- Every supported outcome of `proto.evalWith W x` has outputs equal to `proto.outputOfView` of its
views. -/
theorem Protocol.snd_eq_outputOfView_of_mem_support_evalWith {m : ℕ} {spec : MultiOracleSpec}
    {sc : Schedule m spec} {In Coins Out : Fin m → Type}
    {proto : Protocol m spec sc In Coins Out} {W : MultiOracleWorld spec}
    {x : (i : Fin m) → In i}
    {res : ((i : Fin m) → PartyView In Coins sc i) × ((i : Fin m) → Out i)}
    (h : res ∈ (proto.evalWith W x).support) :
    res.2 = fun i => proto.outputOfView i (res.1 i) := by
  rw [Protocol.evalWith_eq, PMF.mem_support_bind_iff] at h
  obtain ⟨r, _, hrecv⟩ := h
  rw [PMF.mem_support_map_iff] at hrecv
  obtain ⟨recv, _, rfl⟩ := hrecv
  rfl

/-- Real joint distribution of the coalition `I`'s views and all `m` parties' outputs when running
`proto` in world `W` on inputs `x` (Goldreich Def. 7.5.1, Eq. 7.40, p. 696). -/
noncomputable def Protocol.realJoint {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec}
    {In Coins Out : Fin m → Type} (proto : Protocol m spec sc In Coins Out)
    (W : MultiOracleWorld spec) (I : Finset (Fin m)) (x : (i : Fin m) → In i) :
    PMF (((i : I) → PartyView In Coins sc i) × ((i : Fin m) → Out i)) :=
  (proto.evalWith W x).map (Prod.map I.restrict id)

/-! ### Ideal functionalities, coalition simulators, and semi-honest privacy -/

/-- A general (possibly randomized) `m`-party functionality mapping an input tuple to a
distribution over output tuples. -/
abbrev Functionality (m : ℕ) (In Out : Fin m → Type) :=
  ((i : Fin m) → In i) → ProbComp ((i : Fin m) → Out i)

/-- Lift a deterministic `m`-party function to a `Functionality`. -/
def Functionality.ofDeterministic {m : ℕ} {In Out : Fin m → Type}
    (f : ((i : Fin m) → In i) → (i : Fin m) → Out i) : Functionality m In Out :=
  fun x => pure (f x)

/-- A simulator for a static coalition `I : Finset (Fin m)` receives the coalition's inputs
`(i : I) → In i` and the coalition's outputs `(i : I) → Out i`, and samples simulated views
`(i : I) → PartyView In Coins sc i`. It is an arbitrary `ProbComp`: unlike Goldreich's
simulators, it need not run in probabilistic polynomial time. -/
abbrev CoalitionSimulator {m : ℕ} {spec : MultiOracleSpec} (sc : Schedule m spec)
    (In Coins Out : Fin m → Type) (I : Finset (Fin m)) :=
  ((i : I) → In i) → ((i : I) → Out i) → ProbComp ((i : I) → PartyView In Coins sc i)

/-- Ideal joint view-and-output sampler (Goldreich Def. 7.2.1 Eqs. 7.9–7.10, p. 620; Def. 7.5.1
Eq. 7.40, p. 696): samples the full functionality output `y ← f x`, feeds the coalition's inputs
and outputs to the simulator `S`, and returns `(v, y)`. -/
def idealJoint {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec}
    {In Coins Out : Fin m → Type} (f : Functionality m In Out) (I : Finset (Fin m))
    (S : CoalitionSimulator sc In Coins Out I) (x : (i : Fin m) → In i) :
    ProbComp (((i : I) → PartyView In Coins sc i) × ((i : Fin m) → Out i)) := do
  let y ← f x
  let v ← S (I.restrict x) (I.restrict y)
  return (v, y)

/-- Perfect semi-honest privacy for all static coalitions `I : Finset (Fin m)`
(Goldreich Def. 7.5.1, Eq. 7.40, p. 696; cf. Def. 7.2.1, Eqs. 7.9–7.10, p. 620), with exact
equality in place of computational indistinguishability. The simulators `S` are unrestricted:
Goldreich requires a probabilistic polynomial-time simulator, and this definition does not. -/
def PerfectSemiHonestPrivate {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec}
    {In Coins Out : Fin m → Type} (proto : Protocol m spec sc In Coins Out)
    (W : MultiOracleWorld spec) (f : Functionality m In Out)
    (S : (I : Finset (Fin m)) → CoalitionSimulator sc In Coins Out I) : Prop :=
  ∀ (I : Finset (Fin m)) (x : (i : Fin m) → In i),
    ProbComp.eval (idealJoint f I (S I) x) = proto.realJoint W I x

/-- Perfect semi-honest privacy against all proper static coalitions `I ≠ Finset.univ`, with the
same exact equality and unrestricted simulators as `PerfectSemiHonestPrivate`. -/
def PerfectSemiHonestPrivateProper {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec}
    {In Coins Out : Fin m → Type} (proto : Protocol m spec sc In Coins Out)
    (W : MultiOracleWorld spec) (f : Functionality m In Out)
    (S : (I : Finset (Fin m)) → CoalitionSimulator sc In Coins Out I) : Prop :=
  ∀ (I : Finset (Fin m)), I ≠ Finset.univ → ∀ (x : (i : Fin m) → In i),
    ProbComp.eval (idealJoint f I (S I) x) = proto.realJoint W I x

/-- Full-coalition perfect semi-honest privacy implies proper-coalition privacy. -/
theorem PerfectSemiHonestPrivate.proper
    {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec} {In Coins Out : Fin m → Type}
    {proto : Protocol m spec sc In Coins Out} {W : MultiOracleWorld spec}
    {f : Functionality m In Out}
    {S : (I : Finset (Fin m)) → CoalitionSimulator sc In Coins Out I}
    (h : PerfectSemiHonestPrivate proto W f S) :
    PerfectSemiHonestPrivateProper proto W f S :=
  fun I _ x => h I x

/-- Bridge lemma (Goldreich Def. 7.5.1, Eqs. 7.39–7.40, p. 696; cf. Def. 7.2.1, Eqs. 7.7–7.10,
p. 620, and equivalence remark on p. 621): for a deterministic functionality `f`, matching the
marginal coalition view distribution (Eq. 7.39, cf. Eqs. 7.7–7.8) together with perfect output
correctness on the support yields full joint view-and-output privacy (Eq. 7.40, cf. Eqs. 7.9–7.10).
-/
theorem perfectSemiHonestPrivate_of_deterministic
    {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec} {In Coins Out : Fin m → Type}
    (proto : Protocol m spec sc In Coins Out) (W : MultiOracleWorld spec)
    (f : ((i : Fin m) → In i) → (i : Fin m) → Out i)
    (S : (I : Finset (Fin m)) → CoalitionSimulator sc In Coins Out I)
    (hView : ∀ I x,
      ProbComp.eval (S I (I.restrict x) (I.restrict (f x))) =
        (proto.evalWith W x).map (fun r => I.restrict r.1))
    (hOut : ∀ x r, r ∈ (proto.evalWith W x).support → r.2 = f x) :
    PerfectSemiHonestPrivate proto W (Functionality.ofDeterministic f) S := by
  intro I x
  simp only [idealJoint, Functionality.ofDeterministic, pure_bind, bind_pure_comp,
    ProbComp.eval_map, hView I x, PMF.map_comp, Protocol.realJoint]
  refine PMF.map_congr_on_support (proto.evalWith W x) _ _ fun r hr => ?_
  simp [Prod.map, hOut x r hr]

end Cslib.Crypto.Protocols.MPC
