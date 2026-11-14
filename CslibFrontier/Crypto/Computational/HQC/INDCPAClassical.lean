/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.HQC.INDCPA
public import CslibFrontier.Crypto.Primitives.HQC.Encoding
public import CslibFrontier.Computability.Probabilistic.CoinTape.Bounds
public import CslibFrontier.Computability.Probabilistic.PPT.PairCapture
public import CslibFrontier.Computability.Probabilistic.Sampling
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Composition.Space

/-!
# Classical word programs for the HQC IND-CPA reductions

This module starts the machine-certified classical layer below the exact finite game identities in
`CslibFrontier.Crypto.Computational.HQC.INDCPA`. It defines the actual typed probabilistic programs
for the two source distinguishers. `twoDQCSDProgram` receives an explicit coin sampler so the
production finite-word sampler and its approximation error remain visible; the ideal source game
is recovered only under an explicit equality of laws. `threeDQCSDProgram` has no encryption-coin
sampler and matches the finite 3-DQCSD-PT distinguisher directly.

The security parameter is encoded in unary and paired with the transparent DQCSD sample encoding.
The fixed `PKEParams` value is static program data. It must be charged in the specialized program
description together with the wrapper/controller, copies, marshalling and interpreter overhead.
This layer retains actual finite PTM terms and their native clocks, workspace and fixed coin tapes;
encoded description size and compiler/interpreter costs remain open until #5287/#5409. These are
rigorous direct-machine resources, not byte or CPU estimates. Here “native” means direct execution
of a classical finite-control table, not the native quantum/QPPT realization in #5281. This module
does not claim a final IND-CPA endpoint or a post-quantum reduction.

## Main definitions

* `Cslib.Crypto.HQC.twoDQCSDProgram`: executable classical `B1` with an explicit coin sampler.
* `Cslib.Crypto.HQC.threeDQCSDProgram`: executable classical `B2`.
* `Cslib.Crypto.HQC.encTwoDQCSDInput`, `encThreeDQCSDInput`: their complete runtime inputs.
* `Cslib.Crypto.HQC.ClassicalWrapperPPT`: machine certificates for the actual HQC challenge
  marshalling performed between the adversary stages.
* `Cslib.Crypto.HQC.TwoDQCSDNativeStages`, `ThreeDQCSDNativeStages`: explicit finite PTM stages
  and construction-selected nested `MultiTapePTM.comp` machines.
* `Cslib.Crypto.HQC.TwoDQCSDNativeResources`, `ThreeDQCSDNativeResources`: per-stage and composed
  time, workspace, randomness, query, request, reply and handler coordinates.

## Main results

* `Cslib.Crypto.HQC.eval_twoDQCSDProgram_eq_distinguisher`: `B1` matches the reviewed finite game
  when its explicit sampler has the ideal encryption-coin law.
* `Cslib.Crypto.HQC.eval_threeDQCSDProgram`: `B2` matches the reviewed finite game exactly.
* `Cslib.Crypto.HQC.isPPTOn_twoDQCSDProgram`, `isPPTOn_threeDQCSDProgram`: strict machine
  witnesses assembled from the adversary, sampler and wrapper certificates.
* `Cslib.Crypto.HQC.TwoDQCSDNativeStages.realizes`, `ThreeDQCSDNativeStages.realizes`: exact
  canonical-word semantics of the construction-selected machines.
* `Cslib.Crypto.HQC.TwoDQCSDNativeStages.eval_eq_distinguisher`,
  `ThreeDQCSDNativeStages.eval_eq_distinguisher`: exact fixed-coin laws against #5277's games.
-/

@[expose] public section

namespace Cslib.Crypto.HQC

open Probability Turing.MultiTapeTM

variable (P : PKEParams) [NeZero P.n]

/-- Complete runtime input of the classical 2-DQCSD-P reduction: unary security parameter and
the two-block source sample. -/
abbrev TwoDQCSDInput := ℕ × SyndromeSample P.n

/-- Complete runtime input of the classical 3-DQCSD-PT reduction: unary security parameter and
the truncated three-block source sample. -/
abbrev ThreeDQCSDInput := ℕ × TruncatedSyndromeSample P.n P.codeLen

/-- Encoding of the complete 2-DQCSD-P reduction input. -/
def encTwoDQCSDInput : TwoDQCSDInput P ↪ List Bool :=
  encPair encUnary (encSyndromeSample P.n)

/-- Encoding of the complete 3-DQCSD-PT reduction input. -/
def encThreeDQCSDInput : ThreeDQCSDInput P ↪ List Bool :=
  encPair encUnary (encTruncatedSyndromeSample P.n P.codeLen)

/-- Output of the key-dependent-message stage, including the saved adversary state. -/
abbrev ClassicalChoice (State : Type) := MessagePair (PKEMessage P) × State

/-- Encoding of the key-dependent message pair and saved state. -/
def encClassicalChoice {State : Type} (encState : State ↪ List Bool) :
    ClassicalChoice P State ↪ List Bool :=
  encPair (encMessagePair (encBitString P.k)) encState

/-- Input expected by the adversary's guessing-stage machine. -/
abbrev ClassicalGuessInput (State : Type) := ℕ × (State × PKECiphertext P)

/-- Encoding expected by the adversary's guessing-stage machine. -/
def encClassicalGuessInput {State : Type} (encState : State ↪ List Bool) :
    ClassicalGuessInput P State ↪ List Bool :=
  encPair encUnary (encPair encState (encPKECiphertext P))

omit [NeZero P.n] in
/-- Reading a two-block DQCSD sample as an expanded public key performs no representation
conversion: the two field encodings are byte-for-byte identical. -/
@[fun_prop] theorem SyndromeSample.toPKEPublicKey_polyTime :
    ComputableInPolyTime (SyndromeSample.toPKEPublicKey P)
      (encSyndromeSample P.n) (encPKEPublicKey P) :=
  .of_eq fun _ => rfl

omit [NeZero P.n] in
/-- Reading the two public blocks of a truncated sample is polynomial time. The input layout
groups those blocks, so this is a projection of an already encoded pair. -/
@[fun_prop] theorem TruncatedSyndromeSample.toPKEPublicKey_polyTime :
    ComputableInPolyTime (TruncatedSyndromeSample.toPKEPublicKey P)
      (encTruncatedSyndromeSample P.n P.codeLen) (encPKEPublicKey P) := by
  let encPublic := encPair (encBitString P.n) (encBitString P.n)
  let encValues := encPair (encBitString P.n) (encBitString P.codeLen)
  have hprod : ComputableInPolyTime
      (TruncatedSyndromeSample.equivProd P.n P.codeLen)
      (encTruncatedSyndromeSample P.n P.codeLen) (encPair encPublic encValues) :=
    .of_eq fun _ => rfl
  exact ComputableInPolyTime.of_enc_eq hprod.fst' fun _ => rfl

/-- Classical word-level `B1`. The sampler is explicit because replacing the ideal fixed-weight
law by `SampleSupport2` incurs a quantified statistical term. -/
noncomputable def twoDQCSDProgram {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (coinSampler : ℕ → ProbComp (PKECoins P))
    (input : TwoDQCSDInput P) : ProbComp Bool := do
  let pk := input.2.toPKEPublicKey P
  let (messages, state) ← (adversary input.1).choose pk
  let bit ← ProbComp.uniform Bool
  let coins ← coinSampler input.1
  let guess ← (adversary input.1).guess state
    (pkeEncrypt P encode pk (messages.select bit) coins)
  return guess == bit

/-- Classical word-level `B2`. It has no encryption-coin sampler: the source sample already
contains the two ciphertext masks. -/
noncomputable def threeDQCSDProgram {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (input : ThreeDQCSDInput P) : ProbComp Bool := do
  let pk := input.2.toPKEPublicKey P
  let (messages, state) ← (adversary input.1).choose pk
  let bit ← ProbComp.uniform Bool
  let ciphertext := input.2.toPKECiphertext P encode (messages.select bit)
  let guess ← (adversary input.1).guess state ciphertext
  return guess == bit

/-! ### Actual challenge marshalling -/

/-- Complete saved data immediately before `B1` invokes the guessing stage. -/
abbrev TwoDQCSDCoinInput (State : Type) :=
  (((TwoDQCSDInput P × ClassicalChoice P State) × Bool) × PKECoins P)

/-- Saved input and key-dependent-message result immediately before `B1` samples its hidden bit. -/
abbrev TwoDQCSDChoiceInput (State : Type) :=
  TwoDQCSDInput P × ClassicalChoice P State

/-- Encoding immediately before `B1` samples its hidden bit. -/
def encTwoDQCSDChoiceInput {State : Type} (encState : State ↪ List Bool) :
    TwoDQCSDChoiceInput P State ↪ List Bool :=
  encPair (encTwoDQCSDInput P) (encClassicalChoice P encState)

/-- Complete saved data immediately before `B1` samples encryption coins. -/
abbrev TwoDQCSDBitInput (State : Type) :=
  TwoDQCSDChoiceInput P State × Bool

/-- Encoding immediately before `B1` samples encryption coins. -/
def encTwoDQCSDBitInput {State : Type} (encState : State ↪ List Bool) :
    TwoDQCSDBitInput P State ↪ List Bool :=
  encPair (encTwoDQCSDChoiceInput P encState) encBool

/-- Encoding of the complete saved `B1` data before the guessing stage. -/
def encTwoDQCSDCoinInput {State : Type} (encState : State ↪ List Bool) :
    TwoDQCSDCoinInput P State ↪ List Bool :=
  encPair
    (encPair (encPair (encTwoDQCSDInput P) (encClassicalChoice P encState)) encBool)
    (encPKECoins P)

/-- Marshal the actual `B1` guessing-stage input: retain `kappa` and the saved state, select the
key-dependent message, and run deterministic expanded HQC encryption. -/
def twoDQCSDGuessInput {State : Type} (encode : PKEMessage P → Codeword P) :
    TwoDQCSDCoinInput P State → ClassicalGuessInput P State
  | ((((κ, sample), (messages, state)), bit), coins) =>
    (κ, state, pkeEncrypt P encode (sample.toPKEPublicKey P) (messages.select bit) coins)

/-- Complete saved data immediately before `B2` invokes the guessing stage. -/
abbrev ThreeDQCSDBitInput (State : Type) :=
  (ThreeDQCSDInput P × ClassicalChoice P State) × Bool

/-- Saved input and key-dependent-message result immediately before `B2` samples its hidden bit. -/
abbrev ThreeDQCSDChoiceInput (State : Type) :=
  ThreeDQCSDInput P × ClassicalChoice P State

/-- Encoding immediately before `B2` samples its hidden bit. -/
def encThreeDQCSDChoiceInput {State : Type} (encState : State ↪ List Bool) :
    ThreeDQCSDChoiceInput P State ↪ List Bool :=
  encPair (encThreeDQCSDInput P) (encClassicalChoice P encState)

/-- Encoding of the complete saved `B2` data before the guessing stage. -/
def encThreeDQCSDBitInput {State : Type} (encState : State ↪ List Bool) :
    ThreeDQCSDBitInput P State ↪ List Bool :=
  encPair (encPair (encThreeDQCSDInput P) (encClassicalChoice P encState)) encBool

/-- Marshal the actual `B2` guessing-stage input from the truncated source sample. -/
def threeDQCSDGuessInput {State : Type} (encode : PKEMessage P → Codeword P) :
    ThreeDQCSDBitInput P State → ClassicalGuessInput P State
  | (((κ, sample), (messages, state)), bit) =>
    (κ, state, sample.toPKECiphertext P encode (messages.select bit))

/-- The deterministic HQC wrapper computations needed by the two reductions are plain
polynomial time on their complete encodings. These fields certify the actual functions above;
they are not replacement callbacks. Exact time/space bounds and specialized program-description
size are recorded by the quantitative resource layer. -/
structure ClassicalWrapperPPT {State : Type} (encode : PKEMessage P → Codeword P)
    (encState : State ↪ List Bool) : Prop where
  /-- Deterministic encryption and marshalling used by `B1`. -/
  twoGuessInput : ComputableInPolyTime (twoDQCSDGuessInput P encode)
    (encTwoDQCSDCoinInput P encState) (encClassicalGuessInput P encState)
  /-- Deterministic message masking and marshalling used by `B2`. -/
  threeGuessInput : ComputableInPolyTime (threeDQCSDGuessInput P encode)
    (encThreeDQCSDBitInput P encState) (encClassicalGuessInput P encState)

/-! ### Native stage machines -/

/-- One construction-selected closed fair-coin stage. Both typed inputs and outputs retain a
common base input, so later stages have one fixed clock rather than an output-dependent callback.
This is HQC reduction construction data, not a second general probabilistic computability API. -/
structure ClassicalStageMachine {Base Input Output : Type}
    (baseInput : Input → Base) (baseOutput : Output → Base)
    (encInput : Input ↪ List Bool) (encOutput : Output ↪ List Bool)
    (program : Input → ProbComp Output) where
  /-- Number of ordinary work tapes. -/
  tapeCount : ℕ
  /-- Finite control type. -/
  State : Type
  /-- Explicit finiteness of the selected table's control. -/
  [stateFintype : Fintype State]
  /-- The actual closed probabilistic machine term. -/
  machine : Turing.MultiTapePTM tapeCount Bool State
  /-- Complete online clock, indexed by the retained base input. -/
  time : Base → ℕ
  /-- All-branch workspace bound in the nondeterministic-machine model. -/
  workspace : Base → ℕ
  /-- Canonical-word output semantics at the declared clock. -/
  realizes : ∀ input, (ProbComp.eval (program input)).map encOutput =
    ProbComp.eval (machine.runClosed (time (baseInput input)) (encInput input))
  /-- Every branch has halted at the declared clock. -/
  halts : ∀ input final, final ∈ (ProbComp.eval
    (machine.runConfigFrom (ProbComp.uniform Bool) Empty.elim (time (baseInput input))
      (machine.initialConfig (encInput input)))).support → final.tapes.state = none
  /-- The recorded workspace bounds every branch. -/
  runsInSpace : ∀ input,
    machine.toNTM.RunsInSpace (encInput input) (workspace (baseInput input))
  /-- Every supported output retains the stage's base input. -/
  preservesBase : ∀ input output, output ∈ (ProbComp.eval (program input)).support →
    baseOutput output = baseInput input

/-- A final construction-selected stage. Its output need not retain the base input because it is
not fed to another captured stage. -/
structure ClassicalFinalStageMachine {Base Input Output : Type}
    (baseInput : Input → Base) (encInput : Input ↪ List Bool)
    (encOutput : Output ↪ List Bool) (program : Input → ProbComp Output) where
  /-- Number of ordinary work tapes. -/
  tapeCount : ℕ
  /-- Finite control type. -/
  State : Type
  /-- Explicit finiteness of the selected table's control. -/
  [stateFintype : Fintype State]
  /-- The actual closed probabilistic machine term. -/
  machine : Turing.MultiTapePTM tapeCount Bool State
  /-- Complete online clock, indexed by the retained base input. -/
  time : Base → ℕ
  /-- All-branch workspace bound. -/
  workspace : Base → ℕ
  /-- Canonical-word output semantics at the declared clock. -/
  realizes : ∀ input, (ProbComp.eval (program input)).map encOutput =
    ProbComp.eval (machine.runClosed (time (baseInput input)) (encInput input))
  /-- Every branch has halted at the declared clock. -/
  halts : ∀ input final, final ∈ (ProbComp.eval
    (machine.runConfigFrom (ProbComp.uniform Bool) Empty.elim (time (baseInput input))
      (machine.initialConfig (encInput input)))).support → final.tapes.state = none
  /-- The recorded workspace bounds every branch. -/
  runsInSpace : ∀ input,
    machine.toNTM.RunsInSpace (encInput input) (workspace (baseInput input))

/-- Componentwise native resources of one stage. A closed table has no external query, request,
reply or handler coordinate; its fixed saved-coin budget is its declared clock. -/
structure ClassicalStageResources (Base : Type) where
  /-- Number of ordinary work tapes. -/
  tapeCount : ℕ
  /-- Online transition bound. -/
  time : Base → ℕ
  /-- All-branch work-tape-cell bound. -/
  workspace : Base → ℕ
  /-- Fixed fair-bit budget. -/
  randomBits : Base → ℕ
  /-- External query count. -/
  queries : Base → ℕ
  /-- Maximum external request length. -/
  requestBits : Base → ℕ
  /-- Maximum external reply length read by the machine. -/
  replyBits : Base → ℕ
  /-- External handler time. -/
  handlerTime : Base → ℕ

/-- Read the resource coordinates directly from a selected native stage. -/
def ClassicalStageMachine.resources {Base Input Output : Type}
    {baseInput : Input → Base} {baseOutput : Output → Base}
    {encInput : Input ↪ List Bool} {encOutput : Output ↪ List Bool}
    {program : Input → ProbComp Output}
    (stage : ClassicalStageMachine baseInput baseOutput encInput encOutput program) :
    ClassicalStageResources Base where
  tapeCount := stage.tapeCount
  time := stage.time
  workspace := stage.workspace
  randomBits := stage.time
  queries := fun _ => 0
  requestBits := fun _ => 0
  replyBits := fun _ => 0
  handlerTime := fun _ => 0

/-- Read the resource coordinates directly from a selected final native stage. -/
def ClassicalFinalStageMachine.resources {Base Input Output : Type}
    {baseInput : Input → Base} {encInput : Input ↪ List Bool}
    {encOutput : Output ↪ List Bool} {program : Input → ProbComp Output}
    (stage : ClassicalFinalStageMachine baseInput encInput encOutput program) :
    ClassicalStageResources Base where
  tapeCount := stage.tapeCount
  time := stage.time
  workspace := stage.workspace
  randomBits := stage.time
  queries := fun _ => 0
  requestBits := fun _ => 0
  replyBits := fun _ => 0
  handlerTime := fun _ => 0

@[simp] theorem ClassicalStageMachine.resources_tapeCount {Base Input Output : Type}
    {baseInput : Input → Base} {baseOutput : Output → Base}
    {encInput : Input ↪ List Bool} {encOutput : Output ↪ List Bool}
    {program : Input → ProbComp Output}
    (stage : ClassicalStageMachine baseInput baseOutput encInput encOutput program) :
    stage.resources.tapeCount = stage.tapeCount := rfl

@[simp] theorem ClassicalStageMachine.resources_time {Base Input Output : Type}
    {baseInput : Input → Base} {baseOutput : Output → Base}
    {encInput : Input ↪ List Bool} {encOutput : Output ↪ List Bool}
    {program : Input → ProbComp Output}
    (stage : ClassicalStageMachine baseInput baseOutput encInput encOutput program)
    (base : Base) : stage.resources.time base = stage.time base := rfl

@[simp] theorem ClassicalStageMachine.resources_workspace {Base Input Output : Type}
    {baseInput : Input → Base} {baseOutput : Output → Base}
    {encInput : Input ↪ List Bool} {encOutput : Output ↪ List Bool}
    {program : Input → ProbComp Output}
    (stage : ClassicalStageMachine baseInput baseOutput encInput encOutput program)
    (base : Base) : stage.resources.workspace base = stage.workspace base := rfl

@[simp] theorem ClassicalStageMachine.resources_randomBits {Base Input Output : Type}
    {baseInput : Input → Base} {baseOutput : Output → Base}
    {encInput : Input ↪ List Bool} {encOutput : Output ↪ List Bool}
    {program : Input → ProbComp Output}
    (stage : ClassicalStageMachine baseInput baseOutput encInput encOutput program)
    (base : Base) : stage.resources.randomBits base = stage.time base := rfl

@[simp] theorem ClassicalStageMachine.resources_queries {Base Input Output : Type}
    {baseInput : Input → Base} {baseOutput : Output → Base}
    {encInput : Input ↪ List Bool} {encOutput : Output ↪ List Bool}
    {program : Input → ProbComp Output}
    (stage : ClassicalStageMachine baseInput baseOutput encInput encOutput program)
    (base : Base) : stage.resources.queries base = 0 := rfl

@[simp] theorem ClassicalStageMachine.resources_requestBits {Base Input Output : Type}
    {baseInput : Input → Base} {baseOutput : Output → Base}
    {encInput : Input ↪ List Bool} {encOutput : Output ↪ List Bool}
    {program : Input → ProbComp Output}
    (stage : ClassicalStageMachine baseInput baseOutput encInput encOutput program)
    (base : Base) : stage.resources.requestBits base = 0 := rfl

@[simp] theorem ClassicalStageMachine.resources_replyBits {Base Input Output : Type}
    {baseInput : Input → Base} {baseOutput : Output → Base}
    {encInput : Input ↪ List Bool} {encOutput : Output ↪ List Bool}
    {program : Input → ProbComp Output}
    (stage : ClassicalStageMachine baseInput baseOutput encInput encOutput program)
    (base : Base) : stage.resources.replyBits base = 0 := rfl

@[simp] theorem ClassicalStageMachine.resources_handlerTime {Base Input Output : Type}
    {baseInput : Input → Base} {baseOutput : Output → Base}
    {encInput : Input ↪ List Bool} {encOutput : Output ↪ List Bool}
    {program : Input → ProbComp Output}
    (stage : ClassicalStageMachine baseInput baseOutput encInput encOutput program)
    (base : Base) : stage.resources.handlerTime base = 0 := rfl

@[simp] theorem ClassicalFinalStageMachine.resources_tapeCount {Base Input Output : Type}
    {baseInput : Input → Base} {encInput : Input ↪ List Bool}
    {encOutput : Output ↪ List Bool} {program : Input → ProbComp Output}
    (stage : ClassicalFinalStageMachine baseInput encInput encOutput program) :
    stage.resources.tapeCount = stage.tapeCount := rfl

@[simp] theorem ClassicalFinalStageMachine.resources_time {Base Input Output : Type}
    {baseInput : Input → Base} {encInput : Input ↪ List Bool}
    {encOutput : Output ↪ List Bool} {program : Input → ProbComp Output}
    (stage : ClassicalFinalStageMachine baseInput encInput encOutput program)
    (base : Base) : stage.resources.time base = stage.time base := rfl

@[simp] theorem ClassicalFinalStageMachine.resources_workspace {Base Input Output : Type}
    {baseInput : Input → Base} {encInput : Input ↪ List Bool}
    {encOutput : Output ↪ List Bool} {program : Input → ProbComp Output}
    (stage : ClassicalFinalStageMachine baseInput encInput encOutput program)
    (base : Base) : stage.resources.workspace base = stage.workspace base := rfl

@[simp] theorem ClassicalFinalStageMachine.resources_randomBits {Base Input Output : Type}
    {baseInput : Input → Base} {encInput : Input ↪ List Bool}
    {encOutput : Output ↪ List Bool} {program : Input → ProbComp Output}
    (stage : ClassicalFinalStageMachine baseInput encInput encOutput program)
    (base : Base) : stage.resources.randomBits base = stage.time base := rfl

@[simp] theorem ClassicalFinalStageMachine.resources_queries {Base Input Output : Type}
    {baseInput : Input → Base} {encInput : Input ↪ List Bool}
    {encOutput : Output ↪ List Bool} {program : Input → ProbComp Output}
    (stage : ClassicalFinalStageMachine baseInput encInput encOutput program)
    (base : Base) : stage.resources.queries base = 0 := rfl

@[simp] theorem ClassicalFinalStageMachine.resources_requestBits {Base Input Output : Type}
    {baseInput : Input → Base} {encInput : Input ↪ List Bool}
    {encOutput : Output ↪ List Bool} {program : Input → ProbComp Output}
    (stage : ClassicalFinalStageMachine baseInput encInput encOutput program)
    (base : Base) : stage.resources.requestBits base = 0 := rfl

@[simp] theorem ClassicalFinalStageMachine.resources_replyBits {Base Input Output : Type}
    {baseInput : Input → Base} {encInput : Input ↪ List Bool}
    {encOutput : Output ↪ List Bool} {program : Input → ProbComp Output}
    (stage : ClassicalFinalStageMachine baseInput encInput encOutput program)
    (base : Base) : stage.resources.replyBits base = 0 := rfl

@[simp] theorem ClassicalFinalStageMachine.resources_handlerTime {Base Input Output : Type}
    {baseInput : Input → Base} {encInput : Input ↪ List Bool}
    {encOutput : Output ↪ List Bool} {program : Input → ProbComp Output}
    (stage : ClassicalFinalStageMachine baseInput encInput encOutput program)
    (base : Base) : stage.resources.handlerTime base = 0 := rfl

namespace ClassicalStageMachine

variable {Base Input Middle Output : Type}
  {baseInput : Input → Base} {baseMiddle : Middle → Base} {baseOutput : Output → Base}
  {encInput : Input ↪ List Bool} {encMiddle : Middle ↪ List Bool}
  {encOutput : Output ↪ List Bool}
  {program : Input → ProbComp Output}
  {first : Input → ProbComp Middle} {second : Middle → ProbComp Output}

/-- Exact clock of the buffered probabilistic composition compiler. -/
@[expose] def compTime (firstTime secondTime : ℕ) : ℕ :=
  firstTime + (firstTime + 4 + secondTime)

/-- Raw-word execution, including malformed words. No decoder, default typed value or hidden
callback is inserted: the selected table runs directly at the clock of the supplied base input. -/
noncomputable def runRaw
    (stage : ClassicalStageMachine baseInput baseOutput encInput encOutput program)
    (base : Base) (word : List Bool) : ProbComp (List Bool) :=
  stage.machine.runClosed (stage.time base) word

/-- Fixed-coin raw-word replay, including malformed words. -/
def runRawCoins
    (stage : ClassicalStageMachine baseInput baseOutput encInput encOutput program)
    (coins word : List Bool) : List Bool :=
  stage.machine.runClosedCoins coins word

/-- Saved-coin semantics of one named stage. -/
theorem eval_eq_uniform_savedCoins
    (stage : ClassicalStageMachine baseInput baseOutput encInput encOutput program)
    (input : Input) :
    (ProbComp.eval (program input)).map encOutput =
      (BitString.uniformList (stage.time (baseInput input))).map
        (fun coins => stage.machine.runClosedCoins coins (encInput input)) := by
  rw [stage.realizes, stage.machine.eval_runClosed_eq_map_coins]

/-- Forget only the base-preservation law of a named stage. The machine, clock, workspace and
canonical-word semantics remain definitionally unchanged. -/
@[expose] def toFinal
    (stage : ClassicalStageMachine baseInput baseOutput encInput encOutput program) :
    ClassicalFinalStageMachine baseInput encInput encOutput program where
  tapeCount := stage.tapeCount
  State := stage.State
  stateFintype := stage.stateFintype
  machine := stage.machine
  time := stage.time
  workspace := stage.workspace
  realizes := stage.realizes
  halts := stage.halts
  runsInSpace := stage.runsInSpace

end ClassicalStageMachine

namespace ClassicalFinalStageMachine

variable {Base Input Middle Output : Type}
  {baseInput : Input → Base} {baseMiddle : Middle → Base}
  {encInput : Input ↪ List Bool} {encMiddle : Middle ↪ List Bool}
  {encOutput : Output ↪ List Bool}
  {program : Input → ProbComp Output}
  {first : Input → ProbComp Middle} {second : Middle → ProbComp Output}

/-- Raw-word execution of a final stage, including malformed words. -/
noncomputable def runRaw
    (stage : ClassicalFinalStageMachine baseInput encInput encOutput program)
    (base : Base) (word : List Bool) : ProbComp (List Bool) :=
  stage.machine.runClosed (stage.time base) word

/-- Fixed-coin raw-word replay of a final stage, including malformed words. -/
def runRawCoins
    (stage : ClassicalFinalStageMachine baseInput encInput encOutput program)
    (coins word : List Bool) : List Bool :=
  stage.machine.runClosedCoins coins word

/-- Saved-coin semantics of one named final stage. -/
theorem eval_eq_uniform_savedCoins
    (stage : ClassicalFinalStageMachine baseInput encInput encOutput program)
    (input : Input) :
    (ProbComp.eval (program input)).map encOutput =
      (BitString.uniformList (stage.time (baseInput input))).map
        (fun coins => stage.machine.runClosedCoins coins (encInput input)) := by
  rw [stage.realizes, stage.machine.eval_runClosed_eq_map_coins]

/-- Directly compose a final native stage after a base-preserving native stage. -/
@[expose] noncomputable def comp
    (outer : ClassicalFinalStageMachine baseMiddle encMiddle encOutput second)
    (inner : ClassicalStageMachine baseInput baseMiddle encInput encMiddle first) :
    ClassicalFinalStageMachine baseInput encInput encOutput (fun input => do
      let middle ← first input
      second middle) := by
  let CompositeState :=
    inner.State ⊕ ((Turing.MultiTapeTM.MarkWorkState ⊕
      Turing.MultiTapeTM.RewindWorkState) ⊕ outer.State)
  letI := inner.stateFintype
  letI := outer.stateFintype
  letI : Fintype CompositeState := inferInstance
  let machine : Turing.MultiTapePTM
      (outer.tapeCount + inner.tapeCount + 2) Bool CompositeState :=
    outer.machine.comp inner.machine true
  let totalTime (base : Base) :=
    ClassicalStageMachine.compTime (inner.time base) (outer.time base)
  let totalSpace (base : Base) :=
    (outer.tapeCount + inner.tapeCount + 2) *
      (2 * max (max (inner.workspace base) (outer.workspace base))
        (inner.time base + 2) + 1)
  have hmiddle (input : Input) :
      ∀ word ∈ (ProbComp.eval
        (inner.machine.runClosed (inner.time (baseInput input)) (encInput input))).support,
        ∃ middle ∈ (ProbComp.eval (first input)).support, encMiddle middle = word := by
    intro word hword
    rw [← inner.realizes input] at hword
    exact (PMF.mem_support_map_iff _ _ _).mp hword
  have houter (input : Input) :
      ∀ word ∈ (ProbComp.eval
        (inner.machine.runClosed (inner.time (baseInput input)) (encInput input))).support,
        ∀ final ∈ (ProbComp.eval
          (outer.machine.runClosedConfigFrom (outer.time (baseInput input))
            (outer.machine.initialConfig word))).support,
          final.tapes.state = none := by
    intro word hword final hfinal
    obtain ⟨middle, hsupport, rfl⟩ := hmiddle input word hword
    rw [← inner.preservesBase input middle hsupport] at hfinal
    exact outer.halts middle final hfinal
  have hrealizes (input : Input) :
      (ProbComp.eval (do
        let middle ← first input
        second middle)).map encOutput =
        ProbComp.eval (machine.runClosed (totalTime (baseInput input)) (encInput input)) := by
    rw [show totalTime (baseInput input) = inner.time (baseInput input) +
        (inner.time (baseInput input) + 4 + outer.time (baseInput input)) by rfl,
      Turing.MultiTapePTM.eval_comp inner.machine outer.machine true (encInput input)
        (inner.time (baseInput input)) (outer.time (baseInput input))
        (inner.halts input) (houter input), ProbComp.eval_bind, PMF.map_bind]
    change (ProbComp.eval (first input)).bind
        (fun middle => (ProbComp.eval (second middle)).map encOutput) =
      (ProbComp.eval
        (inner.machine.runClosed (inner.time (baseInput input)) (encInput input))).bind
        (fun word => ProbComp.eval
          (outer.machine.runClosed (outer.time (baseInput input)) word))
    rw [← inner.realizes input, PMF.bind_map]
    apply PMF.bind_congr_on_support
    intro middle hmiddleSupport
    dsimp only [Function.comp_def]
    rw [← inner.preservesBase input middle hmiddleSupport]
    exact outer.realizes middle
  have hhalts (input : Input) : ∀ final, final ∈ (ProbComp.eval
      (machine.runClosedConfigFrom (totalTime (baseInput input))
        (machine.initialConfig (encInput input)))).support → final.tapes.state = none := by
    rw [show totalTime (baseInput input) = inner.time (baseInput input) +
        (inner.time (baseInput input) + 4 + outer.time (baseInput input)) by rfl]
    exact Turing.MultiTapePTM.comp_halted inner.machine outer.machine true (encInput input)
      (inner.time (baseInput input)) (outer.time (baseInput input))
      (inner.halts input) (houter input)
  have hspace (input : Input) :
      machine.toNTM.RunsInSpace (encInput input) (totalSpace (baseInput input)) := by
    apply Turing.MultiTapePTM.runsInSpace_toNTM_comp inner.machine outer.machine true
      (inner.halts input) (inner.runsInSpace input)
    · intro word hword
      exact inner.machine.length_output_eval_runClosed_le
        (inner.time (baseInput input)) (encInput input) word hword
    · intro word hword
      obtain ⟨middle, hsupport, rfl⟩ := hmiddle input word hword
      rw [← inner.preservesBase input middle hsupport]
      exact outer.runsInSpace middle
  exact {
    tapeCount := outer.tapeCount + inner.tapeCount + 2
    State := CompositeState
    machine := machine
    time := totalTime
    workspace := totalSpace
    realizes := hrealizes
    halts := hhalts
    runsInSpace := hspace
  }

/-- Final composition retains the concrete probabilistic machine term definitionally. -/
theorem machine_comp
    (outer : ClassicalFinalStageMachine baseMiddle encMiddle encOutput second)
    (inner : ClassicalStageMachine baseInput baseMiddle encInput encMiddle first) :
    (outer.comp inner).machine = outer.machine.comp inner.machine true :=
  rfl

/-- Final composition charges both component workspaces, the intermediate word and all tapes. -/
theorem workspace_comp
    (outer : ClassicalFinalStageMachine baseMiddle encMiddle encOutput second)
    (inner : ClassicalStageMachine baseInput baseMiddle encInput encMiddle first) (base : Base) :
    (outer.comp inner).workspace base =
      (outer.tapeCount + inner.tapeCount + 2) *
        (2 * max (max (inner.workspace base) (outer.workspace base))
          (inner.time base + 2) + 1) :=
  rfl

end ClassicalFinalStageMachine

namespace ClassicalStageMachine

variable {Base Input Middle Output : Type}
  {baseInput : Input → Base} {baseMiddle : Middle → Base} {baseOutput : Output → Base}
  {encInput : Input ↪ List Bool} {encMiddle : Middle ↪ List Bool}
  {encOutput : Output ↪ List Bool}
  {first : Input → ProbComp Middle} {second : Middle → ProbComp Output}

/-- Direct buffered composition of two named stages. The common compiler proof is inherited from
final-stage composition; only the construction-specific base-preservation law is added here. The
returned record definitionally retains `MultiTapePTM.comp`, and no existential machine certificate
is eliminated. -/
@[expose] noncomputable def comp
    (outer : ClassicalStageMachine baseMiddle baseOutput encMiddle encOutput second)
    (inner : ClassicalStageMachine baseInput baseMiddle encInput encMiddle first) :
    ClassicalStageMachine baseInput baseOutput encInput encOutput (fun input => do
      let middle ← first input
      second middle) := by
  let compiled := outer.toFinal.comp inner
  exact {
    tapeCount := compiled.tapeCount
    State := compiled.State
    stateFintype := compiled.stateFintype
    machine := compiled.machine
    time := compiled.time
    workspace := compiled.workspace
    realizes := compiled.realizes
    halts := compiled.halts
    runsInSpace := compiled.runsInSpace
    preservesBase := by
      intro input output houtput
      rw [ProbComp.eval_bind] at houtput
      obtain ⟨middle, hmiddleSupport, houtput⟩ :=
        (PMF.mem_support_bind_iff _ _ _).mp houtput
      exact (outer.preservesBase middle output houtput).trans
        (inner.preservesBase input middle hmiddleSupport)
  }

/-- Composition retains the concrete probabilistic machine term definitionally. -/
theorem machine_comp
    (outer : ClassicalStageMachine baseMiddle baseOutput encMiddle encOutput second)
    (inner : ClassicalStageMachine baseInput baseMiddle encInput encMiddle first) :
    (outer.comp inner).machine = outer.machine.comp inner.machine true :=
  rfl

/-- Base-preserving composition uses the same charged workspace compiler. -/
theorem workspace_comp
    (outer : ClassicalStageMachine baseMiddle baseOutput encMiddle encOutput second)
    (inner : ClassicalStageMachine baseInput baseMiddle encInput encMiddle first) (base : Base) :
    (outer.comp inner).workspace base =
      (outer.tapeCount + inner.tapeCount + 2) *
        (2 * max (max (inner.workspace base) (outer.workspace base))
          (inner.time base + 2) + 1) :=
  rfl

end ClassicalStageMachine

/-! ### Construction-selected `B1` and `B2` machines -/

/-- First `B1` stage: run the key-dependent-message adversary and retain the complete source
input beside its message pair and saved state. -/
noncomputable def twoDQCSDChooseStage {State : Type}
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (input : TwoDQCSDInput P) : ProbComp (TwoDQCSDChoiceInput P State) := do
  let choice ← (adversary input.1).choose (input.2.toPKEPublicKey P)
  return (input, choice)

/-- Sample the hidden challenge bit while retaining the complete preceding state. -/
noncomputable def sampleHiddenBitStage {Input : Type} (input : Input) :
    ProbComp (Input × Bool) := do
  let bit ← ProbComp.uniform Bool
  return (input, bit)

/-- `B1` encryption-coin stage. The sampler remains an explicit program input. -/
noncomputable def twoDQCSDCoinStage {State : Type}
    (coinSampler : ℕ → ProbComp (PKECoins P)) (input : TwoDQCSDBitInput P State) :
    ProbComp (TwoDQCSDCoinInput P State) := do
  let coins ← coinSampler input.1.1.1
  return (input, coins)

/-- Final `B1` stage: marshal the actual guessing input, run the saved-state adversary stage and
compare its answer with the retained hidden bit. -/
noncomputable def twoDQCSDGuessVerdictStage {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (input : TwoDQCSDCoinInput P State) : ProbComp Bool := do
  let guessInput := twoDQCSDGuessInput P encode input
  let guess ← (adversary guessInput.1).guess guessInput.2.1 guessInput.2.2
  return guess == input.1.2

/-- First `B2` stage: run the key-dependent-message adversary and retain the complete truncated
source input beside its message pair and saved state. -/
noncomputable def threeDQCSDChooseStage {State : Type}
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (input : ThreeDQCSDInput P) : ProbComp (ThreeDQCSDChoiceInput P State) := do
  let choice ← (adversary input.1).choose (input.2.toPKEPublicKey P)
  return (input, choice)

/-- Final `B2` stage: preserve the reviewed truncation and selected-message mask, run the saved
guessing stage, and compare with the retained hidden bit. -/
noncomputable def threeDQCSDGuessVerdictStage {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (input : ThreeDQCSDBitInput P State) : ProbComp Bool := do
  let guessInput := threeDQCSDGuessInput P encode input
  let guess ← (adversary guessInput.1).guess guessInput.2.1 guessInput.2.2
  return guess == input.2

/-- Explicit native stages used to construct `B1`. Every field contains an actual finite PTM
term and its checked semantics/resources; none is a Lean callback standing in for a machine. -/
structure TwoDQCSDNativeStages {State : Type}
    (encode : PKEMessage P → Codeword P) (encState : State ↪ List Bool)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (coinSampler : ℕ → ProbComp (PKECoins P)) where
  /-- Captured key-dependent-message stage. -/
  choose : ClassicalStageMachine
    (id : TwoDQCSDInput P → TwoDQCSDInput P)
    (fun input : TwoDQCSDChoiceInput P State => input.1)
    (encTwoDQCSDInput P) (encTwoDQCSDChoiceInput P encState)
    (twoDQCSDChooseStage P adversary)
  /-- Captured fair challenge-bit stage. -/
  hiddenBit : ClassicalStageMachine
    (fun input : TwoDQCSDChoiceInput P State => input.1)
    (fun input : TwoDQCSDBitInput P State => input.1.1)
    (encTwoDQCSDChoiceInput P encState) (encTwoDQCSDBitInput P encState)
    sampleHiddenBitStage
  /-- Captured explicit encryption-coin sampler stage. -/
  sampler : ClassicalStageMachine
    (fun input : TwoDQCSDBitInput P State => input.1.1)
    (fun input : TwoDQCSDCoinInput P State => input.1.1.1)
    (encTwoDQCSDBitInput P encState) (encTwoDQCSDCoinInput P encState)
    (twoDQCSDCoinStage P coinSampler)
  /-- Concrete encryption/marshalling, adversary guess and verdict stage. -/
  guessVerdict : ClassicalFinalStageMachine
    (fun input : TwoDQCSDCoinInput P State => input.1.1.1)
    (encTwoDQCSDCoinInput P encState) encBool
    (twoDQCSDGuessVerdictStage P encode adversary)

/-- Explicit native stages used to construct `B2`. -/
structure ThreeDQCSDNativeStages {State : Type}
    (encode : PKEMessage P → Codeword P) (encState : State ↪ List Bool)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) where
  /-- Captured key-dependent-message stage. -/
  choose : ClassicalStageMachine
    (id : ThreeDQCSDInput P → ThreeDQCSDInput P)
    (fun input : ThreeDQCSDChoiceInput P State => input.1)
    (encThreeDQCSDInput P) (encThreeDQCSDChoiceInput P encState)
    (threeDQCSDChooseStage P adversary)
  /-- Captured fair challenge-bit stage. -/
  hiddenBit : ClassicalStageMachine
    (fun input : ThreeDQCSDChoiceInput P State => input.1)
    (fun input : ThreeDQCSDBitInput P State => input.1.1)
    (encThreeDQCSDChoiceInput P encState) (encThreeDQCSDBitInput P encState)
    sampleHiddenBitStage
  /-- Concrete masking/marshalling, adversary guess and verdict stage. -/
  guessVerdict : ClassicalFinalStageMachine
    (fun input : ThreeDQCSDBitInput P State => input.1.1)
    (encThreeDQCSDBitInput P encState) encBool
    (threeDQCSDGuessVerdictStage P encode adversary)

/-- The construction-selected `B1` table: four explicit stages joined by the buffered PTM
compiler. -/
@[expose] noncomputable def TwoDQCSDNativeStages.compiled {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    {coinSampler : ℕ → ProbComp (PKECoins P)}
    (stages : TwoDQCSDNativeStages P encode encState adversary coinSampler) :=
  stages.guessVerdict.comp (stages.sampler.comp (stages.hiddenBit.comp stages.choose))

/-- The construction-selected `B2` table: three explicit stages joined by the buffered PTM
compiler. -/
@[expose] noncomputable def ThreeDQCSDNativeStages.compiled {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    (stages : ThreeDQCSDNativeStages P encode encState adversary) :=
  stages.guessVerdict.comp (stages.hiddenBit.comp stages.choose)

/-- Every native `B1` stage contribution together with the composed resource map. Description
bits and compiler/interpreter costs are intentionally absent until #5287/#5409. -/
structure TwoDQCSDNativeResources (Input : Type) where
  choose : ClassicalStageResources Input
  hiddenBit : ClassicalStageResources Input
  sampler : ClassicalStageResources Input
  guessVerdict : ClassicalStageResources Input
  total : ClassicalStageResources Input

/-- Every native `B2` stage contribution together with the composed resource map. -/
structure ThreeDQCSDNativeResources (Input : Type) where
  choose : ClassicalStageResources Input
  hiddenBit : ClassicalStageResources Input
  guessVerdict : ClassicalStageResources Input
  total : ClassicalStageResources Input

/-- Componentwise `B1` native resources, retaining each construction stage. -/
def TwoDQCSDNativeStages.resources {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    {coinSampler : ℕ → ProbComp (PKECoins P)}
    (stages : TwoDQCSDNativeStages P encode encState adversary coinSampler) :
    TwoDQCSDNativeResources (TwoDQCSDInput P) where
  choose := stages.choose.resources
  hiddenBit := stages.hiddenBit.resources
  sampler := stages.sampler.resources
  guessVerdict := stages.guessVerdict.resources
  total := stages.compiled.resources

/-- Componentwise `B2` native resources, retaining each construction stage. -/
def ThreeDQCSDNativeStages.resources {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    (stages : ThreeDQCSDNativeStages P encode encState adversary) :
    ThreeDQCSDNativeResources (ThreeDQCSDInput P) where
  choose := stages.choose.resources
  hiddenBit := stages.hiddenBit.resources
  guessVerdict := stages.guessVerdict.resources
  total := stages.compiled.resources

/-- Exact nested clock formula for construction-selected `B1`. -/
theorem TwoDQCSDNativeStages.time_eq {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    {coinSampler : ℕ → ProbComp (PKECoins P)}
    (stages : TwoDQCSDNativeStages P encode encState adversary coinSampler)
    (input : TwoDQCSDInput P) :
    stages.compiled.time input = ClassicalStageMachine.compTime
      (ClassicalStageMachine.compTime
        (ClassicalStageMachine.compTime (stages.choose.time input)
          (stages.hiddenBit.time input))
        (stages.sampler.time input))
      (stages.guessVerdict.time input) := rfl

/-- Exact nested clock formula for construction-selected `B2`. -/
theorem ThreeDQCSDNativeStages.time_eq {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    (stages : ThreeDQCSDNativeStages P encode encState adversary)
    (input : ThreeDQCSDInput P) :
    stages.compiled.time input = ClassicalStageMachine.compTime
      (ClassicalStageMachine.compTime (stages.choose.time input)
        (stages.hiddenBit.time input))
      (stages.guessVerdict.time input) := rfl

/-- The exact buffered-composition clock preserves polynomial bounds componentwise. -/
theorem ClassicalStageMachine.polyBounded_compTime {Input : Type} {size first second : Input → ℕ}
    (hfirst : PolyBounded size first) (hsecond : PolyBounded size second) :
    PolyBounded size (fun input => compTime (first input) (second input)) := by
  exact hfirst.add ((hfirst.add (PolyBounded.const 4)).add hsecond)

/-- A `B1` clock is polynomial whenever each recorded stage clock is polynomial in the canonical
source-input length. -/
theorem TwoDQCSDNativeStages.time_polyBounded {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    {coinSampler : ℕ → ProbComp (PKECoins P)}
    (stages : TwoDQCSDNativeStages P encode encState adversary coinSampler)
    (hchoose : PolyBounded (fun input => (encTwoDQCSDInput P input).length)
      stages.choose.time)
    (hhiddenBit : PolyBounded (fun input => (encTwoDQCSDInput P input).length)
      stages.hiddenBit.time)
    (hsampler : PolyBounded (fun input => (encTwoDQCSDInput P input).length)
      stages.sampler.time)
    (hguessVerdict : PolyBounded (fun input => (encTwoDQCSDInput P input).length)
      stages.guessVerdict.time) :
    PolyBounded (fun input => (encTwoDQCSDInput P input).length) stages.compiled.time := by
  apply (ClassicalStageMachine.polyBounded_compTime
    (ClassicalStageMachine.polyBounded_compTime
      (ClassicalStageMachine.polyBounded_compTime hchoose hhiddenBit) hsampler)
    hguessVerdict).mono
  intro input
  rw [stages.time_eq input]

/-- A `B2` clock is polynomial whenever each recorded stage clock is polynomial in the canonical
source-input length. -/
theorem ThreeDQCSDNativeStages.time_polyBounded {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    (stages : ThreeDQCSDNativeStages P encode encState adversary)
    (hchoose : PolyBounded (fun input => (encThreeDQCSDInput P input).length)
      stages.choose.time)
    (hhiddenBit : PolyBounded (fun input => (encThreeDQCSDInput P input).length)
      stages.hiddenBit.time)
    (hguessVerdict : PolyBounded (fun input => (encThreeDQCSDInput P input).length)
      stages.guessVerdict.time) :
    PolyBounded (fun input => (encThreeDQCSDInput P input).length) stages.compiled.time := by
  apply (ClassicalStageMachine.polyBounded_compTime
    (ClassicalStageMachine.polyBounded_compTime hchoose hhiddenBit) hguessVerdict).mono
  intro input
  rw [stages.time_eq input]

@[simp] theorem TwoDQCSDNativeStages.resources_queries {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    {coinSampler : ℕ → ProbComp (PKECoins P)}
    (stages : TwoDQCSDNativeStages P encode encState adversary coinSampler)
    (input : TwoDQCSDInput P) : stages.resources.total.queries input = 0 := rfl

@[simp] theorem TwoDQCSDNativeStages.resources_requestBits {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    {coinSampler : ℕ → ProbComp (PKECoins P)}
    (stages : TwoDQCSDNativeStages P encode encState adversary coinSampler)
    (input : TwoDQCSDInput P) : stages.resources.total.requestBits input = 0 := rfl

@[simp] theorem TwoDQCSDNativeStages.resources_replyBits {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    {coinSampler : ℕ → ProbComp (PKECoins P)}
    (stages : TwoDQCSDNativeStages P encode encState adversary coinSampler)
    (input : TwoDQCSDInput P) : stages.resources.total.replyBits input = 0 := rfl

@[simp] theorem TwoDQCSDNativeStages.resources_handlerTime {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    {coinSampler : ℕ → ProbComp (PKECoins P)}
    (stages : TwoDQCSDNativeStages P encode encState adversary coinSampler)
    (input : TwoDQCSDInput P) : stages.resources.total.handlerTime input = 0 := rfl

@[simp] theorem ThreeDQCSDNativeStages.resources_queries {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    (stages : ThreeDQCSDNativeStages P encode encState adversary)
    (input : ThreeDQCSDInput P) : stages.resources.total.queries input = 0 := rfl

@[simp] theorem ThreeDQCSDNativeStages.resources_requestBits {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    (stages : ThreeDQCSDNativeStages P encode encState adversary)
    (input : ThreeDQCSDInput P) : stages.resources.total.requestBits input = 0 := rfl

@[simp] theorem ThreeDQCSDNativeStages.resources_replyBits {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    (stages : ThreeDQCSDNativeStages P encode encState adversary)
    (input : ThreeDQCSDInput P) : stages.resources.total.replyBits input = 0 := rfl

@[simp] theorem ThreeDQCSDNativeStages.resources_handlerTime {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    (stages : ThreeDQCSDNativeStages P encode encState adversary)
    (input : ThreeDQCSDInput P) : stages.resources.total.handlerTime input = 0 := rfl

/-- `B1` definitionally contains the nested machine-combinator construction. -/
theorem TwoDQCSDNativeStages.machine_eq {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    {coinSampler : ℕ → ProbComp (PKECoins P)}
    (stages : TwoDQCSDNativeStages P encode encState adversary coinSampler) :
    stages.compiled.machine = stages.guessVerdict.machine.comp
      (stages.sampler.machine.comp
        (stages.hiddenBit.machine.comp stages.choose.machine true) true) true :=
  rfl

/-- `B2` definitionally contains the nested machine-combinator construction. -/
theorem ThreeDQCSDNativeStages.machine_eq {State : Type}
    {encode : PKEMessage P → Codeword P} {encState : State ↪ List Bool}
    {adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State}
    (stages : ThreeDQCSDNativeStages P encode encState adversary) :
    stages.compiled.machine = stages.guessVerdict.machine.comp
      (stages.hiddenBit.machine.comp stages.choose.machine true) true :=
  rfl

omit [NeZero P.n] in
/-- The staged `B1` program is the executable word-level program, with the same sampling order and
saved state. -/
theorem twoDQCSDProgram_eq_stages {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (coinSampler : ℕ → ProbComp (PKECoins P)) (input : TwoDQCSDInput P) :
    twoDQCSDProgram P encode adversary coinSampler input = (do
      let choice ← twoDQCSDChooseStage P adversary input
      let withBit ← sampleHiddenBitStage choice
      let withCoins ← twoDQCSDCoinStage P coinSampler withBit
      twoDQCSDGuessVerdictStage P encode adversary withCoins) := by
  simp [twoDQCSDProgram, twoDQCSDChooseStage, sampleHiddenBitStage,
    twoDQCSDCoinStage, twoDQCSDGuessVerdictStage]

omit [NeZero P.n] in
/-- The staged `B2` program is the executable word-level program, preserving the reviewed
truncation, parity schedule, selected-message mask and saved state. -/
theorem threeDQCSDProgram_eq_stages {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) (input : ThreeDQCSDInput P) :
    threeDQCSDProgram P encode adversary input = (do
      let choice ← threeDQCSDChooseStage P adversary input
      let withBit ← sampleHiddenBitStage choice
      threeDQCSDGuessVerdictStage P encode adversary withBit) := by
  simp [threeDQCSDProgram, threeDQCSDChooseStage, sampleHiddenBitStage,
    threeDQCSDGuessVerdictStage]

omit [NeZero P.n] in
/-- Exact canonical-word semantics of the construction-selected native `B1` table. -/
theorem TwoDQCSDNativeStages.realizes {State : Type}
    (encode : PKEMessage P → Codeword P) (encState : State ↪ List Bool)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (coinSampler : ℕ → ProbComp (PKECoins P))
    (stages : TwoDQCSDNativeStages P encode encState adversary coinSampler)
    (input : TwoDQCSDInput P) :
    (ProbComp.eval (twoDQCSDProgram P encode adversary coinSampler input)).map encBool =
      ProbComp.eval (stages.compiled.machine.runClosed
        (stages.compiled.time input) (encTwoDQCSDInput P input)) := by
  rw [twoDQCSDProgram_eq_stages P encode adversary coinSampler input]
  exact stages.compiled.realizes input

omit [NeZero P.n] in
/-- Exact canonical-word semantics of the construction-selected native `B2` table. -/
theorem ThreeDQCSDNativeStages.realizes {State : Type}
    (encode : PKEMessage P → Codeword P) (encState : State ↪ List Bool)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (stages : ThreeDQCSDNativeStages P encode encState adversary)
    (input : ThreeDQCSDInput P) :
    (ProbComp.eval (threeDQCSDProgram P encode adversary input)).map encBool =
      ProbComp.eval (stages.compiled.machine.runClosed
        (stages.compiled.time input) (encThreeDQCSDInput P input)) := by
  rw [threeDQCSDProgram_eq_stages P encode adversary input]
  exact stages.compiled.realizes input

omit [NeZero P.n] in
/-- Forget the construction-selected native `B1` table into strict PPT only after its machine,
semantics and resource maps have been fixed. -/
theorem TwoDQCSDNativeStages.isPPTOn {State : Type}
    (encode : PKEMessage P → Codeword P) (encState : State ↪ List Bool)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (coinSampler : ℕ → ProbComp (PKECoins P))
    (stages : TwoDQCSDNativeStages P encode encState adversary coinSampler)
    (hpoly : PolyBounded (fun input => (encTwoDQCSDInput P input).length)
      stages.compiled.time) :
    IsPPTOn (encTwoDQCSDInput P) encBool
      (twoDQCSDProgram P encode adversary coinSampler) := by
  obtain ⟨c, d, htime⟩ := hpoly.exists_le
  letI := stages.compiled.stateFintype
  refine ⟨stages.compiled.tapeCount, stages.compiled.State,
    @Finite.of_fintype _ stages.compiled.stateFintype,
    stages.compiled.machine, c, d, fun input => ?_⟩
  exact (stages.realizes P encode encState adversary coinSampler input).trans
    (stages.compiled.machine.eval_runClosed_eq_of_halted
      (encTwoDQCSDInput P input) (htime input) (stages.compiled.halts input)).symm

omit [NeZero P.n] in
/-- Forget the construction-selected native `B2` table into strict PPT only after its machine,
semantics and resource maps have been fixed. -/
theorem ThreeDQCSDNativeStages.isPPTOn {State : Type}
    (encode : PKEMessage P → Codeword P) (encState : State ↪ List Bool)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (stages : ThreeDQCSDNativeStages P encode encState adversary)
    (hpoly : PolyBounded (fun input => (encThreeDQCSDInput P input).length)
      stages.compiled.time) :
    IsPPTOn (encThreeDQCSDInput P) encBool
      (threeDQCSDProgram P encode adversary) := by
  obtain ⟨c, d, htime⟩ := hpoly.exists_le
  letI := stages.compiled.stateFintype
  refine ⟨stages.compiled.tapeCount, stages.compiled.State,
    @Finite.of_fintype _ stages.compiled.stateFintype,
    stages.compiled.machine, c, d, fun input => ?_⟩
  exact (stages.realizes P encode encState adversary input).trans
    (stages.compiled.machine.eval_runClosed_eq_of_halted
      (encThreeDQCSDInput P input) (htime input) (stages.compiled.halts input)).symm

/-! ### Strict machine witnesses -/

omit [NeZero P.n] in
/-- The actual classical `B2` program is strict PPT when both adversary stages are strict PPT and
the concrete HQC masking/marshalling wrapper has its machine certificate. The construction uses
closed private randomness only, so its external query count and request length are both zero. -/
theorem isPPTOn_threeDQCSDProgram {State : Type}
    (encode : PKEMessage P → Codeword P) (encState : State ↪ List Bool)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (hadversary : TwoStage.IsPPT (encPKEPublicKey P)
      (encMessagePair (encBitString P.k)) (encPKECiphertext P) encBool encState adversary)
    (hwrapper : ClassicalWrapperPPT P encode encState) :
    IsPPTOn (encThreeDQCSDInput P) encBool (threeDQCSDProgram P encode adversary) := by
  let encChoice := encClassicalChoice P encState
  let encChoiceInput := encPair (encThreeDQCSDInput P) encChoice
  have hprepare : ComputableInPolyTime
      (fun input : ThreeDQCSDInput P => (input.1, input.2.toPKEPublicKey P))
      (encThreeDQCSDInput P) (encPair encUnary (encPKEPublicKey P)) := by
    fun_prop
  have hchoose : IsPPTOn (encThreeDQCSDInput P) encChoice
      (fun input => (adversary input.1).choose (input.2.toPKEPublicKey P)) :=
    hadversary.choose.preprocess hprepare
  have hbit : IsPPTOn encChoiceInput encBool (fun _ => ProbComp.uniform Bool) :=
    isPPTOn_uniform_bool encChoiceInput
  have hguess : IsPPTOn (encThreeDQCSDBitInput P encState) encBool
      (fun input => (adversary (threeDQCSDGuessInput P encode input).1).guess
        (threeDQCSDGuessInput P encode input).2.1
        (threeDQCSDGuessInput P encode input).2.2) :=
    hadversary.guess.preprocess hwrapper.threeGuessInput
  have hverdict : ComputableInPolyTime
      (fun input : ThreeDQCSDBitInput P State × Bool => input.2 == input.1.2)
      (encPair (encThreeDQCSDBitInput P encState) encBool) encBool := by
    fun_prop
  have hguessVerdict : IsPPTOn (encThreeDQCSDBitInput P encState) encBool
      (fun input => do
        let guess ← (adversary (threeDQCSDGuessInput P encode input).1).guess
          (threeDQCSDGuessInput P encode input).2.1
          (threeDQCSDGuessInput P encode input).2.2
        return guess == input.2) := by
    simpa only [bind_pure_comp] using hguess.map_with hverdict
  have htail : IsPPTOn encChoiceInput encBool
      (fun input => do
        let bit ← ProbComp.uniform Bool
        let guessInput := threeDQCSDGuessInput P encode (input, bit)
        let guess ← (adversary guessInput.1).guess guessInput.2.1 guessInput.2.2
        return guess == bit) := by
    have hguessVerdict' : IsPPTOn (encPair encChoiceInput encBool) encBool
        (fun input => do
          let guess ← (adversary (threeDQCSDGuessInput P encode input).1).guess
            (threeDQCSDGuessInput P encode input).2.1
            (threeDQCSDGuessInput P encode input).2.2
          return guess == input.2) := by
      simpa only [encChoiceInput, encChoice, encThreeDQCSDInput, encClassicalChoice,
        encThreeDQCSDBitInput] using hguessVerdict
    exact hbit.bind_with hguessVerdict'
  have htail' : IsPPTOn (encPair (encThreeDQCSDInput P) encChoice) encBool
      (fun input => do
        let bit ← ProbComp.uniform Bool
        let guessInput := threeDQCSDGuessInput P encode (input, bit)
        let guess ← (adversary guessInput.1).guess guessInput.2.1 guessInput.2.2
        return guess == bit) := by
    simpa only [encChoiceInput] using htail
  have hcompiled := hchoose.bind_with
    (second := fun original choice => do
      let bit ← ProbComp.uniform Bool
      let guessInput := threeDQCSDGuessInput P encode ((original, choice), bit)
      let guess ← (adversary guessInput.1).guess guessInput.2.1 guessInput.2.2
      return guess == bit) htail'
  refine hcompiled.congr fun input => ?_
  rfl

omit [NeZero P.n] in
/-- The actual classical `B1` program is strict PPT when both adversary stages, the explicit
encryption-coin sampler and the deterministic encryption/marshalling wrapper have strict machine
certificates. The sampler remains a named input so a finite `SampleSupport2` implementation cannot
be silently identified with the ideal fixed-weight law. -/
theorem isPPTOn_twoDQCSDProgram {State : Type}
    (encode : PKEMessage P → Codeword P) (encState : State ↪ List Bool)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (coinSampler : ℕ → ProbComp (PKECoins P))
    (hadversary : TwoStage.IsPPT (encPKEPublicKey P)
      (encMessagePair (encBitString P.k)) (encPKECiphertext P) encBool encState adversary)
    (hsampler : IsPPTOn encUnary (encPKECoins P) coinSampler)
    (hwrapper : ClassicalWrapperPPT P encode encState) :
    IsPPTOn (encTwoDQCSDInput P) encBool
      (twoDQCSDProgram P encode adversary coinSampler) := by
  let encChoice := encClassicalChoice P encState
  let encChoiceInput := encPair (encTwoDQCSDInput P) encChoice
  let encBitInput := encPair encChoiceInput encBool
  have hprepare : ComputableInPolyTime
      (fun input : TwoDQCSDInput P => (input.1, input.2.toPKEPublicKey P))
      (encTwoDQCSDInput P) (encPair encUnary (encPKEPublicKey P)) := by
    fun_prop
  have hchoose : IsPPTOn (encTwoDQCSDInput P) encChoice
      (fun input => (adversary input.1).choose (input.2.toPKEPublicKey P)) :=
    hadversary.choose.preprocess hprepare
  have hbit : IsPPTOn encChoiceInput encBool (fun _ => ProbComp.uniform Bool) :=
    isPPTOn_uniform_bool encChoiceInput
  have hparameter : ComputableInPolyTime
      (fun input : (TwoDQCSDInput P × ClassicalChoice P State) × Bool => input.1.1.1)
      encBitInput encUnary := by
    fun_prop
  have hcoins : IsPPTOn encBitInput (encPKECoins P)
      (fun input : (TwoDQCSDInput P × ClassicalChoice P State) × Bool =>
        coinSampler input.1.1.1) :=
    hsampler.preprocess hparameter
  have hguess : IsPPTOn (encTwoDQCSDCoinInput P encState) encBool
      (fun input => (adversary (twoDQCSDGuessInput P encode input).1).guess
        (twoDQCSDGuessInput P encode input).2.1
        (twoDQCSDGuessInput P encode input).2.2) :=
    hadversary.guess.preprocess hwrapper.twoGuessInput
  have hverdict : ComputableInPolyTime
      (fun input : TwoDQCSDCoinInput P State × Bool => input.2 == input.1.1.2)
      (encPair (encTwoDQCSDCoinInput P encState) encBool) encBool := by
    fun_prop
  have hguessVerdict : IsPPTOn (encTwoDQCSDCoinInput P encState) encBool
      (fun input => do
        let guess ← (adversary (twoDQCSDGuessInput P encode input).1).guess
          (twoDQCSDGuessInput P encode input).2.1
          (twoDQCSDGuessInput P encode input).2.2
        return guess == input.1.2) := by
    simpa only [bind_pure_comp] using hguess.map_with hverdict
  have hguessVerdict' : IsPPTOn (encPair encBitInput (encPKECoins P)) encBool
      (fun input => do
        let guess ← (adversary (twoDQCSDGuessInput P encode input).1).guess
          (twoDQCSDGuessInput P encode input).2.1
          (twoDQCSDGuessInput P encode input).2.2
        return guess == input.1.2) := by
    simpa only [encBitInput, encChoiceInput, encChoice, encTwoDQCSDInput,
      encClassicalChoice, encTwoDQCSDCoinInput] using hguessVerdict
  have hcoinTail : IsPPTOn encBitInput encBool
      (fun input => do
        let coins ← coinSampler input.1.1.1
        let guessInput := twoDQCSDGuessInput P encode (input, coins)
        let guess ← (adversary guessInput.1).guess guessInput.2.1 guessInput.2.2
        return guess == input.2) := by
    exact hcoins.bind_with
      (second := fun input coins => do
        let guessInput := twoDQCSDGuessInput P encode (input, coins)
        let guess ← (adversary guessInput.1).guess guessInput.2.1 guessInput.2.2
        return guess == input.2) hguessVerdict'
  have hcoinTail' : IsPPTOn (encPair encChoiceInput encBool) encBool
      (fun input => do
        let coins ← coinSampler input.1.1.1
        let guessInput := twoDQCSDGuessInput P encode (input, coins)
        let guess ← (adversary guessInput.1).guess guessInput.2.1 guessInput.2.2
        return guess == input.2) := by
    simpa only [encBitInput] using hcoinTail
  have hbitTail : IsPPTOn encChoiceInput encBool
      (fun input => do
        let bit ← ProbComp.uniform Bool
        let coins ← coinSampler input.1.1
        let guessInput := twoDQCSDGuessInput P encode ((input, bit), coins)
        let guess ← (adversary guessInput.1).guess guessInput.2.1 guessInput.2.2
        return guess == bit) := by
    exact hbit.bind_with
      (second := fun input bit => do
        let coins ← coinSampler input.1.1
        let guessInput := twoDQCSDGuessInput P encode ((input, bit), coins)
        let guess ← (adversary guessInput.1).guess guessInput.2.1 guessInput.2.2
        return guess == bit) hcoinTail'
  have hbitTail' : IsPPTOn (encPair (encTwoDQCSDInput P) encChoice) encBool
      (fun input => do
        let bit ← ProbComp.uniform Bool
        let coins ← coinSampler input.1.1
        let guessInput := twoDQCSDGuessInput P encode ((input, bit), coins)
        let guess ← (adversary guessInput.1).guess guessInput.2.1 guessInput.2.2
        return guess == bit) := by
    simpa only [encChoiceInput] using hbitTail
  have hcompiled := hchoose.bind_with
    (second := fun original choice => do
      let bit ← ProbComp.uniform Bool
      let coins ← coinSampler original.1
      let guessInput := twoDQCSDGuessInput P encode (((original, choice), bit), coins)
      let guess ← (adversary guessInput.1).guess guessInput.2.1 guessInput.2.2
      return guess == bit) hbitTail'
  refine hcompiled.congr fun input => ?_
  rfl

omit [NeZero P.n] in
/-- If the explicit `B1` sampler has the ideal encryption-coin law, the executable program is
exactly the finite 2-DQCSD-P distinguisher already used by the game identity. -/
theorem eval_twoDQCSDProgram_eq_distinguisher {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (coinSampler : ℕ → ProbComp (PKECoins P)) (input : TwoDQCSDInput P)
    (hcoins : ProbComp.eval (coinSampler input.1) = ProbComp.eval (pkeSampleCoins P)) :
    ProbComp.eval (twoDQCSDProgram P encode adversary coinSampler input) =
      twoDQCSDDistinguisher P encode (adversary input.1) input.2 := by
  simp only [twoDQCSDProgram, twoDQCSDDistinguisher, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_uniform]
  rw [hcoins]
  rfl

omit [NeZero P.n] in
/-- The executable `B2` program is exactly the finite 3-DQCSD-PT distinguisher already used by
the second game identity. -/
theorem eval_threeDQCSDProgram {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) (input : ThreeDQCSDInput P) :
    ProbComp.eval (threeDQCSDProgram P encode adversary input) =
      threeDQCSDDistinguisher P encode (adversary input.1) input.2 := by
  simp only [threeDQCSDProgram, threeDQCSDDistinguisher, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_uniform]
  rfl

omit [NeZero P.n] in
/-- The construction-selected native `B1` table, replayed on its exact fixed fair-coin budget,
agrees with the reviewed 2-DQCSD-P game modulo only the named ideal sampler bridge. -/
theorem TwoDQCSDNativeStages.eval_eq_distinguisher {State : Type}
    (encode : PKEMessage P → Codeword P) (encState : State ↪ List Bool)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (coinSampler : ℕ → ProbComp (PKECoins P))
    (stages : TwoDQCSDNativeStages P encode encState adversary coinSampler)
    (input : TwoDQCSDInput P)
    (hcoins : ProbComp.eval (coinSampler input.1) = ProbComp.eval (pkeSampleCoins P)) :
    (twoDQCSDDistinguisher P encode (adversary input.1) input.2).map encBool =
      (BitString.uniformList (stages.compiled.time input)).map
        (fun coins => stages.compiled.machine.runClosedCoins coins
          (encTwoDQCSDInput P input)) := by
  rw [← eval_twoDQCSDProgram_eq_distinguisher P encode adversary coinSampler input hcoins,
    stages.realizes P encode encState adversary coinSampler input,
    stages.compiled.machine.eval_runClosed_eq_map_coins]

omit [NeZero P.n] in
/-- The construction-selected native `B2` table, replayed on its exact fixed fair-coin budget,
agrees with the reviewed finite 3-DQCSD-PT game. -/
theorem ThreeDQCSDNativeStages.eval_eq_distinguisher {State : Type}
    (encode : PKEMessage P → Codeword P) (encState : State ↪ List Bool)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (stages : ThreeDQCSDNativeStages P encode encState adversary)
    (input : ThreeDQCSDInput P) :
    (threeDQCSDDistinguisher P encode (adversary input.1) input.2).map encBool =
      (BitString.uniformList (stages.compiled.time input)).map
        (fun coins => stages.compiled.machine.runClosedCoins coins
          (encThreeDQCSDInput P input)) := by
  rw [← eval_threeDQCSDProgram P encode adversary input,
    stages.realizes P encode encState adversary input,
    stages.compiled.machine.eval_runClosed_eq_map_coins]

/-! ### Saved-coin laws against the reviewed finite games -/

omit [NeZero P.n] in
/-- A strict `B1` realization has one total deterministic saved-coin evaluator. Every seed yields
a supported result, and every sufficiently long uniform seed gives exactly the reviewed finite
2-DQCSD-P distinguisher when the explicit encryption-coin sampler has the ideal law. -/
theorem exists_twoDQCSD_savedCoinEvaluator {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (coinSampler : ℕ → ProbComp (PKECoins P))
    (hppt : IsPPTOn (encTwoDQCSDInput P) encBool
      (twoDQCSDProgram P encode adversary coinSampler))
    (hcoins : ∀ κ, ProbComp.eval (coinSampler κ) = ProbComp.eval (pkeSampleCoins P)) :
    ∃ (c d : ℕ) (evaluate : TwoDQCSDInput P → List Bool → Bool),
      ComputableInPolyTime (fun input => evaluate input.1 input.2)
        (encPair (encTwoDQCSDInput P) encBits) encBool ∧
      (∀ input coins,
        evaluate input coins ∈ (ProbComp.eval
          (twoDQCSDProgram P encode adversary coinSampler input)).support) ∧
      ∀ input length, c * ((encTwoDQCSDInput P input).length + 1) ^ d ≤ length →
        twoDQCSDDistinguisher P encode (adversary input.1) input.2 =
          (BitString.uniformList length).map (evaluate input) := by
  obtain ⟨c, d, evaluate, hevaluate, hsupported, hlaw, -⟩ :=
    hppt.exists_total_seeded_evaluator_with_length
  refine ⟨c, d, evaluate, hevaluate, hsupported, fun input length hlength => ?_⟩
  rw [← eval_twoDQCSDProgram_eq_distinguisher P encode adversary coinSampler input
    (hcoins input.1)]
  exact hlaw input length hlength

omit [NeZero P.n] in
/-- A strict `B2` realization has one total deterministic saved-coin evaluator whose sufficiently
long uniform seeds give exactly the reviewed finite 3-DQCSD-PT distinguisher. -/
theorem exists_threeDQCSD_savedCoinEvaluator {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : ℕ → TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State)
    (hppt : IsPPTOn (encThreeDQCSDInput P) encBool
      (threeDQCSDProgram P encode adversary)) :
    ∃ (c d : ℕ) (evaluate : ThreeDQCSDInput P → List Bool → Bool),
      ComputableInPolyTime (fun input => evaluate input.1 input.2)
        (encPair (encThreeDQCSDInput P) encBits) encBool ∧
      (∀ input coins,
        evaluate input coins ∈ (ProbComp.eval
          (threeDQCSDProgram P encode adversary input)).support) ∧
      ∀ input length, c * ((encThreeDQCSDInput P input).length + 1) ^ d ≤ length →
        threeDQCSDDistinguisher P encode (adversary input.1) input.2 =
          (BitString.uniformList length).map (evaluate input) := by
  obtain ⟨c, d, evaluate, hevaluate, hsupported, hlaw, -⟩ :=
    hppt.exists_total_seeded_evaluator_with_length
  refine ⟨c, d, evaluate, hevaluate, hsupported, fun input length hlength => ?_⟩
  rw [← eval_threeDQCSDProgram P encode adversary input]
  exact hlaw input length hlength

end Cslib.Crypto.HQC
