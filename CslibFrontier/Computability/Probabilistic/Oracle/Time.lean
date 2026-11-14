/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Time
public import CslibFrontier.Computability.Probabilistic.Oracle
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import CslibFrontier.Computability.Probabilistic.Oracle.Normalization
import CslibFrontier.Computability.Probabilistic.Oracle.Tidy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.QueryBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.QueryTake
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ExtendTapes
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.InputFromTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.OutputToTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PrepareInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.EncLen

/-!
# Explicit-time intrinsically halting oracle realizations

`Cslib.Probability.ComputesOracleInTimeOn input output t program` strengthens `IsOraclePPTOn` by
giving an explicit step schedule `t : α → ℕ` and requiring that one finite-control fair-coin oracle
machine realizes the complete joint output and external-state law across all shared stateful
handlers AND has actually halted (`final.1.tapes.state = none`) on every supported execution at
step `t a`.

As in the closed case (`CslibFrontier.Computability.Probabilistic.Time`), actual halting makes step
monotonicity (`ComputesOracleInTimeOn.mono`) hold unconditionally without requiring the larger
schedule to be computable. Every `t a`-step execution makes at most `t a` external queries, each of
word length at most `t a` (`ComputesOracleInTimeOn.query_bounds`). Because cryptographic security
bounds often track step count `t` and query count `q` separately (`q ≤ t`), this module also
defines `ComputesOracleInTimeAndQueriesOn` and parameterized `ComputesOracleInTimeAndQueries`.

Together with the clean-phase normalization compiler of
`CslibFrontier.Computability.Probabilistic.Oracle.Normalization`, `IsOraclePPTOn` and `IsOraclePPT`
are equivalent to `ComputesOracleInTimeOn` and `ComputesOracleInTime` under polynomially bounded
step schedules (`isOraclePPTOn_iff_exists_polyBounded_computesOracleInTimeOn`,
`isOraclePPT_iff_exists_polyBounded_computesOracleInTime`).

## Main definitions

* `Cslib.Probability.ComputesOracleInTimeOn`: uniform halting oracle-machine realization within an
  explicit step schedule.
* `Cslib.Probability.ComputesOracleInTime`: parameterized halting oracle-machine realization on a
  unary security parameter and auxiliary input length.
* `Cslib.Probability.ComputesOracleInTimeAndQueriesOn`,
  `Cslib.Probability.ComputesOracleInTimeAndQueries`: joint explicit `(t, q)` time-and-query bounds.

## Main results

* `Cslib.Probability.ComputesOracleInTimeOn.mono`: unconditional step-schedule monotonicity.
* `Cslib.Probability.ComputesOracleInTimeOn.congr`,
  `Cslib.Probability.ComputesOracleInTimeOn.length_le`: joint-law congruence and supported output
  length bound `≤ t a`.
* `Cslib.Probability.ComputesOracleInTimeOn.query_bounds`, `.isQueryBounded`: external query-count
  and query-length bounds `≤ t a`.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.computesOracleInTimeOn`: plain deterministic
  computations lift with exact step bound `t`.
* `Cslib.Probability.ComputesInTimeOn.computesOracleInTimeOn`,
  `Cslib.Probability.ComputesOracleInTimeOn.computesInTimeOn`: exact step-preserving lifts between
  closed and channel-free oracle realizations.
* `Cslib.Probability.ComputesOracleInTimeOn.uniform_bool`, `.query_take_pair`, `.query_take`,
  `.bind_sample_left`, `.bind_sample_right`, `.preprocess`, `.map`: quantitative primitives and
  buffered compositions with explicit machine-independent step bounds.
* `Cslib.Probability.isOraclePPTOn_iff_exists_polyBounded_computesOracleInTimeOn`,
  `Cslib.Probability.isOraclePPT_iff_exists_polyBounded_computesOracleInTime`: equivalence with
  `IsOraclePPTOn` and `IsOraclePPT`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapters 3, 7.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Sections 3.11,
  4.1.
-/

public section

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
  _root_.Turing.MultiTapePTM

/-- One finite-control oracle machine realizes the joint output and external-state distribution of
`program` within `t a` steps across all shared stateful handlers, and has halted on every supported
execution at step `t a`. -/
@[expose] def ComputesOracleInTimeOn {Operation α β : Type} [DecidableEq Operation]
    (input : α ↪ List Bool) (output : β ↪ List Bool) (t : α → ℕ)
    (program : α → WordOracleComp Operation β) : Prop :=
  Finite Operation ∧ ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Operation),
    ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (output <$> program a) s =
        ProbOracleComp.runWith oracle (machine.runOracle (t a) (input a)) s ∧
      ∀ final ∈ (ProbOracleComp.runWith oracle
          (machine.runOracleConfigFrom (t a) (machine.initialConfig (input a))) s).support,
        final.1.tapes.state = none

/-- Uniform halting oracle realization on a unary security parameter and auxiliary word, indexed by
`(n, aux.length)`. -/
@[expose] def ComputesOracleInTime {Operation β : Type} [DecidableEq Operation]
    (output : β ↪ List Bool) (t : ℕ → ℕ → ℕ)
    (program : ℕ → List Bool → WordOracleComp Operation β) : Prop :=
  ComputesOracleInTimeOn (encPair encUnary encBits) output
    (fun input => t input.1 input.2.length) (fun input => program input.1 input.2)

/-- Joint explicit `(t, q)` realization: `program` is realized by a halting oracle machine within
`t a` steps and makes at most `q a` external queries on every execution path. -/
@[expose] def ComputesOracleInTimeAndQueriesOn {Operation α β : Type} [DecidableEq Operation]
    (input : α ↪ List Bool) (output : β ↪ List Bool) (t q : α → ℕ)
    (program : α → WordOracleComp Operation β) : Prop :=
  ComputesOracleInTimeOn input output t program ∧
    ∀ a, (program a).IsQueryBounded (q a)

/-- Parameterized joint `(t, q)` time-and-query realization on a unary security parameter and
auxiliary word. -/
@[expose] def ComputesOracleInTimeAndQueries {Operation β : Type} [DecidableEq Operation]
    (output : β ↪ List Bool) (t q : ℕ → ℕ → ℕ)
    (program : ℕ → List Bool → WordOracleComp Operation β) : Prop :=
  ComputesOracleInTime output t program ∧
    ∀ n aux, (program n aux).IsQueryBounded (q n aux.length)

/-! ### Private machine-level helpers -/

private theorem of_computesTidily {Operation α β : Type} [DecidableEq Operation]
    [Finite Operation] {input : α ↪ List Bool} {output : β ↪ List Bool} {t : α → ℕ}
    {program : α → WordOracleComp Operation β}
    {k : ℕ} {Control : Type} [Finite Control]
    (machine : MultiTapePTM k Bool Control Operation)
    (h : ∀ a, machine.ComputesTidily (input a) (t a) (output <$> program a)) :
    ComputesOracleInTimeOn input output t program := by
  refine ⟨inferInstance, k, Control, inferInstance, machine, fun a State oracle s => ?_⟩
  refine ⟨((h a).runOracle oracle s).symm, ?_⟩
  exact ((h a) []).halted oracle s (machine.initialConfig (input a))
    (Cfg.init_eq_wordsCfg machine.initial (input a)) (fun _ => rfl)

private theorem runOracleConfigFrom_ofClosed {k : ℕ} {State Operation : Type}
    [DecidableEq Operation] (machine : MultiTapePTM k Bool State) (fuel : ℕ) {x : List Bool}
    (ch : Operation → Channel Bool) (cfg : Config k Bool State Empty x) :
    (ofClosed (Operation := Operation) machine).runOracleConfigFrom fuel
        { tapes := cfg.tapes, channels := ch } =
      (fun final => { tapes := final.tapes, channels := ch }) <$>
        ProbOracleComp.sample (machine.runClosedConfigFrom fuel cfg) := by
  let embed (c : Config k Bool State Empty x) : Config k Bool State Operation x :=
    { tapes := c.tapes, channels := ch }
  have hsim := MultiTapeMachine.runConfigFrom_map machine
    (ofClosed (Operation := Operation) machine)
    (fun choices => choices <$> ProbOracleComp.sample
      (spec := fun _ : Operation × List Bool => List Bool) (ProbComp.uniform Bool))
    (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun oracle _ => oracle.elim) (fun op word => ProbOracleComp.query (op, word)) embed
    (fun c => by
      cases hs : c.tapes.state with
      | none => simp [MultiTapeMachine.runConfigFrom, embed, hs]
      | some state =>
        have hanswer : c.answerSymbols = Empty.elim := funext fun oracle => oracle.elim
        dsimp only [embed]
        simp only [MultiTapeMachine.runConfigFrom, hs, hanswer, bind_map_left, map_bind]
        congr 1 with bit : 1
        cases htr : machine.tr state c.tapes.inputSymbol c.tapes.workTapeSymbols Empty.elim bit with
        | step action symbol move =>
          simp only [ofClosed, htr, map_pure]
          congr 1
          refine Config.ext rfl (funext fun op => ?_)
          cases hop : ch op
          simp [Config.step, hop]
        | query oracle next => exact oracle.elim)
  change MultiTapeMachine.runConfigFrom (ofClosed (Operation := Operation) machine) _ _ fuel
    (embed cfg) = _
  rw [hsim]
  simp only [runClosedConfigFrom, MultiTapePTM.runConfigFrom, ProbOracleComp.sample,
    OracleComp.interpret_map, MultiTapeMachine.interpret_runConfigFrom]
  congr 2 with oracle : 1
  exact oracle.elim

private theorem runWith_runOracleConfigFrom_ofClosed {k : ℕ} {State Operation OracleState : Type}
    [DecidableEq Operation] (machine : MultiTapePTM k Bool State)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (fuel : ℕ) {x : List Bool} (ch : Operation → Channel Bool)
    (cfg : Config k Bool State Empty x) (s : OracleState) :
    ProbOracleComp.runWith oracle
        ((ofClosed (Operation := Operation) machine).runOracleConfigFrom fuel
          { tapes := cfg.tapes, channels := ch }) s =
      (ProbComp.eval (machine.runClosedConfigFrom fuel cfg)).map
        (fun final => ({ tapes := final.tapes, channels := ch }, s)) := by
  rw [runOracleConfigFrom_ofClosed, ProbOracleComp.runWith_map, ProbOracleComp.runWith_sample,
    PMF.map_comp]
  rfl

section BufferedOracleComp

variable {k₀ k₁ : ℕ} {State₀ State₁ Operation OracleState : Type} {x : List Bool}

private def oReserve (k₁ : ℕ) (cfg : Config k₀ Bool State₀ Operation x) :
    Config (k₁ + k₀) Bool State₀ Operation x :=
  cfg.embed (Fin.natAddEmb k₁) (fun _ _ => none) (fun _ => 0)

private def oBuffer (k₁ : ℕ) (cfg : Config k₀ Bool State₀ Operation x) :
    Config (k₁ + k₀ + 2) Bool State₀ Operation x :=
  (OutputToTape.config (oReserve k₁ cfg)).embed Fin.castSuccEmb (fun _ _ => none) (fun _ => 0)

private def oSource (m₁ : MultiTapePTM k₀ Bool State₀ Operation) (k₁ : ℕ) :
    MultiTapePTM (k₁ + k₀ + 2) Bool State₀ Operation :=
  ((m₁.extendTapes (Fin.natAddEmb k₁)).outputToTape).extendTapes Fin.castSuccEmb

private def oConsumer (m₂ : MultiTapePTM k₁ Bool State₁ Operation) (k₀ : ℕ) :
    MultiTapePTM (k₁ + k₀ + 2) Bool State₁ Operation :=
  (m₂.extendTapes (Fin.castAddEmb k₀)).inputFromTape

private noncomputable def oContinuation (m₂ : MultiTapePTM k₁ Bool State₁ Operation) (k₀ : ℕ)
    (mark : Bool) : MultiTapePTM (k₁ + k₀ + 2) Bool
      ((MarkWorkState ⊕ RewindWorkState) ⊕ State₁) Operation :=
  (ofDeterministic (prepareInput (k₁ + k₀) mark)).seq (oConsumer m₂ k₀)

private noncomputable def oComp (m₂ : MultiTapePTM k₁ Bool State₁ Operation)
    (m₁ : MultiTapePTM k₀ Bool State₀ Operation) (mark : Bool) :
    MultiTapePTM (k₁ + k₀ + 2) Bool
      (State₀ ⊕ ((MarkWorkState ⊕ RewindWorkState) ⊕ State₁)) Operation :=
  (oSource m₁ k₁).seq (oContinuation m₂ k₀ mark)

private def oConsumerConfig (mark : Bool) (cfg₀ : Config k₀ Bool State₀ Operation x)
    (cfg₁ : Config k₁ Bool State₁ Operation cfg₀.tapes.output) :
    Config (k₁ + k₀ + 2) Bool State₁ Operation x :=
  InputFromTape.config mark
    (cfg₁.embed (Fin.castAddEmb k₀)
      (oReserve k₁ cfg₀).tapes.workTapes (oReserve k₁ cfg₀).tapes.workTapePos)
    x cfg₀.tapes.inputPos

private def oReady (mark : Bool) (k₁ : ℕ) (cfg₀ : Config k₀ Bool State₀ Operation x) :
    Config (k₁ + k₀ + 2) Bool (MarkWorkState ⊕ RewindWorkState) Operation x where
  tapes := ⟨none, cfg₀.tapes.inputPos,
    Fin.append (oReserve k₁ cfg₀).tapes.workTapes
      ![tapeOfList cfg₀.tapes.output, Function.update (fun _ => none) (-1) (some mark)],
    Fin.append (oReserve k₁ cfg₀).tapes.workTapePos (fun _ => 0), []⟩
  channels := cfg₀.channels

private theorem oBuffer_tapes (k₁ : ℕ) (cfg₀ : Config k₀ Bool State₀ Operation x) :
    (oBuffer k₁ cfg₀).tapes =
      ⟨cfg₀.tapes.state, cfg₀.tapes.inputPos,
        Fin.append (oReserve k₁ cfg₀).tapes.workTapes
          ![tapeOfList cfg₀.tapes.output, fun _ => none],
        Fin.append (oReserve k₁ cfg₀).tapes.workTapePos
          ![(cfg₀.tapes.output.length : ℤ), 0], []⟩ := by
  have happend {α : Type} (f : Fin (k₁ + k₀) → α) (a b : α) :
      Fin.lastCases b (Fin.lastCases a f) = Fin.append f ![a, b] := by
    have hsnoc {n : ℕ} (f : Fin n → α) (a : α) :
        (Fin.lastCases a f : Fin (n + 1) → α) = Fin.snoc f a := by
      funext i
      induction i using Fin.lastCases <;> simp
    change Fin.lastCases b (Fin.lastCases a f) = Fin.append f (Fin.cons a (Fin.cons b Fin.elim0))
    rw [hsnoc, hsnoc, Fin.append_right_cons, Fin.append_right_eq_snoc]
    rfl
  simp only [oBuffer, Config.embed, OutputToTape.config, MultiTapeTM.embed_castSucc,
    MultiTapeTM.outCfg, happend]
  rfl

private theorem runFrom_oPrepare (mark : Bool) (k₁ : ℕ)
    (cfg₀ : Config k₀ Bool State₀ Operation x) :
    (prepareInput (k₁ + k₀) mark).runFrom
        ((oBuffer k₁ cfg₀).tapes.withState
          (some (prepareInput (k₁ + k₀) mark).q₀)) (cfg₀.tapes.output.length + 4) =
      (oReady mark k₁ cfg₀).tapes := by
  rw [MultiTapeTM.runFrom_prepareInput mark _ cfg₀.tapes.output
    (by rw [oBuffer_tapes]; simp) (by rw [oBuffer_tapes]; simp) (by rw [oBuffer_tapes]; simp)]
  rw [oBuffer_tapes]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.addCases with
  | left i => simp [oReady, Function.update_of_ne (Fin.castAdd_ne_natAdd i _)]
  | right i => fin_cases i <;> simp [oReady]

private theorem start_oReady (m₂ : MultiTapePTM k₁ Bool State₁ Operation) (mark : Bool)
    (cfg₀ : Config k₀ Bool State₀ Operation x) :
    Sequential.start (oConsumer m₂ k₀) (oReady mark k₁ cfg₀) =
      oConsumerConfig mark cfg₀
        { tapes := Cfg.init m₂.initial cfg₀.tapes.output, channels := cfg₀.channels } := by
  refine Config.ext ?_ rfl
  simp only [Sequential.start, oReady, oConsumerConfig, InputFromTape.config, Config.embed,
    MultiTapeTM.embed_castAdd, MultiTapeTM.inCfg, Cfg.init, oReserve,
    MultiTapeTM.embed_natAdd, Cfg.withState]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.addCases with
  | left i => induction i using Fin.addCases <;> simp
  | right i => fin_cases i <;> simp

private theorem runOracleConfigFrom_oSource [DecidableEq Operation]
    (m₁ : MultiTapePTM k₀ Bool State₀ Operation) (k₁ fuel : ℕ) (x : List Bool) :
    (oSource m₁ k₁).runOracleConfigFrom fuel ((oSource m₁ k₁).initialConfig x) =
      oBuffer k₁ <$> m₁.runOracleConfigFrom fuel (m₁.initialConfig x) := by
  simp only [oSource, runOracleConfigFrom,
    MultiTapeMachine.initialConfig_extendTapes,
    MultiTapeMachine.initialConfig_outputToTape,
    MultiTapePTM.runConfigFrom_embed,
    MultiTapePTM.runConfigFrom_outputToTape,
    Functor.map_map]
  rfl

private theorem runOracleConfigFrom_oConsumer [DecidableEq Operation]
    (m₂ : MultiTapePTM k₁ Bool State₁ Operation) (mark : Bool)
    (cfg₀ : Config k₀ Bool State₀ Operation x)
    (cfg₁ : Config k₁ Bool State₁ Operation cfg₀.tapes.output) (fuel : ℕ) :
    (oConsumer m₂ k₀).runOracleConfigFrom fuel (oConsumerConfig mark cfg₀ cfg₁) =
      oConsumerConfig mark cfg₀ <$> m₂.runOracleConfigFrom fuel cfg₁ := by
  simp only [oConsumer, oConsumerConfig, runOracleConfigFrom,
    MultiTapePTM.runConfigFrom_inputFromTape,
    MultiTapePTM.runConfigFrom_embed,
    Functor.map_map]
  rfl

private theorem runWith_oContinuation [DecidableEq Operation]
    (m₂ : MultiTapePTM k₁ Bool State₁ Operation)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (mark : Bool) (cfg₀ : Config k₀ Bool State₀ Operation x) (prepareTime runTime : ℕ)
    (s₁ : OracleState) (hprepare : cfg₀.tapes.output.length + 4 ≤ prepareTime)
    (hrun : ∀ final ∈ (ProbOracleComp.runWith oracle
      (m₂.runOracleConfigFrom runTime
        { tapes := Cfg.init m₂.initial cfg₀.tapes.output, channels := cfg₀.channels }) s₁).support,
      final.1.tapes.state = none) :
    ProbOracleComp.runWith oracle
      ((oContinuation m₂ k₀ mark).runOracleConfigFrom (prepareTime + runTime)
        (Sequential.start (oContinuation m₂ k₀ mark) (oBuffer k₁ cfg₀))) s₁ =
      (ProbOracleComp.runWith oracle (m₂.runOracleConfigFrom runTime
        { tapes := Cfg.init m₂.initial cfg₀.tapes.output, channels := cfg₀.channels }) s₁).map
        (fun (final, s₂) => (Sequential.right (oConsumerConfig mark cfg₀ final), s₂)) := by
  let prep := prepareInput (k₁ + k₀) mark
  let initial := Sequential.start (ofDeterministic prep) (oBuffer k₁ cfg₀)
  have hdet := runFrom_oPrepare mark k₁ cfg₀
  change prep.runFrom initial.tapes (cfg₀.tapes.output.length + 4) = _ at hdet
  have hprep : prep.runFrom initial.tapes prepareTime = (oReady mark k₁ cfg₀).tapes := by
    rw [prep.runFrom_eq_of_halt initial.tapes hprepare (by rw [hdet]; rfl), hdet]
  have hstate : ProbOracleComp.runWith oracle
      ((ofDeterministic prep).runOracleConfigFrom prepareTime initial) s₁ =
      PMF.pure (oReady mark k₁ cfg₀, s₁) := by
    rw [run_interpret_runOracleConfigFrom_ofDeterministic, hprep]
    rfl
  have hconsumer_halt : ∀ final ∈ (ProbOracleComp.runWith oracle
      ((oConsumer m₂ k₀).runOracleConfigFrom runTime
        (oConsumerConfig mark cfg₀
          { tapes := Cfg.init m₂.initial cfg₀.tapes.output, channels := cfg₀.channels }))
      s₁).support, final.1.tapes.state = none := by
    intro final hfinal
    rw [runOracleConfigFrom_oConsumer, ProbOracleComp.runWith_map] at hfinal
    obtain ⟨⟨res, s₂⟩, hres, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hrun (res, s₂) hres
  change ProbOracleComp.runWith oracle
    (((ofDeterministic prep).seq (oConsumer m₂ k₀)).runOracleConfigFrom
      _ (Sequential.left (oConsumer m₂ k₀) initial)) s₁ = _
  rw [run_interpret_runOracleConfigFrom_seq _ _ oracle _ prepareTime runTime s₁
    (by simp [hstate, oReady])
    (by
      rintro ⟨resCfg, resState⟩ hresult
      rw [hstate, PMF.mem_support_pure_iff] at hresult
      rcases Prod.mk.inj hresult with ⟨rfl, rfl⟩
      rw [start_oReady]
      exact hconsumer_halt),
    hstate, PMF.pure_bind, start_oReady, runOracleConfigFrom_oConsumer, ProbOracleComp.runWith_map,
    PMF.map_comp]
  rfl

private theorem runWith_oComp [DecidableEq Operation]
    (m₁ : MultiTapePTM k₀ Bool State₀ Operation)
    (m₂ : MultiTapePTM k₁ Bool State₁ Operation)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (mark : Bool) (x : List Bool) (t₁ t₂ : ℕ) (s : OracleState)
    (hfirst : ∀ final ∈ (ProbOracleComp.runWith oracle
      (m₁.runOracleConfigFrom t₁ (m₁.initialConfig x)) s).support,
      final.1.tapes.state = none)
    (hsecond : ∀ result ∈ (ProbOracleComp.runWith oracle
      (m₁.runOracleConfigFrom t₁ (m₁.initialConfig x)) s).support,
      ∀ final ∈ (ProbOracleComp.runWith oracle
        (m₂.runOracleConfigFrom t₂
          { tapes := Cfg.init m₂.initial result.1.tapes.output,
            channels := result.1.channels }) result.2).support,
        final.1.tapes.state = none) :
    ProbOracleComp.runWith oracle ((oComp m₂ m₁ mark).runOracleConfigFrom
        (t₁ + (t₁ + 4 + t₂)) ((oComp m₂ m₁ mark).initialConfig x)) s =
      (ProbOracleComp.runWith oracle (m₁.runOracleConfigFrom t₁ (m₁.initialConfig x)) s).bind
        (fun (cfg₀, s₁) =>
          (ProbOracleComp.runWith oracle (m₂.runOracleConfigFrom t₂
            { tapes := Cfg.init m₂.initial cfg₀.tapes.output,
              channels := cfg₀.channels }) s₁).map
            (fun (cfg₁, s₂) =>
              (Sequential.right (Sequential.right (oConsumerConfig mark cfg₀ cfg₁)), s₂))) := by
  have hlen : ∀ result ∈ (ProbOracleComp.runWith oracle
      (m₁.runOracleConfigFrom t₁ (m₁.initialConfig x)) s).support,
      result.1.tapes.output.length ≤ t₁ := by
    rintro ⟨cfg₀, s₁⟩ hres
    have h := length_output_le_of_mem_support_runOracleConfigFrom m₁ oracle t₁
      (m₁.initialConfig x) s hres
    simpa [MultiTapeMachine.initialConfig, Cfg.init] using h
  change ProbOracleComp.runWith oracle
    (((oSource m₁ k₁).seq (oContinuation m₂ k₀ mark)).runOracleConfigFrom
      _ (Sequential.left (oContinuation m₂ k₀ mark) ((oSource m₁ k₁).initialConfig x))) s = _
  rw [run_interpret_runOracleConfigFrom_seq _ _ oracle _ t₁ (t₁ + 4 + t₂) s
    (by
      intro result hresult
      rw [runOracleConfigFrom_oSource, ProbOracleComp.runWith_map] at hresult
      obtain ⟨⟨cfg₀, s₁⟩, hcfg₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
      exact hfirst (cfg₀, s₁) hcfg₀)
    (by
      intro result hresult final hfinal
      rw [runOracleConfigFrom_oSource, ProbOracleComp.runWith_map] at hresult
      obtain ⟨⟨cfg₀, s₁⟩, hcfg₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
      dsimp only [Prod.map_apply, id_eq] at hfinal
      have hlen₀ : cfg₀.tapes.output.length ≤ t₁ := hlen (cfg₀, s₁) hcfg₀
      rw [runWith_oContinuation m₂ oracle mark cfg₀ (t₁ + 4) t₂ s₁
        (by omega) (hsecond (cfg₀, s₁) hcfg₀)] at hfinal
      obtain ⟨⟨cfg₁, s₂⟩, hcfg₁, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
      change cfg₁.tapes.state.map Sum.inr = none
      rw [hsecond (cfg₀, s₁) hcfg₀ (cfg₁, s₂) hcfg₁]
      rfl),
    runOracleConfigFrom_oSource, ProbOracleComp.runWith_map, PMF.bind_map]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨cfg₀, s₁⟩ hcfg₀ => ?_
  dsimp only [Function.comp_def, Prod.map_apply, id_eq]
  have hlen₀ : cfg₀.tapes.output.length ≤ t₁ := hlen (cfg₀, s₁) hcfg₀
  rw [runWith_oContinuation m₂ oracle mark cfg₀ (t₁ + 4) t₂ s₁
    (by omega) (hsecond (cfg₀, s₁) hcfg₀), PMF.map_comp]
  rfl

end BufferedOracleComp

/-! ### Basic properties of `ComputesOracleInTimeOn` -/

namespace ComputesOracleInTimeOn

variable {Operation α β γ : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
  {t t₁ t₂ : α → ℕ} {program program' : α → WordOracleComp Operation γ}

/-- Finiteness of the operation channel type is part of the certificate. -/
theorem finite_operations (h : ComputesOracleInTimeOn input output t program) :
    Finite Operation := h.1

/-- Enlarging the step schedule preserves halting oracle realization unconditionally, without
requiring the larger schedule to be computable. -/
theorem mono (h : ComputesOracleInTimeOn input output t₁ program) (hle : ∀ a, t₁ a ≤ t₂ a) :
    ComputesOracleInTimeOn input output t₂ program := by
  obtain ⟨hops, k, Control, hfinite, machine, hmachine⟩ := h
  refine ⟨hops, k, Control, hfinite, machine, fun a State oracle s => ?_⟩
  obtain ⟨hlaw, hhalt⟩ := hmachine a State oracle s
  have hcfg := run_interpret_runOracleConfigFrom_eq_of_halted machine oracle
    (machine.initialConfig (input a)) (hle a) s hhalt
  refine ⟨?_, ?_⟩
  · rw [hlaw, runOracle_eq_map, runOracle_eq_map, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_map, hcfg]
  · intro final hfinal
    rw [hcfg] at hfinal
    exact hhalt final hfinal

/-- Equality of the complete joint output/state semantics preserves halting oracle realization. -/
theorem congr (h : ComputesOracleInTimeOn input output t program)
    (heq : ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (program a) s =
        ProbOracleComp.runWith oracle (program' a) s) :
    ComputesOracleInTimeOn input output t program' := by
  obtain ⟨hops, k, Control, hfinite, machine, hmachine⟩ := h
  refine ⟨hops, k, Control, hfinite, machine, fun a State oracle s => ?_⟩
  obtain ⟨hlaw, hhalt⟩ := hmachine a State oracle s
  refine ⟨?_, hhalt⟩
  simpa only [ProbOracleComp.runWith_map, heq] using hlaw

/-- Every supported encoded output has length at most `t a`, regardless of oracle reply lengths. -/
theorem length_le (h : ComputesOracleInTimeOn input output t program) (a : α)
    {State : Type} (oracle : Operation × List Bool → StateT State PMF (List Bool))
    (s s' : State) {result : γ}
    (hresult : (result, s') ∈ (ProbOracleComp.runWith oracle (program a) s).support) :
    (output result).length ≤ t a := by
  obtain ⟨_, k, Control, _, machine, hmachine⟩ := h
  have hmap : (output result, s') ∈
      (ProbOracleComp.runWith oracle (output <$> program a) s).support := by
    rw [ProbOracleComp.runWith_map]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(result, s'), hresult, rfl⟩
  rw [(hmachine a State oracle s).1] at hmap
  exact machine.length_output_runOracle_le oracle (t a) (input a) (output result) s s' hmap

/-- Instrumenting the private oracle state with a transcript shows that `program a` makes at most
`t a` external queries on every path, each of payload length at most `t a`. -/
theorem query_bounds (h : ComputesOracleInTimeOn input output t program) (a : α) :
    (program a).IsQueryBounded (t a) ∧
      (program a).QueriesSatisfy fun request => request.2.length ≤ t a := by
  obtain ⟨_, k, Control, _, machine, hmachine⟩ := h
  obtain ⟨hcalls, hsize⟩ := machine.query_bounds_runOracle (t a) (input a)
  have hrun (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool))
      (s s' : State) (result : List Bool)
      (transcript : OracleComp.Transcript (fun _ : Operation × List Bool => List Bool))
      (hmem : (result, s', transcript) ∈ (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
        (output <$> program a) (s, [])).support) :
      transcript.length ≤ t a ∧ ∀ entry ∈ transcript, entry.1.2.length ≤ t a := by
    rw [(hmachine a (State × OracleComp.Transcript (fun _ : Operation × List Bool => List Bool))
      (OracleComp.withTranscript oracle) (s, [])).1] at hmem
    exact ⟨hcalls.length_transcript_le oracle hmem, hsize.forall_mem_transcript oracle hmem⟩
  have hcalls' : ProbOracleComp.IsQueryBounded (output <$> program a) (t a) :=
    ProbOracleComp.isQueryBounded_of_length_transcript_le fun State oracle s s' result
      transcript hmem => (hrun State oracle s s' result transcript hmem).1
  have hsize' : ProbOracleComp.QueriesSatisfy
      (fun request => request.2.length ≤ t a) (output <$> program a) :=
    ProbOracleComp.queriesSatisfy_of_forall_mem_transcript fun State oracle s s' result
      transcript hmem => (hrun State oracle s s' result transcript hmem).2
  exact ⟨(OracleComp.isCostBounded_map_iff _ _ _).mp hcalls',
    (OracleComp.queriesSatisfy_map_iff _ _).mp hsize'⟩

/-- Every execution path of `program a` makes at most `t a` external queries. -/
theorem isQueryBounded (h : ComputesOracleInTimeOn input output t program) (a : α) :
    (program a).IsQueryBounded (t a) :=
  (h.query_bounds a).1

/-- Every external query issued by `program a` has payload length at most `t a`. -/
theorem queriesSatisfy_length_le (h : ComputesOracleInTimeOn input output t program) (a : α) :
    (program a).QueriesSatisfy fun request => request.2.length ≤ t a :=
  (h.query_bounds a).2

/-- A step-`t` oracle realization automatically satisfies the `(t, t)` time-and-query bound. -/
theorem computesOracleInTimeAndQueriesOn (h : ComputesOracleInTimeOn input output t program) :
    ComputesOracleInTimeAndQueriesOn input output t t program :=
  ⟨h, h.isQueryBounded⟩

/-- Sampling one private fair bit takes `1` step and leaves every external oracle untouched. -/
theorem uniform_bool [Finite Operation] (input : α ↪ List Bool) :
    ComputesOracleInTimeOn (Operation := Operation) input encBool (fun _ => 1)
      (fun _ => ProbOracleComp.sample (ProbComp.uniform Bool)) :=
  of_computesTidily coinMachine fun a => computesTidily_coinMachine (input a)

/-- One bounded-prefix external query `(op, q)` reading at most `limit` reply bits runs in
`4 * q.length + 2 * limit + 6` steps. -/
theorem query_take_pair [Finite Operation] (op : Operation) :
    ComputesOracleInTimeOn (encPair encBits encUnary) encBits
      (fun request : List Bool × ℕ => 4 * request.1.length + 2 * request.2 + 6)
      (fun request => List.take request.2 <$>
        ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool)
          (op, request.1)) :=
  of_computesTidily (queryTakePTM op) fun request =>
    (computesTidily_queryTakePTM op request.1 request.2).congr fun _ _ _ => by
      simp only [encBits, Function.Embedding.coe_refl, id_map]

/-- Sequence a closed halting probabilistic computation `ProbOracleComp.sample (first a)` before
any halting oracle continuation `second`, in `2 * t₁ a + t₂' a + 4` steps. -/
theorem bind_sample_left {first : α → ProbComp β} {second : β → WordOracleComp Operation γ}
    {t₂ : β → ℕ} {t₂' : α → ℕ}
    (hfirst : ComputesInTimeOn input middle t₁ first)
    (hsecond : ComputesOracleInTimeOn middle output t₂ second)
    (ht₂ : ∀ a b, b ∈ (ProbComp.eval (first a)).support → t₂ b ≤ t₂' a) :
    ComputesOracleInTimeOn input output (fun a => 2 * t₁ a + t₂' a + 4)
      (fun a => do
        let b ← ProbOracleComp.sample (first a)
        second b) := by
  obtain ⟨k₁, State₁, hfin₁, m₁, hm₁⟩ := hfirst
  obtain ⟨hops, k₂, State₂, hfin₂, m₂, hm₂⟩ := hsecond
  refine ⟨hops, k₂ + k₁ + 2, _, inferInstance,
    oComp m₂ (ofClosed (Operation := Operation) m₁) true, fun a State oracle s => ?_⟩
  obtain ⟨hout₁, hhalt₁⟩ := hm₁ a
  have hfirst_run : ProbOracleComp.runWith oracle
      ((ofClosed (Operation := Operation) m₁).runOracleConfigFrom (t₁ a)
        ((ofClosed (Operation := Operation) m₁).initialConfig (input a))) s =
      (ProbComp.eval (m₁.runClosedConfigFrom (t₁ a) (m₁.initialConfig (input a)))).map
        (fun final => ({ tapes := final.tapes, channels := fun _ => {} }, s)) :=
    runWith_runOracleConfigFrom_ofClosed m₁ oracle (t₁ a) (fun _ => {})
      (m₁.initialConfig (input a)) s
  have hhalt₁_open : ∀ final ∈ (ProbOracleComp.runWith oracle
      ((ofClosed (Operation := Operation) m₁).runOracleConfigFrom (t₁ a)
        ((ofClosed (Operation := Operation) m₁).initialConfig (input a))) s).support,
      final.1.tapes.state = none := by
    rw [hfirst_run]
    intro final hfinal
    obtain ⟨cfg, hcfg, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hhalt₁ cfg hcfg
  have hmem_word : ∀ cfg ∈ (ProbComp.eval
      (m₁.runClosedConfigFrom (t₁ a) (m₁.initialConfig (input a)))).support,
      ∃ b ∈ (ProbComp.eval (first a)).support, middle b = cfg.tapes.output := by
    intro cfg hcfg
    have hout_mem : cfg.tapes.output ∈ (ProbComp.eval (m₁.runClosed (t₁ a) (input a))).support := by
      rw [runClosed_eq_map, ProbComp.eval_map]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨cfg, hcfg, rfl⟩
    rw [← hout₁] at hout_mem
    exact (PMF.mem_support_map_iff _ _ _).mp hout_mem
  have hhalt₂_word : ∀ word (b : β), b ∈ (ProbComp.eval (first a)).support →
      middle b = word →
      ∀ final ∈ (ProbOracleComp.runWith oracle
        (m₂.runOracleConfigFrom (t₂' a) (m₂.initialConfig word)) s).support,
        final.1.tapes.state = none := by
    rintro _ b hb rfl final hfinal
    rw [run_interpret_runOracleConfigFrom_eq_of_halted m₂ oracle
      (m₂.initialConfig (middle b)) (ht₂ a b hb) s (hm₂ b State oracle s).2] at hfinal
    exact (hm₂ b State oracle s).2 final hfinal
  have hhalt₂_open : ∀ result ∈ (ProbOracleComp.runWith oracle
      ((ofClosed (Operation := Operation) m₁).runOracleConfigFrom (t₁ a)
        ((ofClosed (Operation := Operation) m₁).initialConfig (input a))) s).support,
      ∀ final ∈ (ProbOracleComp.runWith oracle
        (m₂.runOracleConfigFrom (t₂' a)
          { tapes := Cfg.init m₂.initial result.1.tapes.output,
            channels := result.1.channels }) result.2).support,
        final.1.tapes.state = none := by
    intro result hresult final hfinal
    rw [hfirst_run] at hresult
    obtain ⟨cfg, hcfg, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    obtain ⟨b, hb, hmid⟩ := hmem_word cfg hcfg
    exact hhalt₂_word cfg.tapes.output b hb hmid final hfinal
  have hstep : 2 * t₁ a + t₂' a + 4 = t₁ a + (t₁ a + 4 + t₂' a) := by omega
  dsimp only
  rw [hstep]
  have hcomp := runWith_oComp (ofClosed (Operation := Operation) m₁) m₂ oracle true
    (input a) (t₁ a) (t₂' a) s hhalt₁_open hhalt₂_open
  refine ⟨?_, ?_⟩
  · have hout := congrArg (PMF.map (Prod.map (fun final => final.tapes.output) id)) hcomp
    conv_rhs => rw [runOracle_eq_map, ProbOracleComp.runWith_map]
    refine Eq.trans ?_ hout.symm
    rw [hfirst_run, PMF.map_bind, PMF.bind_map, map_bind, ProbOracleComp.runWith_bind]
    simp only [ProbOracleComp.runWith_sample, PMF.bind_map]
    have hlaw_word : ∀ (cfg : Config k₁ Bool State₁ Empty (input a)) (b : β),
        b ∈ (ProbComp.eval (first a)).support → middle b = cfg.tapes.output →
        PMF.map (Prod.map
            (fun final : Config (k₂ + k₁ + 2) Bool
                (State₁ ⊕ ((MarkWorkState ⊕ RewindWorkState) ⊕ State₂)) Operation (input a) =>
              final.tapes.output) id)
          (PMF.map (fun (cfg₁, s₂) =>
            (Sequential.right (State₀ := State₁)
              (Sequential.right (State₀ := MarkWorkState ⊕ RewindWorkState)
                (oConsumerConfig true
                  ({ tapes := cfg.tapes, channels := fun _ => {} } :
                    Config k₁ Bool State₁ Operation (input a)) cfg₁)), s₂))
            (ProbOracleComp.runWith oracle
              (m₂.runOracleConfigFrom (t₂' a) (m₂.initialConfig cfg.tapes.output)) s)) =
        ProbOracleComp.runWith oracle (output <$> second b) s := by
      intro cfg b hb hmid
      rw [PMF.map_comp]
      trans PMF.map (Prod.map (fun cfg₁ => cfg₁.tapes.output) id)
        (ProbOracleComp.runWith oracle
          (m₂.runOracleConfigFrom (t₂' a) (m₂.initialConfig cfg.tapes.output)) s)
      · congr 1
      · rw [← ProbOracleComp.runWith_map, ← runOracle_eq_map]
        have hpad : ∀ word, middle b = word →
            ProbOracleComp.runWith oracle (m₂.runOracle (t₂' a) word) s =
              ProbOracleComp.runWith oracle (output <$> second b) s := by
          rintro _ rfl
          rw [runOracle_eq_map, ProbOracleComp.runWith_map,
            run_interpret_runOracleConfigFrom_eq_of_halted m₂ oracle
              (m₂.initialConfig (middle b)) (ht₂ a b hb) s (hm₂ b State oracle s).2,
            ← ProbOracleComp.runWith_map, ← runOracle_eq_map, (hm₂ b State oracle s).1]
        exact hpad cfg.tapes.output hmid
    classical
    let cont (word : List Bool) : PMF (List Bool × State) :=
      if h : ∃ b, middle b = word then
        ProbOracleComp.runWith oracle (output <$> second (Classical.choose h)) s
      else PMF.pure ([], s)
    have hcont (b : β) :
        cont (middle b) = ProbOracleComp.runWith oracle (output <$> second b) s := by
      have hex : ∃ b', middle b' = middle b := ⟨b, rfl⟩
      have hchoose : Classical.choose hex = b := middle.injective (Classical.choose_spec hex)
      simp only [cont, hex, ↓reduceDIte, hchoose]
    calc (ProbComp.eval (first a)).bind
          ((fun bs => ProbOracleComp.runWith oracle (output <$> second bs.1) bs.2) ∘
            fun x => (x, s))
        = (ProbComp.eval (first a)).bind (fun b => cont (middle b)) := by
          refine PMF.bind_congr_on_support _ _ _ fun b _ => ?_
          simp only [Function.comp_apply, hcont]
      _ = ((ProbComp.eval (first a)).map middle).bind cont := by
          rw [PMF.bind_map]; rfl
      _ = (ProbComp.eval (m₁.runClosed (t₁ a) (input a))).bind cont := by rw [hout₁]
      _ = (ProbComp.eval (m₁.runClosedConfigFrom (t₁ a) (m₁.initialConfig (input a)))).bind
            (fun cfg => cont cfg.tapes.output) := by
          rw [runClosed_eq_map, ProbComp.eval_map, PMF.bind_map]
          rfl
      _ = _ := by
          refine PMF.bind_congr_on_support _ _ _ fun cfg hcfg => ?_
          obtain ⟨b, hb, hmid⟩ := hmem_word cfg hcfg
          rw [← hmid, hcont b]
          exact (hlaw_word cfg b hb hmid).symm
  · intro final hfinal
    rw [hcomp] at hfinal
    obtain ⟨⟨cfg₀, s₁⟩, hcfg₀, htarget⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    obtain ⟨⟨cfg₁, s₂⟩, hcfg₁, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp htarget
    change (cfg₁.tapes.state.map Sum.inr).map Sum.inr = none
    rw [hhalt₂_open (cfg₀, s₁) hcfg₀ (cfg₁, s₂) hcfg₁]
    rfl

/-- Sequence a halting oracle computation `first a` before a closed halting continuation
`ProbOracleComp.sample (second b)`, in `2 * t₁ a + t₂' a + 4` steps. -/
theorem bind_sample_right {first : α → WordOracleComp Operation β} {second : β → ProbComp γ}
    {t₂ : β → ℕ} {t₂' : α → ℕ}
    (hfirst : ComputesOracleInTimeOn input middle t₁ first)
    (hsecond : ComputesInTimeOn middle output t₂ second)
    (ht₂ : ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool))
      s s' b, (b, s') ∈ (ProbOracleComp.runWith oracle (first a) s).support → t₂ b ≤ t₂' a) :
    ComputesOracleInTimeOn input output (fun a => 2 * t₁ a + t₂' a + 4)
      (fun a => do
        let b ← first a
        ProbOracleComp.sample (second b)) := by
  obtain ⟨hops, k₁, State₁, hfin₁, m₁, hm₁⟩ := hfirst
  obtain ⟨k₂, State₂, hfin₂, m₂, hm₂⟩ := hsecond
  refine ⟨hops, k₂ + k₁ + 2, _, inferInstance,
    oComp (ofClosed (Operation := Operation) m₂) m₁ true, fun a State oracle s => ?_⟩
  obtain ⟨hlaw₁, hhalt₁⟩ := hm₁ a State oracle s
  have hmem_word : ∀ cfg₀ s₁,
      (cfg₀, s₁) ∈ (ProbOracleComp.runWith oracle
        (m₁.runOracleConfigFrom (t₁ a) (m₁.initialConfig (input a))) s).support →
      ∃ b, (b, s₁) ∈ (ProbOracleComp.runWith oracle (first a) s).support ∧
        middle b = cfg₀.tapes.output := by
    intro cfg₀ s₁ hcfg₀
    have hout_mem : (cfg₀.tapes.output, s₁) ∈
        (ProbOracleComp.runWith oracle (m₁.runOracle (t₁ a) (input a)) s).support := by
      rw [runOracle_eq_map, ProbOracleComp.runWith_map]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(cfg₀, s₁), hcfg₀, rfl⟩
    rw [← hlaw₁, ProbOracleComp.runWith_map] at hout_mem
    obtain ⟨⟨b, s₁'⟩, hb, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hout_mem
    rcases Prod.mk.inj heq with ⟨hmid, rfl⟩
    exact ⟨b, hb, hmid⟩
  have hhalt₂_word : ∀ word (b : β) (s₁ : State),
      (b, s₁) ∈ (ProbOracleComp.runWith oracle (first a) s).support →
      middle b = word →
      ∀ cfg₁ ∈ (ProbComp.eval (m₂.runClosedConfigFrom (t₂' a) (m₂.initialConfig word))).support,
        cfg₁.tapes.state = none := by
    rintro _ b s₁ hb rfl cfg₁ hcfg₁
    rw [m₂.eval_runClosedConfigFrom_eq_of_halted _
      (ht₂ a State oracle s s₁ b hb) (hm₂ b).2] at hcfg₁
    exact (hm₂ b).2 cfg₁ hcfg₁
  have hhalt₂_open : ∀ result ∈ (ProbOracleComp.runWith oracle
      (m₁.runOracleConfigFrom (t₁ a) (m₁.initialConfig (input a))) s).support,
      ∀ final ∈ (ProbOracleComp.runWith oracle
        ((ofClosed (Operation := Operation) m₂).runOracleConfigFrom (t₂' a)
          { tapes := Cfg.init (ofClosed (Operation := Operation) m₂).initial result.1.tapes.output,
            channels := result.1.channels }) result.2).support,
        final.1.tapes.state = none := by
    rintro ⟨cfg₀, s₁⟩ hcfg₀ final hfinal
    obtain ⟨b, hb, hmid⟩ := hmem_word cfg₀ s₁ hcfg₀
    change final ∈ (ProbOracleComp.runWith oracle
      ((ofClosed (Operation := Operation) m₂).runOracleConfigFrom (t₂' a)
        { tapes := (m₂.initialConfig cfg₀.tapes.output).tapes,
          channels := cfg₀.channels }) s₁).support at hfinal
    rw [runWith_runOracleConfigFrom_ofClosed] at hfinal
    obtain ⟨cfg₁, hcfg₁, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hhalt₂_word cfg₀.tapes.output b s₁ hb hmid cfg₁ hcfg₁
  have hstep : 2 * t₁ a + t₂' a + 4 = t₁ a + (t₁ a + 4 + t₂' a) := by omega
  dsimp only
  rw [hstep]
  have hcomp := runWith_oComp m₁ (ofClosed (Operation := Operation) m₂) oracle true
    (input a) (t₁ a) (t₂' a) s hhalt₁ hhalt₂_open
  refine ⟨?_, ?_⟩
  · have hout := congrArg (PMF.map (Prod.map (fun final => final.tapes.output) id)) hcomp
    conv_rhs => rw [runOracle_eq_map, ProbOracleComp.runWith_map]
    refine Eq.trans ?_ hout.symm
    rw [PMF.map_bind, map_bind, ProbOracleComp.runWith_bind]
    classical
    let cont (p : List Bool × State) : PMF (List Bool × State) :=
      if h : ∃ b, middle b = p.1 then
        ((ProbComp.eval (second (Classical.choose h))).map output).map (fun w => (w, p.2))
      else PMF.pure ([], p.2)
    have hcont (b : β) (s₁ : State) :
        cont (middle b, s₁) = ((ProbComp.eval (second b)).map output).map (fun w => (w, s₁)) := by
      have hex : ∃ b', middle b' = middle b := ⟨b, rfl⟩
      have hchoose : Classical.choose hex = b := middle.injective (Classical.choose_spec hex)
      simp only [cont, hex, ↓reduceDIte, hchoose]
    calc (ProbOracleComp.runWith oracle (first a) s).bind
          (fun bs => ProbOracleComp.runWith oracle
            (output <$> ProbOracleComp.sample (second bs.1)) bs.2)
        = (ProbOracleComp.runWith oracle (first a) s).bind
            (fun bs => cont (middle bs.1, bs.2)) := by
          refine PMF.bind_congr_on_support _ _ _ fun ⟨b, s₁⟩ _ => ?_
          rw [hcont, ← ProbOracleComp.sample_map, ProbOracleComp.runWith_sample, ProbComp.eval_map]
      _ = ((ProbOracleComp.runWith oracle (first a) s).map
            (fun bs => (middle bs.1, bs.2))).bind cont := by
          rw [PMF.bind_map]; rfl
      _ = (ProbOracleComp.runWith oracle (middle <$> first a) s).bind cont := by
          rw [ProbOracleComp.runWith_map]; rfl
      _ = (ProbOracleComp.runWith oracle (m₁.runOracle (t₁ a) (input a)) s).bind cont := by
          rw [hlaw₁]
      _ = (ProbOracleComp.runWith oracle
            (m₁.runOracleConfigFrom (t₁ a) (m₁.initialConfig (input a))) s).bind
            (fun r => cont (r.1.tapes.output, r.2)) := by
          rw [runOracle_eq_map, ProbOracleComp.runWith_map, PMF.bind_map]
          rfl
      _ = _ := by
          refine PMF.bind_congr_on_support _ _ _ fun ⟨cfg₀, s₁⟩ hcfg₀ => ?_
          obtain ⟨b, hb, hmid⟩ := hmem_word cfg₀ s₁ hcfg₀
          dsimp only [Function.comp_def]
          change cont (cfg₀.tapes.output, s₁) =
            PMF.map (Prod.map
                (fun final : Config (k₂ + k₁ + 2) Bool
                    (State₁ ⊕ ((MarkWorkState ⊕ RewindWorkState) ⊕ State₂)) Operation (input a) =>
                  final.tapes.output) id)
              (PMF.map _ (ProbOracleComp.runWith oracle
                ((ofClosed (Operation := Operation) m₂).runOracleConfigFrom (t₂' a)
                  { tapes := (m₂.initialConfig cfg₀.tapes.output).tapes,
                    channels := cfg₀.channels }) s₁))
          rw [runWith_runOracleConfigFrom_ofClosed, PMF.map_comp, PMF.map_comp]
          have hproj : ((Prod.map
              (fun final : Config (k₂ + k₁ + 2) Bool
                  (State₁ ⊕ ((MarkWorkState ⊕ RewindWorkState) ⊕ State₂)) Operation (input a) =>
                final.tapes.output) id ∘
              fun x =>
                (Sequential.right (State₀ := State₁)
                  (Sequential.right (State₀ := MarkWorkState ⊕ RewindWorkState)
                    (oConsumerConfig true cfg₀ x.1)), x.2)) ∘
              fun final : Config k₂ Bool State₂ Empty cfg₀.tapes.output =>
                (({ tapes := final.tapes, channels := cfg₀.channels } :
                  Config k₂ Bool State₂ Operation cfg₀.tapes.output), s₁)) =
              fun final => (final.tapes.output, s₁) := rfl
          rw [hproj]
          change cont (cfg₀.tapes.output, s₁) =
            PMF.map ((fun w => (w, s₁)) ∘
              fun final : Config k₂ Bool State₂ Empty cfg₀.tapes.output => final.tapes.output)
              (ProbComp.eval (m₂.runClosedConfigFrom (t₂' a) (m₂.initialConfig cfg₀.tapes.output)))
          rw [← PMF.map_comp, ← ProbComp.eval_map, ← runClosed_eq_map]
          have hpad : ∀ word, middle b = word →
              cont (word, s₁) =
                (ProbComp.eval (m₂.runClosed (t₂' a) word)).map (fun w => (w, s₁)) := by
            rintro _ rfl
            rw [hcont, m₂.eval_runClosed_eq_of_halted _ (ht₂ a State oracle s s₁ b hb) (hm₂ b).2,
              (hm₂ b).1]
          exact hpad cfg₀.tapes.output hmid
  · intro final hfinal
    rw [hcomp] at hfinal
    obtain ⟨⟨cfg₀, s₁⟩, hcfg₀, htarget⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfinal
    obtain ⟨⟨cfg₁, s₂⟩, hcfg₁, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp htarget
    change (cfg₁.tapes.state.map Sum.inr).map Sum.inr = none
    rw [hhalt₂_open (cfg₀, s₁) hcfg₀ (cfg₁, s₂) hcfg₁]
    rfl

/-- A polynomially bounded halting oracle schedule gives a strict `IsOraclePPTOn` certificate. -/
theorem isOraclePPTOn (ht : PolyBounded (fun a => (input a).length) t)
    (h : ComputesOracleInTimeOn input output t program) :
    IsOraclePPTOn input output program := by
  obtain ⟨c, d, hle⟩ := ht.exists_le
  obtain ⟨hops, k, Control, hfinite, machine, hmachine⟩ := h.mono hle
  exact ⟨hops, k, Control, hfinite, machine, c, d,
    fun a State oracle s => (hmachine a State oracle s).1⟩

end ComputesOracleInTimeOn

/-- A program returning its declared encoding has the same explicit-time halting oracle
certificates. -/
theorem computesOracleInTimeOn_iff_encoded {Operation α β : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {output : β ↪ List Bool} {t : α → ℕ}
    {program : α → WordOracleComp Operation β} :
    ComputesOracleInTimeOn input output t program ↔
      ComputesOracleInTimeOn input encBits t (fun a => output <$> program a) := by
  simp only [ComputesOracleInTimeOn, encBits, Function.Embedding.coe_refl, id_map]

/-- Lift a closed halting realization to an open oracle realization via `ProbOracleComp.sample`,
preserving the exact step schedule `t`. -/
theorem ComputesInTimeOn.computesOracleInTimeOn {Operation α β : Type} [DecidableEq Operation]
    [Finite Operation] {input : α ↪ List Bool} {output : β ↪ List Bool} {t : α → ℕ}
    {program : α → ProbComp β} (h : ComputesInTimeOn input output t program) :
    ComputesOracleInTimeOn (Operation := Operation) input output t
      (fun a => ProbOracleComp.sample (program a)) := by
  obtain ⟨k, State, hfinite, machine, hmachine⟩ := h
  refine ⟨inferInstance, k, State, hfinite, ofClosed machine, fun a OracleState oracle s => ?_⟩
  obtain ⟨hout, hhalt⟩ := hmachine a
  refine ⟨?_, ?_⟩
  · rw [run_interpret_runOracle_ofClosed, ← hout, ← ProbOracleComp.sample_map,
      ProbOracleComp.runWith_sample, ProbComp.eval_map]
  · intro final hfinal
    change final ∈ (ProbOracleComp.runWith oracle
      ((ofClosed (Operation := Operation) machine).runOracleConfigFrom (t a)
        { tapes := (machine.initialConfig (input a)).tapes, channels := fun _ => {} })
      s).support at hfinal
    rw [runWith_runOracleConfigFrom_ofClosed] at hfinal
    obtain ⟨cfg, hcfg, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hhalt cfg hcfg

/-- A sampled closed program certified without external channels (`Operation := Empty`) is a closed
halting realization with the exact same step schedule `t`. -/
theorem ComputesOracleInTimeOn.computesInTimeOn {α β : Type}
    {input : α ↪ List Bool} {output : β ↪ List Bool} {t : α → ℕ}
    {program : α → ProbComp β}
    (h : ComputesOracleInTimeOn (Operation := Empty) input output t
      (fun a => ProbOracleComp.sample (program a))) :
    ComputesInTimeOn input output t program := by
  obtain ⟨_, k, Control, hfinite, machine, hmachine⟩ := h
  refine ⟨k, Control, hfinite, machine, fun a => ?_⟩
  obtain ⟨hlaw, hhalt⟩ := hmachine a Unit (fun q => q.1.elim) ()
  refine ⟨?_, ?_⟩
  · have hout := congrArg (PMF.map Prod.fst) hlaw
    rw [← ProbOracleComp.sample_map, ProbOracleComp.runWith_sample,
      runOracle_eq_sample_runClosed, ProbOracleComp.runWith_sample,
      PMF.map_comp, PMF.map_comp, ProbComp.eval_map] at hout
    have hid : (Prod.fst ∘ fun word : List Bool => (word, ())) = id := rfl
    rwa [hid, PMF.map_id, PMF.map_id] at hout
  · intro final hfinal
    have heq : machine.runOracleConfigFrom (t a) (machine.initialConfig (input a)) =
        ProbOracleComp.sample
          (machine.runClosedConfigFrom (t a) (machine.initialConfig (input a))) := by
      simp only [runOracleConfigFrom, runClosedConfigFrom, MultiTapePTM.runConfigFrom,
        ProbOracleComp.sample, MultiTapeMachine.interpret_runConfigFrom]
      congr 1
      funext oracle
      exact oracle.elim
    apply hhalt (final, ())
    rw [heq, ProbOracleComp.runWith_sample]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, hfinal, rfl⟩

end Cslib.Probability

/-- Lift a plain deterministic time-and-space computation to a halting oracle realization with the
exact same step bound `t`. -/
theorem Turing.MultiTapeTM.ComputableInTimeAndSpace.computesOracleInTimeOn
    {Operation α β : Type} [DecidableEq Operation] [Finite Operation]
    {input : α ↪ List Bool} {output : β ↪ List Bool} {f : α → β} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f input output t s) :
    Cslib.Probability.ComputesOracleInTimeOn (Operation := Operation) input output t
      (fun a => pure (f a)) :=
  (h.computesInTimeOn.computesOracleInTimeOn (Operation := Operation)).congr
    fun _ _ _ _ => by simp

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeTM

/-- Deterministically prepare the input of a halting oracle program in
`2 * tf a + tp (prepare a) + 4` steps. -/
theorem ComputesOracleInTimeOn.preprocess {Operation α β γ : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
    {tp : β → ℕ} {tf sf : α → ℕ} {program : β → WordOracleComp Operation γ} {prepare : α → β}
    (hprogram : ComputesOracleInTimeOn middle output tp program)
    (hprepare : ComputableInTimeAndSpace prepare input middle tf sf) :
    ComputesOracleInTimeOn input output (fun a => 2 * tf a + tp (prepare a) + 4)
      (fun a => program (prepare a)) := by
  refine (hprogram.bind_sample_left hprepare.computesInTimeOn ?_).congr fun _ _ _ _ => by simp
  intro a b hb
  rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hb
  rw [hb]

/-- Deterministically postprocess every result of a halting oracle program in
`2 * tp a + tf' a + 4` steps. -/
theorem ComputesOracleInTimeOn.map {Operation α β γ : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
    {tp tf' : α → ℕ} {tf sf : β → ℕ} {program : α → WordOracleComp Operation β} {f : β → γ}
    (hprogram : ComputesOracleInTimeOn input middle tp program)
    (hf : ComputableInTimeAndSpace f middle output tf sf)
    (htf : ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool))
      s s' b, (b, s') ∈ (ProbOracleComp.runWith oracle (program a) s).support → tf b ≤ tf' a) :
    ComputesOracleInTimeOn input output (fun a => 2 * tp a + tf' a + 4)
      (fun a => f <$> program a) := by
  refine (hprogram.bind_sample_right hf.computesInTimeOn htf).congr fun _ _ _ _ => ?_
  simp

/-- Postprocess a halting oracle program with a deterministic length-indexed bound under a monotone
step function, using `hprogram.length_le` to bound intermediate encoded words by `tp a`. -/
theorem ComputesOracleInTimeOn.map_ofLength {Operation α β γ : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
    {tp : α → ℕ} {tf sf : ℕ → ℕ} {program : α → WordOracleComp Operation β} {f : β → γ}
    (hprogram : ComputesOracleInTimeOn input middle tp program)
    (hf : ComputableInTimeAndSpaceOfLength f middle output tf sf)
    (hmono : Monotone tf) :
    ComputesOracleInTimeOn input output (fun a => 2 * tp a + tf (tp a) + 4)
      (fun a => f <$> program a) :=
  hprogram.map hf fun a _ oracle s s' _ hb => hmono (hprogram.length_le a oracle s s' hb)

/-- Issue one bounded-prefix external query `(op, request a)` reading at most `limit a` reply bits,
given a plain deterministic computation preparing `(request a, limit a)`. -/
theorem ComputesOracleInTimeOn.query_take {Operation α : Type} [DecidableEq Operation]
    [Finite Operation] (op : Operation) {input : α ↪ List Bool}
    {request : α → List Bool} {limit : α → ℕ} {tf sf : α → ℕ}
    (hprepare : ComputableInTimeAndSpace (fun a => (request a, limit a))
      input (encPair encBits encUnary) tf sf) :
    ComputesOracleInTimeOn input encBits
      (fun a => 2 * tf a + (4 * (request a).length + 2 * limit a + 6) + 4)
      (fun a => List.take (limit a) <$>
        ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool)
          (op, request a)) :=
  (ComputesOracleInTimeOn.query_take_pair op).preprocess hprepare

/-- **Uniform strict oracle PPT is equivalent to halting oracle realization under a polynomially
bounded step schedule.** The forward direction normalizes any `IsOraclePPTOn` witness via
`IsOraclePPTOn.isTidyOraclePPTOn`; the backward direction pads via `ComputesOracleInTimeOn.mono`. -/
theorem isOraclePPTOn_iff_exists_polyBounded_computesOracleInTimeOn
    {Operation α β : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {output : β ↪ List Bool}
    {program : α → WordOracleComp Operation β} :
    IsOraclePPTOn input output program ↔
      ∃ t, PolyBounded (fun a => (input a).length) t ∧
        ComputesOracleInTimeOn input output t program := by
  constructor
  · intro h
    obtain ⟨hops, k, Control, hfinite, machine, c, d, htidy⟩ := h.isTidyOraclePPTOn
    exact ⟨fun a => c * ((input a).length + 1) ^ d,
      PolyBounded.of_forall_le c d (fun _ => le_rfl),
      @of_computesTidily Operation α β _ hops input output _ program
        k Control hfinite machine htidy⟩
  · rintro ⟨t, ht, hcomp⟩
    exact hcomp.isOraclePPTOn ht

/-! ### Joint `(t, q)` properties and parameterized API -/

namespace ComputesOracleInTimeAndQueriesOn

variable {Operation α β γ : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
  {t t₁ t₂ q q₁ q₂ : α → ℕ} {program program' : α → WordOracleComp Operation γ}

/-- Monotonicity in both the step schedule and the query budget. -/
theorem mono (h : ComputesOracleInTimeAndQueriesOn input output t₁ q₁ program)
    (ht : ∀ a, t₁ a ≤ t₂ a) (hq : ∀ a, q₁ a ≤ q₂ a) :
    ComputesOracleInTimeAndQueriesOn input output t₂ q₂ program :=
  ⟨h.1.mono ht, fun a => (h.2 a).mono (hq a)⟩

/-- Deterministic preprocessing updates the step bound while preserving the query budget. -/
theorem preprocess {tp qp : β → ℕ} {tf sf : α → ℕ}
    {program : β → WordOracleComp Operation γ} {prepare : α → β}
    (hprogram : ComputesOracleInTimeAndQueriesOn middle output tp qp program)
    (hprepare : ComputableInTimeAndSpace prepare input middle tf sf) :
    ComputesOracleInTimeAndQueriesOn input output
      (fun a => 2 * tf a + tp (prepare a) + 4) (fun a => qp (prepare a))
      (fun a => program (prepare a)) :=
  ⟨hprogram.1.preprocess hprepare, fun a => hprogram.2 (prepare a)⟩

/-- Deterministic postprocessing updates the step bound while preserving the query budget `q a`. -/
theorem map {tp qp tf' : α → ℕ} {tf sf : β → ℕ}
    {program : α → WordOracleComp Operation β} {f : β → γ}
    (hprogram : ComputesOracleInTimeAndQueriesOn input middle tp qp program)
    (hf : ComputableInTimeAndSpace f middle output tf sf)
    (htf : ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool))
      s s' b, (b, s') ∈ (ProbOracleComp.runWith oracle (program a) s).support → tf b ≤ tf' a) :
    ComputesOracleInTimeAndQueriesOn input output (fun a => 2 * tp a + tf' a + 4) qp
      (fun a => f <$> program a) :=
  ⟨hprogram.1.map hf htf, fun a => (OracleComp.isCostBounded_map_iff _ _ _).mpr (hprogram.2 a)⟩

/-- Closed private sampling followed by an oracle continuation preserves the continuation's query
budget bound `q₂' a`. -/
theorem bind_sample_left {first : α → ProbComp β} {second : β → WordOracleComp Operation γ}
    {t₂ q₂ : β → ℕ} {t₂' q₂' : α → ℕ}
    (hfirst : ComputesInTimeOn input middle t₁ first)
    (hsecond : ComputesOracleInTimeAndQueriesOn middle output t₂ q₂ second)
    (ht₂ : ∀ a b, b ∈ (ProbComp.eval (first a)).support → t₂ b ≤ t₂' a)
    (hq₂ : ∀ a b, q₂ b ≤ q₂' a) :
    ComputesOracleInTimeAndQueriesOn input output (fun a => 2 * t₁ a + t₂' a + 4) q₂'
      (fun a => do
        let b ← ProbOracleComp.sample (first a)
        second b) := by
  refine ⟨hsecond.1.bind_sample_left hfirst ht₂, fun a => ?_⟩
  simpa using (ProbOracleComp.IsQueryBounded.sample (first a)).bind
    fun b => (hsecond.2 b).mono (hq₂ a b)

/-- An oracle computation followed by closed private postprocessing preserves the oracle
computation's query budget `q₁ a`. -/
theorem bind_sample_right {first : α → WordOracleComp Operation β} {second : β → ProbComp γ}
    {t₂ : β → ℕ} {t₂' : α → ℕ}
    (hfirst : ComputesOracleInTimeAndQueriesOn input middle t₁ q₁ first)
    (hsecond : ComputesInTimeOn middle output t₂ second)
    (ht₂ : ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool))
      s s' b, (b, s') ∈ (ProbOracleComp.runWith oracle (first a) s).support → t₂ b ≤ t₂' a) :
    ComputesOracleInTimeAndQueriesOn input output (fun a => 2 * t₁ a + t₂' a + 4) q₁
      (fun a => do
        let b ← first a
        ProbOracleComp.sample (second b)) := by
  refine ⟨hfirst.1.bind_sample_right hsecond ht₂, fun a => ?_⟩
  simpa using (hfirst.2 a).bind fun b => ProbOracleComp.IsQueryBounded.sample (second b)

end ComputesOracleInTimeAndQueriesOn

namespace ComputesOracleInTime

variable {Operation β : Type} [DecidableEq Operation] {output : β ↪ List Bool}
  {t t₁ t₂ : ℕ → ℕ → ℕ} {program program' : ℕ → List Bool → WordOracleComp Operation β}

/-- Expose the underlying `ComputesOracleInTimeOn` certificate on `encPair encUnary encBits`. -/
theorem on (h : ComputesOracleInTime output t program) :
    ComputesOracleInTimeOn (encPair encUnary encBits) output
      (fun input => t input.1 input.2.length) (fun input => program input.1 input.2) := h

/-- Enlarging a parameterized step schedule preserves halting oracle realization unconditionally. -/
theorem mono (h : ComputesOracleInTime output t₁ program) (hle : ∀ n m, t₁ n m ≤ t₂ n m) :
    ComputesOracleInTime output t₂ program :=
  h.on.mono fun input => hle input.1 input.2.length

/-- Equality of the complete joint output/state semantics preserves parameterized halting
realization. -/
theorem congr (h : ComputesOracleInTime output t program)
    (heq : ∀ n aux (State : Type)
      (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (program n aux) s =
        ProbOracleComp.runWith oracle (program' n aux) s) :
    ComputesOracleInTime output t program' :=
  h.on.congr fun input => heq input.1 input.2

/-- Every execution path of `program n aux` makes at most `t n aux.length` external queries. -/
theorem isQueryBounded (h : ComputesOracleInTime output t program) (n : ℕ) (aux : List Bool) :
    (program n aux).IsQueryBounded (t n aux.length) :=
  h.on.isQueryBounded (n, aux)

/-- Every supported encoded output on `(n, aux)` has length at most `t n aux.length`. -/
theorem length_le (h : ComputesOracleInTime output t program) (n : ℕ) (aux : List Bool)
    {State : Type} (oracle : Operation × List Bool → StateT State PMF (List Bool))
    (s s' : State) {result : β}
    (hresult : (result, s') ∈ (ProbOracleComp.runWith oracle (program n aux) s).support) :
    (output result).length ≤ t n aux.length :=
  h.on.length_le (n, aux) oracle s s' hresult

/-- A polynomially bounded parameterized halting oracle schedule gives `IsOraclePPT`. -/
theorem isOraclePPT (ht : PolyBounded (fun p : ℕ × ℕ => p.1 + p.2) (Function.uncurry t))
    (h : ComputesOracleInTime output t program) :
    IsOraclePPT output program := by
  refine IsOraclePPTOn.isOraclePPT (h.on.isOraclePPTOn ?_)
  refine ht.comp (g := fun input : ℕ × List Bool => (input.1, input.2.length)) ?_
  refine PolyBounded.of_forall_le 1 1 fun input => ?_
  enc_len [pow_one, one_mul]

end ComputesOracleInTime

/-- **Parameterized uniform strict oracle PPT is equivalent to `ComputesOracleInTime` under a
polynomially bounded schedule in `n + aux.length`.** -/
theorem isOraclePPT_iff_exists_polyBounded_computesOracleInTime
    {Operation β : Type} [DecidableEq Operation] {output : β ↪ List Bool}
    {program : ℕ → List Bool → WordOracleComp Operation β} :
    IsOraclePPT output program ↔
      ∃ t : ℕ → ℕ → ℕ,
        PolyBounded (fun p : ℕ × ℕ => p.1 + p.2) (Function.uncurry t) ∧
        ComputesOracleInTime output t program := by
  constructor
  · intro h
    obtain ⟨t₀, ht₀, hcomp⟩ := isOraclePPTOn_iff_exists_polyBounded_computesOracleInTimeOn.mp h.on
    obtain ⟨c, d, hle⟩ := ht₀.exists_le
    refine ⟨fun n m => c * 2 ^ d * (n + m + 1) ^ d,
      PolyBounded.of_forall_le (c * 2 ^ d) d (fun p => le_rfl), ?_⟩
    refine hcomp.mono fun input => (hle input).trans ?_
    have hsize : (encPair encUnary encBits input).length + 1 ≤
        2 * (input.1 + input.2.length + 1) := by
      enc_len
    calc c * ((encPair encUnary encBits input).length + 1) ^ d
        ≤ c * (2 * (input.1 + input.2.length + 1)) ^ d :=
          Nat.mul_le_mul_left c (Nat.pow_le_pow_left hsize d)
      _ = c * 2 ^ d * (input.1 + input.2.length + 1) ^ d := by
          rw [Nat.mul_pow, ← Nat.mul_assoc]
  · rintro ⟨t, ht, hcomp⟩
    exact hcomp.isOraclePPT ht

/-- **Parameterized uniform strict oracle PPT is equivalent to `ComputesOracleInTimeAndQueries`
under polynomially bounded time and query schedules.** -/
theorem isOraclePPT_iff_exists_polyBounded_computesOracleInTimeAndQueries
    {Operation β : Type} [DecidableEq Operation] {output : β ↪ List Bool}
    {program : ℕ → List Bool → WordOracleComp Operation β} :
    IsOraclePPT output program ↔
      ∃ t q : ℕ → ℕ → ℕ,
        PolyBounded (fun p : ℕ × ℕ => p.1 + p.2) (Function.uncurry t) ∧
        PolyBounded (fun p : ℕ × ℕ => p.1 + p.2) (Function.uncurry q) ∧
        ComputesOracleInTimeAndQueries output t q program := by
  constructor
  · intro h
    obtain ⟨t, ht, hcomp⟩ := isOraclePPT_iff_exists_polyBounded_computesOracleInTime.mp h
    exact ⟨t, t, ht, ht, hcomp, hcomp.isQueryBounded⟩
  · rintro ⟨t, _, ht, _, hcomp, _⟩
    exact hcomp.isOraclePPT ht

end Cslib.Probability
