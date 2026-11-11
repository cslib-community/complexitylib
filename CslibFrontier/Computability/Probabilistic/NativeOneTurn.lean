/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import CslibFrontier.Probability.FiniteDisintegration
public import CslibFrontier.Probability.FiniteTableOfPMF
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# A native randomized one-turn selector represented by behavioral tables

Two actual clocked fair-coin multi-tape machines surround one external batch.
The first emits a private word; the driver retains that word and passes it,
together with the entire response, to the second machine. Observation adapters
specify the batch and decoded output. No representation law is an input.

The first machine's saved coins are conditioned on its observed batch. The
resulting output table averages the actual continuation machine over that
posterior, preserving private-state/action correlations and all observable laws.
The response law may depend on the whole prior transcript encoded in `input`.
The finite action observation must include every query/cutoff parameter visible
to the environment; the batch need not be the only component of that observation.

This is a concrete clocked two-phase protocol, not a decomposition theorem for
arbitrary open PTMs. The caller supplies raw-word observation/input adapters;
no compiler or complexity claim for these adapters is made. Clocks do not count
against the external response deadline. Actual supported halting permits padding.
This protocol and its representation proof are an implementation bridge, not a
claimed paper endpoint.

## Main results

* `behavioralRun_toPMF`: exact actual native joint-law representation.
* `run_encoded`: supported raw-word correctness preserves encoded output laws.
* `mean_eq_native`: preservation of every finite observable expectation.
* `run_pad_first`, `run_pad_finish`: actual supported halting permits clock padding.
-/

public section
noncomputable section
namespace Cslib.Probability
open Cslib.Optimization.OneConstraint
open Turing Turing.MultiTapePTM

/-- Native machines and raw-word adapters for a single external turn. Private
storage is the first machine's output packet, retained by the protocol driver. -/
structure NativeOneTurn (A R O : Type) where
  /-- Number of first-phase work tapes. -/
  firstTapes : ℕ
  /-- First-phase finite control. -/
  FirstState : Type
  /-- Control is finite, as required of an encoded PTM. -/
  firstFinite : Finite FirstState
  /-- Actual first fair-coin machine. -/
  first : MultiTapePTM firstTapes Bool FirstState
  /-- Local first-phase clock. -/
  firstClock : ℕ
  /-- Decode the selected batch from its emitted packet. -/
  action : List Bool → A
  /-- Number of continuation work tapes. -/
  finishTapes : ℕ
  /-- Continuation finite control. -/
  FinishState : Type
  /-- Continuation control is finite. -/
  finishFinite : Finite FinishState
  /-- Actual continuation fair-coin machine. -/
  finish : MultiTapePTM finishTapes Bool FinishState
  /-- Local continuation clock. -/
  finishClock : ℕ
  /-- Pass the retained packet and complete response to the continuation. -/
  prepare : List Bool → R → List Bool
  /-- Decode its actual output word. -/
  output : List Bool → O

namespace NativeOneTurn
variable {A R O : Type} [Fintype A] [Fintype R] [Fintype O]
variable (M : NativeOneTurn A R O)

/-- The complete native continuation output law, including its fresh fair coins. -/
@[expose] def finishLaw (packet : List Bool) (r : R) : PMF O :=
  (ProbComp.eval (M.finish.runClosed M.finishClock (M.prepare packet r))).map M.output

/-- Actual joint action/response/output law of the two native phases. -/
@[expose] def run (input : List Bool) (respond : A → Distribution R ℝ) : PMF (A × R × O) := do
  let packet ← ProbComp.eval (M.first.runClosed M.firstClock input)
  let r ← (respond (M.action packet)).toPMF
  (M.finishLaw packet r).map fun o => (M.action packet, r, o)

/-- Actual raw terminal words before decoding, retaining the full public tuple. -/
@[expose] def rawRun (input : List Bool) (respond : A → Distribution R ℝ) :
    PMF (A × R × List Bool) := do
  let packet ← ProbComp.eval (M.first.runClosed M.firstClock input)
  let r ← (respond (M.action packet)).toPMF
  (ProbComp.eval (M.finish.runClosed M.finishClock (M.prepare packet r))).map
    fun word => (M.action packet, r, word)

/-- Standard output-encoding correctness on actual supported native executions.
It constrains raw words, not a supplied equality of probability laws. -/
@[expose] def OutputsEncoded (encode : O ↪ List Bool) (input : List Bool)
    (respond : A → Distribution R ℝ) : Prop :=
  ∀ packet ∈ (ProbComp.eval (M.first.runClosed M.firstClock input)).support,
    ∀ r ∈ (respond (M.action packet)).toPMF.support,
      ∀ word ∈ (ProbComp.eval
        (M.finish.runClosed M.finishClock (M.prepare packet r))).support,
        encode (M.output word) = word

omit [Fintype A] [Fintype O] in
/-- An actual supported encoding contract implies equality with the raw-word law.
Thus the behavioral representation can be used with genuine encoded outputs,
without assuming the desired representation law as a premise. -/
theorem run_encoded (encode : O ↪ List Bool) (input : List Bool)
    (respond : A → Distribution R ℝ) (h : M.OutputsEncoded encode input respond) :
    (M.run input respond).map (fun (a, r, o) => (a, r, encode o)) =
      M.rawRun input respond := by
  simp only [run, rawRun, finishLaw, Cslib.Probability.PMF.monad_bind_eq_bind,
    PMF.map_bind, PMF.map_comp]
  apply Cslib.Probability.PMF.bind_congr_on_support
  intro packet hp
  apply Cslib.Probability.PMF.bind_congr_on_support
  intro r hr
  simp only [PMF.map]
  apply Cslib.Probability.PMF.bind_congr_on_support
  intro word hw
  simp only [Function.comp_apply, h packet hp r hr word hw]

/-- Independent fair coins for every first-phase transition, including padding
bits ignored by configurations that have already halted. -/
@[expose] def coins : Distribution (Fin M.firstClock → Bool) ℝ :=
  Distribution.ofPMF (PMF.uniformOfFintype _)

/-- Replay the actual native transition table on the saved first-phase coins. -/
@[expose] def packet (input : List Bool) (s : Fin M.firstClock → Bool) : List Bool :=
  M.first.runClosedCoins (List.ofFn s) input

/-- Observed first-batch law derived from actual native replay. -/
@[expose] def actionTable (input : List Bool) : Distribution A ℝ :=
  M.coins.map (fun s => M.action (M.packet input s))

/-- Output law conditional on the observed batch and response. The posterior
retains correlations between private saved state and the chosen batch. -/
@[expose] def outputTable (input : List Bool) (a : A) (r : R) : Distribution O ℝ :=
  (M.coins.posterior (fun s => M.action (M.packet input s)) a).bind
    (fun s => Distribution.ofPMF (M.finishLaw (M.packet input s) r))

/-- Behavioral experiment assembled from the constructed tables. -/
@[expose] def behavioralRun (input : List Bool) (respond : A → Distribution R ℝ) :
    Distribution (A × R × O) ℝ :=
  (M.actionTable input).bind fun a => (respond a).bind fun r =>
    (M.outputTable input a r).map fun o => (a, r, o)

omit [Fintype A] [Fintype R] [Fintype O] in
private theorem replay_law (input : List Bool) :
    M.coins.toPMF.map (M.packet input) =
      ProbComp.eval (M.first.runClosed M.firstClock input) := by
  rw [coins, Distribution.toPMF_ofPMF, eval_runClosed_eq_map_coins,
    BitString.uniformList, PMF.map_comp]
  rfl

omit [Fintype R] [Fintype O] in
/-- The constructed first-action table is the actual native action marginal. -/
theorem actionTable_toPMF (input : List Bool) :
    (M.actionTable input).toPMF =
      (ProbComp.eval (M.first.runClosed M.firstClock input)).map M.action := by
  rw [actionTable, Distribution.toPMF_map, ← M.replay_law, PMF.map_comp]
  rfl

/-- The behavioral joint mass factors into action, response and conditional
output, enabling inspection of the derived conditional probabilities. -/
theorem behavioralRun_weight (input : List Bool) (respond : A → Distribution R ℝ)
    (a : A) (r : R) (o : O) :
    (M.behavioralRun input respond).weight (a, r, o) =
      (M.actionTable input).weight a * (respond a).weight r *
        (M.outputTable input a r).weight o := by
  classical
  simp [behavioralRun, Distribution.bind, Distribution.map, Prod.mk.injEq, ite_and, mul_assoc]

/-- Exact representation of the actual native experiment, including joint
observations, without an assumed representation or conditional-law identity. -/
theorem behavioralRun_toPMF (input : List Bool) (respond : A → Distribution R ℝ) :
    (M.behavioralRun input respond).toPMF = M.run input respond := by
  let action := fun s => M.action (M.packet input s)
  let next := fun s a => (respond a).bind fun r =>
    (Distribution.ofPMF (M.finishLaw (M.packet input s) r)).map fun o => (a, r, o)
  have h := congrArg Distribution.toPMF (M.coins.posterior_bind action next)
  dsimp only [next] at h
  simp only [Distribution.toPMF_bind, Distribution.toPMF_map,
    Distribution.toPMF_ofPMF] at h
  calc
    _ = (M.coins.map action).toPMF.bind (fun a =>
        (M.coins.posterior action a).toPMF.bind fun s =>
          (respond a).toPMF.bind fun r =>
            (M.finishLaw (M.packet input s) r).map fun o => (a, r, o)) := by
      simp only [behavioralRun, actionTable, outputTable, Distribution.toPMF_bind,
        Distribution.toPMF_map, Distribution.toPMF_ofPMF, PMF.map_bind]
      congr 1
      funext a
      exact PMF.bind_comm _ _ _
    _ = M.coins.toPMF.bind (fun s => (respond (action s)).toPMF.bind fun r =>
        (M.finishLaw (M.packet input s) r).map fun o => (action s, r, o)) := by
      simpa only [Distribution.toPMF_map] using h
    _ = M.run input respond := by
      simp only [run, Cslib.Probability.PMF.monad_bind_eq_bind]
      rw [← M.replay_law input, PMF.bind_map]
      rfl

/-- Direct encoded-output representation: actual native word correctness,
rather than an assumed equality of laws, yields the behavioral raw-word law. -/
theorem behavioralRun_encoded (input : List Bool) (respond : A → Distribution R ℝ)
    (encode : O ↪ List Bool) (h : M.OutputsEncoded encode input respond) :
    (M.behavioralRun input respond).toPMF.map (fun (a, r, o) => (a, r, encode o)) =
      M.rawRun input respond := by
  rw [M.behavioralRun_toPMF]
  exact M.run_encoded encode input respond h

/-- Every finite observable expectation is exactly its actual native-run value.
In particular this simultaneously preserves success, issued tokens and duration. -/
theorem mean_eq_native (input : List Bool) (respond : A → Distribution R ℝ)
    (f : A × R × O → ℝ) :
    (M.behavioralRun input respond).mean f =
      ∑ t, (M.run input respond t).toReal * f t := by
  rw [← M.behavioralRun_toPMF input respond]
  simp only [Distribution.mean, Distribution.toPMF_real]

/-- Supported actual halting of both phases. This is a machine termination
contract, not a supplied representation law. No local clock is charged as tokens
or included in physical oracle duration. -/
@[expose] def Halts (input : List Bool) (respond : A → Distribution R ℝ) : Prop :=
  (∀ cfg ∈ (ProbComp.eval (M.first.runClosedConfigFrom M.firstClock
      (M.first.initialConfig input))).support, cfg.tapes.state = none) ∧
  ∀ packet ∈ (ProbComp.eval (M.first.runClosed M.firstClock input)).support,
    ∀ r ∈ (respond (M.action packet)).support,
      ∀ cfg ∈ (ProbComp.eval (M.finish.runClosedConfigFrom M.finishClock
        (M.finish.initialConfig (M.prepare packet r)))).support, cfg.tapes.state = none

omit [Fintype A] [Fintype O] in
/-- A larger continuation clock cannot change the actual joint law after supported
halting. Termination is used through the native machine's padding theorem. -/
theorem run_pad_finish (input : List Bool) (respond : A → Distribution R ℝ)
    (h : M.Halts input respond) (n : ℕ) (hn : M.finishClock ≤ n) :
    ({ M with finishClock := n } : NativeOneTurn A R O).run input respond =
      M.run input respond := by
  unfold run
  apply Cslib.Probability.PMF.bind_congr_on_support
  intro packet hp
  apply Cslib.Probability.PMF.bind_congr_on_support
  intro r hr
  have hr' : r ∈ (respond (M.action packet)).support := by
    have hpos : 0 < ((respond (M.action packet)).toPMF r).toReal :=
      ENNReal.toReal_pos hr ((respond (M.action packet)).toPMF.apply_ne_top r)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa only [Distribution.toPMF_real] using hpos⟩
  simp only [finishLaw]
  rw [eval_runClosed_eq_of_halted M.finish _ hn (h.2 packet hp r hr')]

omit [Fintype A] [Fintype O] in
/-- Padding an actually halted first phase preserves the private packet law and
therefore the whole actual experiment, not just the selected batch marginal. -/
theorem run_pad_first (input : List Bool) (respond : A → Distribution R ℝ)
    (h : M.Halts input respond) (n : ℕ) (hn : M.firstClock ≤ n) :
    ({ M with firstClock := n } : NativeOneTurn A R O).run input respond =
      M.run input respond := by
  unfold run
  rw [eval_runClosed_eq_of_halted M.first input hn h.1]
  rfl

end NativeOneTurn
end Cslib.Probability
