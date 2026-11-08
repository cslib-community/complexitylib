/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.NativeOpenSelection
public import Complexity.Probability.PMF.StoppedProcess
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Actual unbounded open native stopped execution

[Wang2027], model PDF pp. 4--6, Theorem 5/Appendix A.5 pp. 12,16 and
Theorem 6 pp. 12--13, permit arbitrary local computation outside the oracle
deadline. A uniform native instruction bound is therefore not a source premise.

`terminal` removes that bound by the increasing limit of actual clocked halted
masses. The complete native configuration, private state, raw transcript and
accumulated resources are retained jointly. `none` means divergence, separately
from a halted failure or an accepted empty output. No representation identity,
almost-sure halting, bounded bill or integrability is an admission hypothesis.

This original bridge covers unbounded discrete stopped observations. It does not
collapse silent native steps into source oracle turns, establish batch codecs or
cancellation contracts, construct native upper selectors, or represent general
nonatomic response laws. Charges on divergent executions are not terminal bills;
this module does not silently assign them zero cost.

## Main results

* `terminal_behavioral`: actual unbounded joint observations equal behavioral clock limits.
* `terminal_provenance`: actual successful terminal outputs have response provenance.
* `terminal_normalized`: normalization preserves the entire unbounded joint outcome law.
* `terminal_score`: monotone convergence for every nonnegative stopped native score.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeUnboundedExecution
open NativeOpenExecution NativeOpenSelection Turing
open scoped ENNReal
variable {Operation Private Control J : Type} {k : ℕ} {input : List Bool}
variable [DecidableEq Operation]
variable (machine : MultiTapePTM k Bool Control Operation) (env : Environment Operation Private)

/-- Native halting, independent of the contents of the output tape. -/
@[expose] def halted (world : World k Control Operation Private input) : Prop :=
  world.config.tapes.state = none

instance : DecidablePred (halted (k := k) (Control := Control) (Operation := Operation)
    (Private := Private) (input := input)) := fun _ => inferInstanceAs (Decidable (_ = none))

/-- Native halting makes the actual transition kernel absorbing. -/
theorem step_halted (world : World k Control Operation Private input) (h : halted world) :
    step machine env world = PMF.pure world := by
  simp only [step, show world.config.tapes.state = none from h]

/-- Actual stopped native law with no common finite instruction clock.
Missing halted mass is divergence; full native worlds are retained on termination. -/
@[expose] def terminal (world : World k Control Operation Private input) :
    PMF (Option (World k Control Operation Private input)) :=
  StoppedProcess.terminal (step machine env) halted (step_halted machine env) world

/-- Every positive-mass terminal state is reached at some actual finite clock. -/
theorem terminal_support (world next : World k Control Operation Private input) :
    some next ∈ (terminal machine env world).support ↔
      halted next ∧ ∃ fuel, next ∈ (execute machine env fuel world).support := by
  simp only [terminal, StoppedProcess.terminal_support, execute_eq_stateLaw]

open Classical in
/-- Actual halted mass at an arbitrary clock, with live configurations excluded. -/
@[expose] def haltedMass (fuel : ℕ) (world : World k Control Operation Private input) : ℝ≥0∞ :=
  ∑' next, if halted next then execute machine env fuel world next else 0

/-- Actual almost-sure termination is exactly exhaustion of halted mass. It is
not an assumed uniform clock or a behavioral representation premise. -/
theorem terminal_none_eq_zero (world : World k Control Operation Private input) :
    terminal machine env world none = 0 ↔ ⨆ fuel, haltedMass machine env fuel world = 1 := by
  change 1 - (∑' next, StoppedProcess.terminalMass (step machine env) halted world next) = 0 ↔ _
  have hm := StoppedProcess.terminalMass_sum_le (step machine env) halted
    (step_halted machine env) world
  have he : (∑' next, StoppedProcess.terminalMass (step machine env) halted world next) =
      ⨆ fuel, haltedMass machine env fuel world := by
    unfold StoppedProcess.terminalMass
    rw [StoppedProcess.tsum_iSup_nat _
      (StoppedProcess.stopped_mono (step machine env) halted (step_halted machine env) world)]
    simp only [haltedMass, StoppedProcess.stopped, execute_eq_stateLaw]
  rw [tsub_eq_zero_iff_le]
  rw [← he]
  exact ⟨fun h => le_antisymm hm h, fun h => h.ge⟩

/-- Every nonnegative stopped score has exactly its actual clock-limit
expectation, without assuming an integrable or bounded total bill. -/
theorem terminal_score (world : World k Control Operation Private input)
    (score : World k Control Operation Private input → ℝ≥0∞) :
    (∑' next, terminal machine env world (some next) * score next) =
      ⨆ fuel, ∑' next, (if halted next then execute machine env fuel world next else 0) *
        score next := by
  simpa only [terminal, StoppedProcess.stopped, execute_eq_stateLaw] using
    StoppedProcess.terminal_score (step machine env) halted (step_halted machine env) world score

variable [DecidableEq J]
variable (parse : Operation → List Bool → List Bool → Finset J)
variable (decode : List Bool → Option (Finset J)) (accept : Finset J → Bool)

/-- Successful-output-only selection admission on every actual finite run.
There is no uniform clock, law-equality, termination or expected-cost requirement. -/
@[expose] def SelectionOnly (world : World k Control Operation Private input) : Prop :=
  ∀ fuel, NativeOpenSelection.SelectionOnly machine env parse decode accept fuel world

/-- Every accepted unbounded terminal output has actual response provenance. -/
theorem terminal_provenance (world next : World k Control Operation Private input)
    (h : SelectionOnly machine env parse decode accept world)
    (hn : some next ∈ (terminal machine env world).support) (C : Finset J)
    (hc : result decode next = some C) (ha : accept C = true) :
    C ⊆ proposals parse next.memory.events := by
  obtain ⟨_, fuel, hf⟩ := (terminal_support machine env world next).mp hn
  exact h fuel next hf C hc ha

/-- Failed-family normalization preserves actual joint history, stopping,
acceptance, token bill and external duration, including divergence probability. -/
theorem terminal_normalized (world : World k Control Operation Private input)
    (h : SelectionOnly machine env parse decode accept world) :
    (terminal machine env world).map
        (Option.map fun next => outcome accept (view parse decode next)) =
      (terminal machine env world).map (Option.map fun next => outcome accept
        ⟨next.memory.events, next.config.tapes.state.isNone, result decode next⟩) := by
  simp only [PMF.map]
  apply PMF.bind_congr_on_support
  intro next hn
  cases next with
  | none => rfl
  | some next =>
    obtain ⟨_, fuel, hf⟩ := (terminal_support machine env world next).mp hn
    have ha : accepted accept (normalized parse decode next) =
        accepted accept (result decode next) := by
      cases hr : result decode next with
      | none => simp [accepted, normalized, hr]
      | some C =>
        by_cases hp : C ⊆ proposals parse next.memory.events
        · simp [accepted, normalized, hr, hp]
        · have ha : accept C = false := by
            cases he : accept C
            · rfl
            · exact False.elim (hp (h fuel next hf C hr he))
          simp [accepted, normalized, hr, hp, ha]
    exact congrArg PMF.pure (by simp only [Option.map_some, outcome, view, ha])

open Classical in
/-- Concrete unbounded representation: each joint stopped public observation
has the increasing-limit law of the behavioral kernels constructed from actual
native hidden paths. No supplied representation contract or clock bound occurs. -/
theorem terminal_behavioral (world : World k Control Operation Private input)
    (z : View Operation J) :
    (terminal machine env world).map (Option.map (view parse decode)) (some z) =
      ⨆ fuel, ∑' history,
        ObservedProcess.publicLaw (step machine env) (view parse decode) fuel world history *
          (if (history.headD (view parse decode world)).halted = true ∧
            history.headD (view parse decode world) = z then 1 else 0) := by
  exact StoppedProcess.terminal_observed (step machine env) halted (step_halted machine env)
    world (view parse decode) (fun v => v.halted = true)
    (by intro next; simp [view, halted]) z

open Classical in
/-- The terminating observation masses constructed entirely from behavioral
clocked public path laws, without a uniform native instruction bound. -/
@[expose] def behavioralMass (world : World k Control Operation Private input)
    (z : View Operation J) : ℝ≥0∞ :=
  ⨆ fuel, ∑' history,
    ObservedProcess.publicLaw (step machine env) (view parse decode) fuel world history *
      (if (history.headD (view parse decode world)).halted = true ∧
        history.headD (view parse decode world) = z then 1 else 0)

/-- The constructed behavioral stopped masses form a subprobability law. -/
theorem behavioralMass_sum_le (world : World k Control Operation Private input) :
    (∑' z, behavioralMass machine env parse decode world z) ≤ 1 := by
  let q := (terminal machine env world).map (Option.map (view parse decode))
  have he : (∑' z, behavioralMass machine env parse decode world z) = ∑' z, q (some z) := by
    apply tsum_congr
    intro z
    exact (terminal_behavioral machine env parse decode world z).symm
  rw [he]
  have hq := q.tsum_coe
  rw [← (Equiv.optionEquivSumPUnit.{0, 0} (View Operation J)).symm.tsum_eq,
    Summable.tsum_sum CompleteLattice.summable CompleteLattice.summable] at hq
  simp only [Equiv.optionEquivSumPUnit_symm_inl,
    Equiv.optionEquivSumPUnit_symm_inr, tsum_fintype, Fintype.sum_unique] at hq
  rw [← hq]
  exact le_self_add

/-- Actual unbounded behavioral observation law, completing any remaining
mass with divergence. Its inputs are the derived public kernels, not a supplied
machine-to-policy representation. -/
@[expose] def behavioral (world : World k Control Operation Private input) :
    PMF (Option (View Operation J)) :=
  StoppedProcess.withDivergence (behavioralMass machine env parse decode world)
    (behavioralMass_sum_le machine env parse decode world)

/-- Equality of complete unbounded joint observation laws, including divergence,
native halting, actual query/response paths and both accumulated resources. -/
theorem terminal_behavioral_law (world : World k Control Operation Private input) :
    (terminal machine env world).map (Option.map (view parse decode)) =
      behavioral machine env parse decode world := by
  apply StoppedProcess.option_ext
  intro z
  exact terminal_behavioral machine env parse decode world z

/-- Any admitted selection-only machine has a constructed unbounded behavioral
law with the same actual joint path, stopping, accepted output, bill and duration
observations. Failed-output normalization and divergence are separate. -/
theorem behavioral_outcome_law (world : World k Control Operation Private input)
    (h : SelectionOnly machine env parse decode accept world) :
    (behavioral machine env parse decode world).map (Option.map (outcome accept)) =
      (terminal machine env world).map (Option.map fun next => outcome accept
        ⟨next.memory.events, next.config.tapes.state.isNone, result decode next⟩) := by
  rw [← terminal_behavioral_law, PMF.map_comp]
  convert terminal_normalized machine env parse decode accept world h using 1
  congr 1
  funext next
  cases next <;> rfl

end Cslib.Probability.NativeUnboundedExecution
