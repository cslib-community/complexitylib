/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.ObservedProcess
public import CslibFrontier.Probability.PMF.SequentialHistory
public import CslibFrontier.Probability.StochasticDomination.Adapted
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Sequential observations of append-only recorded processes

An actual hidden-state transition appends one response to its recorded history.
Conditioning the actual state law on those records constructs a sequential response
kernel with exactly the same complete history law. A final posterior observation
preserves private-state/output correlation as well. No representation equality,
finite hidden alphabet or independence premise is supplied by the caller.

## Main definitions

* `response`: next-record law from the actual hidden-state posterior.
* `output`: final observation from the actual fixed-horizon posterior.

## Main results

* `history_law`, `expected_sum`: exact complete-record law and extended score means.
* `joint_law`, `output_law`: actual correlated final observations.
-/

public section
noncomputable section
namespace Cslib.Probability.RecordedProcess
open ObservedProcess
open scoped ENNReal
variable {S Ω O : Type}

/-- The actual next-record kernel, conditioned on the entire current record history.
The fallback makes the definition total; the supported append rule ensures that
actual transitions always have a head record. -/
@[expose] def response (step : S → PMF S) (records : S → List Ω) (initial : S)
    (fallback : Ω) (history : List Ω) : PMF Ω :=
  (PMF.posterior (stateLaw step history.length initial) records history).bind fun state =>
    (step state).map fun next => (records next).headD fallback

/-- Actual final observation conditional on a recorded prefix at the fixed horizon. -/
@[expose] def output (step : S → PMF S) (records : S → List Ω) (initial : S)
    (observe : S → O) (n : ℕ) (history : List Ω) : PMF O :=
  (PMF.posterior (stateLaw step n initial) records history).map observe

/-- The constructed sequential process has exactly the actual complete record law.
Only the initial history and structural append rule are hypotheses. -/
theorem history_law (step : S → PMF S) (records : S → List Ω) (initial : S) (fallback : Ω)
    (hinit : records initial = [])
    (hstep : ∀ state next, next ∈ (step state).support → ∃ x, records next = x :: records state)
    (n : ℕ) :
    (PMF.seqProcess (fun _ h => response step records initial fallback (PMF.seqHistory h)) n).map
        PMF.seqHistory = (stateLaw step n initial).map records := by
  induction n with
  | zero => simp [PMF.seqProcess, stateLaw, hinit]
  | succ n ih =>
    rw [PMF.seqProcess, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, PMF.seqHistory_snoc]
    let advance := fun history : List Ω =>
      (PMF.posterior (stateLaw step n initial) records history).bind fun state =>
        (step state).map fun next => (records next).headD fallback :: history
    have he : (fun h : Fin n → Ω =>
        (response step records initial fallback (PMF.seqHistory h)).map
          (fun x => x :: PMF.seqHistory h)) = advance ∘ PMF.seqHistory := by
      funext h
      simp only [response, PMF.length_seqHistory, PMF.map_bind, PMF.map_comp,
        Function.comp_def, advance]
    rw [he, ← PMF.bind_map, ih]
    dsimp only [advance]
    rw [PMF.posterior_bind, stateLaw, PMF.map_bind]
    apply PMF.bind_congr_on_support
    intro state hs
    apply PMF.map_congr_on_support
    intro next hn
    obtain ⟨x, he⟩ := hstep state next hn
    simp only [he, List.headD_cons]

/-- The recorded sequential process preserves the extended mean of every additive
receipt score, including scores accumulated before later divergence. -/
theorem expected_sum (step : S → PMF S) (records : S → List Ω) (initial : S) (fallback : Ω)
    (hinit : records initial = [])
    (hstep : ∀ state next, next ∈ (step state).support → ∃ x, records next = x :: records state)
    (score : Ω → ℝ≥0∞) (n : ℕ) :
    (∑' h, PMF.seqProcess
      (fun _ h => response step records initial fallback (PMF.seqHistory h)) n h *
        ((PMF.seqHistory h).map score).sum) =
      ∑' state, stateLaw step n initial state * ((records state).map score).sum := by
  have he := congrArg (fun p : PMF (List Ω) =>
    ∑' history, p history * (history.map score).sum)
    (history_law step records initial fallback hinit hstep n)
  simpa only [PMF.tsum_map_mul] using he

/-- Sampling the actual conditional output after the constructed receipt process
preserves the entire joint law of records and observed private-state output. -/
theorem joint_law (step : S → PMF S) (records : S → List Ω) (initial : S) (fallback : Ω)
    (hinit : records initial = [])
    (hstep : ∀ state next, next ∈ (step state).support → ∃ x, records next = x :: records state)
    (observe : S → O) (n : ℕ) :
    ((PMF.seqProcess (fun _ h => response step records initial fallback (PMF.seqHistory h)) n).map
      PMF.seqHistory).bind (fun history => (output step records initial observe n history).map
        (fun result => (history, result))) =
      (stateLaw step n initial).map (fun state => (records state, observe state)) := by
  rw [history_law step records initial fallback hinit hstep n]
  simp only [output, PMF.map_comp, Function.comp_def]
  change ((stateLaw step n initial).map records).bind
    (fun history => (PMF.posterior (stateLaw step n initial) records history).bind
      (fun state => PMF.pure (history, observe state))) = _
  rw [PMF.posterior_bind]
  rfl

/-- Marginal observation law after actual posterior extraction from the constructed
record process, including optional outputs that distinguish divergence. -/
theorem output_law (step : S → PMF S) (records : S → List Ω) (initial : S) (fallback : Ω)
    (hinit : records initial = [])
    (hstep : ∀ state next, next ∈ (step state).support → ∃ x, records next = x :: records state)
    (observe : S → O) (n : ℕ) :
    ((PMF.seqProcess (fun _ h => response step records initial fallback (PMF.seqHistory h)) n).map
      PMF.seqHistory).bind (output step records initial observe n) =
      (stateLaw step n initial).map observe := by
  rw [history_law step records initial fallback hinit hstep n]
  change ((stateLaw step n initial).map records).bind
    (fun history => (PMF.posterior (stateLaw step n initial) records history).bind
      (fun state => PMF.pure (observe state))) = _
  rw [PMF.posterior_bind]
  rfl

end Cslib.Probability.RecordedProcess
