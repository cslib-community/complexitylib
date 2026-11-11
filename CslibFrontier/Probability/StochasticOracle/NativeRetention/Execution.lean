/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.Correctness
public import CslibFrontier.Computability.Probabilistic.NativeUnboundedExecution
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Actual open native execution of the compiled retention phase

The generated local machine is embedded into the ordinary open native PTM model.
It halts on every runtime rational input, writes the original source family mask,
and preserves the entire existing oracle memory, invoices and external duration.
No response or hidden metadata is resampled or replaced by a finite alphabet.

## Main results

* `terminal_local`: actual unbounded native local execution terminates with the derived output.
* `local_resources`: previous oracle memory and both resource meters remain identical.

This theorem starts the local phase with its encoded input on the input tape.
Constructing that input from the raw query-channel report and composing the
adaptive query/stop loop remain explicit obligations.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention
open Turing Cslib.Probability NativeOpenExecution
open scoped ENNReal
variable {Private : Type}

/-- The compiled deterministic local code used as an actual open native PTM. -/
def native : MultiTapePTM compiled.tapes Bool compiled.Control Unit :=
  MultiTapePTM.ofDeterministic compiled.machine

/-- Fresh local computation tapes with the entire existing oracle memory preserved. -/
@[expose] def localStart (x : Input) (memory : Memory Unit Private) :
    World compiled.tapes compiled.Control Unit Private (encInput x) :=
  ⟨native.initialConfig (encInput x), memory⟩

/-- Actual local native state after the corresponding deterministic instruction clock. -/
@[expose] def localDone (x : Input) (memory : Memory Unit Private) (t : ℕ) :
    World compiled.tapes compiled.Control Unit Private (encInput x) :=
  ⟨{ (localStart x memory).config with
      tapes := compiled.machine.runFrom (compiled.machine.initCfg (encInput x)) t }, memory⟩

/-- Clocked actual open execution preserves all hidden memory and channels;
the external handler is never queried by the local code. -/
theorem execute_local (env : Environment Unit Private) (x : Input)
    (memory : Memory Unit Private) (t : ℕ) :
    execute native env t (localStart x memory) = PMF.pure (localDone x memory t) := by
  unfold execute
  change ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    ((MultiTapePTM.ofDeterministic compiled.machine).runOracleConfigFrom t
      (localStart x memory).config)).run memory).map _ = _
  rw [← OracleComp.runWith, ← ProbOracleComp.runWith,
    MultiTapePTM.run_interpret_runOracleConfigFrom_ofDeterministic]
  rw [PMF.pure_map]
  rfl

/-- The actual open native local phase halts with its correctly decoded retained
output, independently of the external stateful oracle's behavior. -/
theorem local_halts (env : Environment Unit Private) (x : Input) (memory : Memory Unit Private) :
    ∃ t, execute native env t (localStart x memory) = PMF.pure (localDone x memory t) ∧
      NativeUnboundedExecution.halted (localDone x memory t) ∧
      NativeOpenSelection.result (ConcurrentBatch.decodeFamily x.rows.length)
        (localDone x memory t) = some (outputFamily x) := by
  obtain ⟨t, ht, ho⟩ := compiled_output x
  refine ⟨t, execute_local env x memory t, ht, ?_⟩
  simp only [NativeOpenSelection.result, localDone, ht, Option.isNone_none, ite_true]
  rw [ho, decode_output]

/-- Actual unbounded open execution of the compiled local phase has no divergent
mass. Its native output and full oracle memory are identified, not postulated. -/
theorem terminal_local (env : Environment Unit Private) (x : Input) (memory : Memory Unit Private) :
    ∃ t, NativeUnboundedExecution.terminal native env (localStart x memory) =
        PMF.pure (some (localDone x memory t)) ∧
      NativeOpenSelection.result (ConcurrentBatch.decodeFamily x.rows.length)
        (localDone x memory t) = some (outputFamily x) := by
  obtain ⟨t, he, hh, hr⟩ := local_halts env x memory
  refine ⟨t, ?_, hr⟩
  have hm : 1 ≤ NativeUnboundedExecution.terminal native env (localStart x memory)
      (some (localDone x memory t)) := by
    change 1 ≤ ⨆ fuel, StoppedProcess.stopped (NativeOpenExecution.step native env)
      NativeUnboundedExecution.halted
      fuel (localStart x memory) (localDone x memory t)
    apply le_iSup_of_le t
    simp only [StoppedProcess.stopped, hh, ite_true, ← execute_eq_stateLaw, he, PMF.pure_apply,
      le_refl]
  have hm' := le_antisymm (PMF.coe_le_one _ _) hm
  have hs := (PMF.apply_eq_one_iff _ _).mp hm'
  ext result
  by_cases hz : result = some (localDone x memory t)
  · subst result
    simp [hm', PMF.pure_apply]
  · have hzero : NativeUnboundedExecution.terminal native env (localStart x memory) result = 0 :=
      (PMF.apply_eq_zero_iff _ _).mpr (by rw [hs]; simpa using hz)
    simp [hzero, PMF.pure_apply, hz]

/-- Assembled local-phase endpoint: a positive computed completion decision
produces an actually decoded full cover and its derived dual certificate, with
all existing oracle resources preserved. The condition is the executable Boolean
calculation, not a supplied successful-family witness or probability conclusion. -/
theorem terminal_cover (env : Environment Unit Private) (x : Input)
    (memory : Memory Unit Private) (hx : Valid x) (hc : complete x = true) :
    ∃ t, NativeUnboundedExecution.terminal native env (localStart x memory) =
        PMF.pure (some (localDone x memory t)) ∧
      NativeOpenSelection.result (ConcurrentBatch.decodeFamily x.rows.length)
        (localDone x memory t) = some (outputFamily x) ∧
      (instanceOf x hx).covered ((outputFamily x).image Fin.val) = (instanceOf x hx).ground ∧
      (instanceOf x hx).cost ((outputFamily x).image Fin.val) ≤
        (x.rho : ℝ) * ∑ e ∈ (instanceOf x hx).ground, (instanceOf x hx).dual e ∧
      (localDone x memory t).memory = memory := by
  obtain ⟨t, ht, hr⟩ := terminal_local env x memory
  obtain ⟨hg, hw⟩ := completed_output x hx hc
  exact ⟨t, ht, hr, hg, hw, rfl⟩

/-- Local retention changes no existing token bill, physical duration or provenance
ledger, including when the memory contains correlated earlier oracle replies. -/
theorem local_resources (x : Input) (memory : Memory Unit Private) (t : ℕ) :
    (localDone x memory t).memory = memory ∧
      tokenBill (localDone x memory t).memory.events = tokenBill memory.events ∧
      elapsed (localDone x memory t).memory.events = elapsed memory.events :=
  ⟨rfl, rfl, rfl⟩

end Cslib.Probability.StochasticOracle.NativeRetention
