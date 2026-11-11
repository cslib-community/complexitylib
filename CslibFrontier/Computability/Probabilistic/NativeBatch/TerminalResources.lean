/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeBatch.Quantitative
import CslibFrontier.Probability.PMF.SupportTsum
import Mathlib.Tactic

/-!
# Accrued native bills for almost surely terminating source executions

The whole source trace retains prefix costs on divergent paths. Once termination
is proved, its expected accrued bill equals the expected native terminal invoice.
No integrability or bounded-total-bill premise is needed. A native implementation
must establish termination independently before using this equality.

## Main results

* `expected_charge_eq_terminal`: actual retained-trace expectation equals terminal billing.
* `expected_charge_eq_of_output_memory`: compiled output/memory laws transport accrued expectation.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.Quantitative
open Turing NativeOpenExecution NativeInterface StochasticOracle.ConcurrentBatch Trace
open scoped ENNReal NNReal
variable {n k : ℕ} {Private Control : Type} {input : List Bool}

/-- Almost-sure termination permits terminal invoice accounting. The left side
is the original whole trace, including its convention for divergent prefix bills. -/
theorem expected_charge_eq_terminal (limits : Limits n) (sample : Sampler n Private)
    (machine : MultiTapePTM k Bool Control Unit)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (hzero : world.memory.privateState.history = [])
    (hterminates : NativeUnboundedExecution.terminal machine
      (environment limits sample) world none = 0) :
    expected limits sample machine charge (limits.turns + 1) world =
      ∑' result, NativeUnboundedExecution.terminal machine
        (environment limits sample) world result *
        result.elim 0 (fun next => (tokenBill next.memory.events : ℝ≥0∞)) := by
  rw [← law_native_terminal limits sample machine world hi, PMF.tsum_map_mul]
  apply PMF.tsum_mul_congr_support
  intro state hs
  rcases law_done limits sample machine world hi state hs with hn | ⟨next, he, _⟩
  · have hm : none ∈ (NativeUnboundedExecution.terminal machine
        (environment limits sample) world).support := by
      rw [← law_native_terminal limits sample machine world hi]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨state, hs, by simp [hn]⟩
    exact (hm hterminates).elim
  · simpa only [he, Option.map_some, Option.elim_some, worldOf] using
      (terminal_resources limits sample machine world next hi hzero state hs he).1

/-- Two terminating native implementations with the same actual output/memory
law have the same accrued expected bill. The hypothesis is a semantic transfer
lemma; concrete compilers must derive the law and termination before applying it. -/
theorem expected_charge_eq_of_output_memory {k' : ℕ} {Control' : Type} {input' : List Bool}
    (limits : Limits n) (sample : Sampler n Private)
    (machine : MultiTapePTM k Bool Control Unit)
    (other : MultiTapePTM k' Bool Control' Unit)
    (world : World k Control Unit (ServerState n Private) input)
    (start : World k' Control' Unit (ServerState n Private) input')
    (hi : Invariant limits world.memory) (hj : Invariant limits start.memory)
    (hzero : world.memory.privateState.history = [])
    (hzero' : start.memory.privateState.history = [])
    (hlaw : (NativeUnboundedExecution.terminal machine (environment limits sample) world).map
      (Option.map fun w => (w.config.tapes.output, w.memory)) =
      (NativeUnboundedExecution.terminal other (environment limits sample) start).map
        (Option.map fun w => (w.config.tapes.output, w.memory)))
    (ht : NativeUnboundedExecution.terminal other (environment limits sample) start none = 0) :
    expected limits sample machine charge (limits.turns + 1) world =
      expected limits sample other charge (limits.turns + 1) start := by
  let μ := NativeUnboundedExecution.terminal machine (environment limits sample) world
  let ν := NativeUnboundedExecution.terminal other (environment limits sample) start
  have hterm : μ none = 0 := by
    apply (PMF.apply_eq_zero_iff _ _).mpr
    intro hn
    have hm : none ∈ (μ.map
        (Option.map fun w => (w.config.tapes.output, w.memory))).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨none, hn, rfl⟩
    rw [hlaw] at hm
    obtain ⟨result, hr, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
    cases result with
    | none => exact hr ht
    | some next => cases he
  rw [expected_charge_eq_terminal limits sample machine world hi hzero hterm,
    expected_charge_eq_terminal limits sample other start hj hzero' ht]
  let score : Option (List Bool × Memory Unit (ServerState n Private)) → ℝ≥0∞ :=
    fun result => result.elim 0 (fun pair => (tokenBill pair.2.events : ℝ≥0∞))
  have hleft := PMF.tsum_map_mul μ
    (Option.map fun w => (w.config.tapes.output, w.memory)) score
  have hright := PMF.tsum_map_mul ν
    (Option.map fun w => (w.config.tapes.output, w.memory)) score
  simp only [score, Option.elim_map, Function.comp_def] at hleft hright
  rw [← hleft, hlaw, hright]

end Cslib.Probability.NativeBatch.Quantitative
