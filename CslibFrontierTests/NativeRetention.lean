/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeRetention.Execution
import CslibFrontierTests.NativeBatchProgress
import Mathlib.Tactic

/-!
# Native local retention from runtime rational rows and real source proposals

A nonempty instance rejects a costly proposal, accepts two proper partial covers,
and ignores duplicates/out-of-range indices. The correlated source client derives
its local-phase input from a real report; local native execution preserves the
existing correlated oracle memory and bill/duration. The input serialization is
explicitly a boundary: the adaptive raw-channel parser/query loop is still open.
-/

noncomputable section
open Cslib Cslib.Probability Turing
open StochasticOracle NativeRetention NativeOpenExecution
open scoped NNReal
namespace CslibFrontierTests.NativeRetention

/-- Positive weights and dual prices with two useful proper partial proposals. -/
def data : Input :=
  ⟨[[0], [1], [0,1]], [1,1,5], [1,1], 1, [[2], [0,0], [1], [1,99]]⟩

/-- The promised feasible dual is checked against the actual rows, not supplied
as a desired retention or native output conclusion. -/
theorem valid : Valid data := by
  constructor
  · intro j
    rcases j with _ | (_ | (_ | j)) <;> norm_num [data]
  · intro e
    rcases e with _ | (_ | e) <;> norm_num [data]
  · intro j
    rcases j with _ | (_ | (_ | j)) <;>
      norm_num [elements, ground, data, List.range_succ]

/-- Expensive, useful and repeated proposals exercise both sides of the local test. -/
example : certified data [] [2] = false ∧ certified data [] [0,0] = true ∧
    certified data [0] [1] = true ∧ certified data [0,1] [1,99] = false := by
  norm_num [output, retain, NativeRetention.step, certified, newly, covered,
    NativeRetention.normalize, population, ground, cost, price, data, List.range_succ]

/-- The same runtime algorithm retains each useful candidate exactly once. -/
example : retain data = [0,1] ∧ output data = [true,true,false] := by
  norm_num [output, retain, NativeRetention.step, certified, newly, covered,
    NativeRetention.normalize, population, ground, cost, price, data, List.range_succ]

/-- Completion is computed from runtime coverage, and is not supplied as a success flag. -/
example : complete data = true := by
  norm_num [complete, output, retain, NativeRetention.step, certified, newly, covered,
    NativeRetention.normalize, population, ground, cost, price, data, List.range_succ]

/-- The actual compiled local machine emits a decodable family, terminates,
and leaves an arbitrary stateful oracle and its existing receipts unchanged. -/
example {Private : Type} (env : Environment Unit Private) (memory : Memory Unit Private) :
    ∃ t, NativeUnboundedExecution.terminal native env (localStart data memory) =
        PMF.pure (some (localDone data memory t)) ∧
      NativeOpenSelection.result (ConcurrentBatch.decodeFamily data.rows.length)
        (localDone data memory t) = some (outputFamily data) ∧
      (localDone data memory t).memory = memory := by
  obtain ⟨t, ht, hr⟩ := terminal_local env data memory
  exact ⟨t, ht, hr, rfl⟩

/-- The actual returned family's dual certificate is derived from its rational data. -/
example : (instanceOf data valid).cost ((outputFamily data).image Fin.val) ≤ (data.rho : ℝ) *
    ∑ e ∈ (instanceOf data valid).covered ((outputFamily data).image Fin.val),
      (instanceOf data valid).dual e := output_certificate data valid

/-- Runtime rows for the singleton cover used by the genuine concurrent client. -/
def sourceData (u : Bool) : Input :=
  ⟨[[0]], [1], [1], 1,
    (ConcurrentBatch.parseProposals 3 1
      (ConcurrentBatch.replyOf (NativeBatchPolicy.firstReceipt u)).word).map sourceIndices⟩

private theorem source_proposals (u : Bool) : (sourceData u).proposals =
    [if u then [0] else []] := by
  change (ConcurrentBatch.parseProposals 3 1
    (ConcurrentBatch.encodeReport (NativeBatchPolicy.firstReceipt u).report)).map sourceIndices = _
  rw [ConcurrentBatch.parseProposals_report]
  rw [NativeBatchProgress.first_proposals]
  cases u <;> simp [sourceIndices, List.finRange_succ]

/-- The actual source-derived data has a feasible positive dual on both correlated branches. -/
theorem source_valid (u : Bool) : Valid (sourceData u) := by
  constructor
  · intro j
    cases j <;> norm_num [sourceData]
  · intro e
    cases e <;> norm_num [sourceData]
  · intro j
    cases j <;> norm_num [elements, ground, sourceData, List.range_succ]

/-- The source latent bit is not exposed to the local program: its input is
computed from the actual completed proposal words, with cancellation excluded. -/
example (u : Bool) : output (sourceData u) = [u] := by
  have he : sourceData u = ⟨[[0]], [1], [1], 1, [if u then [0] else []]⟩ := by
    have hp := source_proposals u
    simpa only [sourceData, Input.mk.injEq, true_and] using hp
  rw [he]
  cases u <;> norm_num [output, retain, NativeRetention.step, certified, newly, covered,
    NativeRetention.normalize, population, ground, cost, price, List.range_succ]

/-- Source-derived completion is computed correctly on both branches, rather
than receiving the hidden scenario as a success flag. -/
example (u : Bool) : complete (sourceData u) = u := by
  have he : sourceData u = ⟨[[0]], [1], [1], 1, [if u then [0] else []]⟩ := by
    have hp := source_proposals u
    simpa only [sourceData, Input.mk.injEq, true_and] using hp
  rw [he]
  cases u <;> norm_num [complete, retain, NativeRetention.step, certified, newly, covered,
    NativeRetention.normalize, population, ground, cost, price, List.range_succ]

/-- The local native program runs against the same actual source oracle and
preserves the full correlated first-batch memory, including its cancellation bill. -/
example (u : Bool) : ∃ t,
    NativeUnboundedExecution.terminal native
        (Cslib.Probability.StochasticOracle.ConcurrentBatch.environment
          ConcurrentBatch.limits ConcurrentBatch.sample)
        (localStart (sourceData u) (NativeBatchPolicy.firstMemory u)) =
      PMF.pure (some (localDone (sourceData u) (NativeBatchPolicy.firstMemory u) t)) ∧
    (localDone (sourceData u) (NativeBatchPolicy.firstMemory u) t).memory =
      NativeBatchPolicy.firstMemory u := by
  obtain ⟨t, ht, _⟩ := terminal_local
    (Cslib.Probability.StochasticOracle.ConcurrentBatch.environment
          ConcurrentBatch.limits ConcurrentBatch.sample)
    (sourceData u) (NativeBatchPolicy.firstMemory u)
  exact ⟨t, ht, rfl⟩

/-- Empty ground produces an actual empty family mask without requiring progress. -/
example : output (⟨[], [], [], 1, [[]]⟩ : Input) = [] := by
  norm_num [output, retain, NativeRetention.step, certified, newly, covered,
    NativeRetention.normalize, population, ground, cost, price, data, List.range_succ]

end CslibFrontierTests.NativeRetention
