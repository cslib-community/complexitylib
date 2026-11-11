/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchUpper
import Mathlib.Tactic

/-!
# Native upper-policy empty-ground boundary

The actual constructed program starts from original encoded input. Empty ground,
zero turns and no opportunities give total expected receipt cost zero, without
an integrability/termination/cost premise. Nonempty correlated admission/stopping
clients are in `NativeRetentionBatchAdmission`; positive numerical envelope
clients are in `NativeBatchProgress` and `NativeBatchSuccess`.
-/

noncomputable section
open Cslib.Probability StochasticOracle NativeRetention ConcurrentBatch NativeBatch
open NativeOpenExecution Turing Turing.MultiTapeTM
open scoped NNReal ENNReal
namespace CslibFrontierTests.NativeRetentionUpper

private def data : GuardedStartup.Input := ⟨⟨⟨[], [], [], 1, []⟩, 0, 0, [true]⟩, 0⟩
private def limits : Limits 0 := ⟨fun _ => 1, by intro i; exact Fin.elim0 i, 0, 0⟩
private theorem valid : Valid data.startup.system := by
  constructor <;> intros <;> norm_num [data, elements, ground]

/-- This is a cost conclusion for the constructed native machine, for any source
sampler and original hidden seed, including unbounded hidden-state spaces. -/
example : ∃ (tapes : ℕ) (R : Type) (_ : Finite R)
    (program : MultiTapePTM tapes Bool R Unit), ∀ (sample : Sampler 0 ℕ) (seed : ℕ),
      Quantitative.expected limits sample program Trace.charge 1
        ⟨program.initialConfig (GuardedStartup.encoding data),
          ⟨ConcurrentBatch.initial seed, []⟩⟩ = 0 := by
  let impl := BatchPlanner.controller 0 1
  let tapes := impl.tapes
  let R := impl.Controls
  have hR := impl.finite
  let program := impl.program
  have hp := BatchUpper.upper_controller (n := 0) 1
  refine ⟨tapes, R, hR, program, ?_⟩
  intro sample seed
  have h := hp ℕ limits sample data seed 1 rfl (by decide) (by decide)
    (by norm_num) (by intro i; exact Fin.elim0 i) (by norm_num [data, limits])
    rfl (by decide) valid 1 0 (by norm_num [instanceOf, ground, data])
    ⟨1, by norm_num⟩ (by norm_num) 0
    (by intro t ht; change t < 0 at ht; omega)
    (by intro t ht; change t < 0 at ht; omega)
  obtain ⟨_, htail, _, _⟩ := h
  exact le_antisymm (by simpa only [limits, ENNReal.coe_zero, zero_mul] using htail) bot_le

end CslibFrontierTests.NativeRetentionUpper
