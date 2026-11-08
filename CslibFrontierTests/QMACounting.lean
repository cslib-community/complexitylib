/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.QMA.Counting
import CslibFrontierTests.QMA

/-! `QMA ⊆ PP`: the trace gap of a concrete verifier, its acceptance operator on basis witnesses,
and the containments applied to a language in `QMA`. -/

namespace ComplexityTests.QMACounting

open Cslib Cslib.Quantum Cslib.Complexity Turing.MultiTapeTM
open ComplexityTests.QMA

/-! ### The trace gap of `readWitness` -/

-- On the empty input, `readWitness` measures its one witness qubit, so its acceptance operator is
-- the projection onto `|1⟩`, with no Hadamard gates: `tr(Q^0) = 2` (the dimension) and
-- `tr(Q^d) = 1` for `d ≥ 1`. The trace gaps count the closed paths through `|1⟩` alone.
example : readWitness.traceGap [] 0 = 2 := by decide
example : readWitness.traceGap [] 1 = 1 := by decide
example : readWitness.traceGap [] 3 = 1 := by decide

-- The trace separates yes from no: on the input `[true]` the acceptance operator is the identity
-- (every witness is accepted), so `tr(Q^d) = 2`; on `[false]` it is zero, so `tr(Q^d) = 0` for
-- `d ≥ 1`, matching the soundness bound `2^m s^d` with `s = 0`.
example : readWitness.traceGap [true] 2 = 2 := by decide
example : readWitness.traceGap [false] 2 = 0 := by decide
example (d : ℕ) : (readWitness.traceGap [false] (d + 1) : ℝ) ≤ 0 := by
  refine (readWitness.traceGap_le [false] (s := 0) (fun ψ _ => ?_) (d + 1)).trans_eq (by simp)
  refine (UniformVerifierFamily.acceptProb_eq_zero_of_forall_ket _ _ (fun z => ?_) ψ).le
  rw [acceptProb_readWitness_ket]
  rfl

-- The quadratic form of the acceptance operator is the acceptance probability.
example : RCLike.re (inner ℂ (ket fun _ => true)
    (readWitness.acceptOp [] (ket fun _ : Fin (readWitness.witnessLength [].length) => true))) =
      1 := by
  refine (readWitness.re_inner_acceptOp [] _).trans ?_
  rw [acceptProb_readWitness_ket]
  rfl

-- Restricting a basis state to a set of outcomes containing it keeps its whole weight.
example : ‖restrictOutcomes {true} (ket true)‖ ^ 2 = 1 := by
  rw [norm_restrictOutcomes_sq, measureProb_ket]
  simp

/-! ### The containments -/

-- `QMA ⊆ PP`.
example : HeadOrEmpty ∈ PP encBits := QMA_subset_PP headOrEmpty_mem_QMA

-- `QMA(1, 0) ⊆ PP` for promise problems, without error reduction.
example : PromiseProblem.ofSet HeadOrEmpty ∈ promiseClass (PP encBits) :=
  PromiseQMA_subset_promiseClass_PP (by norm_num) headOrEmpty_mem_PromiseQMA

-- Any constant gap suffices, e.g. completeness `0.51` and soundness `0.5`.
example (Q : PromiseProblem (List Bool))
    (hQ : Q ∈ PromiseQMA (fun _ => 51 / 100) (fun _ => 1 / 2) encBits) :
    Q ∈ promiseClass (PP encBits) :=
  PromiseQMA_subset_promiseClass_PP (by norm_num) hQ

/-! ### An inverse-polynomial gap -/

-- Completeness `1` and soundness `s n = 1 - 1 / (n + 1)`, with `q n = n + 1` and
-- `σ n = 2 n = 2 q n s n` exactly.
theorem mul_one_sub_inv (n : ℕ) : ((n : ℝ) + 1) * (1 - 1 / ((n : ℝ) + 1)) = n := by
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem mem_promiseClass_PP_of_gap (Q : PromiseProblem (List Bool))
    (hQ : Q ∈ PromiseQMA (fun _ => 1) (fun n => 1 - 1 / ((n : ℝ) + 1)) encBits) :
    Q ∈ promiseClass (PP encBits) := by
  refine PromiseQMA_subset_promiseClass_PP_of_gap (q := fun n => n + 1) (σ := fun n => 2 * n)
    (by fun_prop) (by fun_prop) (fun n => ?_) (fun n => ?_) (fun n => ?_) hQ
  all_goals
    have := mul_one_sub_inv n
    push_cast
    linarith

-- The verifier `readWitness`, which places `HeadOrEmpty` in `QMA(1, 0)`, meets this gap.
example : PromiseProblem.ofSet HeadOrEmpty ∈ promiseClass (PP encBits) :=
  mem_promiseClass_PP_of_gap _ (PromiseQMA_mono (fun _ => le_rfl)
    (fun n => sub_nonneg.2 (div_le_one_of_le₀ (by linarith) (by positivity)))
    headOrEmpty_mem_PromiseQMA)

end ComplexityTests.QMACounting
