/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Languages.Probabilistic.UniformNat
public import CslibFrontier.Probability.DDGTree.Rejection

/-!
# Capped block-rejection programs in `ProbComp`

Sequential (`sampleBlockTrials`) and single-tape (`sampleSeededTrials`) `ProbComp` programs for
capped fair-bit block rejection (`Cslib.Probability.BlockRejectionSpec`). Both programs denote
`BlockRejectionSpec.runTrials`: they accept with target-proportional probabilities, fail with
probability `rejectProb ^ trials`, and complete with a fallback element (`sampleBlockCapped`) within
statistical distance `(rejectProb ^ trials).toReal` of the target distribution.

Specializing to `dyadicFinRejectionSpec n` (`sampleUniformFinTrials`) gives an exact-on-acceptance
bounded-index program over fair bits whose rejection probability is at most `(1 / 2) ^ trials` for
every `n ≥ 1`.

## Main definitions

* `Cslib.ProbComp.sampleBlockTrials`: sequential `trials`-round rejection loop in `ProbComp`.
* `Cslib.ProbComp.sampleSeededTrials`: single-tape `trials * width`-bit realization of the same law.
* `Cslib.ProbComp.sampleBlockCapped`: fallback completion in `ProbComp α`.
* `Cslib.ProbComp.sampleUniformFinTrials`: capped dyadic rejection sampler for `Fin n`.

## Main results

* `Cslib.ProbComp.eval_sampleBlockTrials`, `Cslib.ProbComp.eval_sampleSeededTrials`: both `ProbComp`
  programs evaluate to `BlockRejectionSpec.runTrials`.
* `Cslib.ProbComp.eval_sampleBlockCapped`: fallback program evaluates to `runCapped`.
* `Cslib.ProbComp.eval_sampleUniformFinTrials_none_le`: `t`-trial failure probability is at most
  `(1 / 2) ^ t` for `n ≥ 1`.
-/

public section

open scoped ENNReal

namespace Cslib.ProbComp

open BitString Probability

/-- Sequential `ProbComp` program running at most `trials` independent `spec.width`-bit rejection
rounds, stopping as soon as a block is accepted. -/
@[expose] noncomputable def sampleBlockTrials {α : Type} (spec : BlockRejectionSpec α) :
    ℕ → ProbComp (Option α)
  | 0 => pure none
  | t + 1 => do
      let block ← BitString.sampleList spec.width
      match spec.attempt block with
      | some a => pure (some a)
      | none => sampleBlockTrials spec t

/-- Single-tape `ProbComp` program drawing `trials * spec.width` fair bits at once and decoding at
most `trials` blocks via `BlockRejectionSpec.decodeTrials`. -/
@[expose] noncomputable def sampleSeededTrials {α : Type} (spec : BlockRejectionSpec α)
    (trials : ℕ) : ProbComp (Option α) :=
  spec.decodeTrials trials <$> BitString.sampleList (trials * spec.width)

/-- Capped fallback `ProbComp` program returning `fallback` if all `trials` blocks reject. -/
@[expose] noncomputable def sampleBlockCapped {α : Type} (spec : BlockRejectionSpec α)
    (fallback : α) (trials : ℕ) : ProbComp α :=
  (fun o => o.getD fallback) <$> sampleSeededTrials spec trials

theorem eval_sampleSeededTrials {α : Type} (spec : BlockRejectionSpec α) (trials : ℕ) :
    ProbComp.eval (sampleSeededTrials spec trials) = spec.runTrials trials := by
  simp only [sampleSeededTrials, ProbComp.eval_map, BitString.eval_sampleList,
    BlockRejectionSpec.runTrials]

theorem eval_sampleBlockTrials {α : Type} (spec : BlockRejectionSpec α) (trials : ℕ) :
    ProbComp.eval (sampleBlockTrials spec trials) = spec.runTrials trials := by
  induction trials with
  | zero => simp [sampleBlockTrials]
  | succ t ih =>
    rw [sampleBlockTrials, ProbComp.eval_bind, BitString.eval_sampleList,
      BlockRejectionSpec.runTrials_succ, BlockRejectionSpec.singleLaw, PMF.bind_map]
    congr 1
    funext block
    simp only [Function.comp_apply]
    cases spec.attempt block with
    | some a => simp [ProbComp.eval_pure]
    | none => exact ih

theorem eval_sampleBlockTrials_eq_seeded {α : Type} (spec : BlockRejectionSpec α) (trials : ℕ) :
    ProbComp.eval (sampleBlockTrials spec trials) =
      ProbComp.eval (sampleSeededTrials spec trials) := by
  rw [eval_sampleBlockTrials, eval_sampleSeededTrials]

theorem eval_sampleBlockCapped {α : Type} (spec : BlockRejectionSpec α) (fallback : α)
    (trials : ℕ) :
    ProbComp.eval (sampleBlockCapped spec fallback trials) = spec.runCapped fallback trials := by
  simp only [sampleBlockCapped, ProbComp.eval_map, eval_sampleSeededTrials,
    BlockRejectionSpec.runCapped]

/-- Capped dyadic fair-bit rejection sampler for `Fin n` running `trials` blocks of
`Nat.log 2 n + 1` bits. -/
@[expose] noncomputable def sampleUniformFinTrials (n trials : ℕ) : ProbComp (Option (Fin n)) :=
  sampleSeededTrials (dyadicFinRejectionSpec n) trials

theorem eval_sampleUniformFinTrials (n trials : ℕ) :
    ProbComp.eval (sampleUniformFinTrials n trials) =
      (dyadicFinRejectionSpec n).runTrials trials :=
  eval_sampleSeededTrials (dyadicFinRejectionSpec n) trials

theorem eval_sampleUniformFinTrials_none_le (n : ℕ) [NeZero n] (trials : ℕ) :
    ProbComp.eval (sampleUniformFinTrials n trials) none ≤ (1 / 2 : ℝ≥0∞) ^ trials := by
  rw [eval_sampleUniformFinTrials]
  exact runTrials_dyadicFinRejectionSpec_none_le n trials

theorem eval_sampleUniformFinTrials_some (n : ℕ) [NeZero n] (trials : ℕ) (i : Fin n) :
    ProbComp.eval (sampleUniformFinTrials n trials) (some i) =
      (1 - (dyadicFinRejectionSpec n).rejectProb ^ trials) *
        PMF.uniformOfFintype (Fin n) i := by
  rw [eval_sampleUniformFinTrials]
  exact BlockRejectionSpec.runTrials_some_of_singleLaw
    (singleLaw_dyadicFinRejectionSpec_some n) trials i

end Cslib.ProbComp
