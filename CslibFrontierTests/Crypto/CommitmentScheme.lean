/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Commitment.Scheme

/-!
# Tests for typed commitment schemes

`openScheme` commits to a bit by publishing nothing and opening with the bit itself. It is correct
and perfectly hiding, so every adversary has hiding advantage `0`. It is not binding: one adversary
opens the empty commitment to both bits with probability `1`.
-/

namespace CslibFrontierTests.Crypto.CommitmentScheme

open Cslib Cslib.Crypto Cslib.Crypto.Commitment

/-- Commit to a bit with an empty commitment; the opening is the bit. -/
def openScheme : Scheme Unit Bool Unit Bool where
  keyGen := pure ()
  commit _ m := pure ((), m)
  verify _ m _ o := m == o

example : openScheme.Correct := by
  intro _ _ m c o hco
  simp only [openScheme, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hco
  simp [openScheme, hco.2]

/-- Every key of `openScheme` is perfectly hiding: the commitment is always `()`. -/
theorem openScheme_perfectlyHidingAt (k : Unit) : openScheme.PerfectlyHidingAt k := fun _ _ => by
  simp [Scheme.commitment, openScheme]

/-- Every adversary, with any saved-state type, has hiding advantage `0` against `openScheme`. -/
example {σ : Type} (A : TwoStage Unit (MessagePair Bool) Unit Bool σ) :
    Experiment.advantage (openScheme.hidingExperiment A false)
      (openScheme.hidingExperiment A true) = 0 := by
  refine le_antisymm ((openScheme.advantage_hidingExperiment_le (fun _ => false)
    (fun k _ => openScheme_perfectlyHidingAt k) A).trans ?_) zero_le
  simp [Experiment.succProbability, Game.succProbability, openScheme]

/-- Opening the empty commitment to both bits breaks binding with probability `1`. -/
example :
    Experiment.succProbability
      (openScheme.bindingExperiment fun _ => pure ⟨(), false, false, true, true⟩) = 1 := by
  simp [Scheme.bindingExperiment, Scheme.isBindingCollision, openScheme,
    Experiment.succProbability, Game.succProbability]

end CslibFrontierTests.Crypto.CommitmentScheme
