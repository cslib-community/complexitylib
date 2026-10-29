/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Commitment
import Complexity.Crypto.Negligible.Basic
import Complexity.Tactic.PPT

/-!
# Tests for stateful-receiver commitment hiding

A bit-leaking commitment function is rejected by an explicit randomized stateful
`CommitmentReceiver`: in the first stage, the receiver samples a uniform mask bit `m`, sends
`r = [m]`, chooses opposite challenge bits `(m, !m)`, and stores `[m]` in its private state; in the
second stage, it XORs the leaked commitment bit with the saved state bit `m` to recover the
experiment selector `bit` with certainty. Because the committed bit itself is `m ^^ bit` (uniformly
distributed without `state`), this exercises both randomized stage-1 selection and state transfer to
stage 2. We also exercise the plain `ComputableInPolyTime` and `IsPPT` certificates.
-/

namespace ComplexityTests.Crypto.Commitment

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- Deliberately insecure commitment that outputs the committed bit `b` in the clear. -/
def leakCommit (_ : List Bool) (b : Bool) (_ : List Bool) : List Bool :=
  [b]

theorem polyTime_leakCommit :
    ComputableInPolyTime (fun p : List Bool × Bool × List Bool => leakCommit p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBool encBits)) encBits := by
  dsimp only [leakCommit]
  fun_prop

/-- A genuinely randomized stateful commitment receiver: it samples a uniform mask bit `m`, uses
`[m]` as the challenge string `r`, chooses opposite challenge bits `(m, !m)`, saves `[m]` in its
private state, and XORs the commitment bit with the saved state bit in stage 2. -/
noncomputable def statefulReceiver : CommitmentReceiver where
  choose _ _ := do
    let m ← ProbComp.uniform Bool
    pure (([m], (m, !m)), [m])
  guess _ state c := pure (c.headD false ^^ state.headD false)

theorem isPPT_statefulReceiver : statefulReceiver.IsPPT := by
  constructor <;> dsimp only [statefulReceiver] <;> ppt

-- Runtime certificates for the two-stage commitment-hiding experiment, Naor PRG distinguisher,
-- `naorCommit`, and `naorVerify`.
example (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair encBits encBool)) encBool
      (fun p => commitmentHidingGame leakCommit statefulReceiver p.2.1 p.2.2 p.1) ∧
    IsPPT encBool (fun n aux => commitmentHidingGame leakCommit statefulReceiver aux bit n) ∧
    IsPPT encBool (naorReceiverDistinguisher statefulReceiver (fun _ => []) bit) ∧
    ComputableInPolyTime
      (fun p : List Bool × Bool × List Bool => naorCommit id p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBool encBits)) encBits ∧
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × Bool × List Bool =>
        naorVerify id p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (encPair encUnary (encPair encBits (encPair encBits (encPair encBool encBits)))) encBool :=
  ⟨isPPTOn_commitmentHidingGame polyTime_leakCommit isPPT_statefulReceiver,
   isPPT_commitmentHidingGame polyTime_leakCommit isPPT_statefulReceiver bit,
   isPPT_naorReceiverDistinguisher isPPT_statefulReceiver (by fun_prop) bit,
   computableInPolyTime_naorCommit (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop),
   computableInPolyTime_naorVerify
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)⟩

/-- The randomized stateful receiver recovers the challenge selector `bit` with certainty at every
security parameter `n`. -/
theorem eval_commitmentHidingGame_leakCommit (bit : Bool) (n : ℕ) :
    ProbComp.eval (commitmentHidingGame leakCommit statefulReceiver [] bit n) = PMF.pure bit := by
  cases bit <;>
    simp only [commitmentHidingGame, statefulReceiver, leakCommit, ProbComp.eval_bind,
      ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind, ↓reduceIte,
      List.headD_cons, Bool.false_eq_true, bne_self_eq_false, Bool.not_bne_self, PMF.bind_const]

/-- `leakCommit` fails `StatefulHiding` because `statefulReceiver` achieves constant distinguishing
advantage `1`. -/
theorem not_statefulHiding_leakCommit : ¬ StatefulHiding leakCommit := by
  intro hsecure
  have hnegl := hsecure.empty statefulReceiver isPPT_statefulReceiver
  simp only [eval_commitmentHidingGame_leakCommit] at hnegl
  have hone : Game.advantage (PMF.pure false) (PMF.pure true) = 1 := by
    simp [Game.advantage, Game.succProbability]
  rw [hone] at hnegl
  exact not_negligible_const one_ne_zero hnegl

end ComplexityTests.Crypto.Commitment
