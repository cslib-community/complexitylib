/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators

/-!
# Replay verdicts as verifiers

Replaying a fixed fair-coin machine on an instance with a string of saved coins, and testing
whether the output is `[true]`, is a verifier on encoded pairs `(a, w)`. It runs in linear time and
linear space in the encoded pair, because replay itself does
(`Turing.MultiTapePTM.computableInDegree_runClosedCoins`) and the replayed output is no longer
than the replay time. Both readings of a time-bounded machine as a verifier use it: the
certificate as a computation path of a nondeterministic machine
(`Cslib.Complexity.exists_verifier_of_mem_NTIME`), and the random string of a probabilistic one
(`Cslib.Complexity.exists_verifier_of_mem_PromiseBPTIME`).

## Main results

* `Turing.MultiTapePTM.computableInO_decide_runClosedCoins`: the replay verdict is computable in
  linear time and space in the encoded pair.
* `Turing.MultiTapePTM.computableInPolyTime_decide_runClosedCoins`: the replay verdict is
  polynomial-time.
-/

public section

namespace Turing.MultiTapePTM

open MultiTapeTM

variable {k : ℕ} {State : Type} [Finite State] {α : Type} {enc : α ↪ List Bool}

/-- **Replay verdicts are linear-time verifiers.** Replaying `machine` on `enc a` with the saved
coins `w`, and testing whether the output is `[true]`, is computable in linear time and linear space
in the encoded pair `(a, w)`. -/
theorem computableInO_decide_runClosedCoins (machine : MultiTapePTM k Bool State) :
    ComputableInO (fun p : α × List Bool => decide (machine.runClosedCoins p.2 (enc p.1) = [true]))
      (encPair enc encBits) encBool (fun p => (encPair enc encBits p).length)
      (fun p => (encPair enc encBits p).length) := by
  -- replay the coins, then compare the output with `[true]`
  have hswap : ComputableInO (fun p : α × List Bool => (p.2, enc p.1)) (encPair enc encBits)
      (encPair encBits encBits)
      (fun p => (encPair enc encBits p).length +
        ((encPair enc encBits p).length + (enc p.1).length))
      (fun p => (encPair enc encBits p).length +
        ((encPair enc encBits p).length + (enc p.1).length)) :=
    (ComputableInO.snd enc encBits).prod
      ((ComputableInO.of_eq (f := fun x : α => enc x) (encIn := enc) (encMid := encBits)
        fun _ => rfl).comp (ComputableInO.fst enc encBits))
  have hrun := (ComputableInO.of_linear (computableInDegree_runClosedCoins machine)).comp hswap
  obtain ⟨cr, hcr⟩ := hrun.length_le_time
  have heq := ComputableInO.eqWords.comp ((ComputableInO.const (encIn := encPair enc encBits)
    (encMid := encBits) [true]).prod hrun)
  have hfun : ((fun p : List Bool × List Bool => decide (p.1 = p.2)) ∘
      fun p : α × List Bool => ([true], ((fun q : List Bool × List Bool =>
        machine.runClosedCoins q.1 q.2) ∘ fun p : α × List Bool => (p.2, enc p.1)) p)) =
      fun p => decide (machine.runClosedCoins p.2 (enc p.1) = [true]) := by
    funext p
    simp [eq_comm]
  rw [hfun] at heq
  -- every part is linear in the encoded pair, including the replayed output
  have hbound (p : α × List Bool) :
      (encPair enc encBits p).length + ((encPair enc encBits p).length +
        ((encPair enc encBits p).length + (enc p.1).length) +
        (encPair encBits encBits (p.2, enc p.1)).length) +
      2 * ((machine.runClosedCoins p.2 (enc p.1)).length + 2) ≤
        (9 + 10 * cr) * ((encPair enc encBits p).length + 1) := by
    have hc := hcr p
    simp only [Function.comp_apply, encBits_apply] at hc
    have hle : (enc p.1).length ≤ (encPair enc encBits p).length := by
      simp only [encPair_apply, List.length_append, length_frame, encBits_apply]
      omega
    have hsw : (encPair encBits encBits (p.2, enc p.1)).length ≤
        2 * (encPair enc encBits p).length := by
      simp only [encPair_apply, List.length_append, length_frame, encBits_apply]
      omega
    generalize (encPair enc encBits p).length = N at *
    generalize (machine.runClosedCoins p.2 (enc p.1)).length = R at *
    generalize (encPair encBits encBits (p.2, enc p.1)).length = W at *
    have hR : R ≤ cr * (5 * N + 1) := hc.trans (Nat.mul_le_mul_left cr (by omega))
    nlinarith
  refine heq.mono (9 + 10 * cr) (fun p => ?_) fun p => ?_
  · have := hbound p
    simp only [Function.comp_apply, List.length_singleton] at this ⊢
    nlinarith
  · have := hbound p
    simp only [Function.comp_apply, List.length_singleton] at this ⊢
    omega

/-- **Replay verdicts are polynomial-time verifiers.** -/
theorem computableInPolyTime_decide_runClosedCoins (machine : MultiTapePTM k Bool State) :
    ComputableInPolyTime
      (fun p : α × List Bool => decide (machine.runClosedCoins p.2 (enc p.1) = [true]))
      (encPair enc encBits) encBool :=
  (computableInO_decide_runClosedCoins machine).computableInPolyTime
    (.of_forall_le 1 1 fun _ => by simp) (.of_forall_le 1 1 fun _ => by simp)

end Turing.MultiTapePTM
