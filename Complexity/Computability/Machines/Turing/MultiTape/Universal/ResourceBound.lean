/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Machine
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial resource bounds for the universal simulator

The resource functions of Christian Reitwiessner's universal simulator admit explicit polynomial
bounds in the encoded description length, encoded input length, clock length, and number of
simulated steps. These estimates are shared by unary-clock polynomial-time simulation and the
time-hierarchy construction.

## Main results

* `Turing.MultiTapeTM.Universal.computableInO_universal`: a plain native machine certificate
  for the strengthened time and space bounds, including a zero clock.

* `Turing.MultiTapeTM.Universal.runBound_mono`: the space bound grows with the number of steps.
* `Turing.MultiTapeTM.Universal.universal_bounds_le`: for `D, N, L ≤ B` and `1 ≤ J`, the time
  expression is at most `100000 * (B + 1) ^ 4 * J ^ 2` and the space bound is at most
  `200 * (B + 1) ^ 2 * J`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.Universal

/-- The universal simulator's space bound grows with the number of simulated steps. -/
theorem runBound_mono {D N t t' : ℕ} (h : t ≤ t') : runBound D N t ≤ runBound D N t' := by
  unfold runBound ctxBound cfgBound tapeBound
  gcongr

/-- **The resources of the universal run.** If the encoded description, the encoded input and the
number of digits `L` of the clock have length at most `B`, the time of the universal function on
`J ≥ 1` steps is `O((B + 1) ^ 4 * J ^ 2)` and its space `O((B + 1) ^ 2 * J)`.
Here `B` includes the encoded input length, so this is not a fixed-machine quadratic-time
simulation bound when the input length varies. The buffered logarithmic-overhead simulation
requires a different tape representation. -/
theorem universal_bounds_le {D N J B L : ℕ} (hD : D ≤ B) (hN : N ≤ B) (hL : L ≤ B) (hJ : 1 ≤ J) :
    (J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2) ≤ 100000 * (B + 1) ^ 4 * J ^ 2 ∧
      runBound D N J ≤ 200 * (B + 1) ^ 2 * J := by
  set M := B + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have hDM : D + 1 ≤ M := by omega
  have hNM : N + 1 ≤ M := by omega
  have hMJ : M ≤ M * J := Nat.le_mul_of_pos_right _ hJ
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow two_ne_zero _
  have hM2J : M ^ 2 ≤ M ^ 2 * J := Nat.le_mul_of_pos_right _ hJ
  have htape : tapeBound D J ≤ 36 * M * J := by
    unfold tapeBound
    nlinarith
  have hcfg : cfgBound D N J ≤ 80 * M ^ 2 * J := by
    unfold cfgBound
    have : D * (2 * tapeBound D J + 1) ≤ M * (72 * M * J + 1) :=
      Nat.mul_le_mul (by omega) (by linarith)
    nlinarith
  have hctx : ctxBound D N J ≤ 89 * M ^ 2 * J := by
    unfold ctxBound
    nlinarith
  have hrun : runBound D N J ≤ 200 * M ^ 2 * J := by
    unfold runBound
    have : J * (2 * D + 1) ≤ J * (2 * M) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  refine ⟨?_, hrun⟩
  have hM34 : M ^ 3 ≤ M ^ 4 * J :=
    (Nat.pow_le_pow_right hM1 (by omega)).trans (Nat.le_mul_of_pos_right _ hJ)
  have hstep : stepBound D N J ≤ 190 * M ^ 4 * J := by
    unfold stepBound
    have hfirst : (2 * D + 1) * (D + 1) * (ctxBound D N J + 1) ≤ 180 * M ^ 4 * J := by
      calc _ ≤ (2 * M) * M * (90 * M ^ 2 * J) :=
            Nat.mul_le_mul (Nat.mul_le_mul (by omega) hDM) (by nlinarith)
        _ = _ := by ring
    have hbits := length_encNat_le (N + 1)
    have hdigits : ((encNat (N + 1)).length + 1) ^ 2 ≤ (2 * M) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hlookup : (N + 1) * ((encNat (N + 1)).length + 1) ^ 2 ≤
        4 * M ^ 3 := by
      calc _ ≤ M * (4 * M ^ 2) :=
            Nat.mul_le_mul hNM (by nlinarith)
        _ = _ := by ring
    nlinarith
  have hM4 : M ^ 2 * J ≤ M ^ 4 * J :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hM1 (by omega))
  have hL2 : (L + 1) ^ 2 ≤ M ^ 4 * J :=
    (Nat.pow_le_pow_left (by omega) 2).trans (hM2J.trans hM4)
  have hsum : stepBound D N J + runBound D N J + (L + 1) ^ 2 ≤ 391 * M ^ 4 * J := by
    nlinarith
  calc (J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2)
      ≤ (2 * J) * (391 * M ^ 4 * J) := Nat.mul_le_mul (by omega) hsum
    _ ≤ 100000 * M ^ 4 * J ^ 2 := by nlinarith [Nat.zero_le (M ^ 4 * J ^ 2)]


/-- A plain native machine computes the clocked universal function within a quartic factor in
the complete encoded input length and a quadratic factor in the number of simulated steps.
The statement includes a zero clock. Its size factor includes the simulated input and binary
clock, so it does not assert fixed-machine quadratic simulation as those inputs vary. -/
theorem computableInO_universal :
    ComputableInO universal eIn eOut
      (fun i => ((eIn i).length + 1) ^ 4 * (i.2.2 + 1) ^ 2)
      (fun i => ((eIn i).length + 1) ^ 2 * (i.2.2 + 1)) := by
  refine computableTidilyInO_universal.computableInO.mono 100001 (fun i => ?_) (fun i => ?_)
  all_goals
    have hD : descLen i.1 ≤ (eIn i).length := length_le_encPair_left _ _ i
    have hN : (encList encUnary i.2.1).length ≤ (eIn i).length :=
      (length_le_encPair_left _ _ i.2).trans (length_le_encPair_right _ _ i)
    have hL : (encNat i.2.2).length ≤ (eIn i).length :=
      (length_le_encPair_right _ _ i.2).trans (length_le_encPair_right _ _ i)
    obtain ⟨ht, hs⟩ := universal_bounds_le (J := i.2.2 + 1) hD hN hL (by omega)
    have hstep := stepBound_mono (D := descLen i.1) (N := (encList encUnary i.2.1).length)
      le_rfl le_rfl (Nat.le_add_right i.2.2 1)
    have hrun := runBound_mono (D := descLen i.1) (N := (encList encUnary i.2.1).length)
      (Nat.le_add_right i.2.2 1)
  · have htime : (i.2.2 + 1) * (stepBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
        runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
        ((encNat i.2.2).length + 1) ^ 2) ≤
        100000 * ((eIn i).length + 1) ^ 4 * (i.2.2 + 1) ^ 2 :=
      (Nat.mul_le_mul (show i.2.2 + 1 ≤ i.2.2 + 1 + 1 by omega)
        (Nat.add_le_add_right (Nat.add_le_add hstep hrun) _)).trans ht
    have hinput : ((eIn i).length + 1) ^ 2 ≤
        ((eIn i).length + 1) ^ 4 * (i.2.2 + 1) ^ 2 :=
      (Nat.pow_le_pow_right (by omega) (show 2 ≤ 4 by omega)).trans
        (Nat.le_mul_of_pos_right _ (by positivity))
    nlinarith
  · have hinput : (eIn i).length ≤ ((eIn i).length + 1) ^ 2 * (i.2.2 + 1) :=
      (Nat.le_succ _).trans ((Nat.le_self_pow two_ne_zero _).trans
        (Nat.le_mul_of_pos_right _ (by omega)))
    nlinarith

end Turing.MultiTapeTM.Universal
