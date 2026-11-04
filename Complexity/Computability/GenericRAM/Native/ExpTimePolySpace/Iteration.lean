/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native.ExpTimePolySpace

/-!
# Polynomially many exponential-time calls in polynomial space

A native iteration retains time `2 ^ E` times a polynomial and polynomial space when its number
of rounds and live states have polynomial bounds, and every reached round has that same time
exponent in the original input. The callbacks may depend on earlier results. The iterator charges
one maximum round workspace, so the number of rounds does not multiply its space bound.

## Main results

* `Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace.iterate_of_bounds`: iteration under
  polynomial bounds on the round count, initialization, reached states and round resources,
  without increasing the common exponent.
-/

public section

namespace Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace

open Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {encState : β ↪ List Bool}
  {count : α → ℕ} {init : α → β} {step : β → β} {E R Q B : α → ℕ}

/-- **Polynomially many adaptive calls preserve the common exponential time factor.** The
round count and state bounds are measured against the original encoded input. Every reached
round, including the terminal state, must use time at most `R a * 2 ^ E a` and space at most
`Q a`, where `R`, `Q` and the live-state bound `B` are polynomially bounded. -/
theorem iterate_of_bounds (cn : NativeCertificate count enc encNat)
    (ci : NativeCertificate init enc encState) (cs : NativeCertificate step encState encState)
    (hcn : cn.IsPolynomial) (hci : ci.IsPolynomial)
    (hcount : PolyBounded (fun a => (enc a).length) count)
    (hR : PolyBounded (fun a => (enc a).length) R)
    (hQ : PolyBounded (fun a => (enc a).length) Q)
    (hB : PolyBounded (fun a => (enc a).length) B)
    (ht : ∀ a j, j ≤ count a → cs.time (step^[j] (init a)) ≤ R a * 2 ^ E a)
    (hs : ∀ a j, j ≤ count a → cs.space (step^[j] (init a)) ≤ Q a)
    (hb : ∀ a j, j ≤ count a → (encState (step^[j] (init a))).length ≤ B a) :
    (NativeCertificate.iterate cn ci cs).ExpTimePolySpace E := by
  have hclock : PolyBounded (fun a => (enc a).length)
      (fun a => (encNat (count a)).length) := (cn.polyTime hcn).polyBounded_length
  let timeFactor a := cn.time a + ci.time a +
    (count a + 1) * (R a + B a + ((encNat (count a)).length + 1) ^ 2)
  let spaceFactor a := cn.space a + ci.space a + Q a + B a + (encNat (count a)).length
  have htimeFactor : PolyBounded (fun a => (enc a).length) timeFactor :=
    (hcn.1.add hci.1).add
      ((hcount.add (.const 1)).mul ((hR.add hB).add ((hclock.add (.const 1)).pow 2)))
  have hspaceFactor : PolyBounded (fun a => (enc a).length) spaceFactor :=
    (((hcn.2.add hci.2).add hQ).add hB).add hclock
  have htime (a : α) : (NativeCertificate.iterate cn ci cs).time a ≤ timeFactor a * 2 ^ E a := by
    have hmaxT := maxRoundTime_le cs (count a) (init a) (ht a)
    have hmaxB := maxStateLength_le encState step (count a) (init a) (hb a)
    have hbody : maxRoundTime cs (count a) (init a) +
        maxStateLength encState step (count a) (init a) +
        ((encNat (count a)).length + 1) ^ 2 ≤
          (R a + B a + ((encNat (count a)).length + 1) ^ 2) * 2 ^ E a := by
      calc _ ≤ R a * 2 ^ E a + B a * 2 ^ E a +
            ((encNat (count a)).length + 1) ^ 2 * 2 ^ E a :=
            Nat.add_le_add (Nat.add_le_add hmaxT
              (hmaxB.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))))
              (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
        _ = _ := by ring
    rw [iterate_time]
    calc _ ≤ (cn.time a + ci.time a) * 2 ^ E a +
          (count a + 1) * ((R a + B a + ((encNat (count a)).length + 1) ^ 2) * 2 ^ E a) :=
          Nat.add_le_add (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
            (Nat.mul_le_mul_left _ hbody)
      _ = _ := by dsimp only [timeFactor]; ring
  have hspace (a : α) : (NativeCertificate.iterate cn ci cs).space a ≤ spaceFactor a := by
    have hmaxS := maxRoundSpace_le cs (count a) (init a) (hs a)
    have hmaxB := maxStateLength_le encState step (count a) (init a) (hb a)
    simp only [iterate_space, spaceFactor]
    omega
  obtain ⟨ct, dt, htFactor⟩ := htimeFactor.exists_le
  obtain ⟨cq, dq, hqFactor⟩ := hspaceFactor.exists_le
  refine ⟨ct + cq, dt + dq, fun a => ⟨?_, ?_⟩⟩
  · calc _ ≤ timeFactor a * 2 ^ E a := htime a
      _ ≤ (ct * ((enc a).length + 1) ^ dt) * 2 ^ E a :=
          Nat.mul_le_mul_right _ (htFactor a)
      _ ≤ ((ct + cq) * ((enc a).length + 1) ^ (dt + dq)) * 2 ^ E a :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.le_add_right _ _)
            (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_right _ _)))
      _ = _ := by ring
  · exact (hspace a).trans ((hqFactor a).trans
      (Nat.mul_le_mul (Nat.le_add_left _ _)
        (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left _ _))))

end Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace
