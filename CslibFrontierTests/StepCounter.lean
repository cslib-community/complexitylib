/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.StepCounter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.StepCounter.Unary

/-! Binary-input existence, zero/positive signal counts, and native countdown boundary cases. -/

namespace CslibFrontierTests.StepCounter

open Turing MultiTapeMachine MultiTapeTM

private noncomputable def counter : StepCounter := Classical.choice exists_stepCounter

-- Instantiate the complete finite machine, rather than assume a possibly empty specification.
example : Finite counter.State := inferInstance

example : counter.signalTimes 0 = ∅ :=
  (Set.ncard_eq_zero (counter.signalTimes_finite 0)).mp (counter.signal_count 0)

example : (counter.signalTimes 1).ncard = 1 := counter.signal_count 1

example : (counter.signalTimes 3).ncard = 3 := counter.signal_count 3

example (n : ℕ) :
    counter.machine.RunsInTime (encNat n) (counter.timeConstant * (n + 1)) :=
  counter.runsInTime n

example (n t : ℕ) (h : t ∈ counter.signalTimes n) :
    t + 1 ∉ counter.signalTimes n := counter.leaves_signal n t h

-- The prepared controller exposes actual native state times, including all post-halting times.
example (input : List Bool) (t : ℕ) :
    (StepCounter.countdown.runFrom
      (wordsCfg input (some StepCounter.countdown.q₀) (fun _ => []) []) t).state ≠
        some StepCounter.signalState := by
  have h := StepCounter.countdown_signal_iff input 0 t
  simp only [List.replicate_zero] at h
  intro hs
  obtain ⟨i, hi, _⟩ := h.mp hs
  omega

example (input : List Bool) :
    (StepCounter.countdown.runFrom
      (wordsCfg input (some StepCounter.countdown.q₀) (fun _ => [true]) []) 1).state =
        some StepCounter.signalState :=
  (StepCounter.countdown_signal_iff input 1 1).mpr ⟨0, by omega, rfl⟩

example (input : List Bool) (t : ℕ) :
    (StepCounter.countdown.runFrom
      (wordsCfg input (some StepCounter.countdown.q₀) (fun _ => [true, true, true]) []) t).state =
        some StepCounter.signalState ↔ t = 1 ∨ t = 3 ∨ t = 5 := by
  have h := StepCounter.countdown_signal_iff input 3 t
  simp only [List.replicate_succ, List.replicate_zero] at h
  rw [h]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨2, by omega, rfl⟩

example (input : List Bool) :
    (StepCounter.countdown.runFrom
      (wordsCfg input (some StepCounter.countdown.q₀) (fun _ => []) []) 1).Halted :=
  StepCounter.countdown_halted input 0

end CslibFrontierTests.StepCounter
