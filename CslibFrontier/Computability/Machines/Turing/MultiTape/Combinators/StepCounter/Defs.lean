/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Mathlib.Data.Set.Card

/-!
# Native exact step-counter specification

A step counter is one finite native machine, with one designated signal state, which receives
a number in explicit least-significant-first binary encoding. It halts in time `O(n+1)` and
has exactly `n` isolated signal visits. The machine starts outside its signal state and leaves
each signal on the next transition, so visits count entering-and-leaving events. No fixed
spacing or preparation latency is required by this interface.

This is the total-time endpoint of Goldreich's draft Exercise 4.5 [Goldreich2007DraftR2].
No low-space or per-prefix latency requirement is bundled into this specification.

## Main definitions

* `Turing.MultiTapeTM.StepCounter`: a native machine with the exact signal and time contracts.
* `Turing.MultiTapeTM.StepCounter.signalTimes`: all native times at the signal state.

## Main results

* `Turing.MultiTapeTM.StepCounter.signal_count`: exactly `n` signal visits on binary input `n`.
* `Turing.MultiTapeTM.StepCounter.leaves_signal`: every signal is left on the next transition.
* `Turing.MultiTapeTM.StepCounter.initial_ne_signal`: the initial state is not a signal.
-/

public section

namespace Turing.MultiTapeTM

/-- A finite native step counter on the explicit binary input `encNat n`, with a uniform linear
runtime and an exact isolated-signal profile. Preparation time is included in the runtime. -/
structure StepCounter where
  /-- Fixed number of work tapes. -/
  tapeCount : ℕ
  /-- Fixed finite control type. -/
  State : Type
  /-- The machine has finitely many control states. -/
  finiteState : Finite State
  /-- The native deterministic machine. -/
  machine : MultiTapeTM tapeCount Bool State
  /-- The single distinguished signal state. -/
  signal : State
  /-- Uniform coefficient, independent of the runtime input number. -/
  timeConstant : ℕ
  /-- Native running time, including binary preparation and zero input. -/
  runsInTime : ∀ n, machine.RunsInTime (encNat n) (timeConstant * (n + 1))
  /-- The initial state is not a signal. -/
  initial_ne_signal : machine.q₀ ≠ signal
  /-- Every signal is left on the next transition. -/
  leaves_signal : ∀ n t,
    (machine.runFrom (machine.initCfg (encNat n)) t).state = some signal →
    (machine.runFrom (machine.initCfg (encNat n)) (t + 1)).state ≠ some signal
  /-- Exactly the requested number of signal-state visits. -/
  exactSignals : ∀ n,
    {t : ℕ | (machine.runFrom (machine.initCfg (encNat n)) t).state = some signal}.ncard = n

attribute [instance] StepCounter.finiteState

namespace StepCounter

/-- Native times at the single distinguished signal state, on little-endian binary input `n`.
The runtime bound makes this set finite, with no further signals after the machine halts. -/
@[expose] def signalTimes (counter : StepCounter) (n : ℕ) : Set ℕ :=
  {t | (counter.machine.runFrom (counter.machine.initCfg (encNat n)) t).state =
    some counter.signal}

/-- Halting bounds all signal times, including when the requested count is zero. -/
theorem signalTimes_finite (counter : StepCounter) (n : ℕ) : (counter.signalTimes n).Finite := by
  let C := counter.timeConstant * (n + 1)
  refine (Set.finite_range (fun i : Fin C => i.val)).subset ?_
  intro t ht
  have hlt : t < C := by
    by_contra hnot
    have hhalt := runsInTime_iff_halted.mp (counter.runsInTime n)
    have heq := congrArg Cfg.state
      (runFrom_eq_of_halt counter.machine (counter.machine.initCfg (encNat n))
        (by omega : C ≤ t) hhalt)
    change _ = none at hhalt
    change (counter.machine.runFrom (counter.machine.initCfg (encNat n)) t).state =
      some counter.signal at ht
    rw [heq, hhalt] at ht
    contradiction
  exact ⟨⟨t, hlt⟩, rfl⟩

/-- The machine has exactly the requested number of entering-and-leaving signals. -/
theorem signal_count (counter : StepCounter) (n : ℕ) : (counter.signalTimes n).ncard = n :=
  counter.exactSignals n

end StepCounter
end Turing.MultiTapeTM
