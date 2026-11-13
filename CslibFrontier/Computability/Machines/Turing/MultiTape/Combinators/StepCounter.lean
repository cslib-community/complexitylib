/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.StepCounter.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.StepCounter.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# Exact native step counters from binary input

Goldreich's draft Exercise 4.5 [Goldreich2007DraftR2] asks for a machine receiving binary `n`
that issues exactly `n` signals and halts in total time `O(n)`. A signal here is a visit to one
designated state, with both entry and exit required. We use `O(n+1)` to include zero input.

The construction first uses the existing linear-time binary-to-unary conversion, redirects its
exact output to a work tape, and consumes that tape with the native countdown controller.
Preparation contributes to the total runtime and never visits the signal state. No workspace
or per-prefix latency bound is claimed.

## Main results

* `Turing.MultiTapeTM.exists_stepCounter`: a finite native exact step counter exists.
-/

public section

namespace Turing.MultiTapeTM

/-- A finite native machine issues exactly `n` isolated signals on binary input `n` and halts
in time `O(n+1)`, including its preparation phase. -/
theorem exists_stepCounter : Nonempty StepCounter := by
  classical
  obtain ⟨c, ⟨k, Q, hfinite, conv, hconv⟩, _⟩ := ComputableInO.natToUnary.tidy
  let := hfinite
  let prep := conv.outputToWord
  let tail := StepCounter.countdown.extendTapes (tapeEmb (Fin.last k))
  let machine := prep.seq tail
  let signal : (Q ⊕ RewindWorkState) ⊕ MultiTapeMachine.Clock.Control Unit :=
    Sum.inr StepCounter.signalState
  let P := fun n => c * (n + 1) + n + 2
  let mid := fun n => wordsCfg (encNat n) (none : Option (Q ⊕ RewindWorkState))
    (Function.update (fun _ => []) (Fin.last k) (List.replicate n true)) []
  have hprep (n : ℕ) : prep.runFrom (prep.initCfg (encNat n)) (P n) = mid n := by
    have hc : conv.ComputesTidilyInTimeAndSpace (encNat n) (List.replicate n true)
        (c * (n + 1)) (c * (n + 1)) := by
      simpa only [encUnary_apply] using hconv n
    obtain ⟨_, _, hrun, ⟨rfl, rfl⟩, _⟩ := transformsTapes_iff_runFrom.mp hc.outputToWord
      (encNat n) (fun _ => []) [] ⟨rfl, rfl⟩
    simpa only [initCfg_eq_wordsCfg, List.nil_append, List.length_replicate] using hrun
  have hview (n : ℕ) : oneTapeCfg (Fin.last k) ((mid n).withState (some tail.q₀)) =
      wordsCfg (encNat n) (some StepCounter.countdown.q₀)
        (fun _ => List.replicate n true) [] := by
    simp only [mid, oneTapeCfg, Cfg.withState, wordsCfg, tail, extendTapes_q₀,
      Function.update_self]
  have htail (n r : ℕ) :
      (tail.runFrom ((mid n).withState (some tail.q₀)) r).state =
      (StepCounter.countdown.runFrom
        (wordsCfg (encNat n) (some StepCounter.countdown.q₀)
          (fun _ => List.replicate n true) []) r).state := by
    rw [show tail = StepCounter.countdown.extendTapes (tapeEmb (Fin.last k)) from rfl,
      runFrom_tapeEmb, hview, embed_tapeEmb]
  have hprofile (n : ℕ) : ∃ u ≤ P n,
      (∀ t, (machine.runFrom (machine.initCfg (encNat n)) t).state = some signal ↔
        ∃ i < n, t = u + 2 * i + 1) ∧
      (machine.runFrom (machine.initCfg (encNat n)) (u + (2 * n + 1))).Halted := by
    have hh : (prep.runFrom (prep.initCfg (encNat n)) (P n)).Halted := by
      rw [hprep]
      rfl
    obtain ⟨u, hu_le, hu⟩ := exists_haltsAt hh
    have hmid : prep.runFrom (prep.initCfg (encNat n)) u = mid n :=
      (hu.runFrom_eq hu_le).symm.trans (hprep n)
    have hinit : machine.initCfg (encNat n) =
        (prep.initCfg (encNat n)).mapState (handOver tail.q₀) := rfl
    refine ⟨u, hu_le, fun t => ?_, ?_⟩
    · rw [hinit]
      rcases Nat.lt_or_ge t u with ht | ht
      · rw [show machine = prep.seq tail from rfl,
          hu.runFrom_combine_left (handOver_some _) ht.le]
        have hne := hu.not_halted ht
        cases hq : (prep.runFrom (prep.initCfg (encNat n)) t).state with
        | none => exact (hne hq).elim
        | some q =>
          change handOver tail.q₀ (prep.runFrom (prep.initCfg (encNat n)) t).state =
            some (Sum.inr StepCounter.signalState) ↔ _
          rw [hq, handOver_some]
          constructor
          · intro heq
            cases heq
          · rintro ⟨i, hi, heq⟩
            omega
      · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le ht
        rw [show machine = prep.seq tail from rfl, hu.runFrom_seq, hmid]
        change Option.map Sum.inr _ = some (Sum.inr StepCounter.signalState) ↔ _
        rw [Option.map_eq_some_iff]
        simp only [Sum.inr.injEq, exists_eq_right]
        rw [htail, StepCounter.countdown_signal_iff]
        constructor <;> rintro ⟨i, hi, heq⟩ <;> exact ⟨i, hi, by omega⟩
    · rw [hinit, show machine = prep.seq tail from rfl, hu.runFrom_seq, hmid]
      change Option.map Sum.inr _ = none
      rw [Option.map_eq_none_iff, htail]
      exact StepCounter.countdown_halted (encNat n) n
  refine ⟨{
    tapeCount := k + 1
    State := (Q ⊕ RewindWorkState) ⊕ MultiTapeMachine.Clock.Control Unit
    finiteState := inferInstance
    machine := machine
    signal := signal
    timeConstant := c + 3
    runsInTime := ?_
    initial_ne_signal := ?_
    leaves_signal := ?_
    exactSignals := ?_ }⟩
  · intro n
    obtain ⟨u, hu, _, hh⟩ := hprofile n
    apply runsInTime_iff_halted.mpr
    rw [runFrom_eq_of_halt machine _ (by dsimp [P] at hu; nlinarith) hh]
    exact hh
  · change Sum.inl prep.q₀ ≠ Sum.inr StepCounter.signalState
    exact Sum.inl_ne_inr
  · intro n t ht ht'
    obtain ⟨u, _, hp, _⟩ := hprofile n
    obtain ⟨i, _, hi⟩ := (hp t).mp ht
    obtain ⟨j, _, hj⟩ := (hp (t + 1)).mp ht'
    omega
  · intro n
    obtain ⟨u, _, hp, _⟩ := hprofile n
    have hset : {t | (machine.runFrom (machine.initCfg (encNat n)) t).state = some signal} =
        Set.range (fun i : Fin n => u + 2 * i.val + 1) := by
      ext t
      rw [Set.mem_ofPred_eq, hp]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, i.isLt, rfl⟩
    rw [hset, Set.ncard_range_of_injective]
    · simp
    · intro i j hij
      apply Fin.ext
      change u + 2 * i.val + 1 = u + 2 * j.val + 1 at hij
      omega

end Turing.MultiTapeTM
