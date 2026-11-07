/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Finding the original input length by queries

A silent state-returning subroutine scans the original input until the first missing bit. Its
fixed initial state contains no input-dependent data. After exactly `input.length + 1` clocks,
the returned binary counter is the input length. Every physical state occupies logarithmic
space; all five components have native linear-space certificates.
-/

public section

namespace Turing.QueryMachine.InputLength

open MultiTapeTM ComputableInSpace

/-- Current input index and whether the first missing bit has been encountered. -/
abbrev State := ℕ × Bool

/-- Binary index followed by the stopping flag. -/
abbrev encState : State ↪ List Bool := encPair encNat encBool

/-- Scan the original input, retaining only a binary counter. No word is emitted. -/
@[expose] def machine : QueryMachine State where
  init := (0, false)
  query := Prod.fst
  next := fun ((n, _), bit) => if bit.isSome then (n + 1, false) else (n, true)
  emit _ := []
  halted := Prod.snd
  finish _ := []

/-- Every present input bit increments the counter once. -/
theorem run_before_end (w : List Bool) (t : ℕ) (ht : t ≤ w.length) :
    machine.run w t = (t, false) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [QueryMachine.run_succ, ih (by omega)]
    have hlt : t < w.length := by omega
    have hget : w[t]? = some (w[t]) := List.getElem?_eq_getElem hlt
    have hsome : (w[t]?).isSome = true := by rw [hget]; rfl
    simp [QueryMachine.step, QueryMachine.read, machine, hsome]

/-- The first absent bit returns the actual length, without copying the input. -/
theorem run_at_end (w : List Bool) : machine.run w (w.length + 1) = (w.length, true) := by
  rw [QueryMachine.run_succ, run_before_end w _ le_rfl]
  simp [QueryMachine.step, QueryMachine.read, machine]

/-- The subroutine has not stopped before its first absent-bit query. -/
theorem live (w : List Bool) {t : ℕ} (ht : t < w.length + 1) :
    machine.halted (machine.run w t) = false := by
  rw [run_before_end w t (by omega)]
  rfl

/-- The first absent-bit query stops the scan. -/
theorem halted (w : List Bool) : machine.halted (machine.run w (w.length + 1)) = true := by
  rw [run_at_end]
  rfl

/-- The scan counter is bounded by the input length even after it stops. -/
theorem counter_le (w : List Bool) (t : ℕ) : (machine.run w t).1 ≤ w.length := by
  by_cases ht : t ≤ w.length
  · rw [run_before_end w t ht]
    exact ht
  · rw [machine.run_eq_of_le w (halted w) (by omega), run_at_end]

/-- Every clock, including clocks after stopping, stores only a logarithmic counter and flag. -/
theorem length_run_le (w : List Bool) (t : ℕ) :
    (encState (machine.run w t)).length ≤ 2 * (Nat.log2 w.length + 1) + 2 := by
  have hn := length_encNat_le_log2 (counter_le w t)
  simp only [encState, length_encPair, encBool_apply, List.length_singleton]
  omega

/-- The original-input query is the stored binary counter. -/
theorem query_inSpace : ComputableInSpace machine.query encState encNat
    (fun s => (encState s).length) := fst encNat encBool

/-- The halt test is the stored flag. -/
theorem halted_inSpace : ComputableInSpace machine.halted encState encBool
    (fun s => (encState s).length) := snd encNat encBool

/-- Silent emission has constant native space. -/
theorem emit_inSpace : ComputableInSpace machine.emit (encPair encState (encOption encBool))
    encBits (fun p => (encPair encState (encOption encBool) p).length) :=
  budget_const [] (.refl _)

/-- Silent final output has constant native space; callers read the returned counter. -/
theorem finish_inSpace : ComputableInSpace machine.finish encState encBits
    (fun s => (encState s).length) := budget_const [] (.refl _)

/-- The native update only increments the binary index or sets the stopping flag. -/
theorem next_inSpace : ComputableInSpace machine.next (encPair encState (encOption encBool))
    encState (fun p => (encPair encState (encOption encBool) p).length) := by
  have hn := (fst encState (encOption encBool)).fst'
  have hbit := snd encState (encOption encBool)
  have hs : ComputableInSpace (Option.isSome : Option Bool → Bool)
      (encOption encBool) encBool (fun b => (encOption encBool b).length) := of_finite _
  have hsome := budget_comp_linear hs hbit
  exact budget_ite hsome
    (budget_prod (budget_natSucc hn) (budget_const false (.refl _)))
    (budget_prod hn (budget_const true (.refl _)))

end Turing.QueryMachine.InputLength
