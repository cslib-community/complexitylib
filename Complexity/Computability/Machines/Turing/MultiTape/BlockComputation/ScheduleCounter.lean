/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadSpace
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts

/-!
# A native bound guard for sequential schedule search

Repeatedly discarding one fixed-radix schedule row tests whether a binary counter names a
schedule at the supplied horizon. The runtime guard does not construct the exponential upper
bound. Its semantic bound is exact, and every existing typed schedule has a valid counter.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleCounter

open MultiTapeTM MultiTapeTM.ComputableInSpace

/-- The unread suffix after consuming exactly the supplied number of schedule rows. -/
@[expose] def remaining (k : ℕ) (a : ℕ × ℕ) : ℕ :=
  ((ScheduleRead.step k 0 0)^[a.2] (a.1, 0)).1

/-- A schedule number is in range exactly when no unread row remains. -/
@[expose] def valid (k : ℕ) (a : ℕ × ℕ) : Bool := decide (remaining k a = 0)

/-- Both the schedule counter and horizon are explicitly stored binary naturals. -/
abbrev encArgs : (ℕ × ℕ) ↪ List Bool := encPair encNat encNat

/-- The streamed suffix has the exact division semantics, without computing this power. -/
theorem remaining_eq_div (k σ q : ℕ) :
    remaining k (σ, q) = σ / 3 ^ ((k + 1) * q) :=
  ScheduleRead.iterate_fst k 0 0 σ q

/-- The native guard accepts precisely the complete finite numbering of existing schedules. -/
theorem valid_eq_true_iff (k σ q : ℕ) :
    valid k (σ, q) = true ↔ σ < 3 ^ ((k + 1) * q) := by
  simp only [valid, decide_eq_true_eq, remaining_eq_div]
  exact Nat.div_eq_zero_iff_lt (by positivity)

/-- The first excluded counter is rejected, so sequential search need not store its bound. -/
theorem valid_bound (k q : ℕ) : valid k (3 ^ ((k + 1) * q), q) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact Nat.lt_irrefl _ ((valid_eq_true_iff k _ q).mp h)

/-- Advancing an accepted counter stays at most the first excluded counter. -/
theorem succ_le_bound {k σ q : ℕ} (hvalid : valid k (σ, q) = true) :
    σ + 1 ≤ 3 ^ ((k + 1) * q) :=
  Nat.succ_le_of_lt ((valid_eq_true_iff k σ q).mp hvalid)

/-- At horizon zero the unique valid number is zero. -/
theorem valid_zero_horizon (k σ : ℕ) : valid k (σ, 0) = true ↔ σ = 0 := by
  rw [valid_eq_true_iff]
  simp

/-- Every typed movement schedule is represented by an accepted numeric counter. -/
theorem exists_valid_schedule {k q : ℕ} (schedule : Schedule k q) :
    ∃ σ, valid k (σ, q) = true ∧ scheduleOfNat k q σ = schedule := by
  let number := scheduleEquiv k q schedule
  refine ⟨number.val, (valid_eq_true_iff k number.val q).mpr number.isLt, ?_⟩
  rw [scheduleOfNat_eq_symm number.isLt]
  exact (scheduleEquiv k q).symm_apply_apply schedule

/-- Discarding runtime-many fixed-radix rows uses space linear in the actual input storage. -/
theorem remaining_inSpace (k : ℕ) :
    ComputableInSpace (remaining k) encArgs encNat (fun a => (encArgs a).length) := by
  have hinit := budget_prod (fst encNat encNat)
    (budget_const (encB := encNat) 0 (.refl _))
  have hstates (a : ℕ × ℕ) (j : ℕ) (hj : j ≤ a.2) :
      (ScheduleRead.encState ((ScheduleRead.step k 0 0)^[j] (a.1, 0))).length ≤
        (ScheduleRead.encState a).length := by
    have hs := ComputableTidilyInO.length_encNat_mono
      (ScheduleRead.iterate_fst_le k 0 0 a.1 j)
    have hn := ComputableTidilyInO.length_encNat_mono
      ((ScheduleRead.iterate_snd_le k 0 0 a.1 j).trans hj)
    simp only [ScheduleRead.encState, length_encPair]
    omega
  have hrun := budget_iterate (snd encNat encNat) hinit
    (ScheduleRead.step_inSpace k 0 0) hstates (.refl _)
  exact (fst' hrun).of_enc_eq fun _ => rfl

/-- The complete range guard is native and stores neither the exponential bound nor a list. -/
theorem valid_inSpace (k : ℕ) :
    ComputableInSpace (valid k) encArgs encBool (fun a => (encArgs a).length) :=
  (budget_natEq (remaining_inSpace k)
    (budget_const (encB := encNat) 0 (.refl _))).of_enc_eq fun _ => rfl

end Turing.MultiTapePTM.BlockComputation.ScheduleCounter
