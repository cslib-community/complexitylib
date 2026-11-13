/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordUpdate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork

/-!
# In-place growing binary increment

Carry propagation visits only the initial one digits and the first zero or right blank. The
counter grows at a blank when necessary. Rewinding returns its head to zero without copying its
unvisited suffix. The exact clock is twice the initial-one count plus three; true-bit potential
bounds a sequence of increments from blank by five transitions per increment.
-/

public section

namespace Turing.MultiTapeTM.BinaryIncrement

/-- The number of consecutive one digits at the low end of a binary word. -/
@[expose] def initialOnes : List Bool → ℕ
  | [] => 0
  | false :: _ => 0
  | true :: w => initialOnes w + 1

/-- The carry frontier does not extend beyond the incremented word. -/
theorem initialOnes_le_length_incr (w : List Bool) :
    initialOnes w ≤ (NatSucc.incr true w).length := by
  induction w with
  | nil => simp [initialOnes, NatSucc.incr]
  | cons b w ih => cases b <;> simp [initialOnes, NatSucc.incr]; omega

/-- Each carried one pays for one unit of lost true-bit potential. -/
theorem initialOnes_add_count_incr (w : List Bool) :
    initialOnes w + (NatSucc.incr true w).count true = w.count true + 1 := by
  induction w with
  | nil => simp [initialOnes, NatSucc.incr]
  | cons b w ih => cases b <;> simp [initialOnes, NatSucc.incr]; omega

/-- Propagate carry through initial one digits, extending the word on overflow. -/
@[expose] def carry : MultiTapeTM 1 Bool Unit :=
  .ofTr () fun _ _ work => match work 0 with
    | some true => ⟨0, fun _ => (some (some false), 1), none, some ()⟩
    | _ => ⟨0, fun _ => (some (some true), 0), none, none⟩

private def cfg {S : Type} {input : List Bool} (q : Option S) (ip : Fin (input.length + 2))
    (out w : List Bool) (p : ℕ) : Cfg 1 Bool S input :=
  ⟨q, ip, fun _ => tapeOfList w, fun _ => (p : ℤ), out⟩

/-- Carry propagation preserves a prefix already processed and every unvisited high digit. -/
private theorem runFrom_carry {input : List Bool} (ip : Fin (input.length + 2))
    (out pre w : List Bool) :
    carry.runFrom (cfg (some ()) ip out (pre ++ w) pre.length) (initialOnes w + 1) =
      cfg none ip out (pre ++ NatSucc.incr true w) (pre.length + initialOnes w) := by
  induction w generalizing pre with
  | nil =>
    simp [initialOnes, NatSucc.incr, runFrom, step_of_state, tr_ofTr,
      carry, cfg, Action.apply, Cfg.workTapeSymbols, tapeOfList_append_single]
  | cons b w ih =>
    cases b with
    | false =>
      simp [initialOnes, NatSucc.incr, runFrom, step_of_state, tr_ofTr,
        carry, cfg, Action.apply, Cfg.workTapeSymbols, update_tapeOfList_append_cons]
    | true =>
      have hs : carry.step (cfg (some ()) ip out (pre ++ true :: w) pre.length) =
          cfg (some ()) ip out ((pre ++ [false]) ++ w) (pre ++ [false]).length := by
        simp [step_of_state, tr_ofTr, carry, cfg, Action.apply, Cfg.workTapeSymbols,
          update_tapeOfList_append_cons, List.append_assoc]
      rw [show initialOnes (true :: w) + 1 = initialOnes w + 1 + 1 by
          simp [initialOnes],
        runFrom, Function.iterate_succ_apply, hs, ← runFrom, ih]
      simp [cfg, initialOnes, NatSucc.incr, List.append_assoc, Nat.add_assoc, Int.add_comm]

/-- Increment the counter in place and restore its head to zero. -/
@[expose] noncomputable def machine := carry.seq (rewindWork Bool)

/-- The exact clock depends on the carry prefix, not on the full counter width. -/
theorem runFrom_machine {input : List Bool} (ip : Fin (input.length + 2)) (out w : List Bool) :
    machine.runFrom
      ⟨some machine.q₀, ip, fun _ => tapeOfList w, fun _ => 0, out⟩
      (2 * initialOnes w + 3) =
      ⟨none, ip, fun _ => tapeOfList (NatSucc.incr true w), fun _ => 0, out⟩ := by
  have h₀ := runFrom_carry ip out [] w
  have h₁ := runFrom_rewindWork_none ip (tapeOfList (NatSucc.incr true w)) out rfl
    (initialOnes_le_length_incr w)
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h₀
  have h := runFrom_seq (tm₁ := rewindWork Bool) h₀ rfl
    (by simpa [cfg, Cfg.withState] using h₁) rfl
  rw [show 2 * initialOnes w + 3 = initialOnes w + 1 + (initialOnes w + 2) by omega]
  exact h

/-- Canonical binary counters remain canonical, including growth at powers of two. -/
theorem runFrom_bits {input : List Bool} (ip : Fin (input.length + 2)) (out : List Bool)
    (n : ℕ) :
    machine.runFrom
      ⟨some machine.q₀, ip, fun _ => tapeOfList n.bits, fun _ => 0, out⟩
      (2 * initialOnes n.bits + 3) =
      ⟨none, ip, fun _ => tapeOfList (n + 1).bits, fun _ => 0, out⟩ := by
  rw [NatSucc.bits_succ]
  exact runFrom_machine ip out n.bits

/-- Sum of native increment clocks for `q` successive increments. -/
@[expose] def totalClock : ℕ → List Bool → ℕ
  | 0, _ => 0
  | q + 1, w => 2 * initialOnes w + 3 + totalClock q (NatSucc.incr true w)

/-- Carry propagation telescopes against the number of one digits; surrounding loop dispatch
is charged separately. -/
theorem totalClock_le (q : ℕ) (w : List Bool) :
    totalClock q w ≤ 5 * q + 2 * w.count true := by
  induction q generalizing w with
  | zero => simp [totalClock]
  | succ q ih =>
    have hp := initialOnes_add_count_incr w
    have hr := ih (NatSucc.incr true w)
    simp only [totalClock]
    omega

/-- Starting from a blank counter needs at most five native transitions per increment. -/
theorem totalClock_nil_le (q : ℕ) : totalClock q [] ≤ 5 * q := by
  simpa using totalClock_le q []

end Turing.MultiTapeTM.BinaryIncrement
