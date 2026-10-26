/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.FrameMachines
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelTransducer
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelComp
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Direct linear-time and workspace certificates

Machine normalization and composition preserve a common linear bound. No output-space condition
is added: intermediate output is bounded by the actual clock of the first machine.

## Main results

* `ComputableInLinearTimeAndSpace.comp`: direct machine composition.
* `ComputableInLinearTimeAndSpace.const`, `.of_eq`: constant and word-preserving functions.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInLinearTimeAndSpace


variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- A finite transducer gives a common linear bound from its actual clock and zero workspace. -/
theorem of_transducer {Q : Type} [Finite Q] (τ : Transducer Bool Q) {f : α → β}
    (h : ∀ a, encMid (f a) = τ.run τ.q₀ (encIn a)) :
    ComputableInLinearTimeAndSpace f encIn encMid := by
  refine ⟨3, 0, _, inferInstance, τ.toTM, fun a => ?_⟩
  have hm := τ.computesInTimeAndSpace_toTM (encIn a)
  rw [← h a] at hm
  exact ⟨hm.1, hm.2.1.mono (by dsimp; omega), hm.2.2.mono (Nat.zero_le _)⟩

/-- Frame the encoded input using the shared streaming machine. -/
theorem of_frame {f : α → β} (h : ∀ a, encMid (f a) = frame (encIn a)) :
    ComputableInLinearTimeAndSpace f encIn encMid :=
  of_transducer Encodings.frameT fun a => (h a).trans (Encodings.frameT_run _).symm

/-- Read the first framed word, including the prescribed behavior on incomplete frames. -/
theorem of_unframe {f : α → β} (h : ∀ a, encMid (f a) = unframe (encIn a)) :
    ComputableInLinearTimeAndSpace f encIn encMid :=
  of_transducer (Internal.FrameMachines.readFrameT true) fun a =>
    (h a).trans (Internal.FrameMachines.readFrameT_run_true _).symm

/-- Drop the first framed word using the same shared parser. -/
theorem of_dropFrame {f : α → β} (h : ∀ a, encMid (f a) = dropFrame (encIn a)) :
    ComputableInLinearTimeAndSpace f encIn encMid :=
  of_transducer (Internal.FrameMachines.readFrameT false) fun a =>
    (h a).trans (Internal.FrameMachines.readFrameT_run_false _).symm

/-- Reuse the copy machine when the encoded output is the encoded input. -/
theorem of_eq {f : α → β} (h : ∀ a, encMid (f a) = encIn a) :
    ComputableInLinearTimeAndSpace f encIn encMid := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := computableInTimeAndSpace_id (enc := encIn)
  refine ⟨1, k, State, hfinite, tm, fun a => ?_⟩
  simpa only [h a, one_mul] using
    show tm.ComputesInTimeAndSpace (encIn a) (encIn a)
      ((encIn a).length + 1) ((encIn a).length + 1) from
      ⟨(htm a).1, (htm a).2.1, (htm a).2.2.mono (Nat.zero_le _)⟩

/-- A fixed encoded output takes constant time and no workspace. -/
theorem const (b : β) : ComputableInLinearTimeAndSpace (fun _ : α => b) encIn encMid := by
  obtain ⟨c, k, State, hfinite, tm, htm⟩ :=
    computableInTimeAndSpace_of_const (encIn := encIn) (encOut := encMid) b
  exact ⟨c, k, State, hfinite, tm, fun a =>
    ⟨(htm a).1, (htm a).2.1.mono (Nat.le_mul_of_pos_right c (Nat.succ_pos _)),
      (htm a).2.2.mono (Nat.zero_le _)⟩⟩

/-- A fixed function on a finite domain is realized by its finite lookup machine. -/
theorem of_finite [Finite α] (f : α → β) :
    ComputableInLinearTimeAndSpace f encIn encMid := by
  obtain ⟨c, k, State, hfinite, tm, htm⟩ :=
    computableInTimeAndSpace_of_finite (encIn := encIn) (encOut := encMid) f
  exact ⟨c, k, State, hfinite, tm, fun a =>
    ⟨(htm a).1, (htm a).2.1.mono (Nat.le_mul_of_pos_right c (Nat.succ_pos _)),
      (htm a).2.2.mono (Nat.zero_le _)⟩⟩

/-- Compose linear certificates; the clock bounds the stored intermediate word. -/
theorem comp {f : β → γ} {g : α → β}
    (hf : ComputableInLinearTimeAndSpace f encMid encOut)
    (hg : ComputableInLinearTimeAndSpace g encIn encMid) :
    ComputableInLinearTimeAndSpace (fun a => f (g a)) encIn encOut := by
  obtain ⟨c₁, k₁, Q₁, _, tm₁, h₁⟩ := Internal.NormalForm.linear hg
  obtain ⟨c₂, k₂, Q₂, _, tm₂, h₂⟩ := Internal.NormalForm.linear hf
  refine ⟨6 * c₁ + c₂ * (c₁ + 1) + (6 * max k₁ k₂ + 20),
    _, _, inferInstance, tm₂.comp tm₁ true, fun a =>
      (((h₁ a).comp (h₂ (g a)) true).mono ?_ ?_).computesInTimeAndSpace⟩
  all_goals
    have hl := (h₁ a).length_output_le
    have hinput : c₂ * ((encMid (g a)).length + 1) ≤
        c₂ * (c₁ + 1) * ((encIn a).length + 1) := by
      have hm : (encMid (g a)).length + 1 ≤ (c₁ + 1) * ((encIn a).length + 1) := by
        nlinarith
      exact (Nat.mul_le_mul_left c₂ hm).trans_eq (by ring)
    beta_reduce
    have hk := Nat.le_mul_of_pos_right (6 * max k₁ k₂ + 20)
      (Nat.succ_pos (encIn a).length)
    simp only [Nat.succ_eq_add_one] at hk
    have he : (6 * c₁ + c₂ * (c₁ + 1) + (6 * max k₁ k₂ + 20)) *
        ((encIn a).length + 1) = 6 * (c₁ * ((encIn a).length + 1)) +
        c₂ * (c₁ + 1) * ((encIn a).length + 1) +
        (6 * max k₁ k₂ + 20) * ((encIn a).length + 1) := by ring
    rw [he]
    omega

end Turing.MultiTapeTM.ComputableInLinearTimeAndSpace
