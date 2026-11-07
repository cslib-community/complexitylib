/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.RootDecision
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.EncodedTree
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork.Graph

/-!
# Root classification agrees with native halting and output

Wrong schedules give no decision. The actual movement schedule gives a decision precisely when
the source machine has halted by the block boundary; both acceptance and rejection are retained.
The native classifier is connected to the existing functional computation, not to a new model.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.RootDecision

open MultiTapeNTM.ChoiceTable

/-- Native halting at a clock yields its Boolean acceptance decision; live states yield none. -/
@[expose] noncomputable def boundaryDecision {k : ℕ} {Q : Type}
    (M : MultiTapeTM k Bool Q) (w : List Bool) (clock : ℕ) : Option Bool :=
  let cfg := M.runFrom (Cfg.init M.q₀ w) clock
  if cfg.state.isNone then some (decide (cfg.output = [true])) else none

private theorem decision_trueView {k q : ℕ} {Q : Type}
    (M : MultiTapeTM k Bool Q) (w : List Bool) (b : ℕ)
    (σ : Schedule k q) :
    decision (some (trueView (MultiTapePTM.ofDeterministic M) w b σ q)) =
      boundaryDecision M w (q * b) := by
  unfold boundaryDecision
  rw [← boundary_ofDeterministic (input := w) (b := b) M le_rfl]
  cases q with
  | zero => simp [decision, trueView, initialView, boundary, intervalStart_zero, Cfg.init]
  | succ q =>
    simp only [decision, trueView, Cfg.blockControl, OutputTrack.ofWord_eq_accept_iff]

/-- A correctly classified root is the native boundary decision exactly for the actual schedule. -/
theorem decision_eval_eq_boundary {k q s : ℕ} {Q : Type}
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ : ℕ) :
    decision (Encoding.decode e (encodedTree (MultiTapePTM.ofDeterministic M) w b
      (scheduleOfNat k q σ) e).eval) =
      if actualSchedule (MultiTapePTM.ofDeterministic M) w b (q := q) = scheduleOfNat k q σ
      then boundaryDecision M w (q * b) else none := by
  classical
  rw [decode_eval_encodedTree]
  cases hv : value (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ) q with
  | none =>
    have hwrong := (value_final_eq_none_iff (MultiTapePTM.ofDeterministic M) w b
      (scheduleOfNat k q σ)).mp hv
    simp only [decision, hwrong, ↓reduceIte]
  | some v =>
    obtain ⟨hactual, rfl⟩ := (value_final_eq_some_iff (MultiTapePTM.ofDeterministic M) w b
      (scheduleOfNat k q σ) v).mp hv
    rw [ite_eq_left hactual]
    exact decision_trueView M w b (scheduleOfNat k q σ)

end Turing.MultiTapePTM.BlockComputation.RootDecision
