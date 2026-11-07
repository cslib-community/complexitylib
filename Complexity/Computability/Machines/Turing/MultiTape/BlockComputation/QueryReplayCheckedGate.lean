/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayGate
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.Call
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum

/-!
# Total checked replay with paid rejection output

A rejected call retains its actual previous-label word and halts immediately. Its final word
zeros that stored buffer, so rejection cannot allocate a width-sized result from binary metadata.
An accepted call delegates to the native local replay gate on the same original input.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.CheckedGate

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable {k s : ℕ} {Q : Type}

/-- A paid rejection buffer or an active local replay. -/
abbrev State (k : ℕ) (Q : Type) := List Bool ⊕ Gate.State k Q

/-- Rejected calls halt without querying the input; accepted calls perform the existing replay. -/
@[expose] noncomputable def machine (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    QueryMachine (State k Q) where
  init := .inl []
  query := Sum.elim (fun _ => 0) (Gate.machine M e).query
  next := fun (q, symbol) => q.elim (fun word => .inl word)
    (fun active => .inr ((Gate.machine M e).next (active, symbol)))
  emit _ := []
  halted := Sum.elim (fun _ => true) (Gate.machine M e).halted
  finish := Sum.elim (List.map (fun _ => false)) (Gate.machine M e).finish

variable [Finite Q]

/-- The rejection word is stored explicitly, rather than replaced by a binary length. -/
@[expose] noncomputable def encState : State k Q ↪ List Bool :=
  encSum encBits (Gate.encState (k := k) (Q := Q))

private theorem blankFold (l out : List Bool) :
    l.foldl (fun acc _ => acc ++ [false]) out = out ++ l.map (fun _ => false) := by
  induction l generalizing out with
  | nil => simp
  | cons bit l ih => simp [List.foldl_cons, ih, List.append_assoc]

/-- Zero an actual bit word in linear native space. -/
theorem blank_inSpace : ComputableInSpace (List.map (fun _ : Bool => false)) encBits encBits
    (fun word => (encBits word).length) := by
  have hid : ComputableInSpace (fun word : List Bool => word) encBits encBits
      (fun word => (encBits word).length) := of_inO (ComputableInO.of_eq fun _ => rfl)
  have hinit := budget_const (encB := encBits) []
    (show (fun word => (encBits word).length) ≼ fun word => (encBits word).length from .refl _)
  have hstep : ComputableInSpace (fun q : List Bool × Bool => q.1 ++ [false])
      (encPair encBits encBool) encBits (fun q => (encPair encBits encBool q).length) := by
    exact ((fst encBits encBool).append
      (budget_const (encB := encBits) [false] (.refl _)) (fun _ => rfl)).weaken
      (.add (.refl _) (.refl _))
  have hstate (word : List Bool) (i : ℕ) (hi : i ≤ word.length) :
      (encBits ((word.take i).foldl (fun acc _ => acc ++ [false]) [])).length ≤
        4 * ((encBits word).length + 1) := by
    simp only [blankFold, List.nil_append, encBits_apply, List.length_map, List.length_take]
    omega
  have hspace (word : List Bool) (i : ℕ) (hi : i < word.length) :
      (encPair encBits encBool
        ((word.take i).foldl (fun acc _ => acc ++ [false]) [], word[i])).length ≤
          4 * ((encBits word).length + 1) := by
    simp only [blankFold, List.nil_append, length_encPair, encBits_apply, encBool_apply,
      List.length_map, List.length_take, List.length_singleton]
    omega
  have h := foldl hid hinit hstep hspace hstate
  exact h.weaken (.of_le_linear 16 16 fun _ => by omega) |>.of_enc_eq fun word => by
    simp only [blankFold, List.nil_append]

/-- Queries preserve the active gate's original-input interface. -/
theorem machine_query_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).query encState encNat (fun a => (encState a).length) :=
  sumElim (budget_const (encIn := encBits) (encB := encNat) 0 (.refl _))
    (Gate.machine_query_inSpace M e)

/-- A transition preserves its sum tag and charges the complete actual active state. -/
theorem machine_next_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).next (encPair encState (encOption encBool)) encState
      (fun a => (encPair encState (encOption encBool) a).length) := by
  have hleft := budget_comp_linear
    (of_inO (ComputableInO.inl encBits (Gate.encState (k := k) (Q := Q))))
    (fst encBits (encOption encBool))
  have hright := budget_comp_linear
    (of_inO (ComputableInO.inr encBits (Gate.encState (k := k) (Q := Q))))
    (Gate.machine_next_inSpace M e)
  exact sumElimFst hleft hright

/-- No branch emits intermediate output. -/
theorem machine_emit_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).emit (encPair encState (encOption encBool)) encBits
      (fun a => (encPair encState (encOption encBool) a).length) :=
  budget_const [] (.refl _)

/-- Rejection is immediately halted; accepted calls use the replay counter. -/
theorem machine_halted_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).halted encState encBool (fun a => (encState a).length) :=
  sumElim (budget_const (encIn := encBits) (encB := encBool) true (.refl _))
    (Gate.machine_halted_inSpace M e)

/-- Both final branches are paid by their actual stored words/windows. -/
theorem machine_finish_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).finish encState encBits (fun a => (encState a).length) :=
  sumElim blank_inSpace (Gate.machine_finish_inSpace M e)

omit [Finite Q] in
/-- Rejection serializes exactly a FAIL word of the stored buffer's width. -/
theorem finish_inl (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (word : List Bool) :
    (machine M e).finish (.inl word) = List.replicate word.length false := by
  simp [machine]

omit [Finite Q] in
/-- A successful branch step is precisely the underlying local gate step. -/
theorem step_inr (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (q : Gate.State k Q) :
    (machine M e).step w (.inr q) = .inr ((Gate.machine M e).step w q) := by
  by_cases h : (Gate.machine M e).halted q = true <;>
    simp [QueryMachine.step, machine, QueryMachine.read, h]

omit [Finite Q] in
/-- Every accepted replay prefix lifts without changing the underlying state. -/
theorem runFrom_inr (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (q : Gate.State k Q) (n : ℕ) :
    (machine M e).runFrom w (.inr q) n = .inr ((Gate.machine M e).runFrom w q n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [QueryMachine.runFrom_succ, ih, step_inr, QueryMachine.runFrom_succ]

omit [Finite Q] in
/-- A rejected call remains at its paid rejection buffer at every clock. -/
theorem runFrom_inl (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (word : List Bool) (n : ℕ) :
    (machine M e).runFrom w (.inl word) n = .inl word := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [QueryMachine.runFrom_succ, ih]
    simp [QueryMachine.step, machine]

end Turing.MultiTapePTM.BlockComputation.QueryReplay.CheckedGate
