/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine

/-!
# State-returning calls between query machines

`QueryMachine.withCalls` suspends a caller while a callee runs on the same original input.
A request supplies the callee's initial state, and returning supplies its final state to the
caller. Callee emissions are discarded: this construction does not store or return an output
word. In particular, any data retained across a call is part of the explicit machine state.

## Main definitions

* `Turing.QueryMachine.runFrom`: a run starting at a specified state.
* `Turing.QueryMachine.withCalls`: state-returning calls on the original input.

## Main results

* `Turing.QueryMachine.withCalls_runFrom_subroutine_prefix`: exact simulation before return.
* `Turing.QueryMachine.withCalls_runFrom_call`: a call takes the callee's running time plus
  one entry step and one return step.
-/

public section

namespace Turing.QueryMachine

variable {σ τ : Type*}

/-- Run a query machine from an explicitly supplied state. -/
@[expose] def runFrom (M : QueryMachine σ) (w : List Bool) (start : σ) (n : ℕ) : σ :=
  (M.step w)^[n] start

@[simp] theorem runFrom_zero (M : QueryMachine σ) (w : List Bool) (start : σ) :
    M.runFrom w start 0 = start := rfl

theorem runFrom_succ (M : QueryMachine σ) (w : List Bool) (start : σ) (n : ℕ) :
    M.runFrom w start (n + 1) = M.step w (M.runFrom w start n) :=
  Function.iterate_succ_apply' _ _ _

theorem runFrom_add (M : QueryMachine σ) (w : List Bool) (start : σ) (m n : ℕ) :
    M.runFrom w start (m + n) = M.runFrom w (M.runFrom w start m) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← Nat.add_assoc, runFrom_succ, ih, runFrom_succ]

/-- Suspend the caller on a request and resume it with the callee's final state. Both machines
read the same original input. Only ordinary caller steps emit output; call entry, callee steps,
and return emit nothing. The suspended caller and callee states are stored explicitly. -/
@[expose] def withCalls (M : QueryMachine σ) (N : QueryMachine τ)
    (request : σ → Option τ) (resume : σ → τ → σ) : QueryMachine (σ ⊕ (σ × τ)) where
  init := .inl M.init
  query
    | .inl s => match request s with
      | none => M.query s
      | some _ => 0
    | .inr (_, t) => N.query t
  next
    | (.inl s, b) => match request s with
      | none => .inl (M.next (s, b))
      | some t => .inr (s, t)
    | (.inr (s, t), b) =>
      if N.halted t then .inl (resume s t) else .inr (s, N.next (t, b))
  emit
    | (.inl s, b) => match request s with
      | none => M.emit (s, b)
      | some _ => []
    | (.inr _, _) => []
  halted
    | .inl s => M.halted s
    | .inr _ => false
  finish
    | .inl s => M.finish s
    | .inr _ => []

variable (M : QueryMachine σ) (N : QueryMachine τ)
  (request : σ → Option τ) (resume : σ → τ → σ) (w : List Bool)

/-- Without a request, a composite step is precisely a caller step, including halted states. -/
theorem withCalls_step_normal (s : σ) (h : request s = none) :
    (M.withCalls N request resume).step w (.inl s) = .inl (M.step w s) := by
  cases hs : M.halted s <;> simp [step, read, withCalls, h, hs]

/-- Entering a call takes one step and preserves the suspended caller state. -/
theorem withCalls_step_call (s : σ) (t : τ)
    (hs : M.halted s = false) (h : request s = some t) :
    (M.withCalls N request resume).step w (.inl s) = .inr (s, t) := by
  simp [step, withCalls, hs, h]

/-- A live callee step reads exactly the bit that the callee reads on the original input. -/
theorem withCalls_step_subroutine (s : σ) (t : τ) (h : N.halted t = false) :
    (M.withCalls N request resume).step w (.inr (s, t)) =
      .inr (s, N.step w t) := by
  simp [step, read, withCalls, h]

/-- Returning from a halted callee takes one additional step. -/
theorem withCalls_step_return (s : σ) (t : τ) (h : N.halted t = true) :
    (M.withCalls N request resume).step w (.inr (s, t)) = .inl (resume s t) := by
  simp [step, withCalls, h]

/-- Up to its first halt, the callee is simulated step for step. -/
theorem withCalls_runFrom_subroutine_prefix (s : σ) (start : τ) (T : ℕ)
    (hpre : ∀ i < T, N.halted (N.runFrom w start i) = false) :
    (M.withCalls N request resume).runFrom w (.inr (s, start)) T =
      .inr (s, N.runFrom w start T) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [runFrom_succ, ih (fun i hi => hpre i (Nat.lt_succ_of_lt hi))]
    rw [withCalls_step_subroutine M N request resume w s _ (hpre T (Nat.lt_succ_self T))]
    rw [runFrom_succ]

/-- A callee that first halts at `T` returns its final state at time `T + 1`. -/
theorem withCalls_runFrom_return (s : σ) (start : τ) (T : ℕ)
    (hpre : ∀ i < T, N.halted (N.runFrom w start i) = false)
    (hhalt : N.halted (N.runFrom w start T) = true) :
    (M.withCalls N request resume).runFrom w (.inr (s, start)) (T + 1) =
      .inl (resume s (N.runFrom w start T)) := by
  rw [runFrom_succ, withCalls_runFrom_subroutine_prefix M N request resume w s start T hpre]
  exact withCalls_step_return M N request resume w s _ hhalt

/-- Entry and return add two steps to the running time of a state-returning call. -/
theorem withCalls_runFrom_call (s : σ) (start : τ) (T : ℕ)
    (hs : M.halted s = false) (hrequest : request s = some start)
    (hpre : ∀ i < T, N.halted (N.runFrom w start i) = false)
    (hhalt : N.halted (N.runFrom w start T) = true) :
    (M.withCalls N request resume).runFrom w (.inl s) (T + 2) =
      .inl (resume s (N.runFrom w start T)) := by
  rw [show T + 2 = 1 + (T + 1) by omega, runFrom_add]
  rw [show (M.withCalls N request resume).runFrom w (.inl s) 1 =
    .inr (s, start) from withCalls_step_call M N request resume w s start hs hrequest]
  exact withCalls_runFrom_return M N request resume w s start T hpre hhalt

end Turing.QueryMachine
