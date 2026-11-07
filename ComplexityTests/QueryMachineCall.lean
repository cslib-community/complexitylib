/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of query-machine calls)

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-!
# Same-input query calls

A caller requests two one-bit subroutines, at positions zero and one, and returns their XOR.
The callee deliberately emits junk: state-returning calls must discard it. Finite component
certificates instantiate the native composition rules without assuming an input oracle.
-/

@[expose] public section

namespace ComplexityTests.QueryMachineCall

open Turing MultiTapeTM

abbrev Caller := Fin 3 × Bool
abbrev Callee := Bool × Bool × Bool

/-- Read one selected bit and return it in the final state. -/
def reader : QueryMachine Callee where
  init := (false, false, false)
  query s := if s.1 then 1 else 0
  next p := (p.1.1, true, p.2.getD false)
  emit _ := [true, true]
  halted s := s.2.1
  finish _ := [true, true]

/-- The controller advances only when its subroutine returns. -/
def caller : QueryMachine Caller where
  init := (0, false)
  query _ := 0
  next := Prod.fst
  emit _ := []
  halted s := decide (s.1 = 2)
  finish s := [s.2]

def request (s : Caller) : Option Callee :=
  if s.1 = 2 then none else some (decide (s.1 = 1), false, false)

def resume (s : Caller) (t : Callee) : Caller :=
  (if s.1 = 0 then 1 else 2, s.2 ^^ t.2.2)

def machine := caller.withCalls reader request resume

example : machine.output [true, false] 6 = [true] := by decide
example : machine.output [true, true] 6 = [false] := by decide
example : machine.output [] 6 = [false] := by decide
example : machine.output [true, false] 10 = [true] := by decide
example : machine.query (machine.run [true, false] 1) = 0 := by decide
example : machine.query (machine.run [true, false] 4) = 1 := by decide
example : machine.run [true, false] 6 = .inl (2, true) := by decide

/-- An already halted callee still needs one entry and one return step. -/
example (w : List Bool) :
    (caller.withCalls reader (fun _ => some (false, true, true)) resume).runFrom w
      (.inl (0, false)) 2 = .inl (1, true) := by
  change _ = (Sum.inl (resume (0, false) (reader.runFrom w (false, true, true) 0)) :
    Caller ⊕ (Caller × Callee))
  apply QueryMachine.withCalls_runFrom_call caller reader _ resume w (0, false)
    (false, true, true) 0
  · rfl
  · rfl
  · intro i hi
    omega
  · rfl

/-- With no requests, ordinary caller emissions and the final word are preserved. -/
def echo : QueryMachine Bool where
  init := false
  query _ := 0
  next _ := true
  emit p := [p.2.getD false]
  halted := id
  finish _ := [false]

example : (echo.withCalls reader (fun _ => none) (fun s _ => s)).output [true] 3 =
    [true, false] := by decide

noncomputable def encCaller := encPair (encFinite (Fin 3)) encBool
noncomputable def encCallee := encPair encBool (encPair encBool encBool)
noncomputable def encState := encSum encCaller (encPair encCaller encCallee)

example : ComputableInSpace machine.query encState encNat
    (fun s => (encState s).length) :=
  QueryMachine.withCalls_query_inSpace caller reader request resume encCaller encCallee
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
    (ComputableInSpace.of_finite _)

example : ComputableInSpace machine.halted encState encBool
    (fun s => (encState s).length) :=
  QueryMachine.withCalls_halted_inSpace caller reader request resume encCaller encCallee
    (ComputableInSpace.of_finite _)

example : ComputableInSpace machine.finish encState encBits
    (fun s => (encState s).length) :=
  QueryMachine.withCalls_finish_inSpace caller reader request resume encCaller encCallee
    (ComputableInSpace.of_finite _)

example : ComputableInSpace machine.next (encPair encState (encOption encBool)) encState
    (fun p => (encPair encState (encOption encBool) p).length) :=
  QueryMachine.withCalls_next_inSpace caller reader request resume encCaller encCallee
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
    (ComputableInSpace.of_finite _)

example : ComputableInSpace machine.emit (encPair encState (encOption encBool)) encBits
    (fun p => (encPair encState (encOption encBool) p).length) :=
  QueryMachine.withCalls_emit_inSpace caller reader request resume encCaller encCallee
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)

/-- The five composed certificates feed the existing compiler unchanged. -/
example {α β : Type} (enc : α ↪ List Bool) (encOut : β ↪ List Bool)
    (f : α → β) (time S : α → ℕ)
    (hhalt : ∀ a, machine.halted (machine.run (enc a) (time a)) = true)
    (hpre : ∀ a, ∀ t < time a, machine.halted (machine.run (enc a) t) = false)
    (hf : ∀ a, encOut (f a) = machine.output (enc a) (time a))
    (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hsize : ∃ c, ∀ a, ∀ t ≤ time a,
      (encState (machine.run (enc a) t)).length ≤ c * S a) :
    ∃ t c, ComputableInTimeAndSpace f enc encOut t (fun a => c * S a) := by
  apply machine.computableInSpace (encS := encState)
    (QueryMachine.withCalls_query_inSpace caller reader request resume encCaller encCallee
      (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
      (ComputableInSpace.of_finite _))
    (QueryMachine.withCalls_next_inSpace caller reader request resume encCaller encCallee
      (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
      (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
      (ComputableInSpace.of_finite _))
    (QueryMachine.withCalls_emit_inSpace caller reader request resume encCaller encCallee
      (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _))
    (QueryMachine.withCalls_halted_inSpace caller reader request resume encCaller encCallee
      (ComputableInSpace.of_finite _))
    (QueryMachine.withCalls_finish_inSpace caller reader request resume encCaller encCallee
      (ComputableInSpace.of_finite _)) time hhalt hpre hf S hlog hsize

end ComplexityTests.QueryMachineCall
