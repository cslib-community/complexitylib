/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Computability.GenericRAM.Native.Combinators
public import Complexity.Computability.Machines.ReadMachine.Tidy

/-! Native counted constructors and a zero-cost stopped read-machine simulation. -/

@[expose] public section
namespace ComplexityTests.Internal.CountedConsumers
open Turing Turing.MultiTapeTM Cslib.GenericRAM

noncomputable def nativeId : NativeCertificate (fun n : ℕ => n) encNat encNat :=
  .linear (.of_eq fun _ => rfl)

noncomputable def countedId := NativeCertificate.iterate nativeId nativeId nativeId

-- Zero includes the final stopping round; positive counters include every trajectory state.
example :
    (countedId.time 0 = 1 ∧ countedId.space 0 = 0) ∧
    (countedId.time 1 = 14 ∧ countedId.space 1 = 5) ∧
    (countedId.time 2 = 43 ∧ countedId.space 2 = 10) ∧
    ComputableInO (fun n : ℕ => n) encNat encNat countedId.time countedId.space := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  refine countedId.computes.of_enc_eq (g := fun n : ℕ => n) fun n => ?_
  change encNat n = encNat ((id : ℕ → ℕ)^[n] n)
  simp only [Function.iterate_id, id_eq]

def unitWord : Unit ↪ List Bool :=
  ⟨fun _ => [], by intro a b _; cases a; cases b; rfl⟩

/-- A genuinely stopped read machine, with no requested address or emitted output. -/
def stopped : ReadMachine Unit where
  init := ()
  halt _ := true
  addr _ := none
  step _ _ := ((), [])

-- The existing state formulas still charge framing and the binary head position.
example :
    stopped.toStepMachine.init = ((), 1) ∧
    stopped.toStepMachine.halt ((), 0) = true ∧
    stopped.toStepMachine.step ((), 0) none = (((), 0), 0, []) ∧
    ReadMachine.stateT unitWord (fun _ => 0) (fun _ => 0) ((), 0) = 36 ∧
    ReadMachine.stateS unitWord (fun _ => 0) ((), 0) = 6 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- All three component certificates may have zero state-dependent bounds. -/
theorem stoppedResource : stopped.toStepMachine.ResourceCertificate
    (encPair unitWord encNat)
    (ReadMachine.stateT unitWord (fun _ => 0) (fun _ => 0))
    (ReadMachine.stateS unitWord (fun _ => 0)) := by
  refine stopped.toStepMachine_resourceCertificate ?_ ?_ ?_
  · exact ComputableInO.constZero true
  · exact ComputableInO.constZero none
  · have h : ComputableInO (fun _ : Unit × Bool => ((), ([] : List Bool)))
        (encPair unitWord encBool) (encPair unitWord encBits)
        (fun p => (encPair unitWord encBool p).length) (fun _ => 0) :=
      .constZero ((), [])
    exact h.mono 3 (fun _ => by change 2 ≤ 3; decide)
      (fun _ => by change 0 ≤ 3; decide)

end ComplexityTests.Internal.CountedConsumers
