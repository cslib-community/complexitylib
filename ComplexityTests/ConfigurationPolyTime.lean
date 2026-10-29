/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
import Complexity.Tactic.PolyTime

/-! Functional configuration programs with complete storage and input-boundary accounting. -/

namespace ComplexityTests.ConfigurationPolyTime

open Turing Turing.MultiTapeTM Turing.MultiTapeMachine Cslib.Turing

private abbrev Config := FiniteConfig 2 Bool (Fin 2) (Fin 2)

-- Initialization, reply installation, local actions and projections compose as ordinary code.
example (action : Action 2 Bool (Fin 2)) : ComputableInPolyTime
    (fun pair : Config × List Bool =>
      let next := pair.1.receive 0 1 pair.2
      ((next.step action (fun _ => none) (fun _ => .pos)).tapes.output,
        (next.channels 0).2.head))
    (encPair encFiniteConfig encBits) (encPair encBits (encOption encBool)) := by fun_prop

-- Structure update syntax exposes the same certified constructor.
example : ComputableInPolyTime
    (fun cfg : FiniteCfg 2 Bool (Fin 2) =>
      { cfg with output := cfg.output ++ cfg.input }) encFiniteCfg encFiniteCfg := by fun_prop

-- Native observation and state guards do not expose the tuple encoding to clients.
example : ComputableInPolyTime
    (fun cfg : Config => if cfg.tapes.state = none then cfg.tapes.output else cfg.tapes.input)
    encFiniteConfig encBits := .of_tidy (by polytime)

-- Explicit lambdas, named projections and a captured configuration have the same certificates.
example {α : Type} (input : α ↪ List Bool) (cfg : α → Config)
    (hcfg : ComputableInPolyTime cfg input encFiniteConfig) :
    ComputableInPolyTime (fun a => (cfg a).tapes.inputSymbol) input
      (encFinEnum (Option Bool)) := by fun_prop

-- A different input encoding uses its existing conversion certificate; no program rewrite.
example : ComputableInPolyTime (FiniteConfig.init (k := 2) (Oracle := Fin 2) (0 : Fin 2))
    (encList encBool) encFiniteConfig := by fun_prop

-- Boundary positions remain valid even with no input bits or work tapes.
example (action : Action 0 Bool Empty) : ComputableInPolyTime
    (fun cfg : FiniteCfg 0 Bool Empty => (cfg.step action).inputPos.val)
    encFiniteCfg encUnary := by fun_prop

-- The full configuration may have no oracle channels.
example : ComputableInPolyTime (FiniteConfig.init (k := 0) (Oracle := Empty) ())
    encBits encFiniteConfig := by fun_prop

-- Installing a reply of arbitrary length is charged to the encoded input of the operation.
example : ComputableInPolyTime
    (fun pair : Config × List Bool => pair.1.receive 1 0 (pair.2 ++ pair.2))
    (encPair encFiniteConfig encBits) encFiniteConfig := .of_tidy (by polytime)

-- One constant covers every input and every reply, including replies longer than the clock.
example : ∃ c : ℕ, ∀ word answer : List Bool,
    (encFiniteConfig ((FiniteConfig.init (k := 2) (Oracle := Fin 2) (0 : Fin 2) word).receive
      1 1 answer)).length ≤ c * (word.length + answer.length + 2) := by
  obtain ⟨c, hc⟩ := length_encFiniteConfig_le (k := 2) (State := Fin 2) (Oracle := Fin 2)
  refine ⟨c, fun word answer => ?_⟩
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    hc word.length 1 answer.length _
      ((FiniteConfig.spaceBound_init 0 word answer.length).receive 1 1 answer le_rfl)

end ComplexityTests.ConfigurationPolyTime
