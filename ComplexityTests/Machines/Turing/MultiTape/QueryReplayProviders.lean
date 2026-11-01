/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of native provider-window assembly)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayProvidersCorrect
public import ComplexityTests.Machines.Turing.MultiTape.NativeBlockCodec

/-!
# Native provider-window regressions

Provider selection preserves the previous control and uses blank windows at absent ports.
Every provider label is checked even when all ports are absent.
-/

public section

namespace ComplexityTests.QueryReplayProviders

open Turing.MultiTapePTM.BlockComputation.QueryReplay
open Providers
open NativeBlockCodec

def ports : PortMap 1 := fun _ d => if d = 0 then some 2 else if d = 2 then some 0 else none

def previous : RawResult 1 (Fin 1) :=
  (some 0, fun _ => 1, .accept, fun _ => [2, 1, 1, 2, 0, 0])

def providers : ProviderValues 1 (Fin 1) :=
  fun _ _ => (none, fun _ => 0, .empty, fun _ => [1, 2, 0, 0, 2, 1])

example : (let (_, _, _, cells) := combine (2, ports, previous, providers); cells 0) =
    [2, 1, 0, 0, 1, 2] := by decide

example : (let (control, _, _, _) := combine (2, ports, previous, providers); control) =
    some 0 := by decide

-- A huge binary width cannot allocate windows from a short malformed buffer.
def malformed := combine
  (1000000000, ((fun _ _ => none) : PortMap 1), raw, fun _ _ => raw)

example : (let (_, _, _, cells) := malformed; cells 0).length = 9 := by decide

def absent : PortMap 1 := fun _ _ => none

example : (Labels.combine code (1, absent, good, fun _ _ => good)).isSome = true := by decide
example : Labels.combine code (1, absent, fail, fun _ _ => good) = none := by decide
example : Labels.combine code (1, absent, good,
    fun _ d => if d = 2 then fail else good) = none := by decide
example : Labels.combine code (1, absent, good,
    fun _ d => if d = 1 then noncanonicalBlank else good) = none := by decide

end ComplexityTests.QueryReplayProviders
