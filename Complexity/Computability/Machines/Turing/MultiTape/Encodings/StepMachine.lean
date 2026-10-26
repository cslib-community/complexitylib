/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.StepMachineCompiler

/-!
# Resource-certified step machines

`Turing.StepMachine.ResourceCertificate` gives charged plain certificates for the halting test
and one step. Its compiler retains the original time, workspace, halting and output contracts;
whole-run conclusions use uncharged `Turing.MultiTapeTM.ComputableInBigO`.

The realizing-machine constructions and normal-form proofs live in the internal machine kernel.
-/
