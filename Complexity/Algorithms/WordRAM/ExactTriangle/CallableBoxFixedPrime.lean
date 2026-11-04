/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableBoxFixedPrime.Prefix
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableBoxFixedPrime.TimeBound

/-!
# Complete caller-safe box-backed fixed-prime Exact Triangle

`CallableBoxFixedPrime.exec_at` runs the actual box controller from raw original signed
arrays and a dirty caller window. It retains the existing `CallableFixedPrime` ABI: eight
arguments600–607, raw verdict/witness/scans632–636, and the protected low160 selector bank.
The genuine array copy/sum and virtual-width setup are unchanged; `solve` really compiles
`BoxFixedPrime.program`. There is no clean-workspace or supplied solver/execution premise.

`runs_input` delivers original headers and arrays, and returns the same prehalt state and
charged halt, original-weight verdict, original-coordinate witness and one global failure
scan bound. `bounded_reachable_caller` and `bounded_reachable_input` use the existing numerical
admissions and polynomial envelopes for this actual new code at every wider admitted width.
The fixed program has640 registers and at most400014 flat slots including initialized setup
and halt; it never reads physical width.

For `m=9k`, `timeBound_le` adds actual copy/setup/return/halt costs and at most three times the
complete finite box-controller ledger, including preparation, the `D^(-8/125)` aggregate
product term, root/query/controller overhead and one global `F(p)+1` scan reserve.
Parameters and the prime are still explicit inputs. The existing parameter/prime-selecting
host has not switched to this program, and polynomial-factor absorption, actual parameter
retuning and ordinary 3SUM1.9992 remain open. No unconditional final exponent is claimed.
-/
