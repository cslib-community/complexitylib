/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Prefix
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.SourceBounds
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.TimeBound

/-!
# Complete caller-safe box-backed fixed-prime Exact Triangle

`CallableFixedPrime.exec_at` runs the actual box controller from raw original signed
arrays and a dirty caller window. It retains the existing `CallableFixedPrime` ABI: eight
arguments600–607, raw verdict/witness/scans632–636, and the protected low160 selector bank.
The genuine array copy/sum and virtual-width setup are unchanged; `solve` really compiles
`StreamingFixedPrime.program`, constructing and consuming one physical slot per logical
record before a charged heap reset. There is no clean-workspace or supplied solver/execution
premise.

`runs_input` delivers original headers and arrays, and returns the same prehalt state and
charged halt, original-weight verdict, original-coordinate witness and one global failure
scan bound. `bounded_reachable_caller` and `bounded_reachable_input` use the existing numerical
admissions and polynomial envelopes for this actual new code at every wider admitted width.
The fixed program has640 registers and at most400014 flat slots including initialized setup
and halt; it never reads physical width.

For `m=9k`, `timeBound_le` adds actual copy/setup/return/halt costs and at most three times the
complete finite box-controller ledger, including preparation, the `D^(-8/125)` aggregate
product term, root/query/controller overhead and one global `F(p)+1` scan reserve.
Parameters and the prime are explicit inputs of this component. The canonical
`ParameterSelecting.callee` computes them and calls this program, with complete actual time
`Oκ(n^(3-33/20000))`. The ordinary endpoint is `ThreeSum.Decision.exists_one9992_runs`;
this component's finite bound keeps its explicit geometry and selected-prime premises.
-/
