/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.SourceBounds
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.TimeBound

/-!
# Caller-safe complete fixed-prime ExactTriangle solver

The fixed 640-register standard program consumes runtime n,D,g,p, canonical-signed original
matrix pointers and a dirty workspace base. It preserves the selector's entire low 160-register
bank, its argument bank and original memory outside its computed working interval. It copies
only the original three arrays, computes its own virtual word modulus, and invokes the actual
one-time producer and all-record product/witness controller through the memory-window compiler.
No catalogue, layout, solver, witness, execution or time certificate is an algorithm input.

## Main definitions

* `CallableFixedPrime.program`: caller code; arguments 600–607, raw verdict/witness/scans 632–636.
* `CallableFixedPrime.entryProgram`: initialized original-input header delivery and caller code.
* `CallableFixedPrime.admissionWidth`: original-caller threshold including raw dirty words
  before remainder instructions.

## Main results

* `CallableFixedPrime.exec`: complete caller execution, exact original positive/negative decision,
  witness coordinates, caller frames and the single global scan bound S ≤ F(p) + returnedFlag.
* `CallableFixedPrime.runs_input`: actual initialized same-state prefix and charged halt.
* `CallableFixedPrime.timeBound_le`: aggregate charged source work plus real adaptation overhead.
* `CallableFixedPrime.bounded_reachable_caller`: width-independent word/support envelope from
  original caller words, including arbitrary original outside memory.
* `CallableFixedPrime.inputWidth_le_log`, `CallableFixedPrime.prefixBound_le_pow`: positive
  logarithmic initialized admission and polynomial envelope for every wider native prefix.

Correctness requires D=4^m ≥16, g≥1, p in the stated prime window and n≥D^18. Width bounds also
state original scalar, weight, placement and raw-word hypotheses explicitly. The initialized
clients use the original producer input encoding. The wrapper/compiler work is original;
underlying finite source identities and the concrete source solver retain their own credit.
Global parameter/prime choice, the outer ordinary-input host and the complete subquadratic 3SUM
bound remain separate. This module is not a complete solution to that broader objective.
-/
