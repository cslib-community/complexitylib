/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Callee

/-!
# Complete parameter-selecting native ExactTriangle execution

One fixed640-register standard program consumes original raw n,F and canonical-signed matrix
pointers, computes dyadic parameters, selects the attained minimum modular-count prime and
calls the complete caller-safe fixed-prime solver. Its actual computed small flag instead
executes the existing exhaustive solver below the fast regime. All six original arguments
are restored and raw Boolean6 decides the original `ExactTriangle.HasZeroTriangle`.

## Main results

* `callee`: actual `ThreeSum.Host.Callee633`, including a content/layout-independent natural
  time function, positive logarithmic admission and caller-prefix frame. Unused old words
  are arbitrary; physical prefix bounds additionally require their original raw bound.
* `runs_input_uniform`: actual initialized prefix and charged halt in the same final state,
  with original input fit, both verdict directions, restored arguments and complete frame.
* `inputWidth_le_log`: weights bounded by `(n+2)^κ` admit every width at least
  `(12332*(κ+9)+40)*clog₂(n+2)`, including zero and small dimensions.
* `bounded_reachable_polynomial`: all such wider initialized prefixes have words and new
  address support below `(n+2)^(12332*(κ+9)+41)`, independently of physical width.

The initialized input is exactly raw n,F followed by three row-major canonical-signed arrays;
the program computes their pointers. No parameter, prime, layout, run, solver or time
certificate is supplied. The initialized program has at most434015 slots including halt
and never reads physical width. Every save/copy/call/control/return instruction is charged.

This composes the original conservative parameter family and concrete native suppliers.
It does not assert the tuned source exponent, final ordinary-3SUM composition or #1394's
1.9992 endpoint. The selected-prime natural allowance is proved separately from this execution
composition. Original native glue and resource proofs use the existing WordRAM semantics;
no Anthropic Light execution, ring-operation charge or simulation axiom is imported.
-/
