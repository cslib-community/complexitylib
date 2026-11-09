/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.SourceBounds
public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.TimeBound

/-!
# Complete native minimum-count prime selection

One fixed 160-register standard program reads raw `(n,D)` and three canonical signed
matrices, enumerates the square prime window with charged trial division, and calls the
actual cyclic-Strassen counter. It returns an attained minimum modular count, hence the
existing `ExactTriangle.IsSelectedPrime` and its finite false-positive bound apply.

## Main results

* `exec`: concrete caller execution, original-array and dirty-workspace frame.
* `runs_input`: actual original-input prefix and charged halt in the same final state.
* `timeBound_le_subcubic`: all native charges bounded by
  `3704*(sqrt(D)+1)^3*(n+1)^2.81 + 42*(D+1)`. The window dependence is explicit.
* `admissionWidth_le_log`: for `D ≤ n`, `κ ≥ 1` and weights bounded by `(n+2)^κ`,
  physical width `(κ+30)*clog₂(n+2)` suffices at every wider width.
* `bounded_reachable_polynomial`: all such wider prefixes have words and support bounded
  by `(n+2)^(2κ+60)`, independently of physical width.

`D ≥ 16` ensures a nonempty window; general execution permits `D > n` and empty matrices.
No prime list, counter run, time, answer or layout certificate is an input. The flat program
uses at most 32824 slots including halt and does not read physical width. Global ET
parameter/small-input handling, outer host composition and the full 3SUM endpoint remain open.

## References

Selectively adapts the minimum-update policy of Anthropic's
Programs/Sec3/Theorem17/Hashing/ChoosePrime.lean at revision
16a5ce41304fcdaea4e0be7c132e1c361dc26da5. Square enumeration and trial division replace its
prime-list producer. All native execution, word bounds, frames and instruction constants are
proved against the existing WordRAM semantics, without importing Light execution or costs.
-/
