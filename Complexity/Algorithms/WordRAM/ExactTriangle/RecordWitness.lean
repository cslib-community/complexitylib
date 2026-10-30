/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.TimeBound

/-!
# Native per-record ExactTriangle witness recovery

One fixed standard unsigned WordRAM program starts from the existing original `(D,g,n,p)`
headers and three canonical-signed weight arrays. It runs the real producer, selects the first
occupied record, calls the actual native queried product, reads its actual answers/interleaved
pairs and verifies the original signed sums. No catalogue, layout, execution, answer, witness,
fit or time certificate is an algorithm input. The generic caller supports any occupied record.

## Main definitions

* `RecordWitness.program`, `RecordWitness.entryProgram`: caller and initialized code, using
  400 fixed registers with the complete 320-register product bank and 32-register verifier.
* `RecordWitness.admissionWidth`, `RecordWitness.wordBound`: original-input width and prefix
  word/support envelopes, independent of every larger admitted physical width.

## Main results

* `RecordWitness.exec_of_output`: actual product and verification for a genuine producer output.
* `RecordWitness.runs_input`: original `State.init`, same-state prefix `Runs`, charged halt,
  finite chunk/piece correctness, original-coordinate witness and caller frame.
* `RecordWitness.admissionWidth_le_log`, `RecordWitness.wordBound_le_pow`,
  `RecordWitness.bounded_reachable_original`: positive logarithmic width and polynomial words
  and memory support at every prefix, including physical dirty loads before normalization.
* `RecordWitness.initialized_time_le`: preparation and actual product charges, plus all actual
  root/query/control work and scans; unsuccessful records have no extra successful-scan term.

The physical program is fixed and has at most 133120 flat slots including halt. Geometry is
`D=4^m≥16`, `L=19m`, `n≥D^18`, `g≥1`, and `p` in the existing source prime window. The raw
0/1 matrix words are converted exactly once by the reused real product. Native success is
equivalent to an original zero in the selected chunk/piece. The actual scan counter satisfies
`S≤falsePositiveCount+returnedFlag`, where the returned flag is raw unsigned 0/1. All memory
outside the original product window and the low producer bank are preserved.

This is a per-record component. Prime/global parameter selection, the outer ET instance loop,
aggregate subcubic ET analysis and the full ordinary 3SUM 1.9992 endpoint remain open under #1394.
No curated headline abstract is affected.

## References

The original-weight scan and short-circuit accounting adapt
[Scan.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/Scan.lean#L73-L89)
and [ScanPairs.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/ScanPairs.lean#L69-L70).
The native code, initialized composition, fits, frames and instruction constants are original;
no Light-machine execution or resource bound is transferred by assumption. Finite `scanPiece`
returns its first zero, while the native verifier returns its last zero in the same interval;
their failure conditions agree, and every returned original-coordinate witness is verified.
-/
