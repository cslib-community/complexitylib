/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Bounds
public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Flat

/-!
# Actual prepared Exact Triangle records using native box products

The original four headers and three signed weight arrays run `Instances.program`, select an
occupied record, prepare the five scalar header words and appended threshold `m / 9` at level
`21 * m`, and pass physical source pointers to `PointerBoxProduct.program`, which gathers the raw
zero/one matrices and interleaved query occurrences directly into its computed snapshot. No
producer layout, table, sparse-count, solver, run or time certificate is supplied to the
initialized client. Exact product answers, caller frame, preserved producer registers and charged
halt share one final state.

The shared original-input width functions are `RecordProduct.admissionWidth` and
`RecordProduct.admissionWidth_le_log`. The producer is charged by `RecordProduct.preparationTime`;
its output supplies every source pointer and the query-occurrence sparsity condition. The finite
saving `RecordBoxProduct.thin_timeBound` is proved at `m = 9 * k`.

## Main definitions

* `RecordBoxProduct.program`: record preparation, threshold patch and pointer-gather box call.
* `RecordBoxProduct.entryProgram`: `Instances.program` producer followed by the first record call.
* `RecordBoxProduct.gatherTimeBound`: per-record charge for scalar preparation, pointer delivery and
  `PointerBoxProduct.program`.
* `RecordBoxProduct.timeBound`: conservative per-record charge envelope retained by callers, with
  producer work separate.

## Main results

* `RecordBoxProduct.gatherTimeBound_le_timeBound`: `gatherTimeBound` is bounded by `timeBound`.
* `RecordBoxProduct.exec_of_output`: arbitrary occupied record from a genuine `Instances.Output`.
* `RecordBoxProduct.runs_input`: original-input initialized execution, answers, frame and halt.
* `RecordBoxProduct.thin_timeBound`: finite `D^(-8/125)` saving including adapter and halt.

Candidate verification, one-slot fixed-prime traversal and automatic parameter selection build on
this per-record consumer in `BoxRecordWitness`, `StreamingFixedPrime` and `ParameterSelecting`.
-/
