/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Bounds

/-!
# Actual prepared Exact Triangle records using native box products

The original four headers and three signed weight arrays run the existing native
producer, select an actual occupied record, copy its original zero/one matrices and
coordinates, write the changed level/length and appended threshold, and invoke the
actual compiled box product. No producer layout, table, sparse-count, solver, run or
time certificate is supplied to the initialized client. Exact product answers,
caller frame, preserved producer registers and charged halt share one final state.

The shared original-input width functions are `RecordProduct.admissionWidth` and
`RecordProduct.admissionWidth_le_log`. The unchanged producer is charged by
`RecordProduct.preparationTime`; its actual output supplies every pointer and the
query-occurrence sparsity condition. The selected record uses level `21*m` and
threshold `m/9`. Its finite saving is asserted only at `m=9k`.

## Main definitions

* `RecordBoxProduct.program`: actual record preparation, threshold patch and native box call.
* `RecordBoxProduct.entryProgram`: original producer followed by the first actual record call.
* `RecordBoxProduct.timeBound`: complete per-record charge, with producer work separate.

## Main results

* `RecordBoxProduct.exec_of_output`: arbitrary occupied record from a genuine producer output.
* `RecordBoxProduct.runs_input`: original-input initialized execution, answers, frame and halt.
* `RecordBoxProduct.thin_timeBound`: finite `D^(-8/125)` saving including adapter and halt.

This supplies one improved record consumer. The full ET controller and callee still
use the previous backend. Their replacement, aggregate subcubic bound, native parameter
retuning and ordinary-3SUM exponent 1.9992 remain open under #1394.
-/
