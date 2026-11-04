/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.Resources
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.Bilinear

/-!
# Native batches sharing a sparse box table

One fixed 64-register standard WordRAM program reads original signed leaf arrays and
an ordinary wanted-code list, builds the shared geometry and retained values once,
and computes each wanted sparse query. Answers are stored in order, including repeated
requests. No intermediate table, layout, execution or timing oracle is an input.

## Main definitions

* `BoxBatch.queryProgram`: reusable native batch over actual table readback.
* `BoxBatch.program`: original-input preparation followed by the complete batch.
* `BoxBatch.input`: original headers, signed arrays and wanted codes.
* `BoxBatch.admissionWidth`: sufficient physical width derived from original parameters.

## Main results

* `BoxBatch.exec_queryProgram`: charged batch execution, exact answers and memory frames.
* `BoxBatch.runs_wide`: initialized prefix and charged halt sharing the same answer memory.
* `BoxBatch.runs_bilinear`: canonical encodings compute all original bilinear-product coordinates.
* `BoxBatch.queryTime_eq_alpha`: sparse query work plus linear batch overhead.
* `BoxBatch.preparationTime_le`: one separate geometry and retained-table charge.
* `BoxBatch.prefix_bounded`: original-input bounds at every wider execution prefix.

This original native controller reuses the finite query semantics of `BoxQuery`; it
introduces no further source theorem. It consumes the wanted list as original data.
Constructing that list from matrix entries, scheduling all tiles with shared geometry,
and the improved complete thin-product/Exact Triangle bound remain separate work toward
the ordinary-3SUM exponent 1.9992. No end-to-end exponent is claimed here.
-/
