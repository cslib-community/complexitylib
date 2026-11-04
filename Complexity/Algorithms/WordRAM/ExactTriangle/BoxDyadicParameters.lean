/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.BoxDyadicParameters.SourceBounds

/-!
# Computed integer parameters for the native box solver

One fixed sixteen-register program computes 2394-bit logarithm blocks, matrix level 63b,
groups 4^(2b), window 4^(63b), depth 21m and the exact small/fast flag. Actual initialized runs,
charges, original-memory preservation and logarithmic width/polynomial prefixes are proved.
The physical register names and embeddings are the shared `DyadicParameters.Reg` API.
These original integer parameters support the complete 1.9992 composition; this module only
computes them and does not decide a triangle problem by itself.
-/
