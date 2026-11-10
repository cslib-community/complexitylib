/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.DyadicParameters.SourceBounds

/-!
# Computed integer parameters for the native box solver

One fixed sixteen-register program computes 2394-bit logarithm blocks, matrix level 63b,
groups 4^(2b), window 4^(63b), depth 21m and the exact small/fast flag. Actual initialized runs,
charges, original-memory preservation and logarithmic width/polynomial prefixes are proved.
The first fast input size is `2^2394`; smaller inputs are marked for exhaustive solving.
This canonical family replaces the former 1296-bit/36b/19m family. Reusing an old finite bound
requires checking its actual parameter and branch hypotheses. Physical register names and
embeddings remain the `DyadicParameters.Reg` API.
These original integer parameters support the complete 1.9992 composition; this module only
computes them and does not decide a triangle problem by itself.
-/
