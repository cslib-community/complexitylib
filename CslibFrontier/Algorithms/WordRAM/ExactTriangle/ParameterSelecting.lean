/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Asymptotics

/-!
# Automatic native box-backed Exact Triangle

The complete fixed 640-register program computes its integer parameters and a genuine
minimum-count prime, calls the actual box solver, and uses the actual exhaustive branch on
small inputs. Its initialized and matrix-function clients prove both directions of the
original signed-weight verdict while retaining original inputs and the caller frame.
`callee` supplies the existing 633-scratch native host interface with logarithmic admission
coefficient 123357. Its time is uniformly `Oκ(n^(3-33/20000))` for polynomial original weights;
coefficients and thresholds precede all original inputs, selected primes and physical widths.

The canonical scalar/argument/result register names are `ParameterSelecting.Reg`; parameter
fields use `DyadicParameters.Reg`. The fixed-prime controller and its callable wrapper are
`StreamingFixedPrime` and `CallableFixedPrime`; no second conservative pipeline is maintained.
Source-modulus width, dirty-memory clipping and original-word prefix bounds are proved for
this actual program. Native integer parameter tuning and the complete charged composition
are original; the lower-level reductions and box mathematics retain their source credit.
The ordinary composition is `ThreeSum.Decision.exists_one9992_runs`. Its supplier-independent
runtime transfer is in `ThreeSum.Decision.Runtime` and `ThreeSum.Decision.Transfer`: every
actual uniform ET saving `0 < δ ≤ 1` gives every ordinary exponent `a > 2-δ/2`.
-/
