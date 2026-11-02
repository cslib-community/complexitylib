/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.DyadicParameters.SourceBounds

/-!
# Concrete native dyadic parameter preparation

From original n, one fixed 16-register standard program computes
`t = floor(log₂(n)/1296)`, `m = 36t`, `D = 4^m`, `g = 4^t` and `L = 19m` using actual
logarithm and power loops. Its raw flag is one exactly in the positive-t regime. The original
dimension and every memory word are preserved.

## Main results

* `exec`: actual caller computation from n and one derived numerical admission.
* `runs_input`: original State.init prefix and halt, at most `12*log₂(n)+36` instructions.
* `admissionWidth_le_log`: positive sufficient width at most `12*clog₂(n+2)`.
* `bounded_reachable_polynomial`: all admitted wider prefixes have words/support below
  `(n+2)^13`, independently of physical width.

The original mathematical choices satisfy `g^36 = D` and `D^18 ≤ n` for positive n. The fast
flag is one exactly when `2^1296 ≤ n`, which implies `D ≥ 16`. Zero/small inputs are classified;
this program does not yet dispatch a solver. These are deliberately coarse original choices,
not Anthropic's tuned parameters or the final 1.9992 theorem. Selected-prime/fixed-prime/outer
host composition and the full 3SUM endpoint remain open. The fixed program includes halt in
its 128-slot bound and never reads physical width.
-/
