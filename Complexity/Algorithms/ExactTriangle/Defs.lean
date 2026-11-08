/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Int.Notation

/-!
# Exact Triangle on three integer weight matrices

The three parts have `t` vertices each. The matrices give the weights between the first and
second, second and third, and first and third parts. A triangle has weight zero when the sum of
its three edge weights is zero. A reduction can supply these matrices directly to a solver.

## Main definitions

* `ExactTriangle.HasZeroTriangle`: existence of a zero-weight triangle for arbitrary matrices.

## Main results

Algorithmic correctness theorems are stated in consumer modules.

## References

* [V. Vassilevska Williams and R. Williams, *Finding, minimizing, and counting weighted
  subgraphs*][VassilevskaWilliamsWilliams2013]

Adapted from `TriangleInstance.HasZeroTriangle` in `3sum-apsp/PaperStatements.lean`, lines
885–906, at `anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, specialized to `ℤ`
weights and with the three weight matrices passed as separate arguments.
-/

@[expose] public section

namespace Cslib.Algorithms.ExactTriangle

/-- A complete tripartite graph with `t` vertices per part has a zero-weight triangle.
The entries `wAB a b`, `wBC b c` and `wAC a c` weight the edges between parts A–B, B–C and A–C,
respectively. Some vertices `a`, `b`, `c` must satisfy `wAB a b + wBC b c + wAC a c = 0`. -/
def HasZeroTriangle {t : ℕ} (wAB wBC wAC : Fin t → Fin t → ℤ) : Prop :=
  ∃ a b c, wAB a b + wBC b c + wAC a c = 0

end Cslib.Algorithms.ExactTriangle
