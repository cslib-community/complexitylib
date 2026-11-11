/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.TraceRank

/-!
# Rank from trace moments, and rank under a change of scalars

The trace inequality is an equality for the identity matrix, where both sides are `n ^ 2`. A
rational matrix has the same rank over the reals.
-/

public section

namespace CslibFrontierTests.TraceRank

open Matrix

/-- For the identity matrix the trace inequality is the equality `3 ^ 2 = 3 * 3`. -/
theorem trace_inequality_one :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * 1).trace ^ 2 =
      (1 : Matrix (Fin 3) (Fin 3) ℝ).rank *
        ((1ᵀ * 1) * (1ᵀ * 1) : Matrix (Fin 3) (Fin 3) ℝ).trace := by
  simp [rank_one]
  norm_num

example (A : Matrix (Fin 2) (Fin 3) ℚ) : (A.map (algebraMap ℚ ℝ)).rank = A.rank :=
  rank_map_of_field _ A

example (A : Matrix (Fin 2) (Fin 3) ℝ) :
    (Aᵀ * A).trace ^ 2 ≤ A.rank * ((Aᵀ * A) * (Aᵀ * A)).trace :=
  sq_trace_le_rank_mul_trace_sq A

end CslibFrontierTests.TraceRank
