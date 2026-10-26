/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Monotone.Clique.LogarithmicPetals

/-! The dyadic parameter bounds have satisfiable hypotheses and actual computing circuits.
The first instance improves the exponent from the old public bound's `1024` to `2048`.
The second supplies a finite minimum complexity at a vertex count below `k ^ 4`. -/

namespace ComplexityTests.MonotoneCliqueParameters

open Cslib Cslib.Circuits Cslib.Circuits.Clique Cslib.Circuits.Monotone

/-- A real monotone implementation exists, and the stronger bound applies to it. -/
example : ∃ C : Circuit signature (edgeCount (262145 ^ 4)) 1,
    C.Computes interpretation (single (clique (262145 ^ 4) 262145)) ∧
      2 ^ 2048 < C.size := by
  obtain ⟨C, hC⟩ := exists_computes_clique (262145 ^ 4) 262145
  refine ⟨C, hC, ?_⟩
  have hbound := two_pow_mul_two_pow_lt_size_of_computes_clique (t := 8)
    (by norm_num) (by norm_num) (by rfl) hC
  simpa only [show (8 : ℕ) * 2 ^ 8 = 2048 by norm_num] using hbound

private abbrev widerVertexCount : ℕ := 1024 * 8 ^ 2 * 256 ^ 4 * 262145

/-- This vertex count is outside the old fourth-power range. -/
example : widerVertexCount < 262145 ^ 4 := by norm_num [widerVertexCount]

/-- The new range yields a finite circuit complexity above `64 ^ 256`, rather than a bound
that holds only because no monotone circuit computes the function. -/
example : ecomplexity interpretation (single (clique widerVertexCount 262145)) ≠ ⊤ ∧
    ((64 ^ 256 : ℕ) : ℕ∞) <
      ecomplexity interpretation (single (clique widerVertexCount 262145)) := by
  refine ⟨ecomplexity_clique_ne_top _ _, ?_⟩
  have hbound := sixtyFour_pow_two_pow_lt_ecomplexity_clique
    (n := widerVertexCount) (k := 262145) (t := 8)
    (by norm_num) (by norm_num) (by norm_num [widerVertexCount])
  simpa only [show (2 : ℕ) ^ 8 = 256 by norm_num] using hbound

end ComplexityTests.MonotoneCliqueParameters
