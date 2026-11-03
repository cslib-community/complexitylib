/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.BoxParameterSelecting.InputProgram
public import Complexity.Algorithms.WordRAM.ExactTriangle.BoxParameterSelecting.Exec
public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Input

/-!
# Real original-input header execution and input admission

The raw input is n,F followed by canonical-signed AB/BC/AC in row-major order. The existing
counter input representation is reused only as this two-scalar encoding; F is not interpreted
as a supplied prime. All pointers and the workspace boundary are computed by actual code.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.BoxParameterSelecting

open ParameterSelecting

open Cslib.WordRAM

/-- Original scalar words and all original signed matrix words fit before the first instruction. -/
theorem input_fits {W n F : ℕ} (values : List ℤ) (hlen : values.length = 3 * (n * n))
    (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (hW : executionWidth n F (3 + 3 * (n * n)) 3 (3 + n * n) (3 + 2 * (n * n)) values ≤ W) :
    InputFits W (CountPrime.inputWords n F values) := by
  have fit := envelope_fits values hW
  have hn := Nat.le_mul_self n
  refine ⟨?_, ?_⟩
  · simpa only [CountPrime.inputWords, List.length_append, List.length_cons, List.length_nil,
      List.length_map, hlen, Nat.reduceAdd] using fit.of_le (by dsimp only [envelope]; omega)
  · intro v hm
    rcases List.mem_append.mp hm with hm | hm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact fit.of_le (by dsimp only [envelope]; omega)
      · exact fit.of_le (by dsimp only [envelope]; omega)
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hm
      have hb := hv z hz
      apply fit.of_le
      have henc : Signed.encode z ≤ 2 * F + 1 := by unfold Signed.encode; split_ifs <;> omega
      exact henc.trans (by dsimp only [envelope]; omega)

end Cslib.Algorithms.WordRAM.ExactTriangle.BoxParameterSelecting
