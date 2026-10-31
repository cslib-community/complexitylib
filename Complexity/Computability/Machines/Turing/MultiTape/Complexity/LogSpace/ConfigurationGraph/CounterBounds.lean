/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame

/-!
# Polynomial counter bounds for configuration-graph writers

The STCON writer and the fair-coin table writer enumerate the same polynomial compact box.
`configurationCounter_bounds` gives a common bound for the loop counters, original input length,
and ternary symbol/count scratch register in terms of the length of the framed input.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.configurationCounter_bounds`: the standard counter bound.
* `Turing.MultiTapeNTM.ConfigurationGraph.clockedVertexBound_add_one_le_pow`: the clocked box
  and its final counter value have a fixed polynomial bound.
-/

public section

namespace Turing.MultiTapeNTM.ConfigurationGraph

open MultiTapeTM

/-- The polynomial counter bound dominates the compact box plus one, the input length, and two.
The statement includes exponent zero and the empty original word. -/
theorem configurationCounter_bounds {k : ℕ} (D : ℕ) (w : List Bool) :
    vertexBound (k := k) (radix D w.length) + 1 ≤
      ((frame w).length + 1) ^ (D * Fintype.card (Register k) + 1) ∧
    w.length ≤ ((frame w).length + 1) ^ (D * Fintype.card (Register k) + 1) ∧
    2 ≤ ((frame w).length + 1) ^ (D * Fintype.card (Register k) + 1) := by
  set L := w.length
  set E := D * Fintype.card (Register k)
  have hVB : vertexBound (k := k) (radix D L) = (L + 2) ^ E := vertexBound_eq_pow D L
  have hpow : (L + 2) ^ E ≤ (2 * L + 2) ^ E := Nat.pow_le_pow_left (by omega) E
  have hone : 1 ≤ (2 * L + 2) ^ E := Nat.one_le_pow _ _ (by omega)
  have hB : ((frame w).length + 1) ^ (E + 1) = (2 * L + 2) ^ E * (2 * L + 2) := by
    rw [length_frame, show 2 * L + 1 + 1 = 2 * L + 2 by omega, pow_succ]
  have hmul : (2 * L + 2) ^ E * 2 ≤ (2 * L + 2) ^ E * (2 * L + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have hmul' : 2 * L + 2 ≤ (2 * L + 2) ^ E * (2 * L + 2) := Nat.le_mul_of_pos_left _ hone
  rw [hB]
  exact ⟨by omega, by omega, by omega⟩

/-- With the standard polynomial horizon, the full clocked compact box plus one is bounded by
a fixed power of `2 * (n + 1)`, including at the empty input and zero exponents. -/
theorem clockedVertexBound_add_one_le_pow {k : ℕ} (D d n : ℕ) :
    (2 * (2 * (n + 1)) ^ d + 1) * vertexBound (k := k) (radix D n) + 1 ≤
      (2 * (n + 1)) ^ (D * Fintype.card (Register k) + d + 2) := by
  let F := 2 * (n + 1)
  let E := D * Fintype.card (Register k)
  have hF : 2 ≤ F := by dsimp [F]; omega
  have hN : vertexBound (k := k) (radix D n) ≤ F ^ E := by
    rw [vertexBound_eq_pow]
    exact Nat.pow_le_pow_left (by dsimp [F]; omega) E
  have hE : 1 ≤ F ^ E := Nat.one_le_pow _ _ (by omega)
  have hd : 1 ≤ F ^ d := Nat.one_le_pow _ _ (by omega)
  change (2 * F ^ d + 1) * vertexBound (k := k) (radix D n) + 1 ≤ F ^ (E + d + 2)
  calc
    _ ≤ (2 * F ^ d + 1) * F ^ E + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hN) 1
    _ ≤ (F ^ E * F ^ d) * 4 := by nlinarith
    _ ≤ (F ^ E * F ^ d) * F ^ 2 :=
      Nat.mul_le_mul_left _ (by nlinarith [sq_nonneg (F - 2 : ℤ)])
    _ = F ^ (E + d + 2) := by rw [pow_add, pow_add]

end Turing.MultiTapeNTM.ConfigurationGraph
