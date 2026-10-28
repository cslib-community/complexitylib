/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalCall

/-!
# A shared polynomial envelope for native traversal calls

The dynamic heap and all input blocks lie below `H`; each list has at most `n` elements.
The candidate bound, label parameter, magnitude and common group count have fixed bounds
`m,Λ,U,N`. A fourth-degree polynomial covers both existing kernel envelopes, including their
native setup. This bound is later instantiated at the worklist's global heap frontier.

## Main definitions

* `envelope`: a common polynomial bound for the actual native modulus and node calls.

## Main results

* `modulus_budget_le_envelope`: the concrete selector budget is covered.
* `node_budget_le_envelope`: every selected modulus at most `m²` is covered.

The envelope and elementary inequalities are original resource estimates.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- One fixed polynomial in the heap, list, candidate, label, magnitude and output-size bounds. -/
def envelope (H n m Λ U N : ℕ) : ℕ :=
  65536 * (H + n + m ^ 2 + Λ + m + U + N + 100) ^ 4

/-- The common envelope covers each size parameter and every smaller native word. -/
theorem envelope_ge_sum (H n m Λ U N : ℕ) :
    H + n + m ^ 2 + Λ + m + U + N + 100 ≤ envelope H n m Λ U N := by
  have h := Nat.le_self_pow (by decide : 4 ≠ 0)
    (H + n + m ^ 2 + Λ + m + U + N + 100)
  dsimp only [envelope]
  omega

private theorem square_le_fourth {S : ℕ} (hS : 1 ≤ S) : S ^ 2 ≤ S ^ 4 := by
  have hsq : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ hS
  calc S ^ 2 ≤ S ^ 2 * S ^ 2 := Nat.le_mul_of_pos_right _ hsq
    _ = S ^ 4 := by ring

private theorem cube_le_fourth {S : ℕ} (hS : 1 ≤ S) : S ^ 3 ≤ S ^ 4 := by
  calc S ^ 3 ≤ S ^ 3 * S := Nat.le_mul_of_pos_right _ hS
    _ = S ^ 4 := by ring

/-- The exact selector envelope, including all copied source pointers and histogram addresses,
is bounded by one polynomial in the runtime size bounds. -/
theorem modulus_budget_le_envelope (x : Data 128) (H n m Λ U N : ℕ)
    (hheap : x.regs heap ≤ H)
    (hsrc : ∀ j, x.regs (arraySource j) + x.regs (arrayLength j) ≤ H)
    (hlen : ∀ j, x.regs (arrayLength j) ≤ n)
    (hm : x.regs limit ≤ m) (hΛ : x.regs digits ≤ Λ)
    (hcard : x.regs primeCount ≤ m) (hbitmap : x.regs bitmap ≤ H) :
    Modulus.budget ((modulusState x).comap kernel) ≤ envelope H n m Λ U N := by
  let S := H + n + m ^ 2 + Λ + m + U + N + 100
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hline : 7 * H + 3 * n + m ^ 2 + m + 100 ≤ 7 * S := by dsimp [S]; omega
  have ha : 3 * n + 1 ≤ 3 * S := by dsimp [S]; omega
  have hb : 3 * Λ + m + 1 ≤ 3 * S := by dsimp [S]; omega
  have hprod : (3 * n + 1) ^ 2 * (3 * Λ + m + 1) ≤ 27 * S ^ 3 := by
    calc (3 * n + 1) ^ 2 * (3 * Λ + m + 1)
        ≤ (3 * S) ^ 2 * (3 * S) := Nat.mul_le_mul (Nat.pow_le_pow_left ha 2) hb
      _ = 27 * S ^ 3 := by ring
  have hns : x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6) ≤ 3 * n := by
    have h₀ := hlen 0
    have h₁ := hlen 1
    have h₂ := hlen 2
    change x.regs (slot 2) ≤ n at h₀
    change x.regs (slot 4) ≤ n at h₁
    change x.regs (slot 6) ≤ n at h₂
    omega
  have hss : x.regs (slot 1) + x.regs (slot 3) + x.regs (slot 5) ≤ 3 * H := by
    have h₀ := hsrc 0
    have h₁ := hsrc 1
    have h₂ := hsrc 2
    change x.regs (slot 1) + x.regs (slot 2) ≤ H at h₀
    change x.regs (slot 3) + x.regs (slot 4) ≤ H at h₁
    change x.regs (slot 5) + x.regs (slot 6) ≤ H at h₂
    omega
  have hbudget : Modulus.budget ((modulusState x).comap kernel) ≤
      7 * H + 3 * n + (3 * n + 1) ^ 2 * (3 * Λ + m + 1) + m ^ 2 + m + 100 := by
    change x.regs heap + x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6) +
      x.regs heap + x.regs bitmap + x.regs (slot 1) + x.regs (slot 3) + x.regs (slot 5) +
      (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6) + 1) ^ 2 *
        (3 * x.regs digits + x.regs primeCount + 1) + x.regs limit ^ 2 + x.regs limit + 100 ≤ _
    have hp := Nat.mul_le_mul
      (Nat.pow_le_pow_left (Nat.add_le_add_right hns 1) 2)
      (show 3 * x.regs digits + x.regs primeCount + 1 ≤ 3 * Λ + m + 1 by omega)
    have hsq := Nat.pow_le_pow_left hm 2
    omega
  have hsf : S ≤ S ^ 4 := Nat.le_self_pow (by decide) S
  have hcf := cube_le_fourth hS
  change _ ≤ 65536 * S ^ 4
  omega

/-- The node layout, including every allocated output/scratch cell and tag value, is covered
uniformly for every selected product at most `m²`. -/
theorem node_budget_le_envelope (x : Data 128) (H n m Λ U N M : ℕ)
    (hheap : x.regs heap ≤ H) (hlen : ∀ j, x.regs (arrayLength j) ≤ n)
    (hM : M ≤ m ^ 2) (hU : x.regs magnitude ≤ U) (hN : x.regs groups ≤ N) :
    (recordLayout x M).budget ≤ envelope H n m Λ U N := by
  let S := H + n + m ^ 2 + Λ + m + U + N + 100
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hns : (recordLayout x M).total ≤ 3 * n := by
    have h₀ := hlen 0
    have h₁ := hlen 1
    have h₂ := hlen 2
    change x.regs (arrayLength 0) + x.regs (arrayLength 1) + x.regs (arrayLength 2) ≤ 3 * n
    omega
  have hinner : (recordLayout x M).base + (recordLayout x M).total + M +
      (recordLayout x M).N + (recordLayout x M).U + 1 ≤ 3 * S := by
    change x.regs heap + (recordLayout x M).total + M + x.regs groups +
      x.regs magnitude + 1 ≤ 3 * S
    dsimp only [S]
    omega
  calc (recordLayout x M).budget
      ≤ 4096 * (3 * S) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hinner 2)
    _ = 36864 * S ^ 2 := by ring
    _ ≤ 65536 * S ^ 4 := by have := square_le_fourth hS; omega

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
