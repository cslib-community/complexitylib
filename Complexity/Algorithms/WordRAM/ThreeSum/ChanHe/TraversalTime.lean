/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalVisit
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalModel

/-!
# Charged bounds for the native Chan–He worklist

The per-node estimate includes both complete modulus searches and the complete packing program.
It is cubic in the candidate bound, rather than quadratic in the input length. The root estimate
also charges skipped calls, stack transfers, branches and loop control.

## Main definitions

* `visitTime`, `rootTime`: uniform charged bounds for one live visit and one complete root.
* `allocationSize`: maximum fresh allocation for one live visit.

## Main results

* `visit_cost_le`: the exact executed call bound is covered by `visitTime`.
* `allocation_le`: the concrete node allocation is covered by `allocationSize`.

These estimates are original; their starting costs are the proved native execution bounds.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- Both searches, the actual node program, argument delivery and the output-table store. -/
def visitTime (n m N : ℕ) : ℕ :=
  2 * (m + 1) * (102 * n + 15 * m ^ 2 + 102) +
    300 * n + 15 * m ^ 2 + 15 * m + 12 * N + 386

/-- Root setup and every possible transition, including empty and zero-fuel entries. -/
def rootTime (f n m N : ℕ) : ℕ := 70 + Math.work f * (visitTime n m N + 316)

/-- Three heavy count cells, three heavy buffers, four packed blocks, scratch and histogram. -/
def allocationSize (n m N : ℕ) : ℕ := 3 + 6 * n + 4 * N + m ^ 2

/-- The exact charged cost from the complete native visit is uniformly bounded. -/
theorem visit_cost_le (x : Data 128) (n m N M : ℕ)
    (hlen : ∀ j, x.regs (arrayLength j) ≤ n) (hm : x.regs limit ≤ m)
    (hN : x.regs groups ≤ N) (hM : M ≤ m ^ 2) :
    Modulus.cost ((modulusState x).comap kernel) +
      66 * (recordLayout x M).total + 15 * M + 12 * x.regs groups + 277 ≤
        visitTime n m N := by
  have hs : x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6) ≤ 3 * n := by
    have h₀ := hlen 0
    have h₁ := hlen 1
    have h₂ := hlen 2
    change x.regs (slot 2) ≤ n at h₀
    change x.regs (slot 4) ≤ n at h₁
    change x.regs (slot 6) ≤ n at h₂
    omega
  have hp := Nat.mul_le_mul (Nat.add_le_add_right hm 1)
    (show 34 * (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) +
        15 * x.regs limit ^ 2 + 102 ≤ 102 * n + 15 * m ^ 2 + 102 by
      have := Nat.pow_le_pow_left hm 2
      omega)
  change 2 * ((x.regs limit + 1) *
      (34 * (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) +
        15 * x.regs limit ^ 2 + 102) + 9) +
      34 * (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) +
      15 * x.regs limit + 91 +
      66 * (x.regs (slot 2) + x.regs (slot 4) + x.regs (slot 6)) +
      15 * M + 12 * x.regs groups + 277 ≤ _
  dsimp only [visitTime]
  rw [Nat.mul_assoc]
  omega

/-- The actual next heap pointer advances by at most the uniform per-node allocation. -/
theorem allocation_le (x : Data 128) (n m N M : ℕ)
    (hlen : ∀ j, x.regs (arrayLength j) ≤ n) (hN : x.regs groups ≤ N)
    (hM : M ≤ m ^ 2) :
    (recordLayout x M).endpoint ≤ x.regs heap + allocationSize n m N := by
  have h₀ := hlen 0
  have h₁ := hlen 1
  have h₂ := hlen 2
  rw [recordLayout_endpoint]
  change x.regs (slot 2) ≤ n at h₀
  change x.regs (slot 4) ≤ n at h₁
  change x.regs (slot 6) ≤ n at h₂
  dsimp only [allocationSize]
  omega

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
