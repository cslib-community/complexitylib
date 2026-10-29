/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.RawInput

/-!
# Actual producer chunks admit the native query copies

The class scanner's real coordinate stores and the existing finite chunk theorem derive
in-range query words. Their original occurrence count is the descriptor's computed minimum.
The power-of-four query-capacity bound supplies occurrence sparsity without assuming a sparse
execution or replacing a list length by a set cardinality.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The existing computed chunk capacity supplies the stronger occurrence bound at `4^m`. -/
theorem queryCap_mul_two_pow_le (n m : ℕ) : queryCap n (D m) * 2 ^ m ≤ n ^ 2 := by
  have hroot := Nat.sqrt_le ((n ^ 2) ^ 2 / D m)
  have hmul := (Nat.mul_le_mul_right (D m) hroot).trans
    (Nat.div_mul_le_self ((n ^ 2) ^ 2) (D m))
  have hD : D m = (2 ^ m) ^ 2 := by
    change 4 ^ m = (2 ^ m) ^ 2
    rw [← Nat.pow_mul, Nat.mul_comm m 2, Nat.pow_mul]
  have hs : (queryCap n (D m) * 2 ^ m) ^ 2 ≤ (n ^ 2) ^ 2 := by
    change (Nat.sqrt ((n ^ 2) ^ 2 / D m) * 2 ^ m) ^ 2 ≤ _
    rw [mul_pow, ← hD]
    simpa only [pow_two] using hmul
  nlinarith only [hs, Nat.zero_le (queryCap n (D m) * 2 ^ m), Nat.zero_le (n ^ 2)]

/-- The producer's actual scanner stores identify every local chunk occurrence with its
unique existing finite pair. Thus neither coordinate range nor the query count is supplied
as an independent adapter certificate. -/
theorem output_query_coordinates {n D g p : ℕ} (values : ℕ → ℤ)
    (wAB : Fin n → Fin n → ℤ) (hp : p ≠ 0)
    (hAB : ∀ a b, values (pairIndex (a, b)) = wAB a b)
    (hD : 1 ≤ D) (hDn : D ≤ n)
    {initial y : Data 64} (h : Instances.Output n D g p values initial y)
    (rho : Fin p) (k : ℕ)
    (hk : k < numChunks (residueClass wAB p rho) (queryCap n D)) :
    let q := 5 + 6 * (n * n) + p + 2 * rho.val * (n * n) + 2 * (k * queryCap n D)
    let Q := min (queryCap n D) ((residueClass wAB p rho).card - k * queryCap n D)
    (∀ i < Q, y.mem (q + 2 * i) < n ∧ y.mem (q + 2 * i + 1) < n) ∧
      (∀ i < Q, ∃! pair : Fin n × Fin n,
        pair ∈ chunkOf wAB D p rho k ∧
        rankIn (residueClass wAB p rho) pair = k * queryCap n D + i ∧
        y.mem (q + 2 * i) = pair.1.val ∧ y.mem (q + 2 * i + 1) = pair.2.val) := by
  let R := fun q => (values q % (p : ℤ)).toNat
  have hR (pair : Fin n × Fin n) : R (pairIndex pair) = (resFin hp (wAB pair.1 pair.2)).val := by
    dsimp only [R]
    rw [hAB]
    rfl
  have hscan := h.2.2.2.2.2.2.2.2.1
  have hread (q : ℕ) (hq : q < n * n) (hrho : R q = rho.val) :
      y.mem (5 + 6 * (n * n) + p + 2 * rho.val * (n * n) +
        2 * Nat.count (fun j => R j = rho.val) q) = q / n ∧
      y.mem (5 + 6 * (n * n) + p + 2 * rho.val * (n * n) +
        2 * Nat.count (fun j => R j = rho.val) q + 1) = q % n := by
    simpa only [R, Nat.mul_right_comm 2 (n * n) rho.val] using
      hscan rho.val rho.isLt q hq hrho
  have hcap : 0 < queryCap n D := one_le_queryCap hD hDn
  have hpair (i : ℕ) (hi : i < min (queryCap n D)
      ((residueClass wAB p rho).card - k * queryCap n D)) :=
    QuerySpec.chunk_readback wAB hp R hR D rho y.mem
      (5 + 6 * (n * n) + p + 2 * rho.val * (n * n)) hread hcap k hk i hi
  have haddr (i : ℕ) :
      5 + 6 * (n * n) + p + 2 * rho.val * (n * n) + 2 * (k * queryCap n D + i) =
        5 + 6 * (n * n) + p + 2 * rho.val * (n * n) + 2 * (k * queryCap n D) + 2 * i := by
    omega
  dsimp only
  constructor
  · intro i hi
    obtain ⟨pair, hpair, -⟩ := hpair i hi
    rw [haddr i] at hpair
    rw [hpair.2.2.1, hpair.2.2.2]
    exact ⟨pair.1.isLt, pair.2.isLt⟩
  · intro i hi
    simpa only [haddr i] using hpair i hi

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
