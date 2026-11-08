/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Accounting
import Complexity.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Bounds
import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationBounds
import Mathlib.Tactic.Positivity

/-!
# Aggregate box-backed native fixed-prime charges

For `m = 9k`, the actual producer chunk cardinalities derive occurrence sparsity for every
real product.
Summing over the existing finite instances gives an aggregate product saving, with the
one-time preparation and all root/query/controller costs separate. Failed original-weight
scans use one global `F(p)+1` reserve, not that reserve per instance. The fixed prime is still
an input: this does not select parameters or establish the final ET/3SUM source exponent.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Conservative complete envelope: standalone preparation, all logical record charges, one
global failed-scan budget and controller/loop/halt work. The one-slot solver fits this envelope
without executing the standalone all-record preparation. No workspace clearing is charged. -/
@[expose] noncomputable def timeBound {m n : ℕ} (hn : 0 < n) (g p : ℕ)
    (values : List ℤ) (mem : ℕ → ℕ) : ℕ :=
  let V := fun q => values.getD q 0
  let wAB := fun u v : Fin n => V (pairIndex (u, v))
  let wBC := fun b c : Fin n => V (n * n + pairIndex (b, c))
  let wAC := fun u c : Fin n => V (2 * (n * n) + pairIndex (u, c))
  RecordProduct.preparationTime n (D m) g p values +
    (∑ idx ∈ instanceIndices wAB (D m) g p, recordBase (m := m) hn V mem idx) +
    (42 * pieceSize (D m) g + 28) * (falsePositiveCount wAB wBC wAC p + 1) + 7

/-- The existing finite family bounds the sum of actual queried-product charges, including a
standalone halt for each term as a conservative upper bound. Every occurrence bound is derived
from the real chunk count; there is no supplied sparse execution or solver premise. -/
theorem products_time_le {k n g p : ℕ} (hn : 0 < n) (values : ℕ → ℤ) (mem : ℕ → ℕ)
    (hD : 16 ≤ D (9 * k)) (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D (9 * k)))
    (hN : D (9 * k) ^ 18 ≤ n) :
    let I := instanceIndices (fun u v : Fin n => values (pairIndex (u, v))) (D (9 * k)) g p
    let qs := fun idx => RecordProduct.decodedQueries hn mem
      (RecordProduct.recordQueries n (D (9 * k)) p idx)
      (RecordProduct.recordQueryCount n (D (9 * k)) p values idx)
    ((∑ idx ∈ I, (RecordBoxProduct.timeBound (m := 9 * k) (qs idx) + 1) : ℕ) : ℝ) ≤
      125829120 * ((189 * k + 1 : ℕ) : ℝ) ^ 2 * ((9 * k + 1 : ℕ) : ℝ) *
        (D (9 * k) : ℝ) ^ (-(8 / 125 : ℝ)) * (n : ℝ) ^ 3 * g := by
  let I := instanceIndices (fun u v : Fin n => values (pairIndex (u, v))) (D (9 * k)) g p
  let qs := fun idx => RecordProduct.decodedQueries hn mem
    (RecordProduct.recordQueries n (D (9 * k)) p idx)
    (RecordProduct.recordQueryCount n (D (9 * k)) p values idx)
  let R : ℝ := 31457280 * ((189 * k + 1 : ℕ) : ℝ) ^ 2 * ((9 * k + 1 : ℕ) : ℝ) *
    (D (9 * k) : ℝ) ^ (-(8 / 125 : ℝ)) * (n : ℝ) ^ 2
  have hr (idx : InstanceIndex p) :
      ((RecordBoxProduct.timeBound (m := 9 * k) (qs idx) + 1 : ℕ) : ℝ) ≤ R := by
    apply RecordBoxProduct.thin_timeBound _ hN
    rw [RecordProduct.decodedQueries_length]
    exact (Nat.mul_le_mul_right (2 ^ (9 * k)) (min_le_left _ _)).trans
      (RecordProduct.queryCap_mul_two_pow_le n (9 * k))
  have hc : (I.card : ℝ) ≤ 4 * (n : ℝ) * g := by
    exact card_instanceIndices_le _ hD
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D (9 * k))).trans hN) hg hp
  calc
    _ = ∑ idx ∈ I, ((RecordBoxProduct.timeBound (m := 9 * k) (qs idx) + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
    _ ≤ ∑ _idx ∈ I, R := Finset.sum_le_sum (fun idx _ => hr idx)
    _ = I.card * R := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * (n : ℝ) * g) * R := mul_le_mul_of_nonneg_right hc (by dsimp only [R]; positivity)
    _ = _ := by dsimp only [R]; ring

/-- Complete halt-inclusive charged bound, retaining the one-time producer and the single
global failed-scan reserve. Root, query, ordinal, call, return and loop overheads are explicit.
In particular this is not a prime-selection or an unconditional aggregate exponent theorem. -/
theorem timeBound_le {k n g p : ℕ} (hn : 0 < n) (values : List ℤ) (mem : ℕ → ℕ)
    (hD : 16 ≤ D (9 * k)) (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D (9 * k)))
    (hN : D (9 * k) ^ 18 ≤ n) :
    let V := fun q => values.getD q 0
    let F := falsePositiveCount (fun u v : Fin n => V (pairIndex (u, v)))
      (fun b c => V (n * n + pairIndex (b, c)))
      (fun u c => V (2 * (n * n) + pairIndex (u, c))) p
    ((timeBound (m := 9 * k) hn g p values mem : ℕ) : ℝ) ≤
      690 * (n : ℝ) ^ 2 * D (9 * k) * g +
        125829120 * ((189 * k + 1 : ℕ) : ℝ) ^ 2 * ((9 * k + 1 : ℕ) : ℝ) *
          (D (9 * k) : ℝ) ^ (-(8 / 125 : ℝ)) * (n : ℝ) ^ 3 * g +
        (4 * (n : ℝ) * g) * ((5 * Nat.sqrt (D (9 * k)) + 8 * queryCap n (D (9 * k)) + 61 : ℕ) : ℝ) +
        (((42 * pieceSize (D (9 * k)) g + 28) * (F + 1) + 7 : ℕ) : ℝ) := by
  let V := fun q => values.getD q 0
  let I := instanceIndices (fun u v : Fin n => V (pairIndex (u, v))) (D (9 * k)) g p
  let qs := fun idx => RecordProduct.decodedQueries hn mem
    (RecordProduct.recordQueries n (D (9 * k)) p idx)
    (RecordProduct.recordQueryCount n (D (9 * k)) p V idx)
  let extra := 5 * Nat.sqrt (D (9 * k)) + 8 * queryCap n (D (9 * k)) + 61
  have hDn : D (9 * k) ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D (9 * k))).trans hN
  have hprep : (RecordProduct.preparationTime n (D (9 * k)) g p values : ℝ) ≤
      690 * (n : ℝ) ^ 2 * D (9 * k) * g := by
    have hnat : RecordProduct.preparationTime n (D (9 * k)) g p values ≤
        690 * n ^ 2 * D (9 * k) * g := by
      simpa only [RecordProduct.preparationTime, pow_two] using
        PreparationBounds.computed_timeBound_le values hD hDn hg hp
    exact_mod_cast hnat
  have hterms : (∑ idx ∈ I, recordBase (m := 9 * k) hn V mem idx) ≤
      (∑ idx ∈ I, (RecordBoxProduct.timeBound (m := 9 * k) (qs idx) + 1)) + I.card * extra := by
    rw [show I.card * extra = ∑ _idx ∈ I, extra by simp, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro idx _
    have hQ : RecordProduct.recordQueryCount n (D (9 * k)) p V idx ≤ queryCap n (D (9 * k)) :=
      min_le_left _ _
    dsimp only [recordBase, extra, qs]
    omega
  have hc : (I.card : ℝ) ≤ 4 * (n : ℝ) * g := card_instanceIndices_le _ hD hDn hg hp
  have hextra := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg extra : (0 : ℝ) ≤ extra)
  have hprod := products_time_le hn V mem hD hg hp hN
  have hcast := (Nat.cast_le (α := ℝ)).mpr hterms
  push_cast at hcast hprod
  have hbase : ((∑ idx ∈ I, recordBase (m := 9 * k) hn V mem idx : ℕ) : ℝ) ≤
      125829120 * ((189 * k + 1 : ℕ) : ℝ) ^ 2 * ((9 * k + 1 : ℕ) : ℝ) *
          (D (9 * k) : ℝ) ^ (-(8 / 125 : ℝ)) * (n : ℝ) ^ 3 * g + (4 * (n : ℝ) * g) * extra := by
    dsimp only [I, qs] at hcast hprod ⊢
    push_cast
    linarith only [hcast, hextra, hprod]
  dsimp only [timeBound]
  push_cast
  dsimp only [I, V, extra] at hbase hprep ⊢
  push_cast at hbase
  linarith only [hbase, hprep]

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime
