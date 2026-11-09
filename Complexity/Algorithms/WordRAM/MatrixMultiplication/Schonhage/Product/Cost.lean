/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Routing
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Tiles

/-!
# Complete native queried-product instruction ledger

## Main definitions

* `QueriedProduct.timeBound`: actual routing, copies, conversion, shared encoding, one directory
  initialization, all tile calls, reconstruction and original-input restoration; halt is separate.

Every term is derived from ordinary original inputs and the finite pruned trace definition.
No solver or running-time assertion is supplied as an input field.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.Algorithms.MatrixMultiplication.Schonhage
open scoped BigOperators

/-- A uniform instruction bound for either original signed inputs or raw nonnegative inputs.
The raw-conversion envelope charges a multiplication for every original matrix entry. -/
@[expose] public def timeBound {L m N : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N)) : ℕ :=
  routingTimeBound L m N qs.length + (8 * (2 * (N * D m)) + 10) +
    BandPreparation.timeBound L m N + (5 * 10 ^ L + 5) +
    ((∑ t ∈ Finset.range (numBands L m N ^ 2), tileCharge hm qs t) + 2) +
    (9 * qs.length + 3) + (7 * inputEnd m N qs.length + 10)

private theorem sum_bucket_counts (key : ℕ → ℕ) (Q T : ℕ) :
    (∑ t ∈ Finset.range T, Nat.count (fun i => key i = t) Q) =
      Nat.count (fun i => key i < T) Q := by
  induction T with
  | zero => simp
  | succ T ih => rw [Finset.sum_range_succ, ih, CountingSort.count_lt_succ]

private theorem sum_tile_indices (B : ℕ) (f : ℕ × ℕ → ℕ) :
    (∑ t ∈ Finset.range (B ^ 2), f (t / B, t % B)) =
      ∑ p ∈ Finset.range B ×ˢ Finset.range B, f p := by
  have he := (finProdFinEquiv : Fin B × Fin B ≃ Fin (B * B)).symm.sum_comp
    (fun p => f (p.1.val, p.2.val))
  change (∑ t : Fin (B * B), f (t.val / B, t.val % B)) =
    ∑ p : Fin B × Fin B, f (p.1.val, p.2.val) at he
  rw [pow_two, Finset.sum_product,
    ← Fin.sum_univ_eq_sum_range (fun t => f (t / B, t % B)) (B * B), he,
    Fintype.sum_prod_type,
    Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin B, f (i, j.val)) B]
  exact Finset.sum_congr rfl (fun i _ => Fin.sum_univ_eq_sum_range (fun j => f (i, j)) B)

/-- The exact sum of occurrence-dependent call charges uses every original request once.
It uses no distinct-set bound on list multiplicity. -/
public theorem sum_tileCharge {L m N : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N)) :
    (∑ t ∈ Finset.range (numBands L m N ^ 2), tileCharge hm qs t) =
      (4 * L + 66) * numBands L m N ^ 2 + 29 * qs.length +
        ∑ T ∈ tiles L m N,
          PrunedQuery.traceWeight (wantedStrings (MaskTable.layout hm) qs.toFinset T.1 T.2) := by
  have hkey (i : ℕ) (hi : i < qs.length) :
      (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) i < numBands L m N ^ 2 :=
    Wanted.tileKey_lt hm _ (Wanted.inputPairs_lt qs i hi).1 (Wanted.inputPairs_lt qs i hi).2
  have hcount := sum_bucket_counts (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length
    (numBands L m N ^ 2)
  rw [Nat.count_of_forall hkey] at hcount
  simp only [tileCharge, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, smul_eq_mul, ← Finset.mul_sum]
  have htiles := sum_tile_indices (numBands L m N) (fun T =>
    PrunedQuery.traceWeight (wantedStrings (MaskTable.layout hm) qs.toFinset T.1 T.2))
  rw [hcount, htiles]
  unfold tiles
  ring

/-- Sum the actual native kernel trace charges using the existing contributing-leaf bound. -/
public theorem sum_traceWeight_le {L m N : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N)) :
    (∑ T ∈ tiles L m N,
      PrunedQuery.traceWeight (wantedStrings (MaskTable.layout hm) qs.toFinset T.1 T.2)) ≤
      8192 * (L + 1) *
        (∑ T ∈ tiles L m N,
          (leaves (wantedStrings (MaskTable.layout hm) qs.toFinset T.1 T.2)).card) +
        4096 * numBands L m N ^ 2 := by
  have h := Finset.sum_le_sum (s := tiles L m N)
    (fun T _ => PrunedQuery.traceWeight_le
      (wantedStrings (MaskTable.layout hm) qs.toFinset T.1 T.2))
  have hc : (tiles L m N).card = numBands L m N ^ 2 := by
    simp only [tiles, Finset.card_product, Finset.card_range, pow_two]
  have heq (v : ℕ) : 4096 * (2 * (L + 1) * v + 1) = 8192 * (L + 1) * v + 4096 := by ring
  simp_rw [heq] at h
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul,
    hc, Nat.mul_comm (numBands L m N ^ 2) 4096] using h

/-- Every actual phase, including halt, is bounded by original input size, shared encodings,
tile count and contributing leaves. In particular, repeated requests retain a charged term. -/
public theorem timeBound_le {L m N : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N)) :
    timeBound hm qs + 1 ≤ 65536 * (L + 1) *
      (1 + N * D m + qs.length + 2 ^ L + (numBands L m N + 1) * 10 ^ L +
        numBands L m N ^ 2 +
        ∑ T ∈ tiles L m N,
          (leaves (wantedStrings (MaskTable.layout hm) qs.toFinset T.1 T.2)).card) := by
  have htrace := sum_traceWeight_le hm qs
  have hleaves := Nat.zero_le (∑ T ∈ tiles L m N,
    (leaves (wantedStrings (MaskTable.layout hm) qs.toFinset T.1 T.2)).card)
  have hLleaves := Nat.zero_le (L *
    (∑ T ∈ tiles L m N,
      (leaves (wantedStrings (MaskTable.layout hm) qs.toFinset T.1 T.2)).card))
  rw [timeBound, sum_tileCharge]
  unfold routingTimeBound Wanted.timeBound BandPreparation.timeBound inputEnd
  nlinarith only [htrace, hleaves, hLleaves, Nat.zero_le L, Nat.zero_le (2 ^ L),
    Nat.zero_le (10 ^ L), Nat.zero_le (L * 10 ^ L),
    Nat.zero_le (N * D m), Nat.zero_le (L * (N * D m)), Nat.zero_le qs.length,
    Nat.zero_le (L * qs.length), Nat.zero_le (L * 2 ^ L),
    Nat.zero_le (numBands L m N * 10 ^ L), Nat.zero_le (L * (numBands L m N * 10 ^ L)),
    Nat.zero_le (numBands L m N ^ 2), Nat.zero_le (L * numBands L m N ^ 2)]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
