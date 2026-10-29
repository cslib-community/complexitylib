/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.FailureCount

/-!
# Original false positives bound the actual native failed occurrences

Actual answer words and original query coordinates determine the native failure predicate.
For the producer's repetition-free chunk, these occurrences inject into the existing finite
failed scans, whose distinct false-positive bound is already proved. This is a value/readback
lemma: actual execution supplies its premises, with no assumed answer or witness oracle.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Interpret the native failure predicate on real product words. Each failed original query
occurs only once, so its count is bounded by original-weight modular false positives. -/
theorem native_failed_occurrences_le {m n g p : ℕ} (values : ℕ → ℤ)
    (AB BC AC : ℕ → ℕ → ℤ) (wAB wBC wAC : Fin n → Fin n → ℤ)
    (hD : 16 ≤ D m) (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m))
    (hAB : ∀ u v : Fin n, AB u.val v.val = wAB u v)
    (hBC : ∀ u v : Fin n, BC u.val v.val = wBC u v)
    (hAC : ∀ u v : Fin n, AC u.val v.val = wAC u v)
    (hvaluesBC : ∀ b c, values (n * n + pairIndex (b, c)) = wBC b c)
    (hvaluesAC : ∀ a c, values (2 * (n * n) + pairIndex (a, c)) = wAC a c)
    (idx : InstanceIndex p) (hidx : idx ∈ instanceIndices wAB (D m) g p)
    (qs : List (Fin n × Fin n)) (default : Fin n × Fin n) (hqs : qs.Nodup)
    (hquery : ∀ q ∈ qs, q ∈ chunkOf wAB (D m) p idx.1 idx.2.1)
    (a b : ℕ → ℕ) (hcoords : ∀ i : Fin qs.length,
      a i.val = (qs.get i).1.val ∧ b i.val = (qs.get i).2.val)
    (mem : ℕ → ℕ) (out : ℕ)
    (hanswer : ∀ i : Fin qs.length, mem (out + i.val) = Signed.encode
      ((RecordProduct.leftMatrix m n g p values idx *
        RecordProduct.rightMatrix m n g p values idx) (qs.get i).1 (qs.get i).2)) :
    let first := idx.2.2 * pieceSize (D m) g
    let length := min (pieceSize (D m) g) (n - first)
    Nat.count (fun i => mem (out + i) ≠ 0 ∧
      ∀ c : Fin length, AB (a i) (b i) + BC (b i) (first + c.val) +
        AC (a i) (first + c.val) ≠ 0) qs.length ≤ falsePositiveCount wAB wBC wAC p := by
  exact (native_failed_count_le values AB BC AC wAB wBC wAC hD hg hAB hBC hAC
    idx qs default a b hcoords mem out hanswer).trans
    (RecordProduct.failed_occurrences_le values wAB wBC wAC hD hg hp
      hvaluesBC hvaluesAC idx hidx qs default hqs hquery)

/-- The actual native success condition is exactly an original zero triangle in the selected
existing chunk and piece. The nonzero-product condition is derived for every genuine zero. -/
theorem actual_success_iff {m n g p : ℕ} (values : ℕ → ℤ)
    (AB BC AC : ℕ → ℕ → ℤ) (wAB wBC wAC : Fin n → Fin n → ℤ)
    (hD : 16 ≤ D m) (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m))
    (hAB : ∀ u v : Fin n, AB u.val v.val = wAB u v)
    (hBC : ∀ u v : Fin n, BC u.val v.val = wBC u v)
    (hAC : ∀ u v : Fin n, AC u.val v.val = wAC u v)
    (hvaluesBC : ∀ b c, values (n * n + pairIndex (b, c)) = wBC b c)
    (hvaluesAC : ∀ a c, values (2 * (n * n) + pairIndex (a, c)) = wAC a c)
    (idx : InstanceIndex p) (qs : List (Fin n × Fin n))
    (hset : qs.toFinset = chunkOf wAB (D m) p idx.1 idx.2.1)
    (a b : ℕ → ℕ) (hcoords : ∀ i : Fin qs.length,
      a i.val = (qs.get i).1.val ∧ b i.val = (qs.get i).2.val)
    (mem : ℕ → ℕ) (out : ℕ)
    (hanswer : ∀ i : Fin qs.length, mem (out + i.val) = Signed.encode
      ((RecordProduct.leftMatrix m n g p values idx *
        RecordProduct.rightMatrix m n g p values idx) (qs.get i).1 (qs.get i).2)) :
    let first := idx.2.2 * pieceSize (D m) g
    let length := min (pieceSize (D m) g) (n - first)
    (∃ i < qs.length, mem (out + i) ≠ 0 ∧
      ∃ c, first ≤ c ∧ c < first + length ∧ AB (a i) (b i) + BC (b i) c + AC (a i) c = 0) ↔
      ∃ q ∈ chunkOf wAB (D m) p idx.1 idx.2.1,
        ∃ c ∈ piece n (D m) g idx.2.2, weightSum wAB wBC wAC q.1 q.2 c = 0 := by
  let first := idx.2.2 * pieceSize (D m) g
  let length := min (pieceSize (D m) g) (n - first)
  have pair_mem (i : Fin qs.length) : qs.get i ∈ chunkOf wAB (D m) p idx.1 idx.2.1 := by
    rw [← hset, List.mem_toFinset]
    exact List.get_mem _ _
  constructor
  · rintro ⟨i, hi, -, c, hlo, hhi, hz⟩
    let j : Fin qs.length := ⟨i, hi⟩
    have hl := min_le_right (pieceSize (D m) g) (n - first)
    have hn : c < n := by change first ≤ c at hlo; change c < first + length at hhi; omega
    let vertex : Fin n := ⟨c, hn⟩
    have hc : vertex ∈ piece n (D m) g idx.2.2 :=
      (mem_piece_iff_interval hD hg vertex).mpr ⟨hlo, hhi⟩
    obtain ⟨ha, hb⟩ := hcoords j
    have he : AB (a i) (b i) + BC (b i) c + AC (a i) c =
        weightSum wAB wBC wAC (qs.get j).1 (qs.get j).2 vertex := by
      rw [ha, hb]
      change AB (qs.get j).1.val (qs.get j).2.val +
        BC (qs.get j).2.val vertex.val + AC (qs.get j).1.val vertex.val = _
      rw [hAB, hBC, hAC]
      rfl
    exact ⟨qs.get j, pair_mem j, vertex, hc, he.symm.trans hz⟩
  · rintro ⟨q, hq, c, hc, hz⟩
    have hmem : q ∈ qs := by rw [← List.mem_toFinset, hset]; exact hq
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hmem
    obtain ⟨ha, hb⟩ := hcoords j
    have hpair : (lopInstance wAB wBC wAC (D m) g p idx).HasCommonNeighbor q.1 q.2 := by
      apply (hasCommonNeighbor_lopInstance_iff wAB wBC wAC
        (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.ne_zero hq).mpr
      exact ⟨c, hc, by rw [hz]⟩
    have hprod := (RecordProduct.product_ne_zero_iff values wAB wBC wAC hD hg hp
      hvaluesBC hvaluesAC idx q.1 q.2).mpr hpair
    refine ⟨j.val, j.isLt, ?_, c.val, ?_, ?_, ?_⟩
    · intro hzero
      apply hprod
      have he := hanswer j
      rw [hj] at he
      apply Signed.encode_injective
      exact he.symm.trans hzero
    · exact ((mem_piece_iff_interval hD hg c).mp hc).1
    · exact ((mem_piece_iff_interval hD hg c).mp hc).2
    · rw [ha, hb, hj, hAB, hBC, hAC]
      exact hz

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
