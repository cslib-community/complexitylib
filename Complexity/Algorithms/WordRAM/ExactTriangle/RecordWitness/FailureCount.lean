/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Detection
public import Complexity.Algorithms.WordRAM.ExactTriangle.WitnessScan.Finite

/-!
# Actual failed-query words and finite failed occurrences

This value/readback rule keeps the per-record occurrence count before applying any global
false-positive bound. An all-record controller can therefore add these distinct counts once
and inject their union into the existing global failed scans. No execution is assumed here;
actual native calls prove the answer-word and coordinate premises.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual failed accepted queries are bounded by their finite occurrence count, retaining
the record's identity for a later global sum. Repetition assumptions are not needed here. -/
theorem native_failed_count_le {m n g p : ℕ} (values : ℕ → ℤ)
    (AB BC AC : ℕ → ℕ → ℤ) (wAB wBC wAC : Fin n → Fin n → ℤ)
    (hD : 16 ≤ D m) (hg : 1 ≤ g)
    (hAB : ∀ u v : Fin n, AB u.val v.val = wAB u v)
    (hBC : ∀ u v : Fin n, BC u.val v.val = wBC u v)
    (hAC : ∀ u v : Fin n, AC u.val v.val = wAC u v)
    (idx : InstanceIndex p) (qs : List (Fin n × Fin n)) (default : Fin n × Fin n)
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
        AC (a i) (first + c.val) ≠ 0) qs.length ≤
      Nat.count (fun i =>
        (RecordProduct.leftMatrix m n g p values idx *
          RecordProduct.rightMatrix m n g p values idx)
            (qs.getD i default).1 (qs.getD i default).2 ≠ 0 ∧
        scanPiece wAB wBC wAC (D m) g idx.2.2
          (qs.getD i default).1 (qs.getD i default).2 = none) qs.length := by
  apply Nat.count_mono_left
  intro i hi hn
  let j : Fin qs.length := ⟨i, hi⟩
  have hget : qs.getD i default = qs.get j := by
    rw [List.getD_eq_getElem _ _ hi, List.get_eq_getElem]
  rw [hget]
  constructor
  · intro hz
    apply hn.1
    rw [hanswer j, hz]
    rfl
  · apply (WitnessScan.fails_iff_scanPiece_eq_none AB BC AC wAB wBC wAC
      hD hg hAB hBC hAC (qs.get j).1 (qs.get j).2).mp
    obtain ⟨ha, hb⟩ := hcoords j
    simpa only [j, ha, hb] using hn.2

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
