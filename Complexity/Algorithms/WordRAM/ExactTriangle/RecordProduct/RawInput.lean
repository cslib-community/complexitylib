/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Exec

/-!
# Original raw matrix and coordinate spans

These readback lemmas use the existing original product input and row-major numbering.
The query list is the finite mathematical reading of actual native coordinate words; the
adapter copies those words unchanged, and performs no uncharged query decoding operation.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Mathematical reading of an existing interleaved native query block. The modulo is only
a total specification; actual producer coordinates are proved in range before using it. -/
@[expose] def decodedQueries {n : ℕ} (hn : 0 < n) (mem : ℕ → ℕ) (q Q : ℕ) :
    List (Fin n × Fin n) :=
  List.ofFn fun i : Fin Q =>
    (⟨mem (q + 2 * i.val) % n, Nat.mod_lt _ hn⟩,
      ⟨mem (q + 2 * i.val + 1) % n, Nat.mod_lt _ hn⟩)

/-- Decoding retains exactly the original occurrence count. -/
theorem decodedQueries_length {n : ℕ} (hn : 0 < n) (mem : ℕ → ℕ) (q Q : ℕ) :
    (decodedQueries hn mem q Q).length = Q := List.length_ofFn

/-- In-range actual query words are exactly the original coordinate values in the decoded
occurrence. The total specification's modulo does not change valid producer words. -/
theorem decodedQueries_get_val {n : ℕ} (hn : 0 < n) (mem : ℕ → ℕ) (q Q : ℕ)
    (i : Fin (decodedQueries hn mem q Q).length)
    (ha : mem (q + 2 * i.val) < n) (hb : mem (q + 2 * i.val + 1) < n) :
    ((decodedQueries hn mem q Q).get i).1.val = mem (q + 2 * i.val) ∧
      ((decodedQueries hn mem q Q).get i).2.val = mem (q + 2 * i.val + 1) := by
  constructor
  · rw [List.get_eq_getElem]
    simp only [decodedQueries, List.getElem_ofFn]
    exact Nat.mod_eq_of_lt ha
  · rw [List.get_eq_getElem]
    simp only [decodedQueries, List.getElem_ofFn]
    exact Nat.mod_eq_of_lt hb

/-- Every actual in-range coordinate word reappears unchanged in the ordinary callee input. -/
theorem decodedQueries_words {m n q Q : ℕ} (hn : 0 < n) (mem : ℕ → ℕ)
    (X : Matrix (Fin n) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin n) ℤ)
    (hcoord : ∀ i < Q, mem (q + 2 * i) < n ∧ mem (q + 2 * i + 1) < n) :
    ∀ a < 2 * Q, mem (q + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y
        (decodedQueries hn mem q Q)) : State 160).data.mem (5 + 2 * (n * D m) + a) := by
  intro a ha
  have hi : a / 2 < Q := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr (by omega)
  let i : Fin (decodedQueries hn mem q Q).length := ⟨a / 2, by
    rw [decodedQueries_length]; exact hi⟩
  let s : Fin 2 := ⟨a % 2, Nat.mod_lt _ (by decide)⟩
  have hw := QueriedProduct.input_query_word true (19 * m) X Y
    (decodedQueries hn mem q Q) i s
  have hsplit : 2 * (a / 2) + a % 2 = a := by omega
  change (State.init (QueriedProduct.input true (19 * m) X Y
    (decodedQueries hn mem q Q)) : State 160).data.mem
      (QueriedProduct.queryInputBase m n + 2 * (a / 2) + a % 2) = _ at hw
  rw [show QueriedProduct.queryInputBase m n + 2 * (a / 2) + a % 2 =
    5 + 2 * (n * D m) + a by unfold QueriedProduct.queryInputBase; omega] at hw
  rw [hw]
  have hc := hcoord (a / 2) hi
  simp only [decodedQueries, List.get_ofFn, i, Fin.val_cast]
  by_cases hzero : a % 2 = 0
  · have he : s = 0 := Fin.ext hzero
    simp only [he, ↓reduceIte]
    rw [Nat.mod_eq_of_lt hc.1]
    congr 1
    omega
  · have hone : a % 2 = 1 := by have := Nat.mod_lt a (by decide : 0 < 2); omega
    have he : s ≠ 0 := by intro h; exact hzero (congrArg Fin.val h)
    simp only [he, ↓reduceIte]
    rw [Nat.mod_eq_of_lt hc.2]
    congr 1
    omega

/-- A native left-matrix span reads exactly as the ordinary product's original raw input. -/
theorem raw_left_words {m n s : ℕ} (mem : ℕ → ℕ)
    (X : Matrix (Fin n) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin n) ℤ)
    (qs : List (Fin n × Fin n))
    (hX : ∀ (i : Fin n) (k : Fin (D m)), mem (s + (i.val * D m + k.val)) = (X i k).toNat) :
    ∀ a < n * D m, mem (s + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem (5 + a) := by
  intro a ha
  have hd : 0 < D m := by change 0 < 4 ^ m; positivity
  have hi : a / D m < n := (Nat.div_lt_iff_lt_mul hd).mpr ha
  have hk : a % D m < D m := Nat.mod_lt _ hd
  have hw := QueriedProduct.input_matrix_word (L := 19 * m) true X Y qs false
    (a / D m) (a % D m) hi hk
  have he : a / D m * D m + a % D m = a := Nat.div_add_mod' a (D m)
  simp only [BandPreparation.matrixOffset, Bool.false_eq_true, ↓reduceIte, he,
    BandPreparation.matrixValues, QueriedProduct.entryWord, hi, hk, ↓reduceDIte] at hw
  rw [show 5 + a = a + 5 by omega, hw]
  simpa only [he] using hX ⟨a / D m, hi⟩ ⟨a % D m, hk⟩

/-- The right original block retains its `D×n` row-major order. -/
theorem raw_right_words {m n t : ℕ} (hn : 0 < n) (mem : ℕ → ℕ)
    (X : Matrix (Fin n) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin n) ℤ)
    (qs : List (Fin n × Fin n))
    (hY : ∀ (k : Fin (D m)) (i : Fin n), mem (t + (k.val * n + i.val)) = (Y k i).toNat) :
    ∀ a < n * D m, mem (t + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem
        (5 + n * D m + a) := by
  intro a ha
  have hi : a % n < n := Nat.mod_lt _ hn
  have hk : a / n < D m := (Nat.div_lt_iff_lt_mul hn).mpr (by simpa only [Nat.mul_comm] using ha)
  have hw := QueriedProduct.input_matrix_word (L := 19 * m) true X Y qs true
    (a % n) (a / n) hi hk
  have he : a / n * n + a % n = a := Nat.div_add_mod' a n
  simp only [BandPreparation.matrixOffset, ↓reduceIte, he,
    BandPreparation.matrixValues, QueriedProduct.entryWord, hi, hk, ↓reduceDIte] at hw
  rw [show 5 + n * D m + a = a + n * D m + 5 by omega, hw]
  simpa only [he] using hY ⟨a / n, hk⟩ ⟨a % n, hi⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
