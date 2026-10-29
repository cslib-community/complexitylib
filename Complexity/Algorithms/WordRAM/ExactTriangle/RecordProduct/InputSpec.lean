/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Copy

/-!
# Composing the actual copied spans with the original product input

The local input meaning uses the unchanged queried-product `State.init` convention. Matrix
and coordinate readback is separated by the three actual source spans; no encoded bands,
routing data or precomputed execution contract is present in these assertions.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- The original product's first five memory words, including its actual payload length. -/
theorem original_header {m n : ℕ}
    (X : Matrix (Fin n) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin n) ℤ)
    (qs : List (Fin n × Fin n)) :
    (Block.mk 0 5).Realizes
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem
      ![4 + 2 * (n * D m) + 2 * qs.length, 19 * m, m, n, qs.length] := by
  intro j
  change (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem
    (0 + j.val) = _
  fin_cases j
  · change (QueriedProduct.input true (19 * m) X Y qs).length = _
    have h := QueriedProduct.input_length true (19 * m) X Y qs
    unfold QueriedProduct.inputEnd at h
    simpa only [Matrix.cons_val_zero'] using
      (show (QueriedProduct.input true (19 * m) X Y qs).length =
        4 + 2 * (n * D m) + 2 * qs.length by omega)
  · rfl
  · rfl
  · rfl
  · rfl

/-- Exact readback of the five header words and three copied spans identifies the entire
unchanged original input. This is a pure consequence of those native stores and copies. -/
theorem local_input {m n b : ℕ}
    (X : Matrix (Fin n) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin n) ℤ)
    (qs : List (Fin n × Fin n)) (mem : ℕ → ℕ)
    (hhead : (Block.mk b 5).Realizes mem
      ![4 + 2 * (n * D m) + 2 * qs.length, 19 * m, m, n, qs.length])
    (hleft : ∀ a < n * D m, mem (b + 5 + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem (5 + a))
    (hright : ∀ a < n * D m, mem (b + 5 + n * D m + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem
        (5 + n * D m + a))
    (hqueries : ∀ a < 2 * qs.length, mem (b + 5 + 2 * (n * D m) + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem
        (5 + 2 * (n * D m) + a)) :
    ∀ a, a < QueriedProduct.inputEnd m n qs.length → mem (b + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem a := by
  intro a ha
  unfold QueriedProduct.inputEnd at ha
  by_cases h5 : a < 5
  · have hh := hhead ⟨a, h5⟩
    have hs := original_header X Y qs ⟨a, h5⟩
    change mem (b + a) = _ at hh
    change (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem
      (0 + a) = _ at hs
    exact hh.trans (by simpa only [Nat.zero_add] using hs.symm)
  by_cases hl : a < 5 + n * D m
  · have h := hleft (a - 5) (by omega)
    simpa only [Nat.add_assoc, Nat.add_sub_of_le (by omega : 5 ≤ a)] using h
  by_cases hr : a < 5 + 2 * (n * D m)
  · have h := hright (a - (5 + n * D m)) (by omega)
    have he : 5 + n * D m + (a - (5 + n * D m)) = a := by omega
    simpa only [Nat.add_assoc, ← Nat.add_assoc 5 (n * D m), he] using h
  · have h := hqueries (a - (5 + 2 * (n * D m))) (by omega)
    have he : 5 + 2 * (n * D m) + (a - (5 + 2 * (n * D m))) = a := by omega
    simpa only [Nat.add_assoc, ← Nat.add_assoc 5 (2 * (n * D m)), he] using h

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
