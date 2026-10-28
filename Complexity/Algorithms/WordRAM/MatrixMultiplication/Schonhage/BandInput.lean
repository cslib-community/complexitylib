/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandExec
public import Complexity.Foundations.Data.List.RowMajor
import Mathlib.Data.List.GetD

/-!
# Actual initialized header and signed-matrix inputs

## Main definitions

* `BandPreparation.matrixValues`: zero extension of the two original finite matrices for
  stating the already proved native guarded-load specification.

## Main results

* `BandPreparation.input_fits`: the actual initialized list fits from original magnitude
  and parameter bounds.
* `BandPreparation.exec_input`: complete charged native execution from `State.init`.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Original matrix entries, zero extended to natural indices. Right-side `r` denotes a
column of `Y`. This is only the mathematical memory specification; the program loads the
concrete row-major input words, after its actual bounds guard. -/
def matrixValues {m N : ℕ} (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (side : Bool) (r k : ℕ) : ℤ :=
  if hr : r < N then if hk : k < D m then
    if side then Y ⟨k, hk⟩ ⟨r, hr⟩ else X ⟨r, hr⟩ ⟨k, hk⟩ else 0 else 0

/-- The input prefix consists of the native length header, three scalar words and both
original matrices, with no powers, tables or precomputed outputs. -/
theorem input_length {m N : ℕ} (L : ℕ) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) : (input L m N X Y).length + 1 = inputEnd m N := by
  simp only [input, List.flatMap_ofFn_prod, List.length_append, List.length_ofFn,
    List.length_cons, List.length_nil, inputEnd]
  ring

private theorem init_matrix {L m N : ℕ} (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (side : Bool) (r : ℕ) (hr : r < N)
    (k : ℕ) (hk : k < D m) :
    (State.init (input L m N X Y) : State 96).data.mem (matrixOffset m N side r k + 4) =
      encode (matrixValues X Y side r k) := by
  let xs := (List.finRange N).flatMap (fun i => List.ofFn fun k => encode (X i k))
  let ys := (List.finRange (D m)).flatMap (fun k => List.ofFn fun j => encode (Y k j))
  have hxs : xs.length = N * D m := by
    simp only [xs, List.flatMap_ofFn_prod, List.length_ofFn]
  change (Data.init (input L m N X Y) : Data 96).mem _ = _
  rw [show matrixOffset m N side r k + 4 = (matrixOffset m N side r k + 3) + 1 by omega,
    Data.init_mem_succ]
  change ((L :: m :: N :: (xs ++ ys)).getD (matrixOffset m N side r k + 3) 0) = _
  rw [show matrixOffset m N side r k + 3 =
      ((matrixOffset m N side r k + 1) + 1) + 1 by omega]
  simp only [List.getD_cons_succ]
  cases side
  · have hi : r * D m + k < N * D m := by
      have h := (finProdFinEquiv (⟨r, hr⟩, ⟨k, hk⟩)).isLt
      simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.add_comm, Nat.mul_comm] using h
    simp only [matrixOffset, Bool.false_eq_true, ↓reduceIte]
    rw [List.getD_append _ _ _ _ (by simpa only [hxs] using hi)]
    simpa only [xs, matrixValues, dite_eq_left hr, dite_eq_left hk,
      Bool.false_eq_true, ↓reduceIte] using
      (List.getD_flatMap_ofFn (fun i k => encode (X i k)) 0 ⟨r, hr⟩ ⟨k, hk⟩)
  · simp only [matrixOffset, ↓reduceIte]
    rw [List.getD_append_right _ _ _ _ (by rw [hxs]; omega), hxs,
      Nat.add_sub_cancel_right]
    simpa only [ys, matrixValues, dite_eq_left hr, dite_eq_left hk, ↓reduceIte] using
      (List.getD_flatMap_ofFn (fun k j => encode (Y k j)) 0 ⟨k, hk⟩ ⟨r, hr⟩)

/-- The sign/magnitude input encoding uses at most `w+1` bits; the actual native program
uses `w+2` bits for its signed arithmetic kernels. Every input word is covered. -/
theorem input_fits {w L m N : ℕ} (hw : 0 < w) (hm : m ≤ L)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (A : ℤ) (hA : 0 ≤ A) (hX : ∀ i k, |X i k| ≤ A) (hY : ∀ k j, |Y k j| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m N)) : InputFits (w + 2) (input L m N X Y) := by
  have hscalar : Fits (w + 2) (L + N) := (local_fits hfit).of_le (by
    nlinarith only [Nat.zero_le L, Nat.zero_le N, Nat.zero_le (N * D m),
      Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L)])
  have hpow : (1 : ℤ) ≤ (7 ^ L : ℕ) := by
    exact_mod_cast Nat.one_le_pow L 7 (by decide)
  have hAfit : A < (2 : ℤ) ^ (w - 1) := by nlinarith only [hpow, hA, hmag]
  have hvalue (z : ℤ) (hz : |z| ≤ A) : Fits (w + 2) (encode z) := by
    have hb := abs_lt.mp (hz.trans_lt hAfit)
    exact (encode_fits (show GenericRAM.Signed.Fits w z from ⟨hw, hb.1.le, hb.2⟩)).mono
      (by omega)
  refine ⟨?_, ?_⟩
  · apply ((memory_fits hfit).of_le (input_le_memoryEnd L m N)).of_le
    have := input_length L X Y
    omega
  · intro v hv
    simp only [input, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (hv | hv) | hv
    · rcases hv with rfl | rfl | rfl <;> exact hscalar.of_le (by omega)
    · obtain ⟨i, _, hv⟩ := List.mem_flatMap.mp hv
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hv
      exact hvalue _ (hX i k)
    · obtain ⟨k, _, hv⟩ := List.mem_flatMap.mp hv
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
      exact hvalue _ (hY k j)

/-- Complete actual `State.init` execution, with both encoded catalogues, computed tables,
preserved input and outside frame, bounded final state and the complete charged time bound. -/
theorem exec_input {w L m N : ℕ} (hw : 0 < w) (hm : m ≤ L)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (A : ℤ) (hA : 0 ≤ A) (hX : ∀ i k, |X i k| ≤ A) (hY : ∀ k j, |Y k j| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m N)) :
    InputFits (w + 2) (input L m N X Y) ∧
    ∃ y, ExecWithin (w + 2) program (State.init (input L m N X Y)).data y (timeBound L m N) ∧
      y.Bounded (w + 2) ∧ BandParameters L m N y ∧
      (∀ side β, β < numBands L m N → ∀ p, p < 10 ^ L →
        y.mem (catalogueAddress L m N side β p) =
          encode (catalogueValue L m N side (matrixValues X Y side) β p)) ∧
      (∀ a < 2 ^ L, y.mem (inverseBase L m N + a) = MaskTable.lookup L m a) ∧
      (∀ gh : Fin (K0 L m) × Fin (K0 L m),
        y.mem (tableBase L m N + (MaskTable.pairRank gh).val) =
          (MaskTable.selectedMask gh).val) ∧
      (∀ b, ¬(inputEnd m N ≤ b ∧ b < memoryEnd L m N) →
        y.mem b = (State.init (input L m N X Y) : State 96).data.mem b) := by
  have hi := input_fits hw hm X Y A hA hX hY hmag hfit
  let x : Data 96 := (State.init (input L m N X Y)).data
  have hL : x.mem 1 = L := by simp [x, State.init, Data.init, input]
  have hm' : x.mem 2 = m := by simp [x, State.init, Data.init, input]
  have hN : x.mem 3 = N := by simp [x, State.init, Data.init, input]
  have hvalues (side : Bool) (r : ℕ) (hr : r < N) (k : ℕ) (hk : k < D m) :
      |matrixValues X Y side r k| ≤ A := by
    cases side <;> simp only [matrixValues, dite_eq_left hr, dite_eq_left hk,
      Bool.false_eq_true, ↓reduceIte]
    · exact hX _ _
    · exact hY _ _
  obtain ⟨y, he, hp, hv, ht, hf, hframe⟩ := exec hw hm x hL hm' hN
    (matrixValues X Y) (init_matrix X Y) A hA hvalues hmag hfit
  exact ⟨hi, y, he, he.bounded (Data.Bounded.init hi), hp, hv, ht, hf, hframe⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
