/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Program
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Input
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandInput
public import Complexity.Foundations.Data.List.RowMajor
import Mathlib.Data.List.GetD
import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Transfer

/-!
# Original matrix and coordinate inputs for queried products

## Main definitions

* `QueriedProduct.entryWord`: canonical signed words or original raw nonnegative words.
* `QueriedProduct.input`: four scalar headers, both row-major matrices and raw coordinates.

The raw-input program performs actual doubling before calling the signed producer.
In particular, raw 0/1 entries become canonical signed 0/2 words. This input definition
neither supplies encodings nor performs that target conversion on the caller's behalf.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Ordinary source words. In raw mode only nonnegative source values are represented;
the native matrix-copy loop performs the subsequent signed-encoding conversion. -/
@[expose] public def entryWord (bits : Bool) (z : ℤ) : ℕ :=
  if bits then z.toNat else Signed.encode z

/-- Actual doubling converts every nonnegative raw entry into its canonical signed word.
In particular, the raw unsigned zero/one producer convention becomes signed zero/two. -/
public theorem convert_entryWord (bits : Bool) (z : ℤ) (hz : bits = true → 0 ≤ z) :
    (if bits then 2 * entryWord bits z else entryWord bits z) = Signed.encode z := by
  cases bits
  · rfl
  · have hnonneg := hz rfl
    cases z with
    | ofNat n => simp [entryWord, Signed.encode]
    | negSucc n => omega

/-- Both original matrices in their ordinary row-major input order. -/
@[expose] public def matrixInput {m N : ℕ} (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) : List ℕ :=
  (List.finRange N).flatMap (fun i => List.ofFn fun k => entryWord bits (X i k)) ++
    (List.finRange (D m)).flatMap (fun k => List.ofFn fun j => entryWord bits (Y k j))

/-- Actual initialized input, using exactly the existing router's raw coordinate convention. -/
@[expose] public def input {m N : ℕ} (bits : Bool) (L : ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) : List ℕ :=
  [L, m, N, qs.length] ++ matrixInput bits X Y ++ (Wanted.input L m qs).drop 4

/-- The matrix block contains exactly both original input arrays. -/
public theorem matrixInput_length {m N : ℕ} (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) :
    (matrixInput bits X Y).length = 2 * (N * D m) := by
  simp only [matrixInput, List.flatMap_ofFn_prod, List.length_append, List.length_ofFn]
  ring

/-- Every original scalar, matrix entry and coordinate lies within the snapshot prefix. -/
public theorem input_length {m N : ℕ} (bits : Bool) (L : ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) :
    (input bits L X Y qs).length + 1 = inputEnd m N qs.length := by
  have hq := Wanted.input_length L m qs
  simp only [input, List.length_append, matrixInput_length, List.length_cons,
    List.length_nil, List.length_drop, Wanted.inputLimit, inputEnd] at *
  omega

/-- The complete initialized input retains the router's raw coordinate values; the matrices
only shift their original address. No query code or tile is supplied in these words. -/
public theorem input_query_word {m N : ℕ} (bits : Bool) (L : ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (i : Fin qs.length) (s : Fin 2) :
    (State.init (input bits L X Y qs) : State 160).data.mem
        (queryInputBase m N + 2 * i.val + s.val) =
      if s = 0 then (qs.get i).1.val else (qs.get i).2.val := by
  have hw := Wanted.input_word L m qs i s
  change (Data.init (Wanted.input L m qs) : Data 96).mem _ = _ at hw
  rw [show 5 + 2 * i.val + s.val = (4 + 2 * i.val + s.val) + 1 by omega,
    Data.init_mem_succ] at hw
  change (Data.init (input bits L X Y qs) : Data 160).mem _ = _
  rw [show queryInputBase m N + 2 * i.val + s.val =
      (4 + 2 * (N * D m) + 2 * i.val + s.val) + 1 by unfold queryInputBase; omega,
    Data.init_mem_succ]
  unfold input
  rw [List.getD_append_right _ _ _ _ (by
    simp only [List.length_append, matrixInput_length, List.length_cons, List.length_nil]
    omega)]
  simp only [List.length_append, matrixInput_length, List.length_cons, List.length_nil]
  rw [show 4 + 2 * (N * D m) + 2 * i.val + s.val -
      (1 + (1 + (1 + (1 + 0))) + 2 * (N * D m)) = 2 * i.val + s.val by omega]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop] at hw ⊢
  simpa only [Nat.add_assoc] using hw

/-- Both original row-major matrix blocks contain precisely their supplied entry words,
before any copying, sign conversion or encoding takes place. -/
public theorem input_matrix_word {L m N : ℕ} (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (side : Bool) (r k : ℕ) (hr : r < N) (hk : k < D m) :
    (State.init (input bits L X Y qs) : State 160).data.mem
        (BandPreparation.matrixOffset m N side r k + 5) =
      entryWord bits (BandPreparation.matrixValues X Y side r k) := by
  let xs := (List.finRange N).flatMap (fun i => List.ofFn fun k => entryWord bits (X i k))
  let ys := (List.finRange (D m)).flatMap (fun k => List.ofFn fun j => entryWord bits (Y k j))
  have hxs : xs.length = N * D m := by
    simp only [xs, List.flatMap_ofFn_prod, List.length_ofFn]
  have hys : ys.length = D m * N := by
    simp only [ys, List.flatMap_ofFn_prod, List.length_ofFn]
  have hoff : BandPreparation.matrixOffset m N side r k < (xs ++ ys).length := by
    simp only [List.length_append, hxs, hys]
    cases side
    · have h := (finProdFinEquiv (⟨r, hr⟩, ⟨k, hk⟩)).isLt
      simp only [finProdFinEquiv, Equiv.coe_fn_mk] at h
      simp only [BandPreparation.matrixOffset, Bool.false_eq_true, ↓reduceIte]
      nlinarith only [h, Nat.zero_le (N * D m)]
    · have h := (finProdFinEquiv (⟨k, hk⟩, ⟨r, hr⟩)).isLt
      simp only [finProdFinEquiv, Equiv.coe_fn_mk] at h
      simp only [BandPreparation.matrixOffset, ↓reduceIte]
      nlinarith only [h]
  change (Data.init (input bits L X Y qs) : Data 160).mem _ = _
  rw [show BandPreparation.matrixOffset m N side r k + 5 =
      (BandPreparation.matrixOffset m N side r k + 4) + 1 by omega, Data.init_mem_succ]
  change (([L, m, N, qs.length] ++ (xs ++ ys) ++ (Wanted.input L m qs).drop 4).getD
    (BandPreparation.matrixOffset m N side r k + 4) 0) = _
  rw [List.getD_append _ _ _ _ (by
    simp only [List.length_append, List.length_cons, List.length_nil, hxs, hys] at hoff ⊢
    omega)]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_sub_cancel_right]
  cases side
  · have hi : r * D m + k < N * D m := by
      have h := (finProdFinEquiv (⟨r, hr⟩, ⟨k, hk⟩)).isLt
      simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.add_comm, Nat.mul_comm] using h
    simp only [BandPreparation.matrixOffset, Bool.false_eq_true, ↓reduceIte]
    rw [List.getD_append _ _ _ _ (by simpa only [hxs] using hi)]
    simpa only [xs, BandPreparation.matrixValues, dite_eq_left hr, dite_eq_left hk,
      Bool.false_eq_true, ↓reduceIte] using
      List.getD_flatMap_ofFn (fun i k => entryWord bits (X i k)) 0 ⟨r, hr⟩ ⟨k, hk⟩
  · simp only [BandPreparation.matrixOffset, ↓reduceIte]
    rw [List.getD_append_right _ _ _ _ (by rw [hxs]; omega), hxs,
      Nat.add_sub_cancel_right]
    simpa only [ys, BandPreparation.matrixValues, dite_eq_left hr, dite_eq_left hk,
      ↓reduceIte] using
      List.getD_flatMap_ofFn (fun k j => entryWord bits (Y k j)) 0 ⟨k, hk⟩ ⟨r, hr⟩

/-- The original magnitude envelope covers both canonical signed and raw unsigned words.
Raw-word fit does not itself assert nonnegativity of the represented source entries; that
extra semantic premise is used by the actual conversion proof. -/
public theorem entryWord_fits {w L A : ℕ} (hw : 0 < w) (bits : Bool) (z : ℤ)
    (hz : |z| ≤ (A : ℤ)) (hmag : magnitudeBound L A < 2 ^ (w - 1)) :
    Fits (w + 2) (entryWord bits z) := by
  have hA : A < 2 ^ (w - 1) := by
    unfold magnitudeBound at hmag
    omega
  have hAi : (A : ℤ) < (2 : ℤ) ^ (w - 1) := by exact_mod_cast hA
  have hzf : GenericRAM.Signed.Fits w z :=
    ⟨hw, (abs_lt.mp (hz.trans_lt hAi)).1.le, (abs_lt.mp (hz.trans_lt hAi)).2⟩
  cases bits
  · exact (Signed.encode_fits hzf).mono (by omega)
  · have hn : z.toNat ≤ A := Int.toNat_le.mpr ((le_abs_self z).trans hz)
    exact ((show Fits (w - 1) A from hA).mono (show w - 1 ≤ w + 2 by omega)).of_le hn

/-- Every actual initialized word fits from original dimensions and entry magnitudes.
No intermediate machine-state fit certificate is supplied. -/
public theorem input_fits {w L m N A : ℕ} (hw : 0 < w) (hm : m ≤ L) (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hX : ∀ i k, |X i k| ≤ (A : ℤ))
    (hY : ∀ k j, |Y k j| ≤ (A : ℤ)) (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m N qs.length)) :
    InputFits (w + 2) (input bits L X Y qs) := by
  have hs := caller_fits hfit
  have hb := transfer_bounds L m N qs.length
  have hq := Wanted.input_fits hm qs (producer_fits hfit).2
  refine ⟨?_, ?_⟩
  · have hi := input_length bits L X Y qs
    exact allocated_fits hfit (by omega)
  · intro v hv
    simp only [input, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with ((rfl | rfl | rfl | rfl) | hv) | hv
    · exact hs.of_le (by omega)
    · exact hs.of_le (by omega)
    · exact hs.of_le (by omega)
    · exact hs.of_le (by omega)
    · simp only [matrixInput, List.mem_append] at hv
      rcases hv with hv | hv
      · obtain ⟨i, _, hv⟩ := List.mem_flatMap.mp hv
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hv
        exact entryWord_fits hw bits _ (hX i k) hmag
      · obtain ⟨k, _, hv⟩ := List.mem_flatMap.mp hv
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
        exact entryWord_fits hw bits _ (hY k j) hmag
    · exact hq.2 v (List.mem_of_mem_drop hv)

/-- Original raw matrix words are bounded by the original absolute-entry bound, at every
flat position. This supplies the actual conversion loop without an intermediate fit premise. -/
public theorem input_raw_matrix_le {L m N A : ℕ}
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hX : ∀ i k, |X i k| ≤ (A : ℤ))
    (hY : ∀ k j, |Y k j| ≤ (A : ℤ)) (j : ℕ) (hj : j < 2 * (N * D m)) :
    (State.init (input true L X Y qs) : State 160).data.mem (5 + j) ≤ A := by
  have hj' : j < (matrixInput true X Y).length := by rw [matrixInput_length]; exact hj
  have hbound (v : ℕ) (hv : v ∈ matrixInput true X Y) : v ≤ A := by
    simp only [matrixInput, List.mem_append] at hv
    rcases hv with hv | hv
    · obtain ⟨i, _, hv⟩ := List.mem_flatMap.mp hv
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hv
      exact Int.toNat_le.mpr ((le_abs_self _).trans (hX i k))
    · obtain ⟨k, _, hv⟩ := List.mem_flatMap.mp hv
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact Int.toNat_le.mpr ((le_abs_self _).trans (hY k i))
  change (Data.init (input true L X Y qs) : Data 160).mem _ ≤ A
  rw [show 5 + j = (4 + j) + 1 by omega, Data.init_mem_succ]
  unfold input
  rw [List.getD_append _ _ _ _ (by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_sub_cancel_left]
  rw [List.getD_eq_get _ _ ⟨j, hj'⟩]
  exact hbound _ (List.get_mem _ _)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
