/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Producer
public import Complexity.Algorithms.ExactTriangle.PieceBounds
public import Complexity.Algorithms.ExactTriangle.Witnesses
public import Mathlib.Data.Nat.Count
import Complexity.Algorithms.WordRAM.ExactTriangle.MatrixSpec

/-!
# Actual record products detect the existing modular graph

The zero/one value matrices used by the real product adapter have a nonzero product entry
exactly at a common neighbor of the existing finite `lopInstance`. Active middle coordinates
and zero padding follow from the original source prime window and piece geometry. Thus a
consumer can derive detection semantics from the actual product, without an answer oracle.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The value matrices written by the producer and consumed by the actual native product
have precisely the common-neighbor semantics of the existing finite modular instance. -/
theorem product_ne_zero_iff {m n g p : ℕ} (values : ℕ → ℤ)
    (wAB wBC wAC : Fin n → Fin n → ℤ)
    (hD : 16 ≤ D m) (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m))
    (hBC : ∀ b c, values (n * n + pairIndex (b, c)) = wBC b c)
    (hAC : ∀ a c, values (2 * (n * n) + pairIndex (a, c)) = wAC a c)
    (idx : InstanceIndex p) (a b : Fin n) :
    (leftMatrix m n g p values idx * rightMatrix m n g p values idx) a b ≠ 0 ↔
      (lopInstance wAB wBC wAC (D m) g p idx).HasCommonNeighbor a b := by
  classical
  let X := leftMatrix m n g p values idx
  let Y := rightMatrix m n g p values idx
  let G := lopInstance wAB wBC wAC (D m) g p idx
  let A := matrixArgs n (D m) g p idx.1.val idx.2.2
  let Rleft (q : ℕ) := (values (2 * (n * n) + q) % (p : ℤ)).toNat
  let Rright (q : ℕ) := (values (n * n + q) % (p : ℤ)).toNat
  have hpad : A.length * p ≤ D m := pieceLength_mul_le_of_mem_sqrtPrimeWindow hg hp
  have hp0 : 0 < p := (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.pos
  have loadLeft (u c : Fin n) : Rleft (u.val * n + c.val) = (wAC u c).natMod p := by
    change (values (2 * (n * n) + pairIndex (u, c)) % (p : ℤ)).toNat = _
    rw [hAC]
    rfl
  have loadRight (u c : Fin n) : Rright (u.val * n + c.val) = (wBC u c).natMod p := by
    change (values (n * n + pairIndex (u, c)) % (p : ℤ)).toNat = _
    rw [hBC]
    rfl
  have edges (c : Fin n) (hc : c ∈ piece n (D m) g idx.2.2)
      (v : Fin A.length) (label : Fin p) (j : Fin (D m))
      (hv : A.first + v.val = c.val) (hj : j.val = v.val * p + label.val) :
      (X a j = 1 ↔ G.adjA a (⟨c, hc⟩, label)) ∧
      (Y j b = 1 ↔ G.adjB (⟨c, hc⟩, label) b) := by
    have hl := MatrixSpec.left_lopInstance A Rleft wAB wBC wAC g idx.2.1 idx.2.2
      idx.1 rfl a c v label hc hv hpad loadLeft
    have hr := MatrixSpec.right_lopInstance A Rright wAB wBC wAC g idx.2.1 idx.2.2
      idx.1 b c v label hc hv loadRight
    constructor
    · change (WriteMatrices.entry false A Rleft (a.val * D m + j.val) : ℤ) = 1 ↔ _
      rw [hj]
      exact_mod_cast hl
    · change (WriteMatrices.entry true A Rright (j.val * n + b.val) : ℤ) = 1 ↔ _
      rw [hj]
      exact_mod_cast hr
  obtain ⟨hX, hY⟩ := matrices_zero_one m n g p values idx
  have hx : ∀ a j, X a j = 0 ∨ X a j = 1 := by
    intro a j
    have := hX a j
    change 0 ≤ X a j ∧ X a j ≤ 1 at this
    omega
  have hy : ∀ j b, Y j b = 0 ∨ Y j b = 1 := by
    intro j b
    have := hY j b
    change 0 ≤ Y j b ∧ Y j b ≤ 1 at this
    omega
  rw [LopsidedGraph.mul_apply_eq_commonNeighborCount_ofMatrices X Y ∅ hx hy]
  have hnz := (LopsidedGraph.ofMatrices X Y ∅).commonNeighborCount_ne_zero_iff a b
  rw [show ((LopsidedGraph.ofMatrices X Y ∅).commonNeighborCount a b : ℤ) ≠ 0 ↔
      (LopsidedGraph.ofMatrices X Y ∅).commonNeighborCount a b ≠ 0 by exact_mod_cast Iff.rfl]
  rw [hnz]
  change (∃ j : Fin (D m), X a j = 1 ∧ Y j b = 1) ↔ G.HasCommonNeighbor a b
  constructor
  · rintro ⟨j, hleft, hright⟩
    have hj : j.val / p < A.length := by
      by_contra h
      have hz := MatrixSpec.left_padding A Rleft a j (by change A.length ≤ j.val / p; omega)
      change WriteMatrices.entry false A Rleft (a.val * D m + j.val) = 0 at hz
      have hl : (WriteMatrices.entry false A Rleft (a.val * D m + j.val) : ℤ) = 1 := hleft
      rw [hz] at hl
      norm_num at hl
    let v : Fin A.length := ⟨j.val / p, hj⟩
    let label : Fin p := ⟨j.val % p, Nat.mod_lt _ hp0⟩
    have hn : A.first + v.val < n := by
      have hl := min_le_right (pieceSize (D m) g) (n - A.first)
      have hv := v.isLt
      change v.val < min (pieceSize (D m) g) (n - A.first) at hv
      omega
    let c : Fin n := ⟨A.first + v.val, hn⟩
    have hc : c ∈ piece n (D m) g idx.2.2 := by
      apply (mem_piece_iff_interval hD hg c).mpr
      change idx.2.2 * pieceSize (D m) g ≤ A.first + v.val ∧
        A.first + v.val < idx.2.2 * pieceSize (D m) g + A.length
      change A.first ≤ A.first + v.val ∧ A.first + v.val < A.first + A.length
      exact ⟨by omega, Nat.add_lt_add_left v.isLt _⟩
    have he : j.val = v.val * p + label.val := by
      simpa only [v, label, Nat.mul_comm] using (Nat.div_add_mod j.val p).symm
    obtain ⟨heL, heR⟩ := edges c hc v label j rfl he
    exact ⟨(⟨c, hc⟩, label), heL.mp hleft, heR.mp hright⟩
  · rintro ⟨⟨⟨c, hc⟩, label⟩, hleft, hright⟩
    obtain ⟨hv, hlen⟩ := piece_coordinate hD hg c hc
    let v : Fin A.length := ⟨c.val % pieceSize (D m) g, hlen⟩
    have hj : v.val * p + label.val < D m := by
      have hm := Nat.mul_le_mul_right p v.isLt
      rw [Nat.succ_mul] at hm
      have hl := label.isLt
      omega
    let j : Fin (D m) := ⟨v.val * p + label.val, hj⟩
    obtain ⟨heL, heR⟩ := edges c hc v label j hv rfl
    exact ⟨j, heL.mpr hleft, heR.mpr hright⟩

/-- The mathematical answers computed by the actual product discharge the finite recovery
contract. Correct answers are a conclusion here, not a solver assumption. -/
theorem product_answers_correct {m n g p : ℕ} (values : ℕ → ℤ)
    (wAB wBC wAC : Fin n → Fin n → ℤ)
    (hD : 16 ≤ D m) (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m))
    (hBC : ∀ b c, values (n * n + pairIndex (b, c)) = wBC b c)
    (hAC : ∀ a c, values (2 * (n * n) + pairIndex (a, c)) = wAC a c) :
    AnswersCorrect wAB wBC wAC (D m) g p (fun idx q => decide
      ((leftMatrix m n g p values idx * rightMatrix m n g p values idx) q.1 q.2 ≠ 0)) := by
  intro idx _ q _
  simp only [decide_eq_true_eq]
  exact propext (product_ne_zero_iff values wAB wBC wAC hD hg hp hBC hAC idx q.1 q.2)

/-- Distinct occurrences of one actual query chunk that are accepted by the product but
have no original witness inject into the existing finite failed scans. Their number is
therefore bounded by the existing original-weight false-positive count. -/
theorem failed_occurrences_le {m n g p : ℕ} (values : ℕ → ℤ)
    (wAB wBC wAC : Fin n → Fin n → ℤ)
    (hD : 16 ≤ D m) (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m))
    (hBC : ∀ b c, values (n * n + pairIndex (b, c)) = wBC b c)
    (hAC : ∀ a c, values (2 * (n * n) + pairIndex (a, c)) = wAC a c)
    (idx : InstanceIndex p) (hidx : idx ∈ instanceIndices wAB (D m) g p)
    (qs : List (Fin n × Fin n)) (default : Fin n × Fin n) (hqs : qs.Nodup)
    (hquery : ∀ q ∈ qs, q ∈ chunkOf wAB (D m) p idx.1 idx.2.1) :
    Nat.count (fun i =>
      (leftMatrix m n g p values idx * rightMatrix m n g p values idx)
          (qs.getD i default).1 (qs.getD i default).2 ≠ 0 ∧
        scanPiece wAB wBC wAC (D m) g idx.2.2
          (qs.getD i default).1 (qs.getD i default).2 = none) qs.length ≤
      falsePositiveCount wAB wBC wAC p := by
  classical
  let ans : InstanceIndex p → Fin n × Fin n → Bool := fun idx q => decide
    ((leftMatrix m n g p values idx * rightMatrix m n g p values idx) q.1 q.2 ≠ 0)
  let P (i : ℕ) : Prop :=
    (leftMatrix m n g p values idx * rightMatrix m n g p values idx)
        (qs.getD i default).1 (qs.getD i default).2 ≠ 0 ∧
      scanPiece wAB wBC wAC (D m) g idx.2.2
        (qs.getD i default).1 (qs.getD i default).2 = none
  let := Nat.CountSet.fintype P qs.length
  let failures := failedScans wAB wBC wAC (D m) g p ans
  have hget (i : ℕ) (hi : i < qs.length) : qs.getD i default = qs.get ⟨i, hi⟩ := by
    rw [List.getD_eq_getElem _ _ hi, List.get_eq_getElem]
  let f : {i : ℕ // i < qs.length ∧ P i} → {s // s ∈ failures} := fun i =>
    ⟨(idx, qs.get ⟨i.val, i.prop.1⟩), by
      apply Finset.mem_filter.mpr
      refine ⟨mem_acceptedPairs.mpr ⟨hidx, ?_, ?_⟩, ?_⟩
      · exact hquery _ (List.get_mem _ _)
      · have he := i.prop.2.1
        simpa only [ans, decide_eq_true_eq, hget i.val i.prop.1] using he
      · have he := i.prop.2.2
        simpa only [scanOf, hget i.val i.prop.1] using he⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hpair : qs.get ⟨i.val, i.prop.1⟩ = qs.get ⟨j.val, j.prop.1⟩ :=
      congrArg (fun s => s.val.2) hij
    have hi := List.nodup_iff_injective_get.mp hqs hpair
    exact Subtype.ext (congrArg Fin.val hi)
  change Nat.count P qs.length ≤ _
  rw [Nat.count_eq_card_fintype]
  calc
    _ ≤ Fintype.card {s // s ∈ failures} := Fintype.card_le_of_injective f hf
    _ = failures.card := Fintype.card_coe _
    _ ≤ falsePositiveCount wAB wBC wAC p := card_failedScans_le
      (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.ne_zero
      (product_answers_correct values wAB wBC wAC hD hg hp hBC hAC)

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
