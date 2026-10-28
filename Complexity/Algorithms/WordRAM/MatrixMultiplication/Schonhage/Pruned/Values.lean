/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Codes
public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Magnitude

/-!
# Values and flat addresses of the native recursion

## Main definitions

* `PrunedQuery.partialValue`: the requested accumulator after a prefix of the ten terms.

## Main results

* `PrunedQuery.slice_strided`: flat strided leaf arrays agree with the existing `sliceAt`.
* `PrunedQuery.abs_partialValue_le`: every intermediate accumulator has an explicit bound.

These are identities and magnitude bounds for the controller invariant. They do not assume
that a machine executes the recursion.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Finset

/-- The existing leaf indexing has the same least-significant-first decomposition as queries. -/
theorem leafIndex_cons {n : ℕ} (lam : Term) (v : Leaf n) :
    (Encoding.leafIndex (Fin.cons lam v)).val =
      (Encoding.termDigits.symm lam).val + 10 * (Encoding.leafIndex v).val := by
  simp only [Encoding.leafIndex, finFunctionFinEquiv_apply, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
    pow_succ, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  ring

/-- The native prefix/stride update selects exactly the existing mathematical child slice. -/
theorem slice_strided {n : ℕ} (a : ℕ → ℤ) (p s : ℕ) (lam : Term) :
    sliceAt (fun v : Leaf (n + 1) => a (p + s * (Encoding.leafIndex v).val)) lam =
      fun v : Leaf n => a (p + (Encoding.termDigits.symm lam).val * s +
        (s * 10) * (Encoding.leafIndex v).val) := by
  funext v
  change a (p + s * (Encoding.leafIndex (Fin.cons lam v)).val) = _
  rw [leafIndex_cons]
  congr 1
  ring

/-- A frame's prefix and stride put every remaining leaf inside the original encoding array. -/
theorem leafAddress_lt {n p s size : ℕ} (hp : p < s) (hs : s * 10 ^ n = size)
    (v : Leaf n) : p + s * (Encoding.leafIndex v).val < size := by
  have hi := (Encoding.leafIndex v).isLt
  nlinarith

/-- The mathematical value of a requested native accumulator after terms numbered below `k`.
Unrequested directory cells are deliberately unspecified by the native interface. -/
def partialValue {n : ℕ} (a b : Leaf (n + 1) → ℤ) (S : Finset (OutStr (n + 1)))
    (w : OutStr (n + 1)) (k : ℕ) : ℤ :=
  ∑ i : Fin 10 with i.val < k ∧ (Encoding.termDigits i).Contributes (w 0),
    Pruned.childResult a b S (Encoding.termDigits i) (Fin.tail w)

/-- Before the first child, the native accumulator is zero. -/
@[simp]
theorem partialValue_zero {n : ℕ} (a b : Leaf (n + 1) → ℤ)
    (S : Finset (OutStr (n + 1))) (w : OutStr (n + 1)) : partialValue a b S w 0 = 0 := by
  simp [partialValue]

/-- Processing the next term adds exactly its contributing child, or leaves the value unchanged. -/
theorem partialValue_succ {n : ℕ} (a b : Leaf (n + 1) → ℤ)
    (S : Finset (OutStr (n + 1))) (w : OutStr (n + 1)) (k : Fin 10) :
    partialValue a b S w (k.val + 1) = partialValue a b S w k.val +
      if (Encoding.termDigits k).Contributes (w 0) then
        Pruned.childResult a b S (Encoding.termDigits k) (Fin.tail w) else 0 := by
  have hfilter :
      (univ.filter fun i : Fin 10 => i.val < k.val + 1 ∧
        (Encoding.termDigits i).Contributes (w 0)) =
      if (Encoding.termDigits k).Contributes (w 0) then
        insert k (univ.filter fun i : Fin 10 => i.val < k.val ∧
          (Encoding.termDigits i).Contributes (w 0)) else
        univ.filter fun i : Fin 10 => i.val < k.val ∧
          (Encoding.termDigits i).Contributes (w 0) := by
    ext i
    by_cases hc : (Encoding.termDigits k).Contributes (w 0)
    · simp only [mem_filter, mem_univ, true_and, hc, ↓reduceIte, mem_insert]
      constructor
      · rintro ⟨hi, hci⟩
        by_cases he : i = k
        · exact Or.inl he
        · exact Or.inr ⟨by have hne := Fin.val_ne_of_ne he; omega, hci⟩
      · rintro (rfl | ⟨hi, hci⟩)
        · exact ⟨by omega, hc⟩
        · exact ⟨by omega, hci⟩
    · simp only [mem_filter, mem_univ, true_and, hc, ↓reduceIte]
      constructor
      · rintro ⟨hi, hci⟩
        have hne : i ≠ k := fun he => hc (he ▸ hci)
        exact ⟨by have hv := Fin.val_ne_of_ne hne; omega, hci⟩
      · exact fun ⟨hi, hci⟩ => ⟨by omega, hci⟩
  unfold partialValue
  rw [hfilter]
  split_ifs
  · rw [sum_insert (by simp)]
    omega
  · simp

/-- After all ten terms, a requested accumulator is the existing pruned result. -/
theorem partialValue_ten {n : ℕ} (a b : Leaf (n + 1) → ℤ)
    (S : Finset (OutStr (n + 1))) (w : OutStr (n + 1)) (hw : w ∈ S) :
    partialValue a b S w 10 = Pruned.result (n + 1) a b S w := by
  rw [Pruned.result_succ_apply]
  simp only [hw, ↓reduceIte]
  unfold partialValue
  apply sum_equiv Encoding.termDigits
  · intro i
    simp only [mem_filter, mem_univ, true_and, i.isLt]
  · intro _ _
    rfl

/-- Every child's mathematical result has the bound for its remaining depth, including a
skipped empty child whose value is zero. -/
theorem abs_childResult_le {n : ℕ} (a b : Leaf (n + 1) → ℤ) (A B : ℤ)
    (hA : ∀ v, |a v| ≤ A) (hB : ∀ v, |b v| ≤ B)
    (S : Finset (OutStr (n + 1))) (lam : Term) (w : OutStr n) :
    |Pruned.childResult a b S lam w| ≤ 10 ^ n * (A * B) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA fun _ => .P0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB fun _ => .P0)
  unfold Pruned.childResult
  split_ifs
  · exact Pruned.abs_result_le _ _ A B (fun v => hA (Fin.cons lam v))
      (fun v => hB (Fin.cons lam v)) _ _
  · simp only [Pi.zero_apply, abs_zero]
    positivity

/-- The bound covers all partial sums, not only the final recursively specified output. -/
theorem abs_partialValue_le {n : ℕ} (a b : Leaf (n + 1) → ℤ) (A B : ℤ)
    (hA : ∀ v, |a v| ≤ A) (hB : ∀ v, |b v| ≤ B)
    (S : Finset (OutStr (n + 1))) (w : OutStr (n + 1)) (k : ℕ) :
    |partialValue a b S w k| ≤ 10 ^ (n + 1) * (A * B) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA fun _ => .P0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB fun _ => .P0)
  let T := (univ : Finset (Fin 10)).filter fun i =>
    i.val < k ∧ (Encoding.termDigits i).Contributes (w 0)
  have hcard : T.card ≤ 10 := (card_le_univ _).trans_eq (by simp)
  calc
    |partialValue a b S w k| ≤ (T.card : ℤ) * (10 ^ n * (A * B)) :=
      abs_sum_le_card_mul T (fun i _ => abs_childResult_le a b A B hA hB S _ _)
    _ ≤ 10 * (10 ^ n * (A * B)) := by gcongr; exact_mod_cast hcard
    _ = 10 ^ (n + 1) * (A * B) := by ring

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
