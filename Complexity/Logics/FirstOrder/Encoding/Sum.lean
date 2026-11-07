/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Encoding
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.List.GetD

/-!
# Encodings for sums of relational vocabularies

`Vocabulary.sum` enumerates the left language's relation symbols before the right language's.
Consequently concatenating the two lists of relation tables gives the encoding for the sum
language. Table lookup preserves both parts, and well-formedness splits into the corresponding
conditions on the two lists. No tables for function symbols are introduced.

## Main definitions

* `Cslib.Logic.Vocabulary.sum`: the concatenated enumeration of two relational vocabularies.

## Main results

* `Cslib.Logic.Vocabulary.table_sum_inl`, `Cslib.Logic.Vocabulary.table_sum_inr`: lookup in
  concatenated relation tables.
* `Cslib.Logic.Vocabulary.wellFormed_sum_iff`: well-formedness of the combined input, including
  malformed source inputs when the right-hand table count is fixed.
-/

public section

universe u v u' v'

namespace Cslib.Logic.Vocabulary

open FirstOrder Language

variable {L : Language.{u, v}} {L' : Language.{u', v'}}

/-- Enumerate the symbols of the left vocabulary followed by the symbols of the right one. -/
@[expose] def sum (v : Vocabulary L) (w : Vocabulary L') : Vocabulary (L.sum L') where
  count := v.count + w.count
  symbol := finSumFinEquiv.symm.trans
    ((v.symbol.sumCongr w.symbol).trans (Equiv.sigmaSumDistrib L.Relations L'.Relations).symm)

/-- The sum vocabulary has one entry for each entry of its two summands. -/
@[simp] theorem sum_count (v : Vocabulary L) (w : Vocabulary L') :
    (v.sum w).count = v.count + w.count := rfl

/-- A left relation retains its original table index. -/
@[simp] theorem index_sum_inl (v : Vocabulary L) (w : Vocabulary L')
    (r : Σ n, L.Relations n) :
    (v.sum w).index ⟨r.1, Sum.inl r.2⟩ = v.index r := rfl

/-- A right relation's table index is shifted by the number of left relations. -/
@[simp] theorem index_sum_inr (v : Vocabulary L) (w : Vocabulary L')
    (r : Σ n, L'.Relations n) :
    (v.sum w).index ⟨r.1, Sum.inr r.2⟩ = v.count + w.index r := rfl

/-- The arity of a left entry in the combined enumeration is unchanged. -/
@[simp] theorem arity_sum_castAdd (v : Vocabulary L) (w : Vocabulary L') (i : Fin v.count) :
    (v.sum w).arity (Fin.castAdd w.count i) = v.arity i := by
  change ((Equiv.sigmaSumDistrib L.Relations L'.Relations).symm
    ((v.symbol.sumCongr w.symbol) (finSumFinEquiv.symm (Fin.castAdd w.count i)))).1 = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- The arity of a right entry in the combined enumeration is unchanged. -/
@[simp] theorem arity_sum_natAdd (v : Vocabulary L) (w : Vocabulary L') (i : Fin w.count) :
    (v.sum w).arity (Fin.natAdd v.count i) = w.arity i := by
  change ((Equiv.sigmaSumDistrib L.Relations L'.Relations).symm
    ((v.symbol.sumCongr w.symbol) (finSumFinEquiv.symm (Fin.natAdd v.count i)))).1 = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- Left relation tables are preserved by concatenation when the left list has its expected
number of tables. -/
theorem table_sum_inl (v : Vocabulary L) (w : Vocabulary L') (n : ℕ)
    (xs ys : List (List Bool)) (hlen : xs.length = v.count) (r : Σ k, L.Relations k) :
    (v.sum w).table (n, xs ++ ys) ⟨r.1, Sum.inl r.2⟩ = v.table (n, xs) r := by
  simp only [table, index_sum_inl]
  exact List.getD_append xs ys [] _ (hlen ▸ v.index_lt r)

/-- Right relation tables are preserved by concatenation when the left list has its expected
number of tables. -/
theorem table_sum_inr (v : Vocabulary L) (w : Vocabulary L') (n : ℕ)
    (xs ys : List (List Bool)) (hlen : xs.length = v.count) (r : Σ k, L'.Relations k) :
    (v.sum w).table (n, xs ++ ys) ⟨r.1, Sum.inr r.2⟩ = w.table (n, ys) r := by
  simp only [table, index_sum_inr]
  rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.add_sub_cancel_left]

private theorem wellFormed_sum_iff_of_left_length (v : Vocabulary L) (w : Vocabulary L')
    (n : ℕ) (xs ys : List (List Bool)) (hx : xs.length = v.count) :
    (v.sum w).WellFormed (n, xs ++ ys) ↔ v.WellFormed (n, xs) ∧ w.WellFormed (n, ys) := by
  constructor
  · rintro ⟨hlen, htables⟩
    have hy : ys.length = w.count := by simpa [hx] using hlen
    refine ⟨⟨hx, fun i => ?_⟩, ⟨hy, fun i => ?_⟩⟩
    · have h := htables (Fin.castAdd w.count i)
      simpa only [Fin.val_castAdd, arity_sum_castAdd,
        List.getD_append xs ys [] i (by omega)] using h
    · have h := htables (Fin.natAdd v.count i)
      simpa only [Fin.val_natAdd, arity_sum_natAdd,
        List.getD_append_right xs ys [] (v.count + i) (by omega), hx,
        Nat.add_sub_cancel_left] using h
  · rintro ⟨⟨_, hxs⟩, ⟨hy, hys⟩⟩
    refine ⟨by simp [sum_count, hx, hy], ?_⟩
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.val_castAdd, arity_sum_castAdd,
        List.getD_append xs ys [] i (by omega)] using hxs i
    · simpa only [Fin.val_natAdd, arity_sum_natAdd,
        List.getD_append_right xs ys [] (v.count + i) (by omega), hx,
        Nat.add_sub_cancel_left] using hys i

/-- If the number of right tables is fixed, combined well-formedness is exactly well-formedness
of both inputs. In particular a malformed left input cannot be repaired by appending right
tables. -/
theorem wellFormed_sum_iff (v : Vocabulary L) (w : Vocabulary L') (n : ℕ)
    (xs ys : List (List Bool)) (hy : ys.length = w.count) :
    (v.sum w).WellFormed (n, xs ++ ys) ↔ v.WellFormed (n, xs) ∧ w.WellFormed (n, ys) := by
  constructor
  · intro h
    have hx : xs.length = v.count := by simpa [hy] using h.1
    exact (wellFormed_sum_iff_of_left_length v w n xs ys hx).1 h
  · intro h
    exact (wellFormed_sum_iff_of_left_length v w n xs ys h.1.1).2 h

/-- Concatenating well-formed relation tables gives a well-formed sum-language input. -/
theorem WellFormed.sum {v : Vocabulary L} {w : Vocabulary L'} {n : ℕ}
    {xs ys : List (List Bool)} (hx : v.WellFormed (n, xs)) (hy : w.WellFormed (n, ys)) :
    (v.sum w).WellFormed (n, xs ++ ys) :=
  (wellFormed_sum_iff v w n xs ys hy.1).2 ⟨hx, hy⟩

end Cslib.Logic.Vocabulary
