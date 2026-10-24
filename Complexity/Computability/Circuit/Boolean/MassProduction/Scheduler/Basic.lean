/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Synthesis
public import Cslib.Computability.Circuit.Boolean.Synthesis
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.OfFn
public import Mathlib.Order.PiLex
public import Complexity.Algorithms.Lean.Sort.Bitonic.Basic
import Complexity.Algorithms.Lean.Sort.Bitonic.Correctness
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Order.Interval.Finset.Fin

/-!
# Synthesis tools for the scheduler circuit

The scheduler uses the shared circuit synthesis rule (`Synthesis.circuit`),
shared prefix disjunctions (`Synthesis.prefixOr`), and two facts about
sorted arrays: a permuted finite array is a reindexing (`List.Perm.exists_equiv_ofFn`), and in an
array of flags sorted with true flags first, a position holds a true flag exactly when it precedes
the number of true flags (`eq_true_iff_lt_card_of_sorted`).

Gate counts are synthesis budgets: they count every gate, including constants, and do not
certify the running time of any construction.

## Main definitions

* `Cslib.Circuits.Boolean.prefixOr`: the disjunction of the first `j + 1` of `r` functions.

## Main results

* `Cslib.Circuits.Synthesis.prefixOr`: all prefix disjunctions of `r` available functions.
* `List.Perm.exists_equiv_ofFn`: permuted finite arrays differ by a permutation of positions.
* `Cslib.Circuits.Boolean.eq_true_iff_lt_card_of_sorted`: positions of true sorted flags.
* `Cslib.Circuits.Boolean.apply_zero_le_of_toLex_le`: lexicographic order on one bit.
* `Cslib.Circuits.Boolean.sort_flag_eq_true_iff`: positions of true keys after sorting.

## References

* Adapted from MassProduction/Nonuniform/FlagSelection.lean and
  MassProduction/Nonuniform/OrderedPermutation.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

open Finset

/-- Permuted finite arrays differ by a permutation of their positions. -/
theorem List.Perm.exists_equiv_ofFn {α : Type*} {n : ℕ} {f g : Fin n → α}
    (h : (List.ofFn f).Perm (List.ofFn g)) : ∃ σ : Equiv.Perm (Fin n), ∀ i, f i = g (σ i) := by
  classical
  have hf : (List.ofFn f).length = n := List.length_ofFn
  have hg : (List.ofFn g).length = n := List.length_ofFn
  refine ⟨⟨fun i => Fin.cast hg (h.idxBij (Fin.cast hf.symm i)),
    fun j => Fin.cast hf (h.symm.idxBij (Fin.cast hg.symm j)), fun i => ?_, fun j => ?_⟩,
    fun i => ?_⟩
  · simp only [Fin.cast_cast, Fin.cast_eq_self, List.Perm.idxBij_symm_idxBij]
  · simp only [Fin.cast_cast, Fin.cast_eq_self, List.Perm.idxBij_idxBij_symm]
  · have hi := h.getElem_idxBij_eq_getElem (Fin.cast hf.symm i)
    simp only [List.getElem_ofFn, Fin.val_cast] at hi
    simp only [Equiv.coe_fn_mk]
    rw [← hi]
    rfl

namespace Cslib.Circuits

variable {n : ℕ}

namespace Boolean

/-- Every flag is false after a false flag; flags are sorted with true flags first. -/
theorem eq_true_iff_lt_card_of_sorted {k : ℕ} (g : Fin k → Bool)
    (sorted : ∀ i j, i ≤ j → g i = false → g j = false) (j : Fin k) :
    g j = true ↔ j.val < #{i | g i = true} := by
  constructor
  · intro hj
    have hsub : Iic j ⊆ ({i | g i = true} : Finset (Fin k)) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and]
      by_contra hn
      exact absurd (sorted i j (mem_Iic.mp hi) (by simpa using hn)) (by simp [hj])
    have := card_le_card hsub
    rw [Fin.card_Iic] at this
    lia
  · intro hj
    by_contra hn
    have hsub : ({i | g i = true} : Finset (Fin k)) ⊆ Iio j := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      rw [mem_Iio]
      by_contra hle
      exact absurd (sorted j i (not_lt.mp hle) (by simpa using hn)) (by simp [hi])
    have := card_le_card hsub
    rw [Fin.card_Iio] at this
    lia

/-- On one coordinate, lexicographic order is the order of the bit. -/
theorem apply_zero_le_of_toLex_le {x y : Fin 1 → Bool} (h : toLex x ≤ toLex y) : x 0 ≤ y 0 :=
  Pi.apply_le_of_toLex h fun j hj => absurd hj (Fin.not_lt_zero j)

/-- Sorting records by a one-bit key with true keys first puts a true key at position `j` exactly
when `j` is less than the number of true keys. -/
theorem sort_flag_eq_true_iff {α : Type*} (φ : α → Fin 1 → Bool) (p : ℕ)
    (input : Fin (BitonicSort.arity p) → α) (j : Fin (BitonicSort.arity p)) :
    φ (BitonicSort.sort (fun r => toLex (φ r)) p false input j) 0 = true ↔
      j.val < #{i | φ (input i) 0 = true} := by
  rw [← (BitonicSort.sort_perm (fun r => toLex (φ r)) p false input).card_filter_ofFn_eq
    (fun r => φ r 0 = true)]
  refine eq_true_iff_lt_card_of_sorted
    (fun j => φ (BitonicSort.sort (fun r => toLex (φ r)) p false input j) 0)
    (fun j j' hjj' hj => ?_) j
  have h := apply_zero_le_of_toLex_le
    (BitonicSort.antitone_sort (fun r => toLex (φ r)) p input hjj')
  rw [hj] at h
  exact Bool.eq_false_iff.mpr fun h' => by rw [h'] at h; exact absurd h (by decide)

/-- The disjunction of the first `j + 1` of `r` functions. -/
def prefixOr {r : ℕ} (F : Fin r → BooleanFunction n) (j : ℕ) : BooleanFunction n :=
  fun x => decide (∃ e : Fin r, e.val ≤ j ∧ F e x = true)

private theorem prefixOr_zero {r : ℕ} (F : Fin r → BooleanFunction n) (h : 0 < r) :
    prefixOr F 0 = F ⟨0, h⟩ := by
  funext x
  rw [Bool.eq_iff_iff, prefixOr, decide_eq_true_iff]
  constructor
  · rintro ⟨e, he, hx⟩
    rwa [show e = ⟨0, h⟩ from Fin.ext (by lia)] at hx
  · exact fun hx => ⟨⟨0, h⟩, le_rfl, hx⟩

private theorem prefixOr_succ {r : ℕ} (F : Fin r → BooleanFunction n) (j : ℕ) (h : j + 1 < r) :
    prefixOr F (j + 1) = fun x => prefixOr F j x || F ⟨j + 1, h⟩ x := by
  funext x
  rw [Bool.eq_iff_iff, Bool.or_eq_true, prefixOr, prefixOr, decide_eq_true_iff,
    decide_eq_true_iff]
  constructor
  · rintro ⟨e, he, hx⟩
    rcases Nat.lt_or_ge e.val (j + 1) with hlt | hge
    · exact Or.inl ⟨e, by lia, hx⟩
    · exact Or.inr (by rwa [show e = ⟨j + 1, h⟩ from Fin.ext (by lia)] at hx)
  · rintro (⟨e, he, hx⟩ | hx)
    · exact ⟨e, by lia, hx⟩
    · exact ⟨⟨j + 1, h⟩, le_rfl, hx⟩

end Boolean

open Boolean in
/-- All prefix disjunctions of `r` available functions, sharing each prefix with the next: one OR
gate per function after the first. -/
theorem Synthesis.prefixOr {r : ℕ} {s : Set (BooleanFunction n)} (F : Fin r → BooleanFunction n)
    (hF : ∀ e, F e ∈ s) :
    Synthesis interpretation s (Set.range fun e : Fin r => Boolean.prefixOr F e.val) r := by
  suffices h : ∀ J ≤ r, Synthesis interpretation s
      {f | ∃ e : Fin r, e.val < J ∧ f = Boolean.prefixOr F e.val} J by
    exact (h r le_rfl).mono Set.Subset.rfl (by rintro _ ⟨e, rfl⟩; exact ⟨e, e.isLt, rfl⟩) le_rfl
  intro J
  induction J with
  | zero =>
    intro _
    exact Synthesis.of_subset (by rintro _ ⟨e, he, -⟩; exact absurd he (Nat.not_lt_zero _))
  | succ J ih =>
    intro hJ
    have hprev := ih (by lia)
    have hstep : Synthesis interpretation (s ∪ {f | ∃ e : Fin r, e.val < J ∧
        f = Boolean.prefixOr F e.val}) {Boolean.prefixOr F J} 1 := by
      rcases J with _ | J
      · rw [prefixOr_zero F (by lia)]
        exact (Synthesis.of_mem (Or.inl (hF _))).mono Set.Subset.rfl Set.Subset.rfl (by lia)
      · rw [prefixOr_succ F J hJ]
        exact (Synthesis.of_mem (Or.inr ⟨⟨J, by lia⟩, by simp, rfl⟩)).or
          (Synthesis.of_mem (Or.inl (hF _)))
    refine (hprev.comp hstep).mono Set.Subset.rfl ?_ le_rfl
    rintro _ ⟨e, he, rfl⟩
    rcases Nat.lt_or_ge e.val J with hlt | hge
    · exact Or.inl ⟨e, hlt, rfl⟩
    · exact Or.inr (by rw [show e.val = J by lia]; rfl)

end Cslib.Circuits
