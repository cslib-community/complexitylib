/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib; Mathlib's `Archive`, not the library, has the injective case)

public import Complexity.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Basic
import Complexity.Foundations.Order.Mirsky
import Mathlib.Combinatorics.Pigeonhole

/-!
# The Erdős–Szekeres monotone subsequence theorem

A sequence `f : Fin n → β` in a linear order with `r * s < n` has a monotone (non-decreasing)
subsequence of `r + 1` terms or a strictly decreasing subsequence of `s + 1` terms
([ErdosSzekeres1935], p. 467, Theorem, and its `f(i, k)` form on p. 468; there equal values may
count as increasing or decreasing). For injective sequences the first alternative is strictly
increasing.

The proof is the standard reduction to Mirsky's theorem: order the positions by
`i ≤ j ∧ f i ≤ f j`. Its chains are monotone subsequences and its antichains are strictly
decreasing subsequences. If every chain has at most `r` elements, Mirsky's theorem
(`exists_antichain_coloring_iff`) covers the `n > r * s` positions by `r` antichains, and the
pigeonhole principle puts more than `s` of them in one antichain.

Subsequences are `Finset (Fin n)`s of positions. Mathlib's `Archive` has the injective case as
`Theorems100.erdos_szekeres`, but the `Archive` is not part of the Mathlib library. Mathlib proper
has only the infinitary form `exists_increasing_or_nonincreasing_subseq`.

## Main results

* `exists_monotoneOn_or_strictAntiOn_of_mul_lt`: the theorem for arbitrary sequences.
* `exists_strictMonoOn_or_strictAntiOn_of_mul_lt`: the theorem for injective sequences.

## References

* [P. Erdős, G. Szekeres, *A combinatorial problem in geometry*][ErdosSzekeres1935]
-/

public section

section ErdosSzekeres

variable {β : Type*} [LinearOrder β] {n : ℕ}

/-- Positions of a sequence `f : Fin n → β`, ordered by `i ≤ j ∧ f i ≤ f j`. -/
private def SeqPos (_f : Fin n → β) : Type := Fin n

private instance (f : Fin n → β) : PartialOrder (SeqPos f) :=
  PartialOrder.lift (fun i : Fin n => (i, f i)) fun _ _ h => congrArg Prod.fst h

private instance (f : Fin n → β) : Fintype (SeqPos f) := inferInstanceAs (Fintype (Fin n))

/-- The identity `SeqPos f ≃ Fin n`. -/
private def SeqPos.equiv (f : Fin n → β) : SeqPos f ≃ Fin n := Equiv.refl _

private theorem SeqPos.le_iff (f : Fin n → β) {i j : SeqPos f} :
    i ≤ j ↔ SeqPos.equiv f i ≤ SeqPos.equiv f j ∧ f (SeqPos.equiv f i) ≤ f (SeqPos.equiv f j) :=
  Iff.rfl

/-- **Erdős–Szekeres** ([ErdosSzekeres1935], pp. 467–468): a sequence of more than `r * s` terms
in a linear order has a monotone subsequence of `r + 1` terms or a strictly decreasing subsequence
of `s + 1` terms. -/
theorem exists_monotoneOn_or_strictAntiOn_of_mul_lt (f : Fin n → β) {r s : ℕ} (hn : r * s < n) :
    (∃ t : Finset (Fin n), r < t.card ∧ MonotoneOn f t) ∨
      ∃ t : Finset (Fin n), s < t.card ∧ StrictAntiOn f t := by
  classical
  by_contra! h
  obtain ⟨hmono, hanti⟩ := h
  let e := SeqPos.equiv f
  have hchain : ∀ C : Finset (SeqPos f), IsChain (· ≤ ·) (C : Set (SeqPos f)) → C.card ≤ r := by
    intro C hC
    by_contra! hlt
    refine hmono (C.map e.toEmbedding) (by simpa using hlt) ?_
    rintro _ hi _ hj hij
    simp only [Finset.coe_map, Equiv.coe_toEmbedding, Set.mem_image, Finset.mem_coe] at hi hj
    obtain ⟨i, hi, rfl⟩ := hi
    obtain ⟨j, hj, rfl⟩ := hj
    rcases eq_or_ne i j with rfl | hne
    · exact le_rfl
    · rcases hC hi hj hne with h | h
      · exact ((SeqPos.le_iff f).mp h).2
      · exact absurd (e.injective (le_antisymm hij ((SeqPos.le_iff f).mp h).1)) hne
  obtain ⟨c, hc⟩ := exists_antichain_coloring_iff.mpr hchain
  obtain ⟨y, hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := c) (n := s)
    (by rwa [Fintype.card_fin, show Fintype.card (SeqPos f) = n from Fintype.card_fin n])
  refine hanti ((Finset.univ.filter fun x => c x = y).map e.toEmbedding) (by simpa using hy) ?_
  rintro _ hi _ hj hij
  simp only [Finset.coe_map, Equiv.coe_toEmbedding, Set.mem_image, Finset.mem_coe,
    Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  obtain ⟨i, hi, rfl⟩ := hi
  obtain ⟨j, hj, rfl⟩ := hj
  by_contra hle
  exact hc y hi hj (fun h => (ne_of_lt hij) (congrArg e h))
    ((SeqPos.le_iff f).mpr ⟨hij.le, not_lt.mp hle⟩)

/-- **Erdős–Szekeres** for injective sequences ([ErdosSzekeres1935], pp. 467–468): more than
`r * s` distinct terms have a strictly increasing subsequence of `r + 1` terms or a strictly
decreasing subsequence of `s + 1` terms. -/
theorem exists_strictMonoOn_or_strictAntiOn_of_mul_lt {f : Fin n → β} (hf : Function.Injective f)
    {r s : ℕ} (hn : r * s < n) :
    (∃ t : Finset (Fin n), r < t.card ∧ StrictMonoOn f t) ∨
      ∃ t : Finset (Fin n), s < t.card ∧ StrictAntiOn f t :=
  (exists_monotoneOn_or_strictAntiOn_of_mul_lt f hn).imp_left fun ⟨t, ht, hm⟩ =>
    ⟨t, ht, hm.strictMonoOn_of_injOn hf.injOn⟩

end ErdosSzekeres
