/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.List.Count
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Tactic.Push

/-!
# Frequency statistics of streams

The frequency of an item `a` in a stream `s : List α` is `s.count a`. The `k`-th **frequency
moment** is `F_k = ∑ₐ (count a s) ^ k` (`Cslib.Streaming.freqMoment`), and the **largest
frequency** is `F∞ = maxₐ count a s` (`Cslib.Streaming.maxFreq`), the statistics studied by Alon,
Matias and Szegedy [AlonMatiasSzegedy1999]. `F₀` is the number of distinct items, `F₁` the length
of the stream, and the items of a stream are distinct exactly when `F∞ ≤ 1`
(`Cslib.Streaming.maxFreq_le_one_iff`).

The **join size** of two streams `u` and `v` is the inner product of their frequency vectors,
`Cslib.Streaming.joinSize u v = ∑ₐ count a u · count a v`. Read as lists of the join attribute
values of two relations, it is the number of tuples in their equijoin: for key functions `k` and
`l`, the pairs `(a, b)` of `u ×ˢ v` with `k a = l b` number `joinSize (u.map k) (v.map l)`
(`Cslib.Streaming.length_filter_product_eq_joinSize`). When a key may be absent (`k a = none`), as
SQL `NULL` keys are, a pair matches only on a common present key, and the pairs number
`joinSize (u.filterMap k) (v.filterMap l)`
(`Cslib.Streaming.length_filter_product_eq_joinSize_filterMap`). The self-join is `F₂`, and
`joinSize u v ^ 2 ≤ F₂ u F₂ v`. The join-size sketch of Alon, Gibbons, Matias and Szegedy is in
`CslibFrontier.Computability.Streaming.JoinSize`.

## Main definitions

* `Cslib.Streaming.freqMoment`: the frequency moments `F_k` of a stream.
* `Cslib.Streaming.maxFreq`: the largest frequency `F∞` of a stream.
* `Cslib.Streaming.joinSize`: the join size `∑ₐ count a u · count a v` of two streams.

## Main results

* `Cslib.Streaming.freqMoment_zero`: `F₀` is the number of distinct items.
* `Cslib.Streaming.freqMoment_map`: renaming the items injectively keeps the frequency moments.
* `Cslib.Streaming.freqMoment_eq_sum_of_subset`, `Cslib.Streaming.freqMoment_cons_add`,
  `Cslib.Streaming.freqMoment_pos`: for `k ≠ 0`, `F_k` sums over any set containing the items, and
  prepending an item `a` replaces the term `(count a s) ^ k` by `(count a s + 1) ^ k`.
* `Cslib.Streaming.one_le_maxFreq`, `Cslib.Streaming.two_le_maxFreq_of_not_nodup`,
  `Cslib.Streaming.maxFreq_le_one_iff`: `F∞` is at least `1` on nonempty streams, and at most `1`
  exactly on streams of distinct items.
* `Cslib.Streaming.joinSize_eq_sum_map_count`, `Cslib.Streaming.length_filter_product_eq_joinSize`,
  `Cslib.Streaming.length_filter_product_eq_joinSize_filterMap`: the join size sums, over the items
  of the first stream, their counts in the second, so it counts the pairs of an equijoin, with
  total keys or with keys that may be absent.
* `Cslib.Streaming.joinSize_self`, `Cslib.Streaming.joinSize_comm`,
  `Cslib.Streaming.joinSize_sq_le`: the self-join is `F₂`, and `|F ⋈ G|² ≤ F₂(F) F₂(G)`.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*][AlonMatiasSzegedy1999]
* [N. Alon, P. B. Gibbons, Y. Matias, M. Szegedy, *Tracking join and self-join sizes in limited
  storage*][AlonGibbonsMatiasSzegedy1999]
-/

public section

namespace Cslib.Streaming

variable {α : Type*} [DecidableEq α]

/-- The `k`-th **frequency moment** `F_k = ∑ₐ (count a s) ^ k` of a stream. -/
@[expose] def freqMoment (k : ℕ) (s : List α) : ℕ :=
  ∑ a ∈ s.toFinset, s.count a ^ k

/-- `F₀` is the number of distinct items of the stream. -/
theorem freqMoment_zero (s : List α) : freqMoment 0 s = s.toFinset.card := by
  rw [freqMoment, Finset.card_eq_sum_ones]
  simp only [pow_zero]

/-- Renaming the items of a stream injectively keeps its frequency moments. -/
theorem freqMoment_map {α' : Type*} [DecidableEq α'] {f : α → α'} (hf : Function.Injective f)
    (k : ℕ) (s : List α) : freqMoment k (s.map f) = freqMoment k s := by
  unfold freqMoment
  have hT : (s.map f).toFinset = s.toFinset.image f := by
    ext b
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  rw [hT, Finset.sum_image fun a _ b _ h => hf h]
  exact Finset.sum_congr rfl fun a _ => by rw [List.count_map_of_injective _ _ hf]

/-- For `k ≠ 0`, `F_k` is the sum of `(count a s) ^ k` over any set of items containing those of
`s`. -/
theorem freqMoment_eq_sum_of_subset {k : ℕ} (hk : k ≠ 0) {s : List α} {T : Finset α}
    (hT : s.toFinset ⊆ T) : freqMoment k s = ∑ a ∈ T, s.count a ^ k := by
  unfold freqMoment
  refine Finset.sum_subset hT fun a _ ha => ?_
  rw [List.mem_toFinset, ← List.count_eq_zero] at ha
  rw [ha, Nat.zero_pow (Nat.pos_of_ne_zero hk)]

/-- Prepending an item `a` to the stream replaces the term `(count a s) ^ k` of `F_k` by
`(count a s + 1) ^ k`, for `k ≠ 0`. -/
theorem freqMoment_cons_add {k : ℕ} (hk : k ≠ 0) (a : α) (s : List α) :
    freqMoment k (a :: s) + s.count a ^ k = freqMoment k s + (s.count a + 1) ^ k := by
  have hT : s.toFinset ⊆ insert a s.toFinset := Finset.subset_insert _ _
  have hT' : (a :: s).toFinset ⊆ insert a s.toFinset := by rw [List.toFinset_cons]
  rw [freqMoment_eq_sum_of_subset hk hT, freqMoment_eq_sum_of_subset hk hT',
    ← Finset.add_sum_erase _ _ (Finset.mem_insert_self a _),
    ← Finset.add_sum_erase _ _ (Finset.mem_insert_self a _), List.count_cons_self,
    Finset.sum_congr rfl fun x hx =>
      by rw [List.count_cons_of_ne (Finset.ne_of_mem_erase hx).symm]]
  omega

/-- The frequency moments of a nonempty stream are positive. -/
theorem freqMoment_pos (k : ℕ) {s : List α} (hs : s ≠ []) : 0 < freqMoment k s := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil s hs
  exact Finset.sum_pos (fun b hb => Nat.pow_pos (List.count_pos_iff.2 (List.mem_toFinset.1 hb)))
    ⟨a, List.mem_toFinset.2 ha⟩

/-- The largest number of occurrences of an item in the stream `s` (`F∞`; zero for the empty
stream). -/
@[expose] def maxFreq (s : List α) : ℕ :=
  s.toFinset.sup fun a => s.count a

theorem maxFreq_le_one_of_nodup {s : List α} (hs : s.Nodup) : maxFreq s ≤ 1 :=
  Finset.sup_le fun a _ => List.nodup_iff_count_le_one.1 hs a

theorem one_le_maxFreq {s : List α} (hs : s ≠ []) : 1 ≤ maxFreq s := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil s hs
  exact (List.count_pos_iff.2 ha).trans_le (Finset.le_sup (f := fun a => s.count a)
    (List.mem_toFinset.2 ha))

theorem two_le_maxFreq_of_not_nodup {s : List α} (hs : ¬s.Nodup) : 2 ≤ maxFreq s := by
  rw [List.nodup_iff_count_le_one] at hs
  push Not at hs
  obtain ⟨a, ha⟩ := hs
  have hmem : a ∈ s := List.count_pos_iff.1 (by omega)
  exact ha.trans_le (Finset.le_sup (f := fun a => s.count a) (List.mem_toFinset.2 hmem))

/-- The items of a stream are distinct exactly when no item occurs twice. -/
theorem maxFreq_le_one_iff {s : List α} : maxFreq s ≤ 1 ↔ s.Nodup :=
  ⟨fun h => by_contra fun hs => absurd (two_le_maxFreq_of_not_nodup hs) (by omega),
    maxFreq_le_one_of_nodup⟩

/-! ### Join sizes -/

/-- The **join size** `|F ⋈ G| = ∑ₐ count a u · count a v` of the relations whose join attribute
values are listed by the streams `u` and `v`: the inner product of their frequency vectors. -/
@[expose] def joinSize (u v : List α) : ℕ :=
  ∑ a ∈ u.toFinset, u.count a * v.count a

/-- The join size is the sum of `count a u · count a v` over any set of values containing those
of `u`. -/
theorem joinSize_eq_sum_of_subset {u v : List α} {T : Finset α} (hT : u.toFinset ⊆ T) :
    joinSize u v = ∑ a ∈ T, u.count a * v.count a := by
  unfold joinSize
  refine Finset.sum_subset hT fun a _ ha => ?_
  rw [List.mem_toFinset, ← List.count_eq_zero] at ha
  rw [ha, zero_mul]

theorem joinSize_comm (u v : List α) : joinSize u v = joinSize v u := by
  rw [joinSize_eq_sum_of_subset (T := u.toFinset ∪ v.toFinset) Finset.subset_union_left,
    joinSize_eq_sum_of_subset (T := u.toFinset ∪ v.toFinset) Finset.subset_union_right]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- The self-join size of a relation is its second frequency moment. -/
theorem joinSize_self (u : List α) : joinSize u u = freqMoment 2 u := by
  unfold joinSize freqMoment
  exact Finset.sum_congr rfl fun a _ => (sq _).symm

/-- **Join sizes are bounded by self-join sizes**: `|F ⋈ G|² ≤ F₂(F) F₂(G)`, by the
Cauchy–Schwarz inequality. -/
theorem joinSize_sq_le (u v : List α) :
    joinSize u v ^ 2 ≤ freqMoment 2 u * freqMoment 2 v := by
  have hT : u.toFinset ⊆ u.toFinset ∪ v.toFinset := Finset.subset_union_left
  rw [joinSize_eq_sum_of_subset hT, freqMoment_eq_sum_of_subset two_ne_zero hT,
    freqMoment_eq_sum_of_subset two_ne_zero Finset.subset_union_right]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- The join size of `u` and `v` sums, over the items `a` of `u` with multiplicity, the number of
occurrences of `a` in `v`. -/
theorem joinSize_eq_sum_map_count (u v : List α) : joinSize u v = (u.map (v.count ·)).sum := by
  rw [Finset.sum_list_map_count]
  rfl

section Equijoin

variable {β γ : Type*}

/-- **Equijoin cardinality with absent keys.** If the tuples `a` of `u` and `b` of `v` have
optional join keys `k a` and `l b`, the pairs `(a, b)` of `u ×ˢ v` with a common present key
number `joinSize (u.filterMap k) (v.filterMap l)`: a tuple without a key (`none`, such as an SQL
`NULL` key) matches nothing, not even another tuple without a key. -/
theorem length_filter_product_eq_joinSize_filterMap (k : β → Option α) (l : γ → Option α)
    (u : List β) (v : List γ) :
    ((u ×ˢ v).filter fun (a, b) => ∃ c, k a = some c ∧ l b = some c).length =
      joinSize (u.filterMap k) (v.filterMap l) := by
  rw [joinSize_eq_sum_map_count]
  induction u with
  | nil => rfl
  | cons a u ih =>
    rw [List.product_cons, List.filter_append, List.length_append, ih, List.filterMap_cons]
    cases h : k a with
    | none => simp [h]
    | some c =>
      rw [List.map_cons, List.sum_cons, List.count_filterMap, List.filter_map, List.length_map,
        ← List.countP_eq_length_filter]
      refine congrArg (· + _) (List.countP_congr fun b _ => ?_)
      simp [h]

/-- **Equijoin cardinality.** If the tuples `a` of `u` and `b` of `v` have join keys `k a` and
`l b`, the pairs `(a, b)` of `u ×ˢ v` with `k a = l b` number `joinSize (u.map k) (v.map l)`. -/
theorem length_filter_product_eq_joinSize (k : β → α) (l : γ → α) (u : List β) (v : List γ) :
    ((u ×ˢ v).filter fun (a, b) => k a = l b).length = joinSize (u.map k) (v.map l) := by
  rw [← List.filterMap_eq_map, ← List.filterMap_eq_map,
    ← length_filter_product_eq_joinSize_filterMap]
  refine congrArg List.length (List.filter_congr fun (a, b) _ => ?_)
  simp only [Function.comp_apply, Option.some.injEq, exists_eq_left']
  exact decide_eq_decide.2 eq_comm

end Equijoin

end Cslib.Streaming
