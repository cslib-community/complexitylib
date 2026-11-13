/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.Data.Fintype.Powerset

/-!
# Permanents between row and column sets

For finite sets `S` and `T` of indices, `Matrix.permOn M S T` sums, over the bijections `f` from
`S` onto `T`, the products `∏ i ∈ S, M i (f i)`. A bijection is represented by a function on the
whole index type that is the identity outside `S` (`Matrix.bijOn`). When `S` and `T` have
different sizes there is no bijection and the sum is `0`; the permanent is `permOn M univ univ`
(`Matrix.permanent_eq_permOn`).

These sums are the minors of the permanent. They split along a subset of the rows: for
`S' ⊆ S`, `permOn M S T` is the sum over `T' ⊆ T` of `permOn M S' T' * permOn M (S \ S') (T \ T')`
(`Matrix.permOn_split`), the generalized Laplace expansion. For a sum of two matrices,
`permOn (A + C) S T` is the sum over `S' ⊆ S` and `T' ⊆ T` of
`permOn A S' T' * permOn C (S \ S') (T \ T')` (`Matrix.permOn_add`). This is how the
cycle-cover analysis of gadget constructions, such as those of Valiant's theorem
[Valiant][Valiant1979], is carried out on matrices.

## Main definitions

* `Matrix.bijOn`: the functions mapping `S` bijectively onto `T` and fixing everything else.
* `Matrix.permOn`: the permanent sum between a row set and a column set.
* `Matrix.permOnList`: Laplace expansion along explicit lists of rows and columns, for computation.

## Main results

* `Matrix.permanent_eq_permOn`: the permanent is the sum between all rows and all columns.
* `Matrix.permOn_split`: generalized Laplace expansion along a set of rows.
* `Matrix.permOn_add`: the permanent sum of a sum of two matrices.
* `Matrix.permOn_laplace`: expansion along one row.
* `Matrix.permOn_eq_permOnList`: `permOn` evaluated by `permOnList`.
* `Matrix.permOn_eq_card`: for a 0/1 matrix, `permOn` counts the bijections along `1`-entries.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
-/

@[expose] public section

open Finset

namespace Matrix

variable {V R : Type*} [Fintype V] [DecidableEq V] [CommSemiring R]

open Classical in
/-- The functions mapping `S` bijectively onto `T` and fixing every index outside `S`. -/
noncomputable def bijOn (S T : Finset V) : Finset (V → V) :=
  univ.filter fun f => (∀ i ∈ S, f i ∈ T) ∧ (∀ i ∈ S, ∀ j ∈ S, f i = f j → i = j) ∧
    (∀ t ∈ T, ∃ i ∈ S, f i = t) ∧ ∀ i ∉ S, f i = i

theorem mem_bijOn {S T : Finset V} {f : V → V} :
    f ∈ bijOn S T ↔ (∀ i ∈ S, f i ∈ T) ∧ (∀ i ∈ S, ∀ j ∈ S, f i = f j → i = j) ∧
      (∀ t ∈ T, ∃ i ∈ S, f i = t) ∧ ∀ i ∉ S, f i = i := by
  classical
  simp [bijOn]

/-- The permanent sum between the row set `S` and the column set `T`: the sum over bijections
`f` from `S` onto `T` of `∏ i ∈ S, M i (f i)`. -/
noncomputable def permOn (M : Matrix V V R) (S T : Finset V) : R :=
  ∑ f ∈ bijOn S T, ∏ i ∈ S, M i (f i)

/-- The permanent is the permanent sum between all rows and all columns. -/
theorem permanent_eq_permOn (M : Matrix V V R) : M.permanent = permOn M univ univ := by
  rw [← permanent_transpose, permanent, permOn]
  simp only [transpose_apply]
  refine Finset.sum_bij' (fun σ _ => ⇑σ)
    (fun f hf => Equiv.ofBijective f ?_) (fun σ _ => ?_) (fun f hf => mem_univ _)
    (fun σ _ => ?_) (fun f hf => ?_) (fun σ _ => rfl)
  · obtain ⟨-, hinj, hsurj, -⟩ := mem_bijOn.1 hf
    exact ⟨fun i j h => hinj i (mem_univ _) j (mem_univ _) h,
      fun t => let ⟨i, _, hi⟩ := hsurj t (mem_univ _); ⟨i, hi⟩⟩
  · exact mem_bijOn.2 ⟨fun _ _ => mem_univ _, fun i _ j _ h => σ.injective h,
      fun t _ => ⟨σ.symm t, mem_univ _, σ.apply_symm_apply t⟩, fun i hi => absurd (mem_univ i) hi⟩
  · ext; rfl
  · rfl

/-- The permanent sum depends only on the entries in rows `S` and columns `T`. -/
theorem permOn_congr {M N : Matrix V V R} {S T : Finset V}
    (h : ∀ i ∈ S, ∀ j ∈ T, M i j = N i j) : permOn M S T = permOn N S T := by
  refine Finset.sum_congr rfl fun f hf => Finset.prod_congr rfl fun i hi => ?_
  exact h i hi (f i) ((mem_bijOn.1 hf).1 i hi)

/-- A row of `S` vanishing on the columns `T` makes the permanent sum vanish. -/
theorem permOn_eq_zero_of_row {M : Matrix V V R} {S T : Finset V} {i : V} (hi : i ∈ S)
    (h : ∀ j ∈ T, M i j = 0) : permOn M S T = 0 :=
  Finset.sum_eq_zero fun _ hf =>
    Finset.prod_eq_zero hi (h _ ((mem_bijOn.1 hf).1 i hi))

/-- A column of `T` vanishing on the rows `S` makes the permanent sum vanish. -/
theorem permOn_eq_zero_of_col {M : Matrix V V R} {S T : Finset V} {j : V} (hj : j ∈ T)
    (h : ∀ i ∈ S, M i j = 0) : permOn M S T = 0 :=
  Finset.sum_eq_zero fun f hf => by
    obtain ⟨i, hi, rfl⟩ := (mem_bijOn.1 hf).2.2.1 j hj
    exact Finset.prod_eq_zero hi (h i hi)

/-- There is one bijection between empty sets. -/
theorem permOn_empty_left (M : Matrix V V R) (T : Finset V) :
    permOn M ∅ T = if T = ∅ then 1 else 0 := by
  rw [permOn]
  split_ifs with hT
  · subst hT
    have : bijOn (∅ : Finset V) ∅ = {id} := by
      ext f
      simp only [mem_bijOn, notMem_empty, IsEmpty.forall_iff, implies_true, false_and,
        exists_false, not_false_eq_true, forall_const, true_and, mem_singleton]
      exact ⟨fun h => funext h, fun h i => h ▸ rfl⟩
    rw [this, sum_singleton, prod_empty]
  · obtain ⟨t, ht⟩ := nonempty_iff_ne_empty.2 hT
    refine sum_eq_zero fun f hf => ?_
    obtain ⟨i, hi, -⟩ := (mem_bijOn.1 hf).2.2.1 t ht
    exact absurd hi (notMem_empty i)

/-- Restrict a function to `X`: equal to `f` on `X`, the identity elsewhere. -/
private def restrictTo (X : Finset V) (f : V → V) : V → V :=
  fun i => if i ∈ X then f i else i

/-- Glue two functions along `X`. -/
private def glue (X : Finset V) (f₁ f₂ : V → V) : V → V :=
  fun i => if i ∈ X then f₁ i else f₂ i

/-- **Generalized Laplace expansion** along a set `S' ⊆ S` of rows. -/
theorem permOn_split (M : Matrix V V R) {S S' : Finset V} (hS' : S' ⊆ S) (T : Finset V) :
    permOn M S T =
      ∑ T' ∈ T.powerset, permOn M S' T' * permOn M (S \ S') (T \ T') := by
  have hR : ∑ T' ∈ T.powerset, permOn M S' T' * permOn M (S \ S') (T \ T') =
      ∑ x ∈ T.powerset.sigma fun T' => bijOn S' T' ×ˢ bijOn (S \ S') (T \ T'),
        (∏ i ∈ S', M i (x.2.1 i)) * ∏ i ∈ S \ S', M i (x.2.2 i) := by
    rw [sum_sigma]
    refine sum_congr rfl fun T' _ => ?_
    rw [permOn, permOn, sum_mul_sum, sum_product]
  rw [hR, permOn]
  symm
  refine Finset.sum_bij' (fun x _ => glue S' x.2.1 x.2.2)
    (fun f _ => ⟨S'.image f, restrictTo S' f, restrictTo (S \ S') f⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨T', f₁, f₂⟩ hx
    simp only [mem_sigma, mem_powerset, mem_product, mem_bijOn] at hx
    obtain ⟨hT', ⟨h₁m, h₁i, h₁s, h₁o⟩, ⟨h₂m, h₂i, h₂s, h₂o⟩⟩ := hx
    refine mem_bijOn.2 ⟨fun i hi => ?_, fun i hi j hj h => ?_, fun t ht => ?_, fun i hi => ?_⟩
    · simp only [glue]
      split_ifs with h
      · exact hT' (h₁m i h)
      · exact (mem_sdiff.1 (h₂m i (mem_sdiff.2 ⟨hi, h⟩))).1
    · simp only [glue] at h
      by_cases hi' : i ∈ S' <;> by_cases hj' : j ∈ S' <;> simp only [hi', hj', ite_true,
        ite_false] at h
      · exact h₁i i hi' j hj' h
      · exact absurd (h ▸ h₁m i hi') (mem_sdiff.1 (h₂m j (mem_sdiff.2 ⟨hj, hj'⟩))).2
      · exact absurd (h ▸ h₁m j hj') (mem_sdiff.1 (h₂m i (mem_sdiff.2 ⟨hi, hi'⟩))).2
      · exact h₂i i (mem_sdiff.2 ⟨hi, hi'⟩) j (mem_sdiff.2 ⟨hj, hj'⟩) h
    · by_cases htT : t ∈ T'
      · obtain ⟨i, hi, rfl⟩ := h₁s t htT
        exact ⟨i, hS' hi, by simp [glue, hi]⟩
      · obtain ⟨i, hi, rfl⟩ := h₂s _ (mem_sdiff.2 ⟨ht, htT⟩)
        exact ⟨i, (mem_sdiff.1 hi).1, by simp [glue, (mem_sdiff.1 hi).2]⟩
    · have hi' : i ∉ S' := fun h => hi (hS' h)
      simp only [glue, hi', ite_false]
      exact h₂o i fun h => hi (mem_sdiff.1 h).1
  · intro f hf
    obtain ⟨hm, hi, hs, ho⟩ := mem_bijOn.1 hf
    simp only [mem_sigma, mem_powerset, mem_product, mem_bijOn, restrictTo]
    refine ⟨fun t ht => ?_, ⟨fun i hi' => ?_, fun i hi' j hj' h => ?_, fun t ht => ?_,
      fun i hi' => ?_⟩, ⟨fun i hi' => ?_, fun i hi' j hj' h => ?_, fun t ht => ?_,
      fun i hi' => ?_⟩⟩
    · obtain ⟨i, hi', rfl⟩ := mem_image.1 ht
      exact hm i (hS' hi')
    · simp only [hi', ite_true]; exact mem_image_of_mem f hi'
    · simp only [hi', hj', ite_true] at h; exact hi i (hS' hi') j (hS' hj') h
    · obtain ⟨i, hi', rfl⟩ := mem_image.1 ht
      exact ⟨i, hi', by simp [hi']⟩
    · simp [hi']
    · simp only [hi', ite_true]
      refine mem_sdiff.2 ⟨hm i (mem_sdiff.1 hi').1, fun h => ?_⟩
      obtain ⟨j, hj, hji⟩ := mem_image.1 h
      exact (mem_sdiff.1 hi').2 (hi j (hS' hj) i (mem_sdiff.1 hi').1 hji ▸ hj)
    · simp only [hi', hj', ite_true] at h
      exact hi i (mem_sdiff.1 hi').1 j (mem_sdiff.1 hj').1 h
    · obtain ⟨i, hi', rfl⟩ := hs t (mem_sdiff.1 ht).1
      refine ⟨i, mem_sdiff.2 ⟨hi', fun h => (mem_sdiff.1 ht).2 (mem_image_of_mem f h)⟩, ?_⟩
      simp [mem_sdiff.2 ⟨hi', fun h => (mem_sdiff.1 ht).2 (mem_image_of_mem f h)⟩]
    · simp [hi']
  · rintro ⟨T', f₁, f₂⟩ hx
    simp only [mem_sigma, mem_powerset, mem_product, mem_bijOn] at hx
    obtain ⟨hT', ⟨h₁m, h₁i, h₁s, h₁o⟩, ⟨h₂m, h₂i, h₂s, h₂o⟩⟩ := hx
    have himg : S'.image (glue S' f₁ f₂) = T' := by
      ext t
      simp only [mem_image, glue]
      constructor
      · rintro ⟨i, hi, rfl⟩; simp only [hi, ite_true]; exact h₁m i hi
      · intro ht
        obtain ⟨i, hi, rfl⟩ := h₁s t ht
        exact ⟨i, hi, by simp [hi]⟩
    simp only [Sigma.mk.injEq, himg, true_and]
    refine heq_of_eq (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
    · simp only [restrictTo, glue]
      split_ifs with h
      · rfl
      · exact (h₁o i h).symm
    · simp only [restrictTo, glue]
      by_cases h : i ∈ S'
      · simp only [h, ite_true, mem_sdiff, not_true_eq_false, and_false, ite_false]
        exact (h₂o i fun h' => (mem_sdiff.1 h').2 h).symm
      · by_cases h' : i ∈ S
        · simp [h, h']
        · simp only [h, ite_false, mem_sdiff, h', false_and]
          exact (h₂o i fun h'' => h' (mem_sdiff.1 h'').1).symm
  · intro f hf
    obtain ⟨-, -, -, ho⟩ := mem_bijOn.1 hf
    funext i
    simp only [glue, restrictTo]
    by_cases h : i ∈ S'
    · simp [h]
    · by_cases h' : i ∈ S
      · simp [h, h']
      · simp [h, h', ho i h']
  · rintro ⟨T', f₁, f₂⟩ -
    rw [← prod_sdiff hS', mul_comm]
    congr 1
    · exact prod_congr rfl fun i hi => by simp [glue, (mem_sdiff.1 hi).2]
    · exact prod_congr rfl fun i hi => by simp [glue, hi]

open Classical in
/-- **The permanent sum of a sum of two matrices**: choose the rows `S'` taken from `A`, the
columns `T'` they are matched to, and match the remaining rows and columns in `C`. -/
theorem permOn_add (A C : Matrix V V R) (S T : Finset V) :
    permOn (A + C) S T =
      ∑ S' ∈ S.powerset, ∑ T' ∈ T.powerset, permOn A S' T' * permOn C (S \ S') (T \ T') := by
  have hexp : permOn (A + C) S T = ∑ S' ∈ S.powerset,
      permOn (Matrix.of fun i j => if i ∈ S' then A i j else C i j) S T := by
    rw [permOn]
    simp only [Matrix.add_apply, prod_add, permOn, of_apply]
    rw [sum_comm]
    refine sum_congr rfl fun S' hS' => sum_congr rfl fun f _ => ?_
    rw [← prod_sdiff (mem_powerset.1 hS'), mul_comm]
    congr 1
    · exact prod_congr rfl fun i hi => by simp [(mem_sdiff.1 hi).2]
    · exact prod_congr rfl fun i hi => by simp [hi]
  rw [hexp]
  refine sum_congr rfl fun S' hS' => ?_
  rw [permOn_split _ (mem_powerset.1 hS')]
  refine sum_congr rfl fun T' _ => ?_
  congr 1
  · exact permOn_congr fun i hi j _ => by simp [hi]
  · exact permOn_congr fun i hi j _ => by simp [(mem_sdiff.1 hi).2]

/-- The permanent sum from one row to one column is the entry. -/
theorem permOn_singleton (M : Matrix V V R) (i j : V) : permOn M {i} {j} = M i j := by
  rw [permOn]
  have : bijOn ({i} : Finset V) {j} = {Function.update id i j} := by
    ext f
    simp only [mem_bijOn, mem_singleton, forall_eq, exists_eq_left]
    constructor
    · rintro ⟨h1, -, -, h4⟩
      funext k
      by_cases hk : k = i
      · subst hk; simp [h1]
      · simp [Function.update, hk, h4 k hk]
    · rintro rfl
      exact ⟨by simp, by simp, by simp, fun k hk => by simp [Function.update, hk]⟩
  rw [this, sum_singleton, prod_singleton, Function.update_self]

/-- The permanent sum from one row to a set of columns that is not a singleton vanishes. -/
theorem permOn_singleton_left_eq_zero (M : Matrix V V R) (i : V) {T : Finset V}
    (hT : ∀ j, T ≠ {j}) : permOn M {i} T = 0 := by
  rw [permOn]
  refine sum_eq_zero fun f hf => absurd ?_ (hT (f i))
  obtain ⟨hm, -, hs, -⟩ := mem_bijOn.1 hf
  ext t
  simp only [mem_singleton]
  refine ⟨fun ht => ?_, fun ht => ht ▸ hm i (mem_singleton_self i)⟩
  obtain ⟨k, hk, rfl⟩ := hs t ht
  rw [mem_singleton.1 hk]

/-- **Laplace expansion of the permanent sum** along a row `i ∈ S`. -/
theorem permOn_laplace (M : Matrix V V R) {S : Finset V} {i : V} (hi : i ∈ S) (T : Finset V) :
    permOn M S T = ∑ j ∈ T, M i j * permOn M (S.erase i) (T.erase j) := by
  rw [permOn_split M (singleton_subset_iff.2 hi) T]
  have hsub : T.image (fun j => ({j} : Finset V)) ⊆ T.powerset := fun T' hT' => by
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hT'
    exact mem_powerset.2 (singleton_subset_iff.2 hj)
  rw [← sum_subset hsub ?zero, sum_image fun _ _ _ _ h => singleton_injective h]
  · refine sum_congr rfl fun j _ => ?_
    rw [permOn_singleton, sdiff_singleton_eq_erase, sdiff_singleton_eq_erase]
  case zero =>
    intro T' hT' hn
    rw [permOn_singleton_left_eq_zero M i fun j hj => hn (mem_image.2 ⟨j, ?_, hj.symm⟩),
      zero_mul]
    exact singleton_subset_iff.1 (hj ▸ mem_powerset.1 hT')

/-- Laplace expansion along explicit lists of rows and columns: the rows are expanded in list
order, each matched to a remaining column. -/
def permOnList {V R : Type*} [DecidableEq V] [CommSemiring R] (M : V → V → R) :
    List V → List V → R
  | [], [] => 1
  | [], _ :: _ => 0
  | i :: is, cols => (cols.map fun j => M i j * permOnList M is (cols.erase j)).sum

/-- `permOn` is evaluated by `permOnList` on duplicate-free lists of its rows and columns. -/
theorem permOn_eq_permOnList (M : Matrix V V R) (rows cols : List V) (hr : rows.Nodup)
    (hc : cols.Nodup) : permOn M rows.toFinset cols.toFinset = permOnList M rows cols := by
  induction rows generalizing cols with
  | nil =>
    rw [List.toFinset_nil, permOn_empty_left]
    cases cols with
    | nil => simp [permOnList]
    | cons j js => simp [permOnList]
  | cons i is ih =>
    have hi : i ∈ (i :: is).toFinset := by simp
    simp only [permOnList]
    rw [permOn_laplace M hi, ← List.sum_toFinset _ hc]
    · refine sum_congr rfl fun j hj => ?_
      have hr' := (List.nodup_cons.1 hr)
      have he : ((i :: is).toFinset).erase i = is.toFinset := by
        rw [List.toFinset_cons, erase_insert (by simpa using hr'.1)]
      have hce : cols.toFinset.erase j = (cols.erase j).toFinset := by
        ext x
        simp [hc.mem_erase_iff]
      rw [he, hce, ih _ hr'.2 (hc.erase j)]

/-- For a matrix with entries `0` and `1`, `permOn` counts the bijections along `1`-entries. -/
theorem permOn_eq_card {M : Matrix V V ℤ} (hM : ∀ i j, M i j = 0 ∨ M i j = 1) (S T : Finset V) :
    permOn M S T = ((bijOn S T).filter fun f => ∀ i ∈ S, M i (f i) = 1).card := by
  classical
  rw [permOn, card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_congr rfl fun f _ => ?_
  split_ifs with h
  · simp [prod_eq_one h]
  · obtain ⟨i, hi, hne⟩ := not_forall₂.1 h
    exact prod_eq_zero hi ((hM i (f i)).resolve_right hne)

end Matrix
