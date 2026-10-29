/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PairwiseIndependentHash
public import Mathlib.Basic.Real.Basic
import Complexity.Foundations.Data.Finset.Expect
import Complexity.Probability.Uniform
import Mathlib.Algebra.BigOperators.Balance
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
# `k`-wise independent hash families

A family of functions `h i : X → Y`, indexed by a seed `i` drawn uniformly from a finite type `ι`,
is *`k`-wise independent* (`Cslib.Probability.IsKWiseIndependentHash`) if for every set `T` of at
most `k` points the restriction of `h i` to `T` is uniformly distributed on `T → Y`: the values at
any `k` distinct points are independent and uniform [Vadhan, Section 3.5.5][Vadhan2012]; Wegman and
Carter call such families *strongly universal_k* [WegmanCarter1981]. For `k ≥ 2` they are pairwise
independent in the sense of `Cslib.Probability.IsPairwiseIndependentHash`, and `2`-wise
independence is exactly pairwise independence with a seed
(`Cslib.Probability.isKWiseIndependentHash_two_iff`). As in the pairwise case,
probabilities over the seed are densities `Finset.dens` and averages are uniform expectations
`𝔼 i`.

Every function of at most `k` values has the same average as for a truly random function
(`Cslib.Probability.IsKWiseIndependentHash.expect_restrict`); in particular the average of a
product of functions of the values at `k` points is the product of their averages
(`Cslib.Probability.IsKWiseIndependentHash.expect_prod`). Expanding the `2 m`-th power of a sum of
centered bounded scores, a tuple of points contributes only when every point occurs at least twice,
so at most `m` distinct points occur. This gives the `2 m`-th moment bound
`𝔼 (∑ x ∈ S, Z x) ^ (2 m) ≤ m ^ (2 m) |S| ^ m`, and Markov's inequality gives the tail bound
`Pr[|∑ x ∈ S, Z x| ≥ a] ≤ (m² |S| / a²) ^ m`. This is the `k`-th moment method for limited
independence of Bellare and Rompel [BellareRompel1994], whose sharper counting of the contributing
tuples gives a better constant.

## Main definitions

* `Cslib.Probability.IsKWiseIndependentHash`: `k`-wise independent hash families.

## Main results

* `Cslib.Probability.IsKWiseIndependentHash.expect_restrict`,
  `Cslib.Probability.IsKWiseIndependentHash.expect_prod`: functions of at most `k` values average
  as for a truly random function.
* `Cslib.Probability.IsKWiseIndependentHash.isPairwiseIndependentHash`,
  `Cslib.Probability.isKWiseIndependentHash_two_iff`: for `k ≥ 2` the family is pairwise
  independent, and `2`-wise independence is pairwise independence with a seed.
* `Cslib.Probability.IsKWiseIndependentHash.comp_seedEquiv`,
  `Cslib.Probability.IsKWiseIndependentHash.comp`,
  `Cslib.Probability.IsKWiseIndependentHash.map_equiv`,
  `Cslib.Probability.IsKWiseIndependentHash.comp_surjective_addMonoidHom`: preservation of
  `k`-wise independence under seed equivalences, injective domain maps, output equivalences, and
  surjective additive group homomorphisms.
* `Cslib.Probability.isKWiseIndependentHash_of_surjective`: an additive family whose restrictions
  to sets of at most `k` points are onto is `k`-wise independent.
* `Cslib.Probability.IsKWiseIndependentHash.expect_sum_pow_le`: the `2 m`-th moment bound.
* `Cslib.Probability.IsKWiseIndependentHash.dens_filter_le_abs_sum`,
  `Cslib.Probability.IsKWiseIndependentHash.dens_filter_le_abs_sum_sub_expect`: the tail bounds for
  centered scores in `[-1, 1]` and for scores in `[0, 1]`.

## References

* [S. P. Vadhan, *Pseudorandomness*, Section 3.5][Vadhan2012]
* [M. Bellare, J. Rompel, *Randomness-efficient oblivious sampling*][BellareRompel1994]
* [M. N. Wegman, J. L. Carter, *New hash functions and their use in authentication and set
  equality*][WegmanCarter1981]
-/

@[expose] public section

namespace Cslib.Probability

open Finset Fintype
open scoped BigOperators

variable {ι X Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y]

/-- A family of functions `h i : X → Y`, indexed by a seed `i : ι` drawn uniformly at random, is
*`k`-wise independent* if for every set `T` of at most `k` points the restriction of `h i` to `T`
is uniformly distributed on `T → Y`: a `1 / |Y| ^ #T` fraction of the seeds restricts to each
`y : T → Y`. Taking `T = ∅` forces a seed to exist.

The usual definition asks this only for sets of exactly `k` points. When `X` has at least `k`
elements the two agree, since a set of fewer points extends to one of `k` points and the
restriction to the smaller set is a marginal; when `X` has fewer than `k` elements the usual
definition is vacuous, while this one still asks for uniformity on all of `X`. -/
structure IsKWiseIndependentHash (k : ℕ) (h : ι → X → Y) : Prop where
  /-- The values at any set of at most `k` points are independent and uniform. -/
  dens_filter_restrict_eq {T : Finset X} (hT : #T ≤ k) (y : T → Y) :
    dens {i | T.restrict (h i) = y} = ((Fintype.card Y : ℚ≥0) ^ #T)⁻¹

namespace IsKWiseIndependentHash

variable {k : ℕ} {h : ι → X → Y}

/-- A `k`-wise independent family has a seed. -/
theorem nonempty (hh : IsKWiseIndependentHash k h) : Nonempty ι := by
  let y : (∅ : Finset X) → Y := fun x => (notMem_empty _ x.2).elim
  obtain ⟨i, -⟩ : ({i | (∅ : Finset X).restrict (h i) = y} : Finset ι).Nonempty := by
    rw [← dens_ne_zero, hh.dens_filter_restrict_eq (by simp)]
    simp
  exact ⟨i⟩

/-- A `k`-wise independent family is `k'`-wise independent for every `k' ≤ k`. -/
theorem mono (hh : IsKWiseIndependentHash k h) {k' : ℕ} (hk : k' ≤ k) :
    IsKWiseIndependentHash k' h where
  dens_filter_restrict_eq hT y := hh.dens_filter_restrict_eq (hT.trans hk) y

/-- Relabelling the seed space by an equivalence `e : ι' ≃ ι` preserves `k`-wise independence. -/
theorem comp_seedEquiv {ι' : Type*} [Fintype ι'] (hh : IsKWiseIndependentHash k h)
    (e : ι' ≃ ι) : IsKWiseIndependentHash k (fun i' x => h (e i') x) where
  dens_filter_restrict_eq {T} hT y := by
    rw [dens_eq_card_div_card, ← hh.dens_filter_restrict_eq hT y, dens_eq_card_div_card,
      Fintype.card_congr e]
    congr 2
    exact card_equiv e fun i' => by simp

/-- Precomposing the input domain with an injective map `e : X' → X` preserves `k`-wise
independence. -/
theorem comp {X' : Type*} (hh : IsKWiseIndependentHash k h) {e : X' → X}
    (he : Function.Injective e) : IsKWiseIndependentHash k (fun i x' => h i (e x')) where
  dens_filter_restrict_eq {T} hT y := by
    let emb : X' ↪ X := ⟨e, he⟩
    have hmem (z : T.map emb) : ∃ x' ∈ T, emb x' = z.1 := mem_map.1 z.2
    let eT : T ≃ T.map emb :=
      { toFun := fun x => ⟨e x.1, mem_map_of_mem emb x.2⟩
        invFun := fun z => ⟨(hmem z).choose, (hmem z).choose_spec.1⟩
        left_inv := fun x =>
          Subtype.ext (he (hmem ⟨e x.1, mem_map_of_mem emb x.2⟩).choose_spec.2)
        right_inv := fun z => Subtype.ext (hmem z).choose_spec.2 }
    have hcard : #(T.map emb) = #T := card_map emb
    have hmap : #(T.map emb) ≤ k := hcard.le.trans hT
    have hdens := hh.dens_filter_restrict_eq hmap (fun z => y (eT.symm z))
    rw [hcard] at hdens
    rw [← hdens]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hi
      funext z
      have hz : (T.map emb).restrict (h i) z = T.restrict (fun x' => h i (e x')) (eT.symm z) := by
        simp only [restrict]
        exact congrArg (h i) (congrArg Subtype.val (eT.apply_symm_apply z)).symm
      rw [hz, hi]
    · intro hi
      funext x
      have hx := congrFun hi (eT x)
      rw [Equiv.symm_apply_apply] at hx
      exact hx

/-- Postcomposing the output values with an equivalence `e : Y ≃ Z` preserves `k`-wise
independence. -/
theorem map_equiv {Z : Type*} [Fintype Z] [DecidableEq Z] (hh : IsKWiseIndependentHash k h)
    (e : Y ≃ Z) : IsKWiseIndependentHash k (fun i x => e (h i x)) where
  dens_filter_restrict_eq {T} hT z := by
    rw [← Fintype.card_congr e, ← hh.dens_filter_restrict_eq hT (fun x => e.symm (z x))]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, funext_iff, restrict, Equiv.eq_symm_apply]

section Expect

variable {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜]

/-- **Restrictions are uniform**: a function of the values of a `k`-wise independent family at a
set `T` of at most `k` points has the same average as on a uniformly random `y : T → Y`. -/
theorem expect_restrict [DecidableEq X] (hh : IsKWiseIndependentHash k h) {T : Finset X}
    (hT : #T ≤ k) (F : (T → Y) → 𝕜) :
    𝔼 i, F (T.restrict (h i)) = 𝔼 y, F y := by
  have hfib (i : ι) : F (T.restrict (h i)) =
      ∑ y, (if T.restrict (h i) = y then (1 : 𝕜) else 0) * F y := by
    simp only [boole_mul, Fintype.sum_ite_eq]
  simp only [hfib]
  rw [expect_sum_comm]
  simp only [← expect_mul, Fintype.expect_boole, hh.dens_filter_restrict_eq hT, NNRat.cast_inv,
    NNRat.cast_pow, NNRat.cast_natCast]
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Fintype.card_coe, Nat.cast_pow,
    sum_div]
  exact sum_congr rfl fun y _ => by rw [inv_mul_eq_div]

/-- **Products of values average to products of averages**: for a `k`-wise independent family and
a set `T` of at most `k` points, the average of `∏ x ∈ T, f x (h i x)` is
`∏ x ∈ T, 𝔼 y, f x y`. -/
theorem expect_prod (hh : IsKWiseIndependentHash k h) {T : Finset X} (hT : #T ≤ k)
    (f : X → Y → 𝕜) :
    𝔼 i, ∏ x ∈ T, f x (h i x) = ∏ x ∈ T, 𝔼 y, f x y := by
  classical
  have hl (i : ι) : ∏ x ∈ T, f x (h i x) = ∏ x : T, f x (T.restrict (h i) x) :=
    (prod_coe_sort T fun x => f x (h i x)).symm
  simp only [hl]
  rw [hh.expect_restrict hT (fun y => ∏ x : T, f x (y x)), ← prod_coe_sort T,
    Fintype.expect_eq_sum_div_card]
  simp only [Fintype.expect_eq_sum_div_card, div_eq_mul_inv, prod_mul_distrib, prod_const,
    card_univ, ← Fintype.prod_sum, Fintype.card_fun, Nat.cast_pow, inv_pow]

end Expect

/-- Postcomposing the output values with a surjective additive group homomorphism `π : Y →+ Z`
between finite additive groups preserves `k`-wise independence. -/
theorem comp_surjective_addMonoidHom {Z : Type*} [AddGroup Y] [AddGroup Z] [Fintype Z]
    [DecidableEq Z] (hh : IsKWiseIndependentHash k h) (π : Y →+ Z)
    (hπ : Function.Surjective π) : IsKWiseIndependentHash k (fun i x => π (h i x)) where
  dens_filter_restrict_eq {T} hT z := by
    classical
    let πT (y : T → Y) : T → Z := fun x => π (y x)
    have hexp := hh.expect_restrict hT (fun y : T → Y => if πT y = z then (1 : ℚ≥0) else 0)
    simp only [Fintype.expect_boole, NNRat.cast_id] at hexp
    have hfun (i : ι) : (πT (T.restrict (h i)) = z) ↔ (T.restrict (fun x => π (h i x)) = z) :=
      Iff.rfl
    simp only [hfun] at hexp
    rw [hexp]
    have hshift := dens_filter_eq_of_shift (f := πT) (fun c => by
      refine ⟨Equiv.addRight (fun x => (hπ (c x)).choose), fun y => funext fun x => ?_⟩
      simp [πT, Pi.add_apply, map_add, (hπ (c x)).choose_spec]) z
    rw [Fintype.card_fun, Fintype.card_coe, Nat.cast_pow] at hshift
    exact hshift

/-- A `k`-wise independent family with `k ≥ 2` is pairwise independent. -/
theorem isPairwiseIndependentHash (hh : IsKWiseIndependentHash k h)
    (hk : 2 ≤ k) : IsPairwiseIndependentHash h where
  dens_filter_apply_eq x y := by
    classical
    have h1 := hh.dens_filter_restrict_eq (T := {x}) (by simp only [card_singleton]; omega)
      fun _ => y
    rw [card_singleton, pow_one] at h1
    rw [← h1]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, funext_iff, Subtype.forall, mem_singleton,
      restrict, forall_eq]
  dens_filter_apply_eq_and_apply_eq {x₁ x₂} hx y₁ y₂ := by
    classical
    have h2 := hh.dens_filter_restrict_eq (T := {x₁, x₂}) (by rw [card_pair hx]; exact hk)
      fun z => if z.1 = x₁ then y₁ else y₂
    rw [card_pair hx] at h2
    rw [← h2]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h₁, h₂⟩
      funext ⟨z, hz⟩
      rcases mem_insert.1 hz with rfl | hz
      · simp [h₁]
      · obtain rfl := mem_singleton.1 hz
        simp [h₂, hx.symm]
    · intro hy
      exact ⟨by simpa using congrFun hy ⟨x₁, by simp⟩,
        by simpa [hx.symm] using congrFun hy ⟨x₂, by simp⟩⟩

/-- **Pairwise independence is `2`-wise independence**: a family is `2`-wise independent exactly
when it is pairwise independent and has a seed. So the pairwise independent families, such as
`Cslib.Probability.isPairwiseIndependentHash_affineHash`, carry the `k`-wise API for `k = 2`. -/
theorem _root_.Cslib.Probability.isKWiseIndependentHash_two_iff :
    IsKWiseIndependentHash 2 h ↔ IsPairwiseIndependentHash h ∧ Nonempty ι := by
  refine ⟨fun hh => ⟨hh.isPairwiseIndependentHash le_rfl, hh.nonempty⟩, fun ⟨hh, hι⟩ => ⟨?_⟩⟩
  intro T hT y
  classical
  interval_cases hc : #T
  · obtain rfl := card_eq_zero.1 hc
    have : ({i | (∅ : Finset X).restrict (h i) = y} : Finset ι) = univ :=
      filter_true_of_mem fun i _ => funext fun x => (notMem_empty _ x.2).elim
    rw [this, dens_univ]
    simp
  · obtain ⟨x, rfl⟩ := card_eq_one.1 hc
    rw [pow_one, ← hh.dens_filter_apply_eq x (y ⟨x, mem_singleton_self x⟩)]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, funext_iff, Subtype.forall, mem_singleton,
      restrict]
    exact ⟨fun hi => hi x rfl, by rintro hi a rfl; exact hi⟩
  · obtain ⟨x₁, x₂, hx, rfl⟩ := card_eq_two.1 hc
    rw [← hh.dens_filter_apply_eq_and_apply_eq hx (y ⟨x₁, by simp⟩) (y ⟨x₂, by simp⟩)]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, funext_iff, Subtype.forall, mem_insert,
      mem_singleton, restrict]
    constructor
    · intro hi
      exact ⟨hi x₁ (Or.inl rfl), hi x₂ (Or.inr rfl)⟩
    · rintro ⟨h₁, h₂⟩ z (rfl | rfl)
      · exact h₁
      · exact h₂

/-- Tuples of `n` elements of `S` with at most `m ≤ n` distinct entries factor through `Fin m`, so
there are at most `m ^ n * #S ^ m` of them. -/
private theorem card_filter_card_image_le [DecidableEq X] (S : Finset X) {m n : ℕ}
    (hmn : m ≤ n) :
    #{t ∈ piFinset fun _ : Fin n => S | #(univ.image t) ≤ m} ≤ m ^ n * #S ^ m := by
  classical
  calc #{t ∈ piFinset fun _ : Fin n => S | #(univ.image t) ≤ m}
      ≤ #(((piFinset fun _ : Fin n => (univ : Finset (Fin m))) ×ˢ
          (piFinset fun _ : Fin m => S)).image fun q => q.2 ∘ q.1) := by
        refine card_le_card fun t ht => ?_
        rw [mem_filter, mem_piFinset] at ht
        obtain ⟨htS, hcard⟩ := ht
        set I := univ.image t
        let e := I.equivFin
        have hmem (j : Fin n) : t j ∈ I := mem_image_of_mem t (mem_univ j)
        let v (r : Fin m) : X := if hr : r.1 < #I then (e.symm ⟨r, hr⟩).1 else
          t ⟨0, lt_of_lt_of_le (Nat.zero_lt_of_lt r.2) hmn⟩
        refine mem_image.2 ⟨(fun j => Fin.castLE hcard (e ⟨t j, hmem j⟩), v), ?_, ?_⟩
        · refine mem_product.2 ⟨by simp, mem_piFinset.2 fun r => ?_⟩
          by_cases hr : r.1 < #I
          · obtain ⟨j, -, hj⟩ := mem_image.1 (e.symm ⟨r, hr⟩).2
            simp only [v, hr, ↓reduceDIte, ← hj]
            exact htS j
          · simp only [v, hr, ↓reduceDIte]
            exact htS _
        · funext j
          have hlt : (Fin.castLE hcard (e ⟨t j, hmem j⟩)).1 < #I := (e ⟨t j, hmem j⟩).2
          simp only [Function.comp_apply, v, hlt, ↓reduceDIte]
          have : (⟨(Fin.castLE hcard (e ⟨t j, hmem j⟩)).1, hlt⟩ : Fin #I) = e ⟨t j, hmem j⟩ :=
            Fin.ext rfl
          rw [this, Equiv.symm_apply_apply]
    _ ≤ m ^ n * #S ^ m := card_image_le.trans (by simp [card_piFinset])

/-- **The `2 m`-th moment bound for limited independence**: for a `2 m`-wise independent family and
scores `Z x : Y → ℝ` with average `0` and values in `[-1, 1]` at the points `x` of a finite set
`S`, the `2 m`-th moment of `∑ x ∈ S, Z x (h i x)` is at most `m ^ (2 m) * #S ^ m`. Expanding the
power, only tuples of points in which every point occurs at least twice contribute, and these
tuples have at most `m` distinct entries. -/
theorem expect_sum_pow_le {m : ℕ} (hh : IsKWiseIndependentHash (2 * m) h)
    (S : Finset X) (Z : X → Y → ℝ) (hZ : ∀ x ∈ S, 𝔼 y, Z x y = 0)
    (hZ₁ : ∀ x ∈ S, ∀ y, |Z x y| ≤ 1) :
    𝔼 i, (∑ x ∈ S, Z x (h i x)) ^ (2 * m) ≤ m ^ (2 * m) * #S ^ m := by
  classical
  have := hh.nonempty
  simp only [sum_pow']
  rw [expect_sum_comm]
  have hterm : ∀ t ∈ piFinset fun _ : Fin (2 * m) => S,
      𝔼 i, ∏ j, Z (t j) (h i (t j)) ≤ if #(univ.image t) ≤ m then 1 else 0 := by
    intro t ht
    have htS : ∀ x ∈ univ.image t, x ∈ S := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := mem_image.1 hx
      exact mem_piFinset.1 ht j
    have hprod (i : ι) : ∏ j, Z (t j) (h i (t j)) =
        ∏ x ∈ univ.image t, Z x (h i x) ^ #{j | t j = x} :=
      prod_comp (fun x => Z x (h i x)) t
    simp only [hprod]
    rw [hh.expect_prod (card_image_le.trans (by simp)) fun x y => Z x y ^ #{j | t j = x}]
    split_ifs with hI
    · refine (le_abs_self _).trans ?_
      rw [abs_prod]
      refine prod_le_one₀ (fun _ _ => abs_nonneg _) fun x hx => ?_
      have : Nonempty Y := ⟨h (Classical.arbitrary ι) x⟩
      refine (abs_expect_le _ _).trans (expect_le univ_nonempty fun y _ => ?_)
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hZ₁ x (htS x hx) y)
    · obtain ⟨x, hx, hc⟩ : ∃ x ∈ univ.image t, #{j | t j = x} = 1 := by
        by_contra hne
        push Not at hne
        have hsum := card_eq_sum_card_image t (univ : Finset (Fin (2 * m)))
        have h2 : ∑ x ∈ univ.image t, 2 ≤ ∑ x ∈ univ.image t, #{j | t j = x} := by
          refine sum_le_sum fun x hx => ?_
          obtain ⟨j, -, rfl⟩ := mem_image.1 hx
          have hpos : 0 < #{j' | t j' = t j} := card_pos.2 ⟨j, by simp⟩
          have := hne (t j) hx
          omega
        rw [← hsum, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h2
        omega
      rw [prod_eq_zero hx (by simp only [hc, pow_one]; exact hZ x (htS x hx))]
  calc ∑ t ∈ piFinset (fun _ : Fin (2 * m) => S), 𝔼 i, ∏ j, Z (t j) (h i (t j))
      ≤ ∑ t ∈ piFinset (fun _ : Fin (2 * m) => S), if #(univ.image t) ≤ m then (1 : ℝ) else 0 :=
        sum_le_sum hterm
    _ = #{t ∈ piFinset fun _ : Fin (2 * m) => S | #(univ.image t) ≤ m} := by
        rw [sum_boole]
    _ ≤ m ^ (2 * m) * #S ^ m := by
        exact_mod_cast card_filter_card_image_le S (by omega)

/-- **The tail bound for limited independence**: for a `2 m`-wise independent family and scores
`Z x : Y → ℝ` with average `0` and values in `[-1, 1]` at the points of a finite set `S`, the sum
`∑ x ∈ S, Z x (h i x)` has absolute value at least `a > 0` with probability at most
`(m² #S / a²) ^ m`. -/
theorem dens_filter_le_abs_sum {m : ℕ} (hh : IsKWiseIndependentHash (2 * m) h)
    (S : Finset X) (Z : X → Y → ℝ) (hZ : ∀ x ∈ S, 𝔼 y, Z x y = 0)
    (hZ₁ : ∀ x ∈ S, ∀ y, |Z x y| ≤ 1) {a : ℝ} (ha : 0 < a) :
    (dens {i | a ≤ |∑ x ∈ S, Z x (h i x)|} : ℝ) ≤ (m ^ 2 * #S / a ^ 2) ^ m := by
  have hmarkov := Fintype.mul_dens_filter_le_expect
    (f := fun i => (∑ x ∈ S, Z x (h i x)) ^ (2 * m))
    (fun _ => (even_two_mul m).pow_nonneg _) (a ^ (2 * m))
  have hsub : ({i | a ≤ |∑ x ∈ S, Z x (h i x)|} : Finset ι) ⊆
      ({i | a ^ (2 * m) ≤ (∑ x ∈ S, Z x (h i x)) ^ (2 * m)} : Finset ι) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    rw [← (even_two_mul m).pow_abs (∑ x ∈ S, Z x (h i x))]
    exact pow_le_pow_left₀ ha.le hi _
  have hdens : (dens {i | a ≤ |∑ x ∈ S, Z x (h i x)|} : ℝ) ≤
      dens {i | a ^ (2 * m) ≤ (∑ x ∈ S, Z x (h i x)) ^ (2 * m)} := by
    exact_mod_cast dens_le_dens hsub
  have hpow : 0 < a ^ (2 * m) := pow_pos ha _
  calc (dens {i | a ≤ |∑ x ∈ S, Z x (h i x)|} : ℝ)
      ≤ m ^ (2 * m) * #S ^ m / a ^ (2 * m) := by
        rw [le_div_iff₀ hpow, mul_comm]
        exact (mul_le_mul_of_nonneg_left hdens hpow.le).trans
          (hmarkov.trans (hh.expect_sum_pow_le S Z hZ hZ₁))
    _ = (m ^ 2 * #S / a ^ 2) ^ m := by
        rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 m]

/-- **The tail bound for limited independence, for scores in `[0, 1]`**: for a `2 m`-wise
independent family and scores `g x : Y → [0, 1]`, the sum `∑ x ∈ S, g x (h i x)` deviates from its
mean `∑ x ∈ S, 𝔼 y, g x y` by at least `a > 0` with probability at most `(m² #S / a²) ^ m`. -/
theorem dens_filter_le_abs_sum_sub_expect {m : ℕ}
    (hh : IsKWiseIndependentHash (2 * m) h) (S : Finset X) (g : X → Y → ℝ)
    (hg : ∀ x ∈ S, ∀ y, g x y ∈ Set.Icc 0 1) {a : ℝ} (ha : 0 < a) :
    (dens {i | a ≤ |∑ x ∈ S, (g x (h i x) - 𝔼 y, g x y)|} : ℝ) ≤ (m ^ 2 * #S / a ^ 2) ^ m := by
  refine hh.dens_filter_le_abs_sum S (fun x y => g x y - 𝔼 y, g x y) (fun x _ => ?_)
    (fun x hx y => ?_) ha
  · exact Fintype.expect_balance (g x)
  · have : Nonempty Y := ⟨y⟩
    have h0 : 0 ≤ 𝔼 y, g x y := expect_nonneg fun y _ => (hg x hx y).1
    have h1 : 𝔼 y, g x y ≤ 1 := expect_le univ_nonempty fun y _ => (hg x hx y).2
    rw [abs_le]
    constructor <;> linarith [(hg x hx y).1, (hg x hx y).2]

end IsKWiseIndependentHash

/-- **The surjectivity criterion**: let the seeds `ι` form a finite additive group and let the
functions `g i : X → Y` into a finite additive group depend additively on `i`. If for every set
`T` of at most `k` points the restrictions of the `g i` to `T` take every value in `T → Y`, then
the family is `k`-wise independent. -/
theorem isKWiseIndependentHash_of_surjective {k : ℕ} [AddGroup ι] [AddGroup Y]
    (g : ι →+ X → Y)
    (hg : ∀ T : Finset X, #T ≤ k → Function.Surjective fun i => T.restrict (g i)) :
    IsKWiseIndependentHash k fun i => g i where
  dens_filter_restrict_eq {T} hT y := by
    classical
    have h := dens_filter_eq_of_shift (f := fun i => T.restrict (g i)) (fun c => by
      obtain ⟨i₀, hi₀⟩ := hg T hT c
      refine ⟨Equiv.addRight i₀, fun i => ?_⟩
      simp only [Equiv.coe_addRight, map_add, ← hi₀]
      rfl) y
    rw [Fintype.card_fun, Fintype.card_coe, Nat.cast_pow] at h
    convert h

end Cslib.Probability
