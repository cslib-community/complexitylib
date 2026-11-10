/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.PartialAssignment
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Powerset
import CslibFrontier.Foundations.Data.BitString.Agree
import CslibFrontier.Foundations.Data.Nat.Choose
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Counting partial assignments and random restrictions

Over a finite index type `ι`, the partial assignments extending `ρ₀` with exactly `ℓ` free
coordinates number `(m choose ℓ) 2 ^ (m - ℓ)` for the `m` free coordinates of `ρ₀`
(`PartialAssignment.card_extensions`), so `(|ι| choose ℓ) 2 ^ (|ι| - ℓ)` partial assignments leave
exactly `ℓ` coordinates free (`PartialAssignment.card_withFree`). Drawing such a partial assignment
uniformly is drawing a set of `ℓ` free coordinates and a word for the others
(`PartialAssignment.sum_card_filter_outside`), and double counting relates partial assignments
with different numbers of free coordinates (`PartialAssignment.sum_card_filter_extensions`,
`PartialAssignment.sum_extensions_update`); these are the random restrictions of Subbotovskaya's
method and Håstad's switching lemma.

## Main definitions

* `Cslib.BitString.PartialAssignment.extensions`: the extensions of `ρ₀` leaving `ℓ` coordinates
  free.
* `Cslib.BitString.PartialAssignment.withFree`: the partial assignments leaving `ℓ` coordinates
  free.

## Main results

* `Cslib.BitString.PartialAssignment.card_extensions`,
  `Cslib.BitString.PartialAssignment.card_withFree`,
  `Cslib.BitString.PartialAssignment.card_filter_extensions_free_subset`,
  `Cslib.BitString.PartialAssignment.card_extensions_le_two_mul_card_filter_forall_nonempty`:
  counting partial assignments by their free coordinates and union-bounding block survival.
* `Cslib.BitString.PartialAssignment.sum_card_filter_outside`,
  `Cslib.BitString.PartialAssignment.sum_card_filter_extensions`,
  `Cslib.BitString.PartialAssignment.sum_extensions_update`,
  `Cslib.BitString.PartialAssignment.mul_card_extensions_sub_one`: drawing random restrictions and
  double counting extensions.
* `Cslib.BitString.PartialAssignment.mul_card_filter_withFree_le`: two stages of restrictions,
  counted.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
-/

@[expose] public section

namespace Cslib.BitString.PartialAssignment

open Function Finset

variable {ι : Type*} {ρ : PartialAssignment ι} [Fintype ι] [DecidableEq ι]

/-! ### Counting extensions -/

/-- The extensions of `ρ₀` leaving exactly `ℓ` coordinates free. -/
def extensions (ρ₀ : PartialAssignment ι) (ℓ : ℕ) : Finset (PartialAssignment ι) :=
  {ρ | ρ.Extends ρ₀ ∧ #ρ.free = ℓ}

/-- `ρ` is in `ρ₀.extensions ℓ` exactly when it extends `ρ₀` and leaves exactly `ℓ` coordinates
free. -/
@[simp] theorem mem_extensions {ρ₀ : PartialAssignment ι} {ℓ : ℕ} :
    ρ ∈ ρ₀.extensions ℓ ↔ ρ.Extends ρ₀ ∧ #ρ.free = ℓ := by
  simp [extensions]

/-- For a fixed subset `S ∈ powersetCard ℓ ρ₀.free`, there are `2 ^ (#ρ₀.free - ℓ)` extensions in
`ρ₀.extensions ℓ` whose free set is `S`. -/
theorem card_filter_extensions_free_eq (ρ₀ : PartialAssignment ι) (ℓ : ℕ)
    {S : Finset ι} (hS : S ∈ powersetCard ℓ ρ₀.free) :
    #{ρ ∈ ρ₀.extensions ℓ | ρ.free = S} = 2 ^ (#ρ₀.free - ℓ) := by
  obtain ⟨hSsub, hScard⟩ := mem_powersetCard.1 hS
  have : {ρ ∈ ρ₀.extensions ℓ | ρ.free = S} = Fintype.piFinset fun i =>
      if i ∈ S then {none} else if i ∈ ρ₀.free then {some false, some true} else {ρ₀ i} := by
    ext ρ
    simp only [mem_filter, mem_extensions, Fintype.mem_piFinset]
    constructor
    · rintro ⟨⟨hext, -⟩, rfl⟩ i
      by_cases hi : i ∈ ρ.free
      · simp [hi, mem_free.1 hi]
      · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 fun h => hi (mem_free.2 h)
        by_cases hi₀ : i ∈ ρ₀.free
        · cases b <;> simp [hi, hi₀, hb]
        · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 fun h => hi₀ (mem_free.2 h)
          simp only [hi, ↓reduceIte, hi₀, mem_singleton]
          rw [hext i c hc, hc]
    · intro h
      have hfree : ρ.free = S := by
        ext i
        have := h i
        by_cases hi : i ∈ S
        · simp_all
        · by_cases hi₀ : i ∈ ρ₀.free
          · cases hρ : ρ i <;> simp_all
          · simp only [hi, ↓reduceIte, hi₀, mem_singleton] at this
            simp only [mem_free, this, hi, iff_false]
            exact fun h' => hi₀ (mem_free.2 h')
      refine ⟨⟨fun i b hb => ?_, hfree ▸ hScard⟩, hfree⟩
      have hi₀ : i ∉ ρ₀.free := by simp [mem_free, hb]
      have hi : i ∉ S := fun hi => hi₀ (hSsub hi)
      simpa [hi, hi₀, hb] using h i
  rw [this, Fintype.card_piFinset]
  simp only [apply_ite card, card_singleton,
    card_pair (show some false ≠ some true by simp)]
  rw [prod_ite, prod_const_one, one_mul, prod_ite, prod_const,
    prod_const_one, mul_one, filter_filter,
    show ({a | a ∉ S ∧ a ∈ ρ₀.free} : Finset ι) = ρ₀.free \ S by
      ext a
      simp [and_comm], card_sdiff_of_subset hSsub, hScard]

/-- There are `(m choose ℓ) 2 ^ (m - ℓ)` extensions of `ρ₀` leaving `ℓ` of the `m` free
coordinates of `ρ₀` free. -/
theorem card_extensions (ρ₀ : PartialAssignment ι) (ℓ : ℕ) :
    #(ρ₀.extensions ℓ) = (#ρ₀.free).choose ℓ * 2 ^ (#ρ₀.free - ℓ) := by
  rw [card_eq_sum_card_fiberwise (f := free) (t := powersetCard ℓ ρ₀.free)
    fun ρ hρ => mem_powersetCard.2
      ⟨(mem_extensions.1 hρ).1.free_subset, (mem_extensions.1 hρ).2⟩]
  rw [sum_congr rfl fun S hS => card_filter_extensions_free_eq ρ₀ ℓ hS,
    sum_const, card_powersetCard, smul_eq_mul]

/-- The number of extensions in `ρ₀.extensions ℓ` whose free coordinates lie inside `U ⊆ ρ₀.free` is
`C(|U|, ℓ) * 2 ^ (#ρ₀.free - ℓ)`. -/
theorem card_filter_extensions_free_subset (ρ₀ : PartialAssignment ι) (ℓ : ℕ)
    {U : Finset ι} (hU : U ⊆ ρ₀.free) :
    #{ρ ∈ ρ₀.extensions ℓ | ρ.free ⊆ U} = (#U).choose ℓ * 2 ^ (#ρ₀.free - ℓ) := by
  rw [card_eq_sum_card_fiberwise (f := free) (t := powersetCard ℓ U)
    fun ρ hρ => by
      obtain ⟨hρ_ext, hρ_sub⟩ := mem_filter.1 hρ
      exact mem_powersetCard.2 ⟨hρ_sub, (mem_extensions.1 hρ_ext).2⟩]
  rw [sum_congr rfl (g := fun _ => 2 ^ (#ρ₀.free - ℓ)), sum_const, card_powersetCard, smul_eq_mul]
  intro S hS
  obtain ⟨hSsub, hScard⟩ := mem_powersetCard.1 hS
  have hfilter :
      {ρ ∈ {ρ ∈ ρ₀.extensions ℓ | ρ.free ⊆ U} | ρ.free = S} =
        {ρ ∈ ρ₀.extensions ℓ | ρ.free = S} := by
    ext ρ
    simp only [mem_filter]
    exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, h2 ▸ hSsub⟩, h2⟩⟩
  rw [hfilter]
  exact card_filter_extensions_free_eq ρ₀ ℓ (mem_powersetCard.2 ⟨hSsub.trans hU, hScard⟩)

/-- The number of extensions in `ρ₀.extensions ℓ` that fix every coordinate of `B ⊆ ρ₀.free` is
`C(#ρ₀.free - |B|, ℓ) * 2 ^ (#ρ₀.free - ℓ)`. -/
theorem card_filter_extensions_not_nonempty_inter (ρ₀ : PartialAssignment ι) (ℓ : ℕ)
    {B : Finset ι} (hB : B ⊆ ρ₀.free) :
    #{ρ ∈ ρ₀.extensions ℓ | ¬(ρ.free ∩ B).Nonempty} =
      (#ρ₀.free - #B).choose ℓ * 2 ^ (#ρ₀.free - ℓ) := by
  have heq :
      {ρ ∈ ρ₀.extensions ℓ | ¬(ρ.free ∩ B).Nonempty} =
        {ρ ∈ ρ₀.extensions ℓ | ρ.free ⊆ ρ₀.free \ B} := by
    ext ρ
    simp only [mem_filter, not_nonempty_iff_eq_empty]
    refine and_congr_right fun hρ => ?_
    have hsub := (mem_extensions.1 hρ).1.free_subset
    constructor
    · intro hemp i hi
      refine mem_sdiff.2 ⟨hsub hi, fun hiB => ?_⟩
      have : i ∈ (∅ : Finset ι) := hemp ▸ mem_inter.2 ⟨hi, hiB⟩
      exact notMem_empty i this
    · intro hsub'
      ext i
      simp only [mem_inter, notMem_empty, iff_false, not_and]
      intro hi
      exact (mem_sdiff.1 (hsub' hi)).2
  rw [heq, card_filter_extensions_free_subset ρ₀ ℓ sdiff_subset, card_sdiff_of_subset hB]

variable (ι) in
/-- The partial assignments leaving exactly `ℓ` coordinates free: the extensions of the one fixing
nothing. -/
abbrev withFree (ℓ : ℕ) : Finset (PartialAssignment ι) :=
  extensions empty ℓ

/-- `ρ` is in `withFree ι ℓ` exactly when it leaves exactly `ℓ` coordinates free. -/
theorem mem_withFree {ℓ : ℕ} : ρ ∈ withFree ι ℓ ↔ #ρ.free = ℓ := by
  simp

/-- There are `(|ι| choose ℓ) 2 ^ (|ι| - ℓ)` partial assignments leaving exactly `ℓ` coordinates
free. -/
theorem card_withFree (ℓ : ℕ) :
    #(withFree ι ℓ) = (Fintype.card ι).choose ℓ * 2 ^ (Fintype.card ι - ℓ) := by
  rw [card_extensions, free_empty, card_univ]

/-- A partial assignment with `ℓ'` free coordinates extends `C(|ι| - ℓ', ℓ - ℓ')` of the ones
with `ℓ ≥ ℓ'` free coordinates: those that free `ℓ - ℓ'` of its fixed coordinates. -/
theorem card_filter_extends_withFree {ρ' : PartialAssignment ι} {ℓ : ℕ}
    (hℓ : #ρ'.free ≤ ℓ) :
    #((withFree ι ℓ).filter fun ρ => ρ'.Extends ρ) =
      (Fintype.card ι - #ρ'.free).choose (ℓ - #ρ'.free) := by
  have h := card_filter_powersetCard_subset ρ'.free univ ℓ (subset_univ _) hℓ
  rw [card_univ] at h
  rw [← h]
  -- Freeing the coordinates of a superset `F` of `ρ'.free` leaves exactly `F` free.
  have hfree {F : Finset ι} (hsub : ρ'.free ⊆ F) :
      free (fun i => if i ∈ F then none else ρ' i) = F := by
    ext i
    by_cases hi : i ∈ F
    · simp [hi]
    · simp only [mem_free, hi, ↓reduceIte, iff_false]
      exact fun h => hi (hsub (mem_free.2 h))
  refine card_nbij' free (fun F i => if i ∈ F then none else ρ' i) (fun ρ hρ => ?_)
    (fun F hF => ?_) (fun ρ hρ => ?_) (fun F hF => ?_)
  · obtain ⟨hρ, hext⟩ := mem_filter.1 hρ
    exact mem_filter.2 ⟨mem_powersetCard.2 ⟨subset_univ _, (mem_withFree.1 hρ)⟩,
      hext.free_subset⟩
  · obtain ⟨hF, hsub⟩ := mem_filter.1 hF
    refine mem_filter.2 ⟨mem_withFree.2 ?_, fun i b hb => ?_⟩
    · rw [hfree hsub]
      exact (mem_powersetCard.1 hF).2
    · by_cases hi : i ∈ F
      · simp [hi] at hb
      · simpa [hi] using hb
  · obtain ⟨-, hext⟩ := mem_filter.1 hρ
    funext i
    by_cases hi : i ∈ ρ.free
    · simp [hi, mem_free.1 hi]
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 fun h => hi (mem_free.2 h)
      simp [hi, hb, hext i b hb]
  · exact hfree (mem_filter.1 hF).2

/-! ### Drawing random restrictions -/

/-- The words agreeing with a partial assignment outside its free coordinates: `2 ^ ℓ` of them for
`ℓ` free coordinates. -/
theorem card_filter_outside_eq (ρ : PartialAssignment ι) :
    #{z : ι → Bool | outside ρ.free z = ρ} = 2 ^ #ρ.free := by
  rw [← card_filter_forall_notMem_eq ρ.free (ρ.fill fun _ => false)]
  congr 1
  ext z
  simp only [mem_filter, mem_univ, true_and, funext_iff, outside]
  refine forall_congr' fun i => ?_
  by_cases hi : i ∈ ρ.free
  · simp [hi, mem_free.1 hi]
  · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 fun h => hi (mem_free.2 h)
    simp [hi, hc, fill]

/-- **Drawing a free set and a word**: fixing the coordinates outside a set `J` of `ℓ`
coordinates to a word `z` draws every partial assignment with `ℓ` free coordinates `2 ^ ℓ`
times. -/
theorem sum_card_filter_outside (Q : PartialAssignment ι → Prop) [DecidablePred Q] (ℓ : ℕ) :
    ∑ J ∈ (univ : Finset ι).powersetCard ℓ, #{z : ι → Bool | Q (outside J z)} =
      2 ^ ℓ * #{ρ ∈ withFree ι ℓ | Q ρ} := by
  rw [← card_sigma, card_eq_sum_card_fiberwise (f := fun p => outside p.1 p.2)
    (t := (withFree ι ℓ).filter Q) fun p hp => ?_]
  · rw [sum_congr rfl fun ρ hρ => ?_, sum_const, smul_eq_mul, mul_comm]
    have hfree : #ρ.free = ℓ := mem_withFree.1 (mem_filter.1 hρ).1
    rw [← hfree, ← card_filter_outside_eq ρ]
    refine card_nbij' (fun p => p.2) (fun z => ⟨ρ.free, z⟩) (fun p hp => ?_) (fun z hz => ?_)
      (fun p hp => ?_) (fun z _ => rfl)
    · obtain ⟨-, hpρ⟩ := mem_filter.1 hp
      have h1 : p.1 = ρ.free := by rw [← hpρ, free_outside]
      exact mem_filter.2 ⟨mem_univ _, h1 ▸ hpρ⟩
    · have hz' : outside ρ.free z = ρ := (mem_filter.1 hz).2
      refine mem_filter.2 ⟨mem_sigma.2 ⟨mem_powersetCard.2 ⟨subset_univ _, rfl⟩, ?_⟩, hz'⟩
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      change Q (outside ρ.free z)
      rw [hz']
      exact (mem_filter.1 hρ).2
    · obtain ⟨-, hpρ⟩ := mem_filter.1 hp
      have h1 : p.1 = ρ.free := by rw [← hpρ, free_outside]
      exact Sigma.ext h1.symm HEq.rfl
  · obtain ⟨hJ, hz⟩ := mem_sigma.1 hp
    exact mem_filter.2 ⟨mem_withFree.2 (by rw [free_outside]; exact (mem_powersetCard.1 hJ).2),
      (mem_filter.1 hz).2⟩

/-- **Double counting extensions.** Summed over the partial assignments with `ℓ` free coordinates,
the extensions with `ℓ' ≤ ℓ` free coordinates satisfying `P` count each partial assignment with `ℓ'`
free coordinates satisfying `P` once for each of the `C(|ι| - ℓ', ℓ - ℓ')` ones it extends. -/
theorem sum_card_filter_extensions (P : PartialAssignment ι → Prop) [DecidablePred P] {ℓ ℓ' : ℕ}
    (hℓ : ℓ' ≤ ℓ) :
    ∑ ρ ∈ withFree ι ℓ, #{ρ' ∈ ρ.extensions ℓ' | P ρ'} =
      #{ρ' ∈ withFree ι ℓ' | P ρ'} * (Fintype.card ι - ℓ').choose (ℓ - ℓ') := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := withFree ι ℓ)
    (t := (withFree ι ℓ').filter P) (r := fun ρ ρ' => ρ'.Extends ρ)
  have habove (ρ : PartialAssignment ι) : #{ρ' ∈ ρ.extensions ℓ' | P ρ'} =
      #(((withFree ι ℓ').filter P).bipartiteAbove (fun ρ ρ' => ρ'.Extends ρ) ρ) := by
    congr 1
    ext ρ'
    simp only [mem_filter, mem_extensions, bipartiteAbove]
    tauto
  rw [sum_congr rfl fun ρ _ => habove ρ, h, sum_congr rfl fun ρ' hρ' => ?_, sum_const,
    smul_eq_mul]
  have hfree : #ρ'.free = ℓ' := mem_withFree.1 (mem_filter.1 hρ').1
  rw [bipartiteBelow, ← hfree, card_filter_extends_withFree (hfree ▸ hℓ)]

/-- **Double counting one-step extensions.** Summing `g (update ρ i (some b))` over all extensions
`ρ ∈ ρ₀.extensions t`, free coordinates `i ∈ ρ.free`, and constants `b : Bool` counts each
extension `ρ' ∈ ρ₀.extensions (t - 1)` once for each of the `#ρ₀.free - (t - 1)` coordinates of
`ρ₀.free` fixed by `ρ'`. -/
theorem sum_extensions_update (ρ₀ : PartialAssignment ι) {t : ℕ} (ht1 : 1 ≤ t)
    (g : PartialAssignment ι → ℕ) :
    ∑ ρ ∈ ρ₀.extensions t, ∑ i ∈ ρ.free,
        (g (update ρ i (some false)) + g (update ρ i (some true))) =
      (#ρ₀.free - (t - 1)) * ∑ ρ' ∈ ρ₀.extensions (t - 1), g ρ' := by
  rw [show ∑ ρ ∈ ρ₀.extensions t, ∑ i ∈ ρ.free,
        (g (update ρ i (some false)) + g (update ρ i (some true))) =
      ∑ x ∈ ((ρ₀.extensions t).sigma fun ρ => ρ.free) ×ˢ (univ : Finset Bool),
        g (update x.1.1 x.1.2 (some x.2)) by
    rw [sum_product, sum_sigma]
    refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => ?_
    rw [show (univ : Finset Bool) = {false, true} by decide, sum_pair (by decide)]]
  rw [show (#ρ₀.free - (t - 1)) * ∑ ρ' ∈ ρ₀.extensions (t - 1), g ρ' =
      ∑ p ∈ (ρ₀.extensions (t - 1)).sigma (fun ρ' => ρ₀.free \ ρ'.free), g p.1 by
    rw [sum_sigma, mul_sum]
    refine sum_congr rfl fun ρ' hρ' => ?_
    obtain ⟨hext, hfree⟩ := mem_extensions.1 hρ'
    dsimp only
    rw [sum_const, smul_eq_mul, card_sdiff_of_subset hext.free_subset, hfree]]
  refine sum_nbij' (fun x => ⟨update x.1.1 x.1.2 (some x.2), x.1.2⟩)
    (fun y => ⟨⟨update y.1 y.2 none, y.2⟩, (y.1 y.2).getD false⟩)
    (fun x hx => ?_) (fun y hy => ?_) (fun x hx => ?_) (fun y hy => ?_) (fun _ _ => rfl)
  · obtain ⟨⟨hρ, hi⟩, -⟩ := (mem_product.1 hx).imp_left mem_sigma.1
    obtain ⟨hext, hfree⟩ := mem_extensions.1 hρ
    exact mem_sigma.2 ⟨mem_extensions.2 ⟨hext.update_some (hext.free_subset hi) x.2,
      by rw [free_update, card_erase_of_mem hi, hfree]⟩,
      mem_sdiff.2 ⟨hext.free_subset hi, by simp⟩⟩
  · obtain ⟨hρ', hi⟩ := mem_sigma.1 hy
    obtain ⟨hext, hfree⟩ := mem_extensions.1 hρ'
    obtain ⟨hi₀, hi'⟩ := mem_sdiff.1 hi
    exact mem_product.2 ⟨mem_sigma.2 ⟨mem_extensions.2 ⟨hext.update_none hi₀,
      by rw [free_update_none, card_insert_of_notMem hi', hfree]; omega⟩,
      by simp⟩, mem_univ _⟩
  · obtain ⟨⟨-, hi⟩, -⟩ := (mem_product.1 hx).imp_left mem_sigma.1
    ext : 1
    · exact Sigma.ext
        (by dsimp only; rw [update_idem, update_eq_self_iff.2 (mem_free.1 hi).symm]) HEq.rfl
    · simp
  · obtain ⟨-, hi⟩ := mem_sigma.1 hy
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 fun h => (mem_sdiff.1 hi).2 (mem_free.2 h)
    exact Sigma.ext
      (by dsimp only; rw [update_idem, hc, Option.getD_some, update_eq_self_iff.2 hc.symm])
      HEq.rfl

/-- Relating the number of extensions with `t - 1` and `t` free coordinates:
`(#ρ₀.free - (t - 1)) * #(ρ₀.extensions (t - 1)) = 2 * t * #(ρ₀.extensions t)`. -/
theorem mul_card_extensions_sub_one (ρ₀ : PartialAssignment ι) {t : ℕ} (ht1 : 1 ≤ t) :
    (#ρ₀.free - (t - 1)) * #(ρ₀.extensions (t - 1)) = 2 * t * #(ρ₀.extensions t) := by
  have h := (sum_extensions_update ρ₀ ht1 (fun _ => 1)).symm
  rw [sum_const, smul_eq_mul, mul_one] at h
  have hinner (ρ : PartialAssignment ι) (hρ : ρ ∈ ρ₀.extensions t) :
      ∑ i ∈ ρ.free, (1 + 1) = 2 * t := by
    rw [sum_const, smul_eq_mul, (mem_extensions.1 hρ).2]
    ring
  rw [h, sum_congr rfl hinner, sum_const, smul_eq_mul]
  ring

/-- **Union bound for block survival**: if `ρ₀` has `b * m` free coordinates and `B 0, …, B (b - 1)`
are `b` subsets of `ρ₀.free` of size `m`, then for `1 ≤ b` and `2 * b ≤ 2 ^ r`, at least half of
all extensions in `ρ₀.extensions (b * r)` leave at least one free coordinate in every block
`B j`. -/
theorem card_extensions_le_two_mul_card_filter_forall_nonempty
    (ρ₀ : PartialAssignment ι) {b m : ℕ} (hb : 1 ≤ b) (hfree : #ρ₀.free = b * m)
    {B : Fin b → Finset ι} (hBsub : ∀ j, B j ⊆ ρ₀.free) (hBcard : ∀ j, #(B j) = m)
    {r : ℕ} (hbr : 2 * b ≤ 2 ^ r) :
    #(ρ₀.extensions (b * r)) ≤
      2 * #{ρ ∈ ρ₀.extensions (b * r) | ∀ j : Fin b, (ρ.free ∩ B j).Nonempty} := by
  set k := b * r
  set E := ρ₀.extensions k
  set A := {ρ ∈ E | ∀ j : Fin b, (ρ.free ∩ B j).Nonempty}
  set Bad : Fin b → Finset (PartialAssignment ι) :=
    fun j => {ρ ∈ E | ¬(ρ.free ∩ B j).Nonempty}
  have hcompl_sub : E \ A ⊆ univ.biUnion Bad := by
    intro ρ hρ
    obtain ⟨hρE, hρA⟩ := mem_sdiff.1 hρ
    rw [mem_filter, not_and] at hρA
    obtain ⟨j, hj⟩ := not_forall.1 (hρA hρE)
    exact mem_biUnion.2 ⟨j, mem_univ j, mem_filter.2 ⟨hρE, hj⟩⟩
  have hBad_card (j : Fin b) : #(Bad j) = (b * m - m).choose k * 2 ^ (b * m - k) := by
    rw [card_filter_extensions_not_nonempty_inter ρ₀ k (hBsub j), hfree, hBcard j]
  have hE_card : #E = (b * m).choose k * 2 ^ (b * m - k) := by
    rw [card_extensions, hfree]
  have h2sdiff : 2 * #(E \ A) ≤ #E := by
    calc 2 * #(E \ A)
        ≤ 2 * #(univ.biUnion Bad) := Nat.mul_le_mul_left 2 (card_le_card hcompl_sub)
      _ ≤ 2 * ∑ j : Fin b, #(Bad j) := Nat.mul_le_mul_left 2 card_biUnion_le
      _ = 2 * (b * ((b * m - m).choose k * 2 ^ (b * m - k))) := by
          rw [sum_congr rfl fun j _ => hBad_card j, sum_const, card_univ, Fintype.card_fin,
            smul_eq_mul]
      _ = 2 * b * (b * m - m).choose k * 2 ^ (b * m - k) := by ring
      _ ≤ 2 ^ r * (b * m - m).choose k * 2 ^ (b * m - k) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hbr)
      _ ≤ (b * m).choose k * 2 ^ (b * m - k) :=
          Nat.mul_le_mul_right _ (Nat.two_pow_mul_choose_sub_le hb r)
      _ = #E := hE_card.symm
  have hAsub : A ⊆ E := filter_subset _ _
  have hpart : #(E \ A) + #A = #E := card_sdiff_add_card_eq_card hAsub
  omega

/-- **Two stages of restrictions, counted.** Drawing a restriction with `ℓ'` free bits by first
drawing one with `ℓ ≥ ℓ'` free bits and then an extension of it: if at most a `G / c` fraction of
the restrictions with `ℓ` free bits satisfy `B`, and for each other one at most an `H / c` fraction
of its extensions with `ℓ'` free bits satisfy `B'`, then at most a `(G + H) / c` fraction of the
restrictions with `ℓ'` free bits satisfy `B'`. -/
theorem mul_card_filter_withFree_le {n c G H G' ℓ ℓ' : ℕ} (hℓ'ℓ : ℓ' ≤ ℓ) (hℓn : ℓ ≤ n)
    {B B' : PartialAssignment (Fin n) → Prop} [DecidablePred B] [DecidablePred B']
    (h₁ : c * #{ρ ∈ withFree (Fin n) ℓ | B ρ} ≤ G * #(withFree (Fin n) ℓ))
    (h₂ : ∀ ρ ∈ withFree (Fin n) ℓ, ¬ B ρ →
      c * #{ρ' ∈ ρ.extensions ℓ' | B' ρ'} ≤ H * #(ρ.extensions ℓ'))
    (hG : G + H ≤ G') :
    c * #{ρ ∈ withFree (Fin n) ℓ' | B' ρ} ≤ G' * #(withFree (Fin n) ℓ') := by
  set W := withFree (Fin n) ℓ
  set F := (n - ℓ').choose (ℓ - ℓ')
  have hF : 0 < F := Nat.choose_pos (by omega)
  set T := ℓ.choose ℓ' * 2 ^ (ℓ - ℓ')
  have hT : ∀ ρ ∈ W, #(ρ.extensions ℓ') = T := fun ρ hρ => by
    rw [card_extensions, mem_withFree.1 hρ]
  -- each restriction with `ℓ` free bits has few bad extensions, unless it satisfies `B`
  have hper : ∀ ρ ∈ W, c * #{ρ' ∈ ρ.extensions ℓ' | B' ρ'} ≤
      (if B ρ then c else 0) * T + H * T := fun ρ hρ => by
    by_cases hb : B ρ
    · simp only [hb, ↓reduceIte]
      rw [← hT ρ hρ]
      exact (Nat.mul_le_mul_left _ (card_filter_le _ _)).trans (Nat.le_add_right _ _)
    · simp only [hb, ↓reduceIte, zero_mul, zero_add]
      rw [← hT ρ hρ]
      exact h₂ ρ hρ hb
  -- double counting the extensions, with and without the condition
  have hdc := sum_card_filter_extensions B' hℓ'ℓ
  have hall := sum_card_filter_extensions (ι := Fin n) (fun _ => True) hℓ'ℓ
  simp only [filter_true] at hall
  rw [Fintype.card_fin] at hdc hall
  rw [sum_congr rfl hT, sum_const, smul_eq_mul] at hall
  refine Nat.le_of_mul_le_mul_right (?_ : _ * F ≤ _ * F) hF
  calc c * #{ρ ∈ withFree (Fin n) ℓ' | B' ρ} * F
      = ∑ ρ ∈ W, c * #{ρ' ∈ ρ.extensions ℓ' | B' ρ'} := by
        rw [mul_assoc, ← hdc, mul_sum]
    _ ≤ ∑ ρ ∈ W, ((if B ρ then c else 0) * T + H * T) := sum_le_sum hper
    _ = c * #{ρ ∈ W | B ρ} * T + #W * H * T := by
        rw [sum_add_distrib, ← sum_mul, sum_ite, sum_const_zero, add_zero, sum_const,
          smul_eq_mul, sum_const, smul_eq_mul]
        ring
    _ ≤ G * #W * T + #W * H * T := by gcongr
    _ = (G + H) * #(withFree (Fin n) ℓ') * F := by
        rw [mul_assoc _ #(withFree (Fin n) ℓ'), ← hall]
        ring
    _ ≤ G' * #(withFree (Fin n) ℓ') * F := by gcongr

end Cslib.BitString.PartialAssignment
