/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, inclusion matrices of subsets)

public import Complexity.Init
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination

/-!
# Inclusion matrices of subsets

The *inclusion matrix* `W_{t,s}` of a finite set `U` has its rows indexed by the `t`-element
subsets `A` of `U`, its columns by the `s`-element subsets `B`, and the entry `1` when `A ⊆ B`.
**Gottlieb's theorem** [Gottlieb1966] says that for `t ≤ s` and `t + s ≤ #U` the matrix has full
row rank over `ℚ`: a weighting `a` of the `t`-subsets whose sums `∑_{A ⊆ B, #A = t} a A` vanish for
every `s`-subset `B` is zero (`Finset.eq_zero_of_sum_powersetCard_eq_zero`).

The theorem is proved here over any field in which the integers `1, …, s` are nonzero, so in
characteristic zero and in every characteristic larger than `s`. Gottlieb states the rational
case. The proof here, by induction on `U`, divides only by integers between `2` and `s`, so this
mild generalization costs nothing. The induction splits the subsets by an element `x`
(`Finset.sum_powersetCard_succ_insert`). Double counting (`Finset.sum_sum_powersetCard_erase`)
gives the hypothesis for the weights `A ↦ a (insert x A)` of the `(t-1)`-subsets, up to the
factor `s - t + 1`, which is the only division. Both halves then reduce to weightings of the
smaller set with smaller parameters.
Impagliazzo, Pudlák and Sgall use the theorem to bound polynomial-calculus degree
[ImpagliazzoPudlakSgall1999].

## Main results

* `Finset.sum_sum_powersetCard_erase`: each `t`-subset of `B` misses `#B - t` elements of `B`.
* `Finset.sum_powersetCard_succ_insert`: the `(t+1)`-subsets of `insert x B` split by whether they
  contain `x`.
* `Finset.eq_zero_of_sum_powersetCard_eq_zero`: Gottlieb's theorem, over a field in which
  `1, …, s` are nonzero.

## References

* [D. H. Gottlieb, *A certain class of incidence matrices*][Gottlieb1966]
* [R. Impagliazzo, P. Pudlák, J. Sgall, *Lower bounds for the polynomial calculus and the Gröbner
  basis algorithm*][ImpagliazzoPudlakSgall1999]
-/

public section

open Finset

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- **Double counting `t`-subsets.** Summing over the `t`-subsets of `B.erase i` for every `i ∈ B`
counts each `t`-subset `A` of `B` once for each of the `#B - t` elements of `B \ A`. -/
theorem sum_sum_powersetCard_erase {M : Type*} [AddCommMonoid M] (a : Finset α → M) (t : ℕ)
    (B : Finset α) :
    ∑ i ∈ B, ∑ A ∈ (B.erase i).powersetCard t, a A = (#B - t) • ∑ A ∈ B.powersetCard t, a A := by
  calc ∑ i ∈ B, ∑ A ∈ (B.erase i).powersetCard t, a A
      = ∑ i ∈ B, ∑ A ∈ B.powersetCard t, if i ∉ A then a A else 0 := by
        refine sum_congr rfl fun i hi => ?_
        rw [← sum_filter]
        refine sum_congr ?_ fun _ _ => rfl
        ext A
        simp only [mem_powersetCard, mem_filter, subset_erase]
        tauto
    _ = ∑ A ∈ B.powersetCard t, ∑ i ∈ B, if i ∉ A then a A else 0 := sum_comm
    _ = ∑ A ∈ B.powersetCard t, (#B - t) • a A := by
        refine sum_congr rfl fun A hA => ?_
        rw [mem_powersetCard] at hA
        rw [← sum_filter, sum_const, ← sdiff_eq_filter, card_sdiff_of_subset hA.1, hA.2]
    _ = _ := (smul_sum ..).symm

/-- The `(t + 1)`-subsets of `insert x B`, for `x ∉ B`, are the `(t + 1)`-subsets of `B` and the
sets `insert x A` for the `t`-subsets `A` of `B`. -/
theorem sum_powersetCard_succ_insert {M : Type*} [AddCommMonoid M] (a : Finset α → M) {x : α}
    {B : Finset α} (hxB : x ∉ B) (t : ℕ) :
    ∑ A ∈ (insert x B).powersetCard (t + 1), a A =
      ∑ A ∈ B.powersetCard (t + 1), a A + ∑ A ∈ B.powersetCard t, a (insert x A) := by
  have hdisj : Disjoint (B.powersetCard (t + 1)) ((B.powersetCard t).image (insert x)) := by
    rw [disjoint_left]
    intro A h₁ h₂
    obtain ⟨A', _, rfl⟩ := mem_image.1 h₂
    exact hxB ((mem_powersetCard.1 h₁).1 (mem_insert_self x A'))
  have hinj : Set.InjOn (insert x) (B.powersetCard t : Set (Finset α)) := by
    intro A₁ h₁ A₂ h₂ h
    have hx₁ : x ∉ A₁ := fun h' => hxB ((mem_powersetCard.1 (mem_coe.1 h₁)).1 h')
    have hx₂ : x ∉ A₂ := fun h' => hxB ((mem_powersetCard.1 (mem_coe.1 h₂)).1 h')
    rw [← erase_insert hx₁, ← erase_insert hx₂]
    exact congrArg (·.erase x) h
  rw [powersetCard_succ_insert hxB, sum_union hdisj, sum_image hinj]

variable {F : Type*} [Field F]

omit [DecidableEq α] in
/-- **Gottlieb's theorem** [Gottlieb1966]: for `t ≤ s` and `t + s ≤ #U`, the inclusion matrix of
the `t`-subsets against the `s`-subsets of `U` has full row rank. If the weights `a A` of the
`t`-subsets sum to zero inside every `s`-subset `B` of `U`, then every weight is zero.

Gottlieb proves this over `ℚ`; here the field may be any field in which the integers `1, …, s`
are nonzero. -/
theorem eq_zero_of_sum_powersetCard_eq_zero {U : Finset α} {t s : ℕ} (hts : t ≤ s)
    (hsum : t + s ≤ #U) (hU : ∀ j : ℕ, 0 < j → j ≤ s → (j : F) ≠ 0) {a : Finset α → F}
    (ha : ∀ B ∈ U.powersetCard s, ∑ A ∈ B.powersetCard t, a A = 0) :
    ∀ A ∈ U.powersetCard t, a A = 0 := by
  classical
  induction U using Finset.induction_on generalizing t s a with
  | empty =>
    intro A hA
    rw [card_empty] at hsum
    obtain ⟨rfl, rfl⟩ : t = 0 ∧ s = 0 := by omega
    rw [powersetCard_zero, mem_singleton] at hA
    subst hA
    have h := ha ∅ (by rw [powersetCard_zero]; exact mem_singleton_self _)
    rwa [powersetCard_zero, sum_singleton] at h
  | insert x U hx ih =>
    intro A hA
    have hcard : #(insert x U) = #U + 1 := card_insert_of_notMem hx
    rcases Nat.eq_or_lt_of_le hts with rfl | hlt
    · have h := ha A hA
      rw [mem_powersetCard] at hA
      rwa [← hA.2, powersetCard_self, sum_singleton] at h
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · rw [mem_powersetCard, card_eq_zero] at hA
      obtain ⟨B, hB⟩ := (powersetCard_nonempty (s := insert x U) (n := s)).2 (by omega)
      have h := ha B hB
      rw [powersetCard_zero, sum_singleton] at h
      rw [hA.2]
      exact h
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hU' : ∀ j : ℕ, 0 < j → j ≤ s' → (j : F) ≠ 0 := fun j hj hjs =>
      hU j hj (by omega)
    -- the `s`-subsets avoiding `x`
    have eq1 : ∀ B ∈ U.powersetCard (s' + 1), ∑ A ∈ B.powersetCard (t' + 1), a A = 0 :=
      fun B hB => ha B (powersetCard_mono (subset_insert x U) hB)
    -- the `s`-subsets containing `x`
    have eq2 : ∀ B ∈ U.powersetCard s', ∑ A ∈ B.powersetCard (t' + 1), a A +
        ∑ A ∈ B.powersetCard t', a (insert x A) = 0 := by
      intro B hB
      rw [mem_powersetCard] at hB
      have hxB : x ∉ B := fun h => hx (hB.1 h)
      rw [← sum_powersetCard_succ_insert a hxB]
      exact ha _ (mem_powersetCard.2 ⟨insert_subset_insert x hB.1, by
        rw [card_insert_of_notMem hxB, hB.2]⟩)
    -- double counting gives the hypothesis for the weights `A ↦ a (insert x A)`
    have eq3 : ∀ B ∈ U.powersetCard (s' + 1), ∑ A ∈ B.powersetCard t', a (insert x A) = 0 := by
      intro B hB
      have hB' := mem_powersetCard.1 hB
      have h1 := sum_sum_powersetCard_erase a (t' + 1) B
      rw [eq1 B hB, smul_zero] at h1
      have h2 : ∑ i ∈ B, ∑ A ∈ (B.erase i).powersetCard t', a (insert x A) = 0 := by
        have : ∀ i ∈ B, ∑ A ∈ (B.erase i).powersetCard t', a (insert x A) =
            -∑ A ∈ (B.erase i).powersetCard (t' + 1), a A := by
          intro i hi
          have h := eq2 (B.erase i) (mem_powersetCard.2 ⟨(erase_subset i B).trans hB'.1, by
            rw [card_erase_of_mem hi, hB'.2]; rfl⟩)
          linear_combination h
        rw [sum_congr rfl this, sum_neg_distrib, h1, neg_zero]
      rw [sum_sum_powersetCard_erase (fun A => a (insert x A)) t' B, hB'.2, nsmul_eq_mul] at h2
      refine (mul_eq_zero.1 h2).resolve_left ?_
      exact hU (s' + 1 - t') (by omega) (by omega)
    have ha'' : ∀ A ∈ U.powersetCard t', a (insert x A) = 0 :=
      ih (t := t') (s := s' + 1) (a := fun A => a (insert x A)) (by omega) (by omega) hU eq3
    have eq5 : ∀ B ∈ U.powersetCard s', ∑ A ∈ B.powersetCard (t' + 1), a A = 0 := by
      intro B hB
      have h := eq2 B hB
      rwa [sum_eq_zero (fun A hA => ha'' A (powersetCard_mono (mem_powersetCard.1 hB).1 hA)),
        add_zero] at h
    have ha' : ∀ A ∈ U.powersetCard (t' + 1), a A = 0 :=
      ih (t := t' + 1) (s := s') (by omega) (by omega) hU' eq5
    rw [mem_powersetCard] at hA
    by_cases hxA : x ∈ A
    · have hA' : A.erase x ∈ U.powersetCard t' := by
        rw [mem_powersetCard]
        refine ⟨fun y hy => ?_, by rw [card_erase_of_mem hxA, hA.2]; rfl⟩
        exact (mem_insert.1 (hA.1 (mem_of_mem_erase hy))).resolve_left (ne_of_mem_erase hy)
      have h := ha'' _ hA'
      rwa [insert_erase hxA] at h
    · refine ha' A (mem_powersetCard.2 ⟨fun y hy => ?_, hA.2⟩)
      exact (mem_insert.1 (hA.1 hy)).resolve_left fun h => hxA (h ▸ hy)

end Finset
