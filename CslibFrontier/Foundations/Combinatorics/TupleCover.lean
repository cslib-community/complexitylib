/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, finite combinatorics)

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Covering a finite set by few values of a map on tuples

Let `F` map the `t`-tuples of elements of a finite set `R` into a finite set `Y` of fewer than
`2 ^ t` values. Say that a value `y` *covers* `a ∈ R` when `a` is an entry of some tuple of
elements of `R` mapped to `y`. Then at most `⌊log₂ |R|⌋ + 1` values cover all of `R`
(`Finset.exists_tupleCover`).

The proof halves `R`. Some value covers at least half of `R`
(`Finset.exists_halving_tupleCover`): otherwise every value `y` covers fewer than `|R| / 2`
elements, so fewer than `(|R| / 2) ^ t` tuples are mapped to `y`, and the fewer than `2 ^ t` values
account for fewer than `|R| ^ t` tuples, which is all of them. Removing the covered elements and
repeating on the rest takes at most `⌊log₂ |R|⌋ + 1` rounds.

This is the counting behind the theorem of Fortnow and Santhanam that `NP`-hard problems have no
OR-distillation unless `coNP ⊆ NP/poly` [BodlaenderJansenKratsch2014, Theorem 2], in the case of
compression to fewer than `t` bits: `R` is a set of no-instances, `F` compresses a tuple of
no-instances into a short no-instance, and the covering values form the advice. See
`CslibFrontier.Computability.Complexity.Parameterized.Distillation`. The complementary witness lemma
of Dell and van Melkebeek [BodlaenderJansenKratsch2014, Lemma 1] allows compression to
`O(t log t)` bits; that case needs a cover by a number of values polynomial in `t`, not the halving
argument, and is not formalized here.

## Main results

* `Finset.exists_halving_tupleCover`: some value covers at least half of `R`.
* `Finset.exists_tupleCover`: `⌊log₂ |R|⌋ + 1` values cover `R`.

## References

* [H. L. Bodlaender, B. M. P. Jansen, S. Kratsch, *Kernelization lower bounds by
  cross-composition*][BodlaenderJansenKratsch2014]
-/

public section

open Finset

namespace Finset

variable {α β : Type*} {t : ℕ}

open Classical in
/-- The elements of `R` covered by `y`: the entries of `t`-tuples of elements of `R` that `F` maps
to `y`. -/
private noncomputable def tupleCover (R : Finset α) (F : (Fin t → α) → β) (y : β) : Finset α :=
  R.filter fun a => ∃ g : Fin t → α, (∀ i, g i ∈ R) ∧ a ∈ Set.range g ∧ F g = y

private theorem mem_tupleCover {R : Finset α} {F : (Fin t → α) → β} {y : β} {a : α} :
    a ∈ tupleCover R F y ↔
      a ∈ R ∧ ∃ g : Fin t → α, (∀ i, g i ∈ R) ∧ a ∈ Set.range g ∧ F g = y := by
  classical
  unfold tupleCover
  exact Finset.mem_filter

private theorem tupleCover_subset (R : Finset α) (F : (Fin t → α) → β) (y : β) :
    tupleCover R F y ⊆ R :=
  fun _ h => (mem_tupleCover.1 h).1

/-- Some value covers at least half of `R`, in the form of the private `tupleCover`. -/
private theorem exists_two_mul_card_tupleCover (R : Finset α) (hR : R.Nonempty)
    (F : (Fin t → α) → β) (Y : Finset β) (hY : #Y < 2 ^ t)
    (hFY : ∀ g : Fin t → α, (∀ i, g i ∈ R) → F g ∈ Y) :
    ∃ y ∈ Y, #R ≤ 2 * #(tupleCover R F y) := by
  classical
  by_contra hcon
  push Not at hcon
  -- every tuple of elements of `R` consists of elements covered by its image
  have hcount : #(Fintype.piFinset fun _ : Fin t => R) ≤
      ∑ y ∈ Y, #(Fintype.piFinset fun _ : Fin t => tupleCover R F y) := by
    calc #(Fintype.piFinset fun _ : Fin t => R)
        ≤ ∑ y ∈ Y, #((Fintype.piFinset fun _ : Fin t => R).filter fun g => F g = y) := by
          rw [← Finset.card_biUnion]
          · apply Finset.card_le_card
            intro g hg
            rw [Finset.mem_biUnion]
            exact ⟨F g, hFY g (Fintype.mem_piFinset.1 hg), Finset.mem_filter.2 ⟨hg, rfl⟩⟩
          · intro y _ y' _ hne
            rw [Function.onFun, Finset.disjoint_filter]
            intro g _ h1 h2
            exact hne (h1.symm.trans h2)
      _ ≤ ∑ y ∈ Y, #(Fintype.piFinset fun _ : Fin t => tupleCover R F y) := by
          apply Finset.sum_le_sum
          intro y _
          apply Finset.card_le_card
          intro g hg
          rw [Finset.mem_filter, Fintype.mem_piFinset] at hg
          rw [Fintype.mem_piFinset]
          intro i
          exact mem_tupleCover.2 ⟨hg.1 i, g, hg.1, ⟨i, rfl⟩, hg.2⟩
  simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    at hcount
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · -- there are no values, yet the empty tuple has one
    have hYe : Y = ∅ := Finset.card_eq_zero.1 (by simpa using hY)
    have := hFY (fun i => i.elim0) (fun i => i.elim0)
    simp [hYe] at this
  · have hlt : ∀ y ∈ Y, 2 ^ t * #(tupleCover R F y) ^ t < #R ^ t := fun y hy => by
      rw [← mul_pow]
      exact Nat.pow_lt_pow_left (hcon y hy) ht.ne'
    have h1 : 2 ^ t * #R ^ t ≤ ∑ y ∈ Y, 2 ^ t * #(tupleCover R F y) ^ t := by
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ hcount
    have hYne : Y.Nonempty := by
      obtain ⟨a, ha⟩ := hR
      exact ⟨_, hFY (fun _ => a) fun _ => ha⟩
    have h2 : ∑ y ∈ Y, 2 ^ t * #(tupleCover R F y) ^ t < ∑ _y ∈ Y, #R ^ t :=
      Finset.sum_lt_sum_of_nonempty hYne hlt
    rw [Finset.sum_const, smul_eq_mul] at h2
    have h3 : #Y * #R ^ t ≤ 2 ^ t * #R ^ t := Nat.mul_le_mul_right _ hY.le
    omega

/-- **Halving.** If `F` maps the `t`-tuples of elements of a nonempty finite set `R` into a set `Y`
of fewer than `2 ^ t` values, then some value `y ∈ Y` covers at least half of `R`: a subset `C ⊆ R`
with `|R| ≤ 2 |C|` consists of entries of tuples of elements of `R` mapped to `y`. -/
theorem exists_halving_tupleCover (R : Finset α) (hR : R.Nonempty) (F : (Fin t → α) → β)
    (Y : Finset β) (hY : #Y < 2 ^ t) (hFY : ∀ g : Fin t → α, (∀ i, g i ∈ R) → F g ∈ Y) :
    ∃ y ∈ Y, ∃ C ⊆ R, #R ≤ 2 * #C ∧
      ∀ a ∈ C, ∃ g : Fin t → α, (∀ i, g i ∈ R) ∧ a ∈ Set.range g ∧ F g = y := by
  obtain ⟨y, hy, hhalf⟩ := exists_two_mul_card_tupleCover R hR F Y hY hFY
  exact ⟨y, hy, tupleCover R F y, tupleCover_subset R F y, hhalf,
    fun a ha => (mem_tupleCover.1 ha).2⟩

/-- **Covering by few values.** If `F` maps the `t`-tuples of elements of a finite set `R` into a
set `Y` of fewer than `2 ^ t` values, then a set `S ⊆ Y` of at most `⌊log₂ |R|⌋ + 1` values covers
`R`: every `a ∈ R` is an entry of a tuple of elements of `R` mapped into `S`. -/
theorem exists_tupleCover (F : (Fin t → α) → β) (Y : Finset β) (hY : #Y < 2 ^ t) :
    ∀ R : Finset α, (∀ g : Fin t → α, (∀ i, g i ∈ R) → F g ∈ Y) →
      ∃ S ⊆ Y, #S ≤ Nat.log 2 #R + 1 ∧
        ∀ a ∈ R, ∃ g : Fin t → α, (∀ i, g i ∈ R) ∧ a ∈ Set.range g ∧ F g ∈ S := by
  classical
  intro R
  induction R using Finset.strongInduction with
  | H R ih =>
  intro hFY
  rcases R.eq_empty_or_nonempty with rfl | hR
  · exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  obtain ⟨y, hy, hhalf⟩ := exists_two_mul_card_tupleCover R hR F Y hY hFY
  set R' := R \ tupleCover R F y with hR'
  have hcov_pos : 0 < #(tupleCover R F y) := by
    have := hR.card_pos
    omega
  have hR'R : R' ⊂ R :=
    Finset.sdiff_ssubset (tupleCover_subset R F y) (Finset.card_pos.1 hcov_pos)
  by_cases hR'e : R' = ∅
  · refine ⟨{y}, Finset.singleton_subset_iff.2 hy, by simp, fun a ha => ?_⟩
    have hac : a ∈ tupleCover R F y := by
      by_contra hac
      have : a ∈ R' := Finset.mem_sdiff.2 ⟨ha, hac⟩
      simp [hR'e] at this
    obtain ⟨-, g, hg, hag, hgy⟩ := mem_tupleCover.1 hac
    exact ⟨g, hg, hag, by simp [hgy]⟩
  have hpos : 0 < #R' := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hR'e)
  obtain ⟨S', hS'Y, hS'card, hS'⟩ := ih R' hR'R fun g hg =>
    hFY g fun i => (Finset.mem_sdiff.1 (hg i)).1
  refine ⟨insert y S', Finset.insert_subset hy hS'Y, ?_, fun a ha => ?_⟩
  · have hcardR' : 2 * #R' ≤ #R := by
      rw [hR', Finset.card_sdiff_of_subset (tupleCover_subset R F y)]
      have := Finset.card_le_card (tupleCover_subset R F y)
      omega
    have hlog : Nat.log 2 #R' + 1 ≤ Nat.log 2 #R := by
      have h := Nat.log_mono_right (b := 2) hcardR'
      rwa [mul_comm, Nat.log_mul_base Nat.one_lt_two hpos.ne'] at h
    calc #(insert y S') ≤ #S' + 1 := Finset.card_insert_le _ _
      _ ≤ Nat.log 2 #R + 1 := by omega
  · by_cases hac : a ∈ tupleCover R F y
    · obtain ⟨-, g, hg, hag, hgy⟩ := mem_tupleCover.1 hac
      exact ⟨g, hg, hag, hgy ▸ Finset.mem_insert_self _ _⟩
    · obtain ⟨g, hg, hag, hgS⟩ := hS' a (Finset.mem_sdiff.2 ⟨ha, hac⟩)
      exact ⟨g, fun i => (Finset.mem_sdiff.1 (hg i)).1, hag, Finset.mem_insert_of_mem hgS⟩

end Finset
