/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Sunflower
public import Cslib.Foundations.Relation.RelatesInSteps

/-!
# Plucking sunflowers

To *pluck* a sunflower with `p ≥ 2` petals from a family of sets is to remove its petals and add
its core. The core is contained in every petal, so every set of the family still contains a set of
the plucked family (`Pluck.exists_subset`), and the family gets strictly smaller
(`Pluck.card_lt`). Plucking until no sunflower with `p` petals is left therefore terminates after
at most as many plucks as the family has sets, and, by the sunflower lemma, leaves a family of
sets of size at most `w` with at most `sunflowerBound p w` sets (`card_pluckNormalForm_le`). This
is the normalisation step of Razborov's method of approximations
[Jukna, Chapter 9][Jukna2012].

## Main definitions

* `Cslib.Pluck`: the relation of plucking one sunflower.
* `Cslib.pluckNormalForm`: a family reached by plucking that contains no sunflower with `p` petals.

## Main results

* `Cslib.relatesInSteps_pluckNormalForm`: the normal form is reached in at most as many plucks as
  the family has sets.
* `Cslib.card_pluckNormalForm_le`: the size of a normal form of a family of small sets.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib

open Finset Relation

variable {α : Type*} [DecidableEq α] {p w : ℕ} {F G : Finset (Finset α)}

/-- `G` is obtained from `F` by plucking a sunflower with `p` petals: removing the petals and
adding their core. -/
def Pluck (p : ℕ) (F G : Finset (Finset α)) : Prop :=
  ∃ S ⊆ F, S.card = p ∧ ∃ K, IsSunflower S K ∧ G = insert K (F \ S)

namespace Pluck

/-- Plucking makes a family strictly smaller. -/
theorem card_lt (hp : 2 ≤ p) (h : Pluck p F G) : G.card < F.card := by
  obtain ⟨S, hSF, hS, K, -, rfl⟩ := h
  have := card_le_card hSF
  calc (insert K (F \ S)).card ≤ (F \ S).card + 1 := card_insert_le _ _
    _ = F.card - p + 1 := by rw [card_sdiff_of_subset hSF, hS]
    _ < F.card := by omega

/-- Every set of a plucked family is a set of the family or contained in one. -/
theorem exists_superset (hp : 2 ≤ p) (h : Pluck p F G) {t : Finset α} (ht : t ∈ G) :
    ∃ s ∈ F, t ⊆ s := by
  obtain ⟨S, hSF, hS, K, hSK, rfl⟩ := h
  rcases mem_insert.1 ht with rfl | ht
  · obtain ⟨s, hs⟩ := card_pos.1 (by omega : 0 < S.card)
    exact ⟨s, hSF hs, hSK.subset_of_mem (by omega) hs⟩
  · exact ⟨t, (mem_sdiff.1 ht).1, subset_rfl⟩

/-- Every set of a family contains a set of the plucked family. -/
theorem exists_subset (hp : 2 ≤ p) (h : Pluck p F G) {s : Finset α} (hs : s ∈ F) :
    ∃ t ∈ G, t ⊆ s := by
  obtain ⟨S, -, hS, K, hSK, rfl⟩ := h
  by_cases hsS : s ∈ S
  · exact ⟨K, mem_insert_self _ _, hSK.subset_of_mem (by omega) hsS⟩
  · exact ⟨s, mem_insert_of_mem (mem_sdiff.2 ⟨hs, hsS⟩), subset_rfl⟩

/-- Plucking keeps the sets of size at most `w`. -/
theorem forall_card_le (hp : 2 ≤ p) (h : Pluck p F G) (hF : ∀ s ∈ F, s.card ≤ w) :
    ∀ t ∈ G, t.card ≤ w := fun _ ht =>
  let ⟨s, hs, hts⟩ := h.exists_superset hp ht
  (card_le_card hts).trans (hF s hs)

end Pluck

/-- Plucking a family to the end takes at most as many plucks as it has sets. -/
theorem exists_relatesInSteps_not_containsSunflower (hp : 2 ≤ p) (F : Finset (Finset α)) :
    ∃ G m, m ≤ F.card ∧ RelatesInSteps (Pluck p) F G m ∧ ¬ContainsSunflower p G := by
  induction F using (measure Finset.card).wf.induction with
  | h F ih =>
    by_cases hF : ContainsSunflower p F
    · obtain ⟨S, hSF, hS, K, hSK⟩ := hF
      have hpl : Pluck p F (insert K (F \ S)) := ⟨S, hSF, hS, K, hSK, rfl⟩
      have hlt := hpl.card_lt hp
      obtain ⟨G, m, hm, hG, hfree⟩ := ih _ hlt
      exact ⟨G, m + 1, by omega, RelatesInSteps.head _ _ _ _ hpl hG, hfree⟩
    · exact ⟨F, 0, Nat.zero_le _, RelatesInSteps.refl F, hF⟩

open scoped Classical in
/-- A family reached from `F` by plucking that contains no sunflower with `p` petals, for
`2 ≤ p`; for smaller `p` it is `F` itself. -/
noncomputable def pluckNormalForm (p : ℕ) (F : Finset (Finset α)) : Finset (Finset α) :=
  if hp : 2 ≤ p then (exists_relatesInSteps_not_containsSunflower hp F).choose else F

/-- For `2 ≤ p`, the normal form of `F` is reached from `F` in at most `F.card` plucks. -/
theorem relatesInSteps_pluckNormalForm (hp : 2 ≤ p) (F : Finset (Finset α)) :
    ∃ m ≤ F.card, RelatesInSteps (Pluck p) F (pluckNormalForm p F) m := by
  simp only [pluckNormalForm, hp, dite_true]
  obtain ⟨m, hm, hG, -⟩ := (exists_relatesInSteps_not_containsSunflower hp F).choose_spec
  exact ⟨m, hm, hG⟩

/-- For `2 ≤ p`, the normal form contains no sunflower with `p` petals. -/
theorem not_containsSunflower_pluckNormalForm (hp : 2 ≤ p) (F : Finset (Finset α)) :
    ¬ContainsSunflower p (pluckNormalForm p F) := by
  simp only [pluckNormalForm, hp, dite_true]
  exact (exists_relatesInSteps_not_containsSunflower hp F).choose_spec.choose_spec.2.2

/-- Plucking repeatedly keeps the sets of size at most `w`. -/
theorem forall_card_le_of_relatesInSteps_pluck (hp : 2 ≤ p) {m : ℕ}
    (h : RelatesInSteps (Pluck p) F G m) (hF : ∀ s ∈ F, s.card ≤ w) : ∀ t ∈ G, t.card ≤ w := by
  induction h with
  | refl => exact hF
  | tail _ _ _ _ h ih => exact h.forall_card_le hp ih

/-- After plucking repeatedly, every set of the family contains a set of the result. -/
theorem exists_subset_of_relatesInSteps_pluck (hp : 2 ≤ p) {m : ℕ}
    (h : RelatesInSteps (Pluck p) F G m) {s : Finset α} (hs : s ∈ F) : ∃ t ∈ G, t ⊆ s := by
  induction h with
  | refl => exact ⟨s, hs, subset_rfl⟩
  | tail _ _ _ _ h ih =>
    obtain ⟨t, ht, hts⟩ := ih
    obtain ⟨u, hu, hut⟩ := h.exists_subset hp ht
    exact ⟨u, hu, hut.trans hts⟩

/-- If every set of `F` has size at most `w`, so does every set of its normal form. -/
theorem forall_card_le_pluckNormalForm (hF : ∀ s ∈ F, s.card ≤ w) :
    ∀ t ∈ pluckNormalForm p F, t.card ≤ w := by
  by_cases hp : 2 ≤ p
  · obtain ⟨m, -, h⟩ := relatesInSteps_pluckNormalForm hp F
    exact forall_card_le_of_relatesInSteps_pluck hp h hF
  · simpa only [pluckNormalForm, hp, dite_false] using hF

/-- Every set of `F` contains a set of its normal form. -/
theorem exists_subset_of_mem_pluckNormalForm {s : Finset α} (hs : s ∈ F) :
    ∃ t ∈ pluckNormalForm p F, t ⊆ s := by
  by_cases hp : 2 ≤ p
  · obtain ⟨m, -, h⟩ := relatesInSteps_pluckNormalForm hp F
    exact exists_subset_of_relatesInSteps_pluck hp h hs
  · simp only [pluckNormalForm, hp, dite_false]
    exact ⟨s, hs, subset_rfl⟩

/-- A normal form of a family of sets of size at most `w` has at most `sunflowerBound p w` sets. -/
theorem card_pluckNormalForm_le (hp : 2 ≤ p) (hF : ∀ s ∈ F, s.card ≤ w) :
    (pluckNormalForm p F).card ≤ sunflowerBound p w :=
  not_lt.1 fun h => not_containsSunflower_pluckNormalForm hp F
    (containsSunflower_of_forall_card_le p w _ (forall_card_le_pluckNormalForm hF) h)

end Cslib
