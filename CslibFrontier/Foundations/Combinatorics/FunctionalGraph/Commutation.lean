/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

public import Mathlib.Data.Finset.Card
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Sparse commutation defects

If `h` commutes with `f`, changing `f` to `g` can break commutation only at changed inputs
or their preimages under `h`. For injective `h` on a finite type this gives at most twice as
many defects as edited inputs. These facts support sparse-counter circuit bounds.
For the related block characterization of almost-commuting permutations, see
[Moreno and Rivera][MorenoRivera2016], as credited in the source formalization.

## Main definitions

* `Cslib.FunctionalGraph.disagreement`: the finite set on which two endomaps differ.

## Main results

* `Cslib.FunctionalGraph.commutation_defect_subset`: localization of commutation failures.
* `Cslib.FunctionalGraph.commutation_defect_card`: the factor-two bound for injective maps.
* `Cslib.FunctionalGraph.disagreement_image_eq`: edited permutations have the same edited outputs.
* `Cslib.FunctionalGraph.disagreement_conjugate_card`: relabeling preserves the number of edits.

## References

* Adapted from lean/Proofs/CommutationDefect.lean at revision `c4cfa198` of
  [S. Schlesinger, *Square-root circuit bounds for iterated functions*]
  [Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.FunctionalGraph

universe u
variable {α : Type u}

/-- Commuting with a sparse modification creates defects only at modified
inputs or at their preimages under the commuting map. -/
theorem commutation_defect_subset (f g h : α → α) (hc : Function.Commute h f) :
    {x | h (g x) ≠ g (h x)} ⊆ {x | f x ≠ g x} ∪ h ⁻¹' {x | f x ≠ g x} := by
  intro x hx
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_preimage, not_or, not_not] at hn
  exact hx (by rw [← hn.1, hc x, hn.2])

open scoped Classical in
/-- The inputs on which two endomaps disagree. -/
noncomputable def disagreement [Fintype α] (f g : α → α) : Finset α :=
  Finset.univ.filter fun x => f x ≠ g x

/-- A state lies in the disagreement set exactly when `f` and `g` differ there. -/
@[simp] theorem mem_disagreement [Fintype α] (f g : α → α) (x : α) :
    x ∈ disagreement f g ↔ f x ≠ g x := by
  classical
  simp [disagreement]

/-- Injectivity suffices for the uniform factor-two defect bound. -/
theorem commutation_defect_card [Fintype α] (f g h : α → α)
    (hc : Function.Commute h f) (hi : Function.Injective h) :
    (disagreement (h ∘ g) (g ∘ h)).card ≤ 2 * (disagreement f g).card := by
  classical
  let E := disagreement f g
  let P := Finset.univ.filter fun x => h x ∈ E
  have hP : P.card ≤ E.card := by
    calc
      P.card = (P.image h).card := (Finset.card_image_of_injective P hi).symm
      _ ≤ E.card := Finset.card_le_card (by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact (Finset.mem_filter.mp hx).2)
  have hsub : disagreement (h ∘ g) (g ∘ h) ⊆ E ∪ P := by
    intro x hx
    have hd := commutation_defect_subset f g h hc (mem_disagreement _ _ _ |>.mp hx)
    simpa only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_disagreement, Set.mem_union, Set.mem_ofPred_eq, Set.mem_preimage, E, P] using hd
  calc
    _ ≤ (E ∪ P).card := Finset.card_le_card hsub
    _ ≤ E.card + P.card := Finset.card_union_le _ _
    _ ≤ 2 * E.card := by lia

/-- Permutations agreeing away from the edited inputs use the same remaining outputs. -/
theorem disagreement_image_eq [Fintype α] [DecidableEq α] (f g : Equiv.Perm α) :
    (disagreement f g).image f = (disagreement f g).image g := by
  classical
  ext y
  constructor
  · rintro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_image.mpr ⟨g.symm (f x), ?_, by simp⟩
    rw [mem_disagreement] at hx ⊢
    intro he
    have he' : f (g.symm (f x)) = f x := by simpa using he
    have := f.injective he'
    exact hx (by simpa [this] using g.apply_symm_apply (f x) |>.symm)
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_image.mpr ⟨f.symm (g x), ?_, by simp⟩
    rw [mem_disagreement] at hx ⊢
    intro he
    have he' : g (f.symm (g x)) = g x := by simpa using he.symm
    have := g.injective he'
    exact hx (by simpa [this] using f.apply_symm_apply (g x))

/-- Relabeling a finite universe preserves the number of edited successors. -/
theorem disagreement_conjugate_card {β : Type*} [Fintype α] [Fintype β]
    (f g : α → α) (e : α ≃ β) :
    (disagreement (e ∘ f ∘ e.symm) (e ∘ g ∘ e.symm)).card =
      (disagreement f g).card := by
  classical
  symm
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    simpa only [mem_disagreement, Function.comp_apply, Equiv.symm_apply_apply,
      e.injective.ne_iff] using hx
  · intro x _ y _ he
    exact e.injective he
  · intro y hy
    refine ⟨e.symm y, ?_, by simp⟩
    simpa only [mem_disagreement, Function.comp_apply, e.injective.ne_iff] using hy

end Cslib.FunctionalGraph
