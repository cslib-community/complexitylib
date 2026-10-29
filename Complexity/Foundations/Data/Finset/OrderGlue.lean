/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Finset.Sort

/-!
# Gluing functions along ordered finite subsets

## Main definitions

* `Finset.glue`: join two strings along a subset and its complement.

## Main results

* `Finset.eq_glue_iff`, `Finset.glue_inj`: reconstruction and uniqueness.

## References

Adapted selectively from [AlmanWilliams2026, Section 2] and
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. These are finite mathematical
counts and identities; they give no native program or instruction-cost certificate.
-/

@[expose] public section

open Finset

namespace Finset

/-- The complement of a size-`m` subset of `Fin L` has size `L - m`. -/
theorem card_compl_of_card_eq {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) :
    Qᶜ.card = L - m := by
  rw [Finset.card_compl, Fintype.card_fin, hQ]

variable {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)

/-! ### The levels of a set and of its complement, in order -/

/-- The `k`-th lowest level outside `Q` is not a level of `Q`. -/
theorem outerLevel_notMem (k : Fin (L - m)) : (Qᶜ.orderEmbOfFin (card_compl_of_card_eq Q hQ)) k ∉
  Q :=
  mem_compl.mp (Qᶜ.orderEmbOfFin_mem (card_compl_of_card_eq Q hQ) k)

/-- Every level of `Q` is the `k`-th lowest level of `Q` for some `k`. -/
theorem exists_innerLevel {ℓ : Fin L} (hℓ : ℓ ∈ Q) : ∃ k, Finset.orderEmbOfFin Q hQ k = ℓ :=
  (Q.range_orderEmbOfFin hQ).ge hℓ

/-- Every level outside `Q` is the `k`-th lowest level outside `Q` for some `k`. -/
theorem exists_outerLevel {ℓ : Fin L} (hℓ : ℓ ∉ Q) : ∃ k, (Qᶜ.orderEmbOfFin (card_compl_of_card_eq
  Q hQ)) k = ℓ :=
  (Qᶜ.range_orderEmbOfFin (card_compl_of_card_eq Q hQ)).ge (mem_coe.mpr (mem_compl.mpr hℓ))

/-- The levels of `Q` in order depend only on the set `Q`. -/
theorem innerLevel_congr {Q' : Finset (Fin L)} (h : Q' = Q) (hQ' : Q'.card = m) :
    Finset.orderEmbOfFin Q' hQ' = Finset.orderEmbOfFin Q hQ := by
  subst h
  rfl

/-- The levels outside `Q` in order depend only on the set `Q`. -/
theorem outerLevel_congr {Q' : Finset (Fin L)} (h : Q' = Q) (hQ' : Q'.card = m) :
    (Q'ᶜ.orderEmbOfFin (card_compl_of_card_eq Q' hQ')) = (Qᶜ.orderEmbOfFin (card_compl_of_card_eq
      Q hQ)) := by
  subst h
  rfl

/-- A property holds at every level if and only if it holds at the levels of `Q` and at the levels
outside `Q`. -/
theorem forall_level_iff {P : Fin L → Prop} :
    (∀ ℓ, P ℓ) ↔ (∀ k, P (Finset.orderEmbOfFin Q hQ k)) ∧ ∀ k, P ((Qᶜ.orderEmbOfFin
      (card_compl_of_card_eq Q hQ)) k) := by
  refine ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩, fun ⟨hin, hout⟩ ℓ => ?_⟩
  by_cases hℓ : ℓ ∈ Q
  · obtain ⟨k, rfl⟩ := exists_innerLevel Q hQ hℓ
    exact hin k
  · obtain ⟨k, rfl⟩ := exists_outerLevel Q hQ hℓ
    exact hout k

/-- A property cuts out the set `Q` if and only if it holds at the levels of `Q` and fails at the
other levels. -/
theorem filter_eq_iff_forall_level {P : Fin L → Prop} [DecidablePred P] :
    univ.filter P = Q ↔ (∀ k, P (Finset.orderEmbOfFin Q hQ k)) ∧ ∀ k, ¬ P ((Qᶜ.orderEmbOfFin
      (card_compl_of_card_eq Q hQ)) k) := by
  simp only [Finset.ext_iff, forall_level_iff Q hQ, mem_filter, mem_univ, true_and,
    Finset.orderEmbOfFin_mem, outerLevel_notMem Q hQ, iff_true, iff_false]

/-- A property that holds at the `m` levels of `Q`, and at `m` levels in all, cuts out `Q`. -/
theorem filter_eq_of_forall_innerLevel {P : Fin L → Prop} [DecidablePred P]
    (hin : ∀ k, P (Finset.orderEmbOfFin Q hQ k)) (hcard : (univ.filter P).card = m) : univ.filter
      P = Q := by
  refine (eq_of_subset_of_card_le (fun ℓ hℓ => ?_) (hcard.trans hQ.symm).le).symm
  obtain ⟨k, rfl⟩ := exists_innerLevel Q hQ hℓ
  exact mem_filter.mpr ⟨mem_univ _, hin k⟩

/-! ### Gluing two strings along a set of levels -/

variable {α : Type*}

/-- The string that has the letters of `f` at the levels of `Q` and the letters of `g` at the other
levels, both in the order of the levels. -/
def glue (f : Fin m → α) (g : Fin (L - m) → α) : Fin L → α :=
  fun ℓ =>
    if hℓ : ℓ ∈ Q then f ((Q.orderIsoOfFin hQ).symm ⟨ℓ, hℓ⟩)
    else g ((Qᶜ.orderIsoOfFin (card_compl_of_card_eq Q hQ)).symm ⟨ℓ, mem_compl.mpr hℓ⟩)

/-- At the `k`-th lowest level of `Q`, the glued string has the `k`-th letter of `f`. -/
@[simp]
theorem glue_innerLevel (f : Fin m → α) (g : Fin (L - m) → α) (k : Fin m) :
    glue Q hQ f g (Finset.orderEmbOfFin Q hQ k) = f k := by
  rw [glue, dite_eq_left (Finset.orderEmbOfFin_mem Q hQ k)]
  exact congrArg f ((OrderIso.symm_apply_eq _).mpr (Subtype.ext rfl))

/-- At the `k`-th lowest level outside `Q`, the glued string has the `k`-th letter of `g`. -/
@[simp]
theorem glue_outerLevel (f : Fin m → α) (g : Fin (L - m) → α) (k : Fin (L - m)) :
    glue Q hQ f g ((Qᶜ.orderEmbOfFin (card_compl_of_card_eq Q hQ)) k) = g k := by
  rw [glue, dite_eq_right (outerLevel_notMem Q hQ k)]
  exact congrArg g ((OrderIso.symm_apply_eq _).mpr (Subtype.ext rfl))

/-- At the `k`-th lowest level of a set `Q'` that is equal to `Q`, the string glued along `Q` has
the `k`-th letter of `f`. -/
theorem glue_innerLevel_of_eq (f : Fin m → α) (g : Fin (L - m) → α) {Q' : Finset (Fin L)}
    (h : Q' = Q) (hQ' : Q'.card = m) (k : Fin m) : glue Q hQ f g (Finset.orderEmbOfFin Q' hQ' k) =
      f k := by
  rw [innerLevel_congr Q hQ h, glue_innerLevel]

/-- At the `k`-th lowest level outside a set `Q'` that is equal to `Q`, the string glued along `Q`
has the `k`-th letter of `g`. -/
theorem glue_outerLevel_of_eq (f : Fin m → α) (g : Fin (L - m) → α) {Q' : Finset (Fin L)}
    (h : Q' = Q) (hQ' : Q'.card = m) (k : Fin (L - m)) :
    glue Q hQ f g ((Q'ᶜ.orderEmbOfFin (card_compl_of_card_eq Q' hQ')) k) = g k := by
  subst h
  apply glue_outerLevel

variable {f f' : Fin m → α} {g g' : Fin (L - m) → α}

/-- The glued string is the only string with the letters of `f` at the levels of `Q` and the letters
of `g` at the other levels. -/
theorem eq_glue_iff {u : Fin L → α} :
    u = glue Q hQ f g
      ↔ (∀ k, u (Finset.orderEmbOfFin Q hQ k) = f k) ∧ ∀ k, u ((Qᶜ.orderEmbOfFin
        (card_compl_of_card_eq Q hQ)) k) = g k := by
  simp only [funext_iff, forall_level_iff Q hQ, glue_innerLevel, glue_outerLevel]

/-- The two strings can be read off the glued string. -/
theorem glue_inj : glue Q hQ f g = glue Q hQ f' g' ↔ f = f' ∧ g = g' := by
  rw [eq_glue_iff]
  simp only [glue_innerLevel, glue_outerLevel, funext_iff]

/-- A map applied to a glued string, letter by letter. -/
theorem map_glue {β : Type*} (φ : α → β) :
    (fun ℓ => φ (glue Q hQ f g ℓ)) = glue Q hQ (fun k => φ (f k)) (fun k => φ (g k)) := by
  simp only [eq_glue_iff, glue_innerLevel, glue_outerLevel, implies_true, and_self]

/-! ### Alphabets with inner and outer letters -/

variable (IsInner : α → Prop) [DecidablePred IsInner]

/-- If the letters of `f` are inner and those of `g` are outer, then the glued string has its inner
letters exactly at the levels of `Q`. -/
theorem filter_glue (hf : ∀ k, IsInner (f k)) (hg : ∀ k, ¬ IsInner (g k)) :
    (univ.filter fun ℓ => IsInner (glue Q hQ f g ℓ)) = Q := by
  simpa only [filter_eq_iff_forall_level Q hQ, glue_innerLevel, glue_outerLevel] using
    And.intro hf hg

/-- Reconstruct `u` by extracting and reinserting its inner and outer indices. The hypotheses
require that both index projections have the stated reconstruction property on their
respective classes of letters, and that the inner letters of `u` occur exactly on the
size-`m` set `Q`. -/
theorem glue_index {I O : Type*} {inner : I → α} {outer : O → α} {innerIndex : α → I}
    {outerIndex : α → O} (hI : ∀ s, IsInner s → inner (innerIndex s) = s)
    (hO : ∀ s, ¬ IsInner s → outer (outerIndex s) = s) {u : Fin L → α}
    (hu : (univ.filter fun ℓ => IsInner (u ℓ)) = Q) :
    u = glue Q hQ (fun k => inner (innerIndex (u (Finset.orderEmbOfFin Q hQ k))))
      (fun k => outer (outerIndex (u ((Qᶜ.orderEmbOfFin (card_compl_of_card_eq Q hQ)) k)))) := by
  obtain ⟨hin, hout⟩ := (filter_eq_iff_forall_level Q hQ).mp hu
  exact (eq_glue_iff Q hQ).mpr ⟨fun k => (hI _ (hin k)).symm, fun k => (hO _ (hout k)).symm⟩


end Finset
