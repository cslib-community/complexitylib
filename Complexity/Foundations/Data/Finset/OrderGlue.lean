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

* `Finset.glue`: join two functions along a subset and its complement, each enumerated
  by Mathlib's `Finset.orderEmbOfFin`.

## Main results

* `Finset.forall_iff_orderEmbOfFin_and_compl`: split a predicate over the two enumerations.
* `Finset.eq_glue_iff`, `Finset.glue_inj`: reconstruction and uniqueness.
* `Finset.eq_glue_of_reconstruct`: reconstruct values through maps on the two parts.

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

/-! ### Predicates on a subset and its complement -/

/-- A predicate holds everywhere if and only if it holds on the ordered enumerations of
`Q` and its complement. -/
theorem forall_iff_orderEmbOfFin_and_compl {P : Fin L → Prop} :
    (∀ ℓ, P ℓ) ↔ (∀ k, P (Finset.orderEmbOfFin Q hQ k)) ∧ ∀ k, P ((Qᶜ.orderEmbOfFin
      (card_compl_of_card_eq Q hQ)) k) := by
  refine ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩, fun ⟨hin, hout⟩ ℓ => ?_⟩
  by_cases hℓ : ℓ ∈ Q
  · obtain ⟨k, rfl⟩ := (Q.range_orderEmbOfFin hQ).ge hℓ
    exact hin k
  · obtain ⟨k, rfl⟩ := (Qᶜ.range_orderEmbOfFin (card_compl_of_card_eq Q hQ)).ge
      (mem_coe.mpr (mem_compl.mpr hℓ))
    exact hout k

/-- A predicate cuts out `Q` if and only if it holds on its ordered enumeration and fails
on the ordered enumeration of its complement. -/
theorem filter_eq_iff_orderEmbOfFin_and_compl {P : Fin L → Prop} [DecidablePred P] :
    univ.filter P = Q ↔ (∀ k, P (Finset.orderEmbOfFin Q hQ k)) ∧ ∀ k, ¬ P ((Qᶜ.orderEmbOfFin
      (card_compl_of_card_eq Q hQ)) k) := by
  have hcompl (k : Fin (L - m)) :
      Qᶜ.orderEmbOfFin (card_compl_of_card_eq Q hQ) k ∉ Q :=
    mem_compl.mp (Qᶜ.orderEmbOfFin_mem (card_compl_of_card_eq Q hQ) k)
  simp only [Finset.ext_iff, forall_iff_orderEmbOfFin_and_compl Q hQ, mem_filter, mem_univ,
    true_and, Finset.orderEmbOfFin_mem, hcompl, iff_true, iff_false]

/-- A predicate holding on every enumerated element of `Q`, and on `m` elements in all,
cuts out `Q`. -/
theorem filter_eq_of_forall_orderEmbOfFin {P : Fin L → Prop} [DecidablePred P]
    (hin : ∀ k, P (Finset.orderEmbOfFin Q hQ k)) (hcard : (univ.filter P).card = m) : univ.filter
      P = Q := by
  refine (eq_of_subset_of_card_le (fun ℓ hℓ => ?_) (hcard.trans hQ.symm).le).symm
  obtain ⟨k, rfl⟩ := (Q.range_orderEmbOfFin hQ).ge hℓ
  exact mem_filter.mpr ⟨mem_univ _, hin k⟩

/-! ### Gluing functions along an ordered subset -/

variable {α : Type*}

/-- The function taking the values of `f` on `Q` and of `g` on its complement, with each
part enumerated in increasing order. -/
def glue (f : Fin m → α) (g : Fin (L - m) → α) : Fin L → α :=
  fun ℓ =>
    if hℓ : ℓ ∈ Q then f ((Q.orderIsoOfFin hQ).symm ⟨ℓ, hℓ⟩)
    else g ((Qᶜ.orderIsoOfFin (card_compl_of_card_eq Q hQ)).symm ⟨ℓ, mem_compl.mpr hℓ⟩)

/-- Evaluating a glued function on the ordered enumeration of `Q` reads `f`. -/
@[simp]
theorem glue_orderEmbOfFin (f : Fin m → α) (g : Fin (L - m) → α) (k : Fin m) :
    glue Q hQ f g (Finset.orderEmbOfFin Q hQ k) = f k := by
  rw [glue, dite_eq_left (Finset.orderEmbOfFin_mem Q hQ k)]
  exact congrArg f ((OrderIso.symm_apply_eq _).mpr (Subtype.ext rfl))

/-- Evaluating a glued function on the ordered enumeration of the complement reads `g`. -/
@[simp]
theorem glue_orderEmbOfFin_compl (f : Fin m → α) (g : Fin (L - m) → α) (k : Fin (L - m)) :
    glue Q hQ f g ((Qᶜ.orderEmbOfFin (card_compl_of_card_eq Q hQ)) k) = g k := by
  rw [glue, dite_eq_right (mem_compl.mp
    (Qᶜ.orderEmbOfFin_mem (card_compl_of_card_eq Q hQ) k))]
  exact congrArg g ((OrderIso.symm_apply_eq _).mpr (Subtype.ext rfl))

/-- Enumerating a subset equal to `Q` reads the same values from a glued function. -/
theorem glue_orderEmbOfFin_of_eq (f : Fin m → α) (g : Fin (L - m) → α) {Q' : Finset (Fin L)}
    (h : Q' = Q) (hQ' : Q'.card = m) (k : Fin m) : glue Q hQ f g (Finset.orderEmbOfFin Q' hQ' k) =
      f k := by
  subst h
  apply glue_orderEmbOfFin

/-- Enumerating the complement of a subset equal to `Q` reads the same values from a
function glued along `Q`. -/
theorem glue_orderEmbOfFin_compl_of_eq (f : Fin m → α) (g : Fin (L - m) → α) {Q' : Finset (Fin L)}
    (h : Q' = Q) (hQ' : Q'.card = m) (k : Fin (L - m)) :
    glue Q hQ f g ((Q'ᶜ.orderEmbOfFin (card_compl_of_card_eq Q' hQ')) k) = g k := by
  subst h
  apply glue_orderEmbOfFin_compl

variable {f f' : Fin m → α} {g g' : Fin (L - m) → α}

/-- A function is the glued function exactly when its restrictions to both ordered
parts have the stated values. -/
theorem eq_glue_iff {u : Fin L → α} :
    u = glue Q hQ f g
      ↔ (∀ k, u (Finset.orderEmbOfFin Q hQ k) = f k) ∧ ∀ k, u ((Qᶜ.orderEmbOfFin
        (card_compl_of_card_eq Q hQ)) k) = g k := by
  simp only [funext_iff, forall_iff_orderEmbOfFin_and_compl Q hQ, glue_orderEmbOfFin,
    glue_orderEmbOfFin_compl]

/-- Both component functions can be read off their glued function. -/
theorem glue_inj : glue Q hQ f g = glue Q hQ f' g' ↔ f = f' ∧ g = g' := by
  rw [eq_glue_iff]
  simp only [glue_orderEmbOfFin, glue_orderEmbOfFin_compl, funext_iff]

/-- Applying a map to a glued function maps both of its components. -/
theorem map_glue {β : Type*} (φ : α → β) :
    (fun ℓ => φ (glue Q hQ f g ℓ)) = glue Q hQ (fun k => φ (f k)) (fun k => φ (g k)) := by
  simp only [eq_glue_iff, glue_orderEmbOfFin, glue_orderEmbOfFin_compl, implies_true, and_self]

/-! ### Predicates and reconstruction on the two parts -/

variable (P : α → Prop) [DecidablePred P]

/-- If `P` holds on the values of `f` and fails on the values of `g`, it holds on the
glued function exactly at the elements of `Q`. -/
theorem filter_glue (hf : ∀ k, P (f k)) (hg : ∀ k, ¬ P (g k)) :
    (univ.filter fun ℓ => P (glue Q hQ f g ℓ)) = Q := by
  simpa only [filter_eq_iff_orderEmbOfFin_and_compl Q hQ, glue_orderEmbOfFin,
    glue_orderEmbOfFin_compl] using
    And.intro hf hg

/-- Reconstruct `u` from maps that recover its values on the subset defined by `P` and
on its complement. The two reconstruction hypotheses apply on their respective parts. -/
theorem eq_glue_of_reconstruct {β γ : Type*} {fromSubset : β → α} {fromCompl : γ → α}
    {toSubset : α → β} {toCompl : α → γ}
    (hsubset : ∀ a, P a → fromSubset (toSubset a) = a)
    (hcompl : ∀ a, ¬ P a → fromCompl (toCompl a) = a) {u : Fin L → α}
    (hu : (univ.filter fun ℓ => P (u ℓ)) = Q) :
    u = glue Q hQ (fun k => fromSubset (toSubset (u (Finset.orderEmbOfFin Q hQ k))))
      (fun k => fromCompl (toCompl (u ((Qᶜ.orderEmbOfFin (card_compl_of_card_eq Q hQ)) k)))) := by
  obtain ⟨hin, hout⟩ := (filter_eq_iff_orderEmbOfFin_and_compl Q hQ).mp hu
  exact (eq_glue_iff Q hQ).mpr
    ⟨fun k => (hsubset _ (hin k)).symm, fun k => (hcompl _ (hout k)).symm⟩

end Finset
