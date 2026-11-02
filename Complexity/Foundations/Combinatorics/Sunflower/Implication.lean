/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Implication of sets and the Alon–Boppana family bound

Alon and Boppana say that sets `W₁, …, W_r`, not necessarily distinct, *imply* a set `W` when all
their pairwise intersections lie in `W` (`Cslib.ImpliedBy`). Sunflowers with `r` petals imply
their core, and a single set implies every superset of itself.

A family is *implication-minimal* (`Cslib.IsImplicationMinimal`) when no member strictly contains a
set implied by `r` members. The minimal sets of a family closed under implication are such a
family. Alon and Boppana show that an implication-minimal family of sets of at most `k` elements has
at most `(r - 1) ^ k` members (`Cslib.card_le_pow_of_isImplicationMinimal`), without the factor
`k!` of the Erdős–Rado sunflower bound (`Cslib.sunflowerBound`)
[Alon and Boppana, Lemma 3.2][AlonBoppana1987]. The proof is by induction on `r`: fix a member
`D`, split the family according to the trace `C = W ∩ D`, and remove `C`; each part is
implication-minimal for `r - 1`, since `D` supplies the missing set.

## Main definitions

* `Cslib.ImpliedBy`: a set is implied by `r` members of a family.
* `Cslib.IsImplicationMinimal`: no member strictly contains a set implied by `r` members.

## Main results

* `Cslib.card_le_pow_of_isImplicationMinimal`: the Alon–Boppana bound `(r - 1) ^ k`.

## References

* [N. Alon, R. B. Boppana, *The monotone circuit complexity of Boolean functions*,
  Section 3.2][AlonBoppana1987]
-/

@[expose] public section

namespace Cslib

open Finset

variable {α : Type*} [DecidableEq α]

/-- `W` is *implied* by `r` members of `F`: there are `r` members of `F`, not necessarily distinct,
whose pairwise intersections all lie in `W` [Alon and Boppana, Section 3.1][AlonBoppana1987]. -/
def ImpliedBy (r : ℕ) (F : Finset (Finset α)) (W : Finset α) : Prop :=
  ∃ V : Fin r → Finset α, (∀ i, V i ∈ F) ∧ ∀ i j, i ≠ j → V i ∩ V j ⊆ W

/-- A member of a family implies each of its supersets. -/
theorem impliedBy_of_subset {r : ℕ} {F : Finset (Finset α)} {V W : Finset α} (hV : V ∈ F)
    (hVW : V ⊆ W) : ImpliedBy r F W :=
  ⟨fun _ => V, fun _ => hV, fun _ _ _ => inter_subset_left.trans hVW⟩

/-- Implication is monotone in the family. -/
theorem ImpliedBy.mono {r : ℕ} {F G : Finset (Finset α)} {W : Finset α} (h : ImpliedBy r F W)
    (hFG : F ⊆ G) : ImpliedBy r G W :=
  let ⟨V, hV, hVW⟩ := h
  ⟨V, fun i => hFG (hV i), hVW⟩

/-- A family is *implication-minimal* for `r` when no member strictly contains a set implied by `r`
members [Alon and Boppana, property (ii) of `P(r, k)`][AlonBoppana1987]. -/
def IsImplicationMinimal (r : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ W ∈ F, ∀ U, U ⊂ W → ¬ImpliedBy r F U

/-- An implication-minimal family for `2` has at most one member: two distinct members imply their
intersection, which is strictly contained in one of them. -/
private theorem card_le_one_of_isImplicationMinimal_two {F : Finset (Finset α)}
    (hF : IsImplicationMinimal 2 F) : F.card ≤ 1 := by
  refine card_le_one.2 fun a ha b hb => ?_
  by_contra hab
  have himp : ImpliedBy 2 F (a ∩ b) := by
    refine ⟨![a, b], fun i => by fin_cases i <;> simpa, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> simp_all [inter_comm]
  by_cases hUa : a ∩ b = a
  · have hab' : a ∩ b ⊂ b := ssubset_of_subset_of_ne inter_subset_right fun h => hab (hUa ▸ h)
    exact hF b hb _ hab' himp
  · exact hF a ha _ (ssubset_of_subset_of_ne inter_subset_left hUa) himp

/-- Splitting by the trace on a member `D ∈ F` and removing it keeps implication-minimality, with
one implying set fewer: `D` supplies the last one. -/
private theorem isImplicationMinimal_image_sdiff {r : ℕ} {F : Finset (Finset α)}
    (hF : IsImplicationMinimal (r + 1) F) {D : Finset α} (hD : D ∈ F) (C : Finset α) :
    IsImplicationMinimal r ((F.filter (· ∩ D = C)).image (· \ C)) := by
  rintro _ hW' U' hU' ⟨V', hV', hV'U'⟩
  obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
  obtain ⟨hWF, hWD⟩ := mem_filter.1 hW
  choose X hX hXV' using fun i => mem_image.1 (hV' i)
  have hXF i := (mem_filter.1 (hX i)).1
  have hXD i := (mem_filter.1 (hX i)).2
  have hCW : C ⊆ W := hWD ▸ inter_subset_left
  refine hF W hWF (U' ∪ C) ?_
    ⟨Fin.snoc (α := fun _ => Finset α) X D, fun i => ?_, fun i j hij => ?_⟩
  · obtain ⟨x, hxW, hxU⟩ := exists_of_ssubset hU'
    refine (ssubset_iff_of_subset (union_subset (hU'.1.trans sdiff_subset) hCW)).2
      ⟨x, (mem_sdiff.1 hxW).1, ?_⟩
    rw [mem_union, not_or]
    exact ⟨hxU, (mem_sdiff.1 hxW).2⟩
  · induction i using Fin.lastCases with
    | last => simpa using hD
    | cast i => simpa using hXF i
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [inter_comm, hXD j]
        exact subset_union_right
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [hXD i]
        exact subset_union_right
      | cast j =>
        simp only [Fin.snoc_castSucc]
        intro x hx
        by_cases hxC : x ∈ C
        · exact mem_union_right _ hxC
        · refine mem_union_left _ (hV'U' i j (fun h => hij (by rw [h])) ?_)
          rw [← hXV' i, ← hXV' j]
          exact mem_inter.2 ⟨mem_sdiff.2 ⟨(mem_inter.1 hx).1, hxC⟩,
            mem_sdiff.2 ⟨(mem_inter.1 hx).2, hxC⟩⟩

/-- **The Alon–Boppana family bound.** An implication-minimal family for `r ≥ 2` of sets of at most
`k` elements has at most `(r - 1) ^ k` members [Alon and Boppana, Lemma 3.2][AlonBoppana1987]. -/
theorem card_le_pow_of_isImplicationMinimal {r k : ℕ} (hr : 2 ≤ r) {F : Finset (Finset α)}
    (hk : ∀ W ∈ F, W.card ≤ k) (hF : IsImplicationMinimal r F) : F.card ≤ (r - 1) ^ k := by
  induction r, hr using Nat.le_induction generalizing k F with
  | base => simpa using card_le_one_of_isImplicationMinimal_two hF
  | succ r hr ih =>
    rw [Nat.add_sub_cancel]
    obtain rfl | ⟨D, hD⟩ := F.eq_empty_or_nonempty
    · simp
    have hDk := hk D hD
    have hfiber (C : Finset α) (hC : C ∈ D.powerset) :
        (F.filter (· ∩ D = C)).card ≤ (r - 1) ^ (k - C.card) := by
      rw [← card_image_of_injOn (f := (· \ C)) fun W hW W' hW' h => by
        have hW := (mem_filter.1 hW).2
        have hW' := (mem_filter.1 hW').2
        simp only at h
        rw [← sdiff_union_of_subset (hW ▸ inter_subset_left : C ⊆ W),
          ← sdiff_union_of_subset (hW' ▸ inter_subset_left : C ⊆ W'), h]]
      refine ih (fun W' hW' => ?_) (isImplicationMinimal_image_sdiff hF hD C)
      obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
      obtain ⟨hWF, hWD⟩ := mem_filter.1 hW
      rw [card_sdiff_of_subset (hWD ▸ inter_subset_left)]
      exact Nat.sub_le_sub_right (hk W hWF) _
    calc F.card = ∑ C ∈ D.powerset, (F.filter (· ∩ D = C)).card :=
          card_eq_sum_card_fiberwise fun W _ => mem_powerset.2 inter_subset_right
      _ ≤ ∑ C ∈ D.powerset, (r - 1) ^ (k - D.card) * (1 ^ C.card * (r - 1) ^ (D.card - C.card)) :=
          sum_le_sum fun C hC => by
            rw [one_pow, one_mul, ← pow_add]
            refine (hfiber C hC).trans_eq (congrArg _ ?_)
            have := card_le_card (mem_powerset.1 hC)
            omega
      _ = (r - 1) ^ (k - D.card) * r ^ D.card := by
          rw [← mul_sum, sum_pow_mul_eq_add_pow]
          congr 2
          omega
      _ ≤ r ^ (k - D.card) * r ^ D.card :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
      _ = r ^ k := by rw [← pow_add, Nat.sub_add_cancel hDk]

end Cslib
