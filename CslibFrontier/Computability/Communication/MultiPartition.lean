/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Rectangle
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Order.Lattice.Nat

/-!
# Multi-partition rectangle covers

Let `ι` be a finite set of `n` variables. A set of variables `X` is *balanced*
(`MultiPartition.IsBalanced`) when both `X` and its complement have at least `n / 3` elements. A
*balanced rectangle* (`MultiPartition.IsBalancedRectangle`) is a combinatorial rectangle
`Cslib.Circuits.Frontier.rectangle X A B` for some balanced `X`: the inputs whose part on `X` lies
in `A` and whose part on the complement lies in `B`.

The **multi-partition rectangle cover number** of a set of inputs `S`
(`MultiPartition.coverNumber`) is the least number of balanced rectangles, each for its own
balanced partition, whose union is `S`. For a Boolean function `f` and a bit `b`,
`MultiPartition.coverNumberFun b f` is `Cov^m_b(f)` of
[ArenasBroadrickLiewVanDenBroeck2026, Section 3.2]; for a single fixed partition it is the
nondeterministic cover number `Cslib.Communication.Nondeterministic.coverNumberFun`.

A set closed under combining the `X`-part of one member with the rest of another is the rectangle
of its two projections (`MultiPartition.eq_rectangle_of_piecewise_mem`), which is how rectangles
are recognised in practice.

## Main definitions

* `Cslib.Communication.MultiPartition.IsBalanced`,
  `Cslib.Communication.MultiPartition.IsBalancedRectangle`: balanced partitions and rectangles.
* `Cslib.Communication.MultiPartition.IsCover`: a cover by balanced rectangles.
* `Cslib.Communication.MultiPartition.coverNumber`,
  `Cslib.Communication.MultiPartition.coverNumberFun`: the multi-partition cover numbers.

## Main results

* `Cslib.Communication.MultiPartition.eq_rectangle_of_piecewise_mem`: mixing-closed sets are
  rectangles.
* `Cslib.Communication.MultiPartition.exists_isBalanced`: balanced sets exist with two variables.
* `Cslib.Communication.MultiPartition.exists_isCover_card`: the cover by singletons.
* `Cslib.Communication.MultiPartition.IsCover.coverNumber_le`,
  `Cslib.Communication.MultiPartition.le_coverNumber`: bounds through covers.

## References

* [M. Arenas, O. Broadrick, V. Liew, G. Van den Broeck, *d-DNNF is not polynomially closed under
  negation*][ArenasBroadrickLiewVanDenBroeck2026]
* [S. Bova, F. Capelli, S. Mengel, F. Slivovsky, *Knowledge compilation meets communication
  complexity*][BovaCapelliMengelSlivovsky2016]
-/

@[expose] public section

namespace Cslib.Communication.MultiPartition

open Set Cslib.Circuits.Frontier

variable {ι U : Type*}

/-- A set of inputs closed under taking the part on `X` from one member and the rest from another
is the rectangle of its projections. -/
theorem eq_rectangle_of_piecewise_mem [DecidableEq ι] {R : Set (ι → U)} (X : Finset ι)
    (h : ∀ x ∈ R, ∀ y ∈ R, X.piecewise x y ∈ R) :
    R = rectangle (↑X) ((↑X : Set ι).domRestrict '' R) ((↑X : Set ι)ᶜ.domRestrict '' R) := by
  refine subset_antisymm (fun x hx => ⟨⟨x, hx, rfl⟩, x, hx, rfl⟩) ?_
  rintro z ⟨⟨x, hx, hxz⟩, y, hy, hyz⟩
  convert h x hx y hy using 1
  funext i
  by_cases hi : i ∈ X
  · rw [Finset.piecewise_eq_of_mem _ _ _ hi]
    exact (congrFun hxz ⟨i, hi⟩).symm
  · rw [Finset.piecewise_eq_of_notMem _ _ _ hi]
    exact (congrFun hyz ⟨i, hi⟩).symm

variable [Fintype ι]

/-- A set of variables is **balanced** when it and its complement each have at least a third of
the variables. -/
def IsBalanced [DecidableEq ι] (X : Finset ι) : Prop :=
  Fintype.card ι ≤ 3 * X.card ∧ Fintype.card ι ≤ 3 * Xᶜ.card

instance [DecidableEq ι] : DecidablePred (IsBalanced (ι := ι)) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- A **balanced rectangle**: a combinatorial rectangle for the partition of the variables into a
balanced set `X` and its complement. -/
def IsBalancedRectangle [DecidableEq ι] (R : Set (ι → U)) : Prop :=
  ∃ X : Finset ι, IsBalanced X ∧ ∃ A B, R = rectangle (↑X) A B

/-- A family of `k` sets is a **multi-partition cover** of `S` when each is a balanced rectangle,
possibly for different partitions, and their union is `S`. -/
def IsCover [DecidableEq ι] (S : Set (ι → U)) {k : ℕ} (R : Fin k → Set (ι → U)) : Prop :=
  (∀ i, IsBalancedRectangle (R i)) ∧ ⋃ i, R i = S

/-- The **multi-partition rectangle cover number** of `S`: the least number of balanced
rectangles whose union is `S` (`0` if there is no such cover, which happens only with fewer than
two variables). -/
noncomputable def coverNumber [DecidableEq ι] (S : Set (ι → U)) : ℕ :=
  sInf {k | ∃ R : Fin k → Set (ι → U), IsCover S R}

/-- The **multi-partition rectangle `b`-cover number** `Cov^m_b(f)` of a Boolean function:
the multi-partition cover number of `f⁻¹(b)`. -/
noncomputable abbrev coverNumberFun [DecidableEq ι] (b : Bool) (f : (ι → Bool) → Bool) : ℕ :=
  coverNumber (f ⁻¹' {b})

variable [DecidableEq ι]

/-- A set closed under mixing along a balanced `X` is a balanced rectangle. -/
theorem isBalancedRectangle_of_piecewise_mem {R : Set (ι → U)} {X : Finset ι} (hX : IsBalanced X)
    (h : ∀ x ∈ R, ∀ y ∈ R, X.piecewise x y ∈ R) : IsBalancedRectangle R :=
  ⟨X, hX, _, _, eq_rectangle_of_piecewise_mem X h⟩

/-- The empty set is a balanced rectangle once some balanced set exists. -/
theorem isBalancedRectangle_empty {X : Finset ι} (hX : IsBalanced X) :
    IsBalancedRectangle (∅ : Set (ι → U)) :=
  isBalancedRectangle_of_piecewise_mem hX fun _ hx => hx.elim

/-- **Balanced sets exist** between `s` and `t` once there are at least two variables, `s` has at
most about a third of them and `t` at least a third. -/
theorem exists_isBalanced (hn : 2 ≤ Fintype.card ι) {s t : Finset ι} (hst : s ⊆ t)
    (hs : 3 * s.card ≤ Fintype.card ι + 2) (ht : Fintype.card ι ≤ 3 * t.card) :
    ∃ X, s ⊆ X ∧ X ⊆ t ∧ IsBalanced X := by
  set n := Fintype.card ι
  obtain ⟨X, hsX, hXt, hX⟩ := Finset.exists_subsuperset_card_eq hst
    (le_max_left s.card ((n + 2) / 3))
    (max_le (Finset.card_le_card hst) (by omega))
  refine ⟨X, hsX, hXt, ?_, ?_⟩
  · rw [hX]; omega
  · rw [Finset.card_compl, hX]; omega

/-- **Covers by singletons.** With at least two variables, every finite set of inputs is covered
by its singletons, each a balanced rectangle. -/
theorem exists_isCover_card [Fintype U] (hn : 2 ≤ Fintype.card ι)
    (S : Set (ι → U)) [DecidablePred (· ∈ S)] :
    ∃ R : Fin (Finset.univ.filter (· ∈ S)).card → Set (ι → U), IsCover S R := by
  obtain ⟨X, -, -, hX⟩ := exists_isBalanced hn (Finset.empty_subset Finset.univ) (by simp)
    (by simp; omega)
  set T := Finset.univ.filter (· ∈ S)
  refine ⟨fun i => {(T.equivFin.symm i : ι → U)}, fun i =>
    isBalancedRectangle_of_piecewise_mem hX fun x hx y hy => ?_, ?_⟩
  · rw [Set.mem_singleton_iff] at hx hy ⊢
    rw [hx, hy, Finset.piecewise_same]
  · ext x
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      exact (Finset.mem_filter.mp (T.equivFin.symm i).2).2
    · intro hx
      exact ⟨T.equivFin ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩, by simp⟩

/-- A cover bounds the cover number from above. -/
theorem IsCover.coverNumber_le {S : Set (ι → U)} {k : ℕ} {R : Fin k → Set (ι → U)}
    (h : IsCover S R) : coverNumber S ≤ k :=
  Nat.sInf_le (m := k) ⟨R, h⟩

/-- If some cover exists and every cover has at least `m` rectangles, the cover number is at
least `m`. -/
theorem le_coverNumber {S : Set (ι → U)} {m : ℕ}
    (hex : ∃ k, ∃ R : Fin k → Set (ι → U), IsCover S R)
    (h : ∀ k (R : Fin k → Set (ι → U)), IsCover S R → m ≤ k) : m ≤ coverNumber S := by
  obtain ⟨R, hR⟩ := Nat.sInf_mem (s := {k | ∃ R : Fin k → Set (ι → U), IsCover S R}) hex
  exact h (coverNumber S) R hR

end Cslib.Communication.MultiPartition
