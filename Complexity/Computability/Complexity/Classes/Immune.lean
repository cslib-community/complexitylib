/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P.Closure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership

/-!
# Immune and bi-immune sets

A set `A` is **immune** to a class `C` of sets (`Cslib.Complexity.IsImmune`) when it is infinite
and every member of `C` contained in `A` is finite. `A` is **bi-immune** to `C`
(`Cslib.Complexity.IsBiImmune`) when both `A` and its complement are immune to `C`. For
`C = P`, a `P`-immune set has no infinite subset decidable in polynomial time. A `P`-bi-immune set
cannot be told apart from its complement on any infinite polynomial-time decidable set of
instances [Balcázar and Schöning][BalcazarSchoening1985].

For a class containing the universe and closed under removing finite sets, such as `P`
(`Set.Finite.mem_P`), bi-immunity says that every infinite member of the class meets both `A` and
its complement (`Cslib.Complexity.isBiImmune_iff_of_sdiff_finite`,
`Cslib.Complexity.isBiImmune_P_iff`). Diagonalization constructions use this form.

A `P`-bi-immune problem in `E` is constructed in
`Complexity.Computability.Complexity.Classes.Immune.Construction`. Berman's theorem, that
problems complete for `E` or `EXP` are not `P`-immune, is in
`Complexity.Computability.Complexity.Classes.Immune.Complete`.

## Main definitions

* `Cslib.Complexity.IsImmune`: infinite, with only finite subsets in the class.
* `Cslib.Complexity.IsBiImmune`: immune, with an immune complement.

## Main results

* `Cslib.Complexity.IsImmune.mono`, `Cslib.Complexity.IsBiImmune.mono`: immunity to a class gives
  immunity to every subclass.
* `Cslib.Complexity.IsImmune.notMem`: an immune set is not in the class.
* `Cslib.Complexity.isBiImmune_compl`: bi-immunity is invariant under complement.
* `Cslib.Complexity.isImmune_iff_sdiff_nonempty`, `Cslib.Complexity.isBiImmune_iff_nonempty`: every
  infinite member of the class leaves the set, or meets it and leaves it.
* `Cslib.Complexity.isBiImmune_iff_of_sdiff_finite`, `Cslib.Complexity.isBiImmune_P_iff`: for a
  class containing the universe and closed under removing finite sets, the infiniteness conditions
  are automatic.
* `Set.Finite.mem_P`: finite problems are in `P`.

## References

* [J. L. Balcázar, U. Schöning, *Bi-immune sets for complexity classes*][BalcazarSchoening1985]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type*}

/-- `A` is **immune** to the class `C`: `A` is infinite and every member of `C` contained in `A`
is finite [Balcázar and Schöning][BalcazarSchoening1985]. -/
def IsImmune (C : Set (Set α)) (A : Set α) : Prop :=
  A.Infinite ∧ ∀ B ∈ C, B ⊆ A → B.Finite

/-- `A` is **bi-immune** to the class `C`: both `A` and its complement are immune to `C`
[Balcázar and Schöning][BalcazarSchoening1985]. -/
def IsBiImmune (C : Set (Set α)) (A : Set α) : Prop :=
  IsImmune C A ∧ IsImmune C Aᶜ

variable {C D : Set (Set α)} {A : Set α}

theorem isImmune_iff : IsImmune C A ↔ A.Infinite ∧ ∀ B ∈ C, B ⊆ A → B.Finite := Iff.rfl

theorem isBiImmune_iff : IsBiImmune C A ↔ IsImmune C A ∧ IsImmune C Aᶜ := Iff.rfl

theorem IsImmune.infinite (h : IsImmune C A) : A.Infinite := h.1

theorem IsImmune.finite_of_subset (h : IsImmune C A) {B : Set α} (hB : B ∈ C) (hBA : B ⊆ A) :
    B.Finite :=
  h.2 B hB hBA

/-- Immunity to a class gives immunity to every subclass. -/
theorem IsImmune.mono (h : IsImmune C A) (hDC : D ⊆ C) : IsImmune D A :=
  ⟨h.1, fun B hB => h.2 B (hDC hB)⟩

/-- **An immune set is not in the class.** -/
theorem IsImmune.notMem (h : IsImmune C A) : A ∉ C := fun hA => h.1 (h.2 A hA le_rfl)

/-- Infinite subsets of immune sets are immune. -/
theorem IsImmune.subset {A' : Set α} (h : IsImmune C A) (hA' : A'.Infinite) (hA'A : A' ⊆ A) :
    IsImmune C A' :=
  ⟨hA', fun B hB hBA => h.2 B hB (hBA.trans hA'A)⟩

/-- `A` is immune to `C` when it is infinite and every infinite member of `C` leaves `A`. -/
theorem isImmune_iff_sdiff_nonempty :
    IsImmune C A ↔ A.Infinite ∧ ∀ B ∈ C, B.Infinite → (B \ A).Nonempty := by
  refine and_congr_right fun _ => forall₂_congr fun B _ => ?_
  rw [Set.sdiff_nonempty, ← not_imp_not]
  rfl

theorem IsBiImmune.isImmune (h : IsBiImmune C A) : IsImmune C A := h.1

theorem IsBiImmune.isImmune_compl (h : IsBiImmune C A) : IsImmune C Aᶜ := h.2

theorem IsBiImmune.compl (h : IsBiImmune C A) : IsBiImmune C Aᶜ :=
  ⟨h.2, by rw [compl_compl]; exact h.1⟩

/-- **Bi-immunity is invariant under complement.** -/
@[simp]
theorem isBiImmune_compl : IsBiImmune C Aᶜ ↔ IsBiImmune C A :=
  ⟨fun h => by simpa using h.compl, IsBiImmune.compl⟩

/-- Bi-immunity to a class gives bi-immunity to every subclass. -/
theorem IsBiImmune.mono (h : IsBiImmune C A) (hDC : D ⊆ C) : IsBiImmune D A :=
  ⟨h.1.mono hDC, h.2.mono hDC⟩

/-- The complement of a bi-immune set is not in the class. -/
theorem IsBiImmune.compl_notMem (h : IsBiImmune C A) : Aᶜ ∉ C := h.2.notMem

/-- `A` is bi-immune to `C` when `A` and its complement are infinite and every infinite member of
`C` meets `A` and leaves it. -/
theorem isBiImmune_iff_nonempty :
    IsBiImmune C A ↔ A.Infinite ∧ Aᶜ.Infinite ∧
      ∀ B ∈ C, B.Infinite → (B ∩ A).Nonempty ∧ (B \ A).Nonempty := by
  rw [IsBiImmune, isImmune_iff_sdiff_nonempty, isImmune_iff_sdiff_nonempty]
  simp only [Set.sdiff_compl]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    exact ⟨h₁, h₃, fun B hB hBi => ⟨h₄ B hB hBi, h₂ B hB hBi⟩⟩
  · rintro ⟨h₁, h₃, h⟩
    exact ⟨⟨h₁, fun B hB hBi => (h B hB hBi).2⟩, h₃, fun B hB hBi => (h B hB hBi).1⟩

/-- **Bi-immunity by meeting and leaving.** If `C` contains the universe and is closed under
removing finite sets, `A` is bi-immune to `C` exactly when every infinite member of `C` meets `A`
and leaves it. -/
theorem isBiImmune_iff_of_sdiff_finite [Infinite α] (huniv : Set.univ ∈ C)
    (hsdiff : ∀ B ∈ C, ∀ F : Set α, F.Finite → B \ F ∈ C) :
    IsBiImmune C A ↔ ∀ B ∈ C, B.Infinite → (B ∩ A).Nonempty ∧ (B \ A).Nonempty := by
  rw [isBiImmune_iff_nonempty]
  refine ⟨fun h => h.2.2, fun h => ⟨fun hA => ?_, fun hA => ?_, h⟩⟩
  · obtain ⟨x, hx₁, hx₂⟩ := (h _ (hsdiff _ huniv _ hA) (Set.infinite_univ.sdiff hA)).1
    exact hx₁.2 hx₂
  · obtain ⟨x, hx₁, hx₂⟩ := (h _ (hsdiff _ huniv _ hA) (Set.infinite_univ.sdiff hA)).2
    exact hx₂ (by simpa using hx₁.2)

/-- **Finite problems are in `P`**, decided by comparing the encoded instance with the encodings
of the finitely many members. -/
theorem _root_.Set.Finite.mem_P {β : Type} {enc : β ↪ List Bool} {F : Set β} (hF : F.Finite) :
    F ∈ P enc := by
  classical
  refine ⟨fun b => decide (enc b ∈ hF.toFinset.toList.map enc), ?_, fun b => ?_⟩
  · have : ComputableInPolyTime (fun b : β => enc b) enc encBits := .of_eq fun _ => rfl
    fun_prop
  · simp

/-- **`P`-bi-immunity by meeting and leaving**: `A` is `P`-bi-immune exactly when every infinite
problem in `P` meets `A` and leaves it. -/
theorem isBiImmune_P_iff {β : Type} [Infinite β] {enc : β ↪ List Bool} {A : Set β} :
    IsBiImmune (P enc) A ↔ ∀ B ∈ P enc, B.Infinite → (B ∩ A).Nonempty ∧ (B \ A).Nonempty :=
  isBiImmune_iff_of_sdiff_finite univ_mem_P fun _ hB _ hF => diff_mem_P hB hF.mem_P

end Cslib.Complexity
