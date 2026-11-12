/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable
import CslibFrontier.Computability.Complexity.Classes.P.Closure
import CslibFrontier.Computability.Complexity.Classes.P.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Unpair

/-!
# Recursively presentable classes and finite-variation closure

Schöning's uniform diagonalization theorem [Schöning][Schoening1982] separates two complexity
classes whenever each is **recursively presentable** (`Cslib.Complexity.RecursivelyPresentable`)
and **closed under finite variations** (`Cslib.Complexity.ClosedUnderFiniteVariation`). A class of
sets is recursively presentable when it is the range `i ↦ {a | F (i, a) = true}` of a total
computable Boolean function `F` taking the index `i` in unary; because `ℕ` is nonempty, the empty
class is excluded. Closure under finite variations means closure under finite symmetric
differences.

This module isolates the two predicates and their basic closure properties from the delayed
diagonalization construction of
`CslibFrontier.Computability.Complexity.Classes.UniformDiagonalization`, while
`CslibFrontier.Computability.Complexity.Classes.RecursivelyPresentable.PolyTime` presents `P`,
polynomial-time transducers, and lower `≤ₘᵖ`-cones without importing that construction. As a
result, `CslibFrontier.Computability.Complexity.Classes.RecursivelyPresentable.Classes` need not
import delayed diagonalization; `CslibFrontier.Computability.Complexity.Classes.Ladner.Density`
imports `UniformDiagonalization` to construct intermediate degrees.

## Main definitions

* `Cslib.Complexity.RecursivelyPresentable`: classes of the form `{a | F (i, a) = true}` for a
  computable `F`, with the index `i` in unary.
* `Cslib.Complexity.ClosedUnderFiniteVariation`: closure under finite symmetric differences.

## Main results

* `Cslib.Complexity.exists_notMem_and_mem_of_notMem_P`: a problem outside `P` has both a non-member
  and a member.
* `Cslib.Complexity.ClosedUnderFiniteVariation.infinite_symmDiff`: a set outside a class closed
  under finite variations is infinitely different from every member.
* `Cslib.Complexity.ClosedUnderFiniteVariation.compl`,
  `Cslib.Complexity.ClosedUnderFiniteVariation.of_inter_union_mem_P`,
  `Cslib.Complexity.closedUnderFiniteVariation_P`: closure under finite variations for complement
  classes, classes closed under intersection and union with `P`, and `P` itself.
* `Cslib.Complexity.RecursivelyPresentable.compl`,
  `Cslib.Complexity.RecursivelyPresentable.iUnion_of_isComputable`: recursive presentability passes
  to complement classes and uniformly computable countable unions.

## References

* [U. Schöning, *A uniform approach to obtain diagonal sets in complexity
  classes*][Schoening1982]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM
open scoped symmDiff

/-- A class of sets is **recursively presentable** when it is the class of the sets
`{a | F (i, a) = true}`, `i : ℕ`, for a computable `F`. Such a class is nonempty, so the empty class
is not recursively presentable. -/
@[expose] def RecursivelyPresentable {α : Type} (enc : α ↪ List Bool) (C : Set (Set α)) : Prop :=
  ∃ F : ℕ × α → Bool, IsComputable F (encPair encUnary enc) encBool ∧
    C = Set.range fun i => {a | F (i, a) = true}

/-- A class of sets is **closed under finite variations** when it contains every set finitely
different from one of its members. -/
@[expose] def ClosedUnderFiniteVariation {α : Type} (C : Set (Set α)) : Prop :=
  ∀ ⦃L L' : Set α⦄, L ∈ C → (L ∆ L').Finite → L' ∈ C

/-- A problem outside `P` is neither `∅` nor `Set.univ`, so it has a non-member and a member. -/
theorem exists_notMem_and_mem_of_notMem_P {α : Type} {enc : α ↪ List Bool} {B : Set α}
    (hB : B ∉ P enc) : (∃ y₀, y₀ ∉ B) ∧ (∃ y₁, y₁ ∈ B) := by
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hB ((Set.eq_univ_of_forall fun y => not_not.mp fun hy => h ⟨y, hy⟩) ▸ univ_mem_P)
  · by_contra h
    have heq : B = ∅ := Set.ext fun y => ⟨fun hy => absurd ⟨y, hy⟩ h, False.elim⟩
    exact hB (heq ▸ empty_mem_P)

/-- A set outside a class closed under finite variations is infinitely different from each of its
members. -/
theorem ClosedUnderFiniteVariation.infinite_symmDiff {α : Type} {C : Set (Set α)}
    (hC : ClosedUnderFiniteVariation C) {A L : Set α} (hA : A ∉ C) (hL : L ∈ C) :
    (A ∆ L).Infinite :=
  fun hfin => hA (hC hL (symmDiff_comm A L ▸ hfin))

/-- Closure under finite variations passes to the complement class `compl ⁻¹' C`. -/
theorem ClosedUnderFiniteVariation.compl {α : Type} {C : Set (Set α)}
    (hC : ClosedUnderFiniteVariation C) : ClosedUnderFiniteVariation (compl ⁻¹' C) := by
  intro L L' hL hfin
  have hsymm : Lᶜ ∆ L'ᶜ = L ∆ L' := by
    ext x
    simp only [Set.mem_symmDiff, Set.mem_compl_iff]
    tauto
  exact hC hL (hsymm ▸ hfin)

/-- Any class closed under intersection and union with problems in `P` is closed under finite
variations: `L' = (L ∩ (L ∆ L')ᶜ) ∪ ((L ∆ L') \ L)`, and finite sets belong to `P`. -/
theorem ClosedUnderFiniteVariation.of_inter_union_mem_P {α : Type} {enc : α ↪ List Bool}
    {C : Set (Set α)} (hinter : ∀ ⦃L M⦄, L ∈ C → M ∈ P enc → L ∩ M ∈ C)
    (hunion : ∀ ⦃L M⦄, L ∈ C → M ∈ P enc → L ∪ M ∈ C) :
    ClosedUnderFiniteVariation C := by
  intro L L' hL hfin
  have h₁ : (L ∆ L')ᶜ ∈ P enc := compl_mem_P hfin.mem_P
  have h₂ : (L ∆ L') \ L ∈ P enc := (hfin.subset Set.sdiff_subset).mem_P
  have heq : L' = L ∩ (L ∆ L')ᶜ ∪ (L ∆ L') \ L := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff,
      Set.mem_symmDiff]
    tauto
  exact heq ▸ hunion (hinter hL h₁) h₂

/-- **`P` is closed under finite variations.** -/
theorem closedUnderFiniteVariation_P {α : Type} (enc : α ↪ List Bool) :
    ClosedUnderFiniteVariation (P enc) := fun L L' hL hfin =>
  symmDiff_symmDiff_cancel_left L L' ▸ symmDiff_mem_P hL hfin.mem_P

/-- Recursive presentability passes to the complement class `compl ⁻¹' C` by negating the
presentation. -/
theorem RecursivelyPresentable.compl {α : Type} {enc : α ↪ List Bool} {C : Set (Set α)}
    (hC : RecursivelyPresentable enc C) : RecursivelyPresentable enc (compl ⁻¹' C) := by
  obtain ⟨F, hF, rfl⟩ := hC
  refine ⟨fun p => !F p,
    (IsComputable.of_finite (encIn := encBool) (encMid := encBool) Bool.not).comp hF, ?_⟩
  ext A
  simp only [Set.mem_preimage, Set.mem_range, Bool.not_eq_true']
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    ext a
    have ha := Set.ext_iff.mp hi a
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff] at ha ⊢
    cases h : F (i, a) <;> simp_all
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    cases F (i, a) <;> simp

/-- A countable union `⋃ k, C k` of classes uniformly presented by one computable function of
`((k, i), a)` is recursively presentable via `Nat.unpair`. -/
theorem RecursivelyPresentable.iUnion_of_isComputable {α : Type} {enc : α ↪ List Bool}
    {C : ℕ → Set (Set α)} {F : (ℕ × ℕ) × α → Bool}
    (hF : IsComputable F (encPair (encPair encUnary encUnary) enc) encBool)
    (hC : ∀ k, C k = Set.range fun i => {a | F ((k, i), a) = true}) :
    RecursivelyPresentable enc (⋃ k, C k) := by
  have hunpair : ComputableInPolyTime (fun p : ℕ × α => (p.1.unpair, p.2))
      (encPair encUnary enc) (encPair (encPair encUnary encUnary) enc) :=
    (ComputableInPolyTime.unary_unpair.comp (.fst encUnary enc)).prod (.snd encUnary enc)
  obtain ⟨_, _, _, _, hunpair'⟩ := hunpair
  refine ⟨fun p => F (p.1.unpair, p.2), hF.comp hunpair'.isComputable, ?_⟩
  ext A
  simp only [Set.mem_iUnion, hC, Set.mem_range]
  constructor
  · rintro ⟨k, i, rfl⟩
    exact ⟨Nat.pair k i, by simp only [Nat.unpair_pair]⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m.unpair.1, m.unpair.2, rfl⟩

end Cslib.Complexity
