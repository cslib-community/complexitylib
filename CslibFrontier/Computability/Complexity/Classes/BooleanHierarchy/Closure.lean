/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BooleanHierarchy
public import CslibFrontier.Foundations.Order.BooleanSubalgebra
import CslibFrontier.Computability.Complexity.Classes.NP.Witness

/-!
# Boolean closure of the Boolean hierarchy

Finite nested differences over a class closed under union and intersection are closed under
intersection and difference, with explicit (not necessarily optimal) level bounds. If the base
contains the universe, their union is also closed under union. Applied to NP, this proves the
Boolean closure of `BooleanHierarchy` [Cai et al.][CaiEtAl1988].

## Main results

* `inter_mem_differenceHierarchy`, `diff_mem_differenceHierarchy`: intersections of levels `n`
  and `m` belong to level `n * m`; differences belong to level `n * (m + 1)`.
* `inter_mem_BH`, `diff_mem_BH`, `union_mem_BH`: explicit finite-level closure bounds over NP.
* `inter_mem_BooleanHierarchy`, `diff_mem_BooleanHierarchy`, `union_mem_BooleanHierarchy`,
  `symmDiff_mem_BooleanHierarchy`: closure of the full Boolean hierarchy.

## References

* [J.-Y. Cai et al., *The Boolean Hierarchy I: Structural Properties*][CaiEtAl1988]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type*} {C : Set (Set α)}

/-- Pasting a hierarchy set into a base-class region can be implemented by nested differences. -/
private theorem paste_mem_differenceHierarchy
    (hU : ∀ E ∈ C, ∀ F ∈ C, E ∪ F ∈ C) {n m : ℕ} {A B E : Set α}
    (hA : A ∈ differenceHierarchy C n) (hB : B ∈ differenceHierarchy C m)
    (hE : E ∈ C) (hBE : B ⊆ E) :
    (A \ E) ∪ B ∈ differenceHierarchy C (2 * n + m) := by
  induction n generalizing m A B with
  | zero =>
    have h : A = ∅ := hA
    subst h
    simpa using hB
  | succ n ih =>
    obtain ⟨F, hF, D, hD, rfl⟩ := hA
    have hp := ih hD (show E \ B ∈ differenceHierarchy C (m + 1) from
      ⟨E, hE, B, hB, rfl⟩) Set.sdiff_subset
    have heq : ((F \ D) \ E) ∪ B = (F ∪ E) \ ((D \ E) ∪ (E \ B)) := by
      ext a
      have := @hBE a
      simp only [Set.mem_union, Set.mem_sdiff] at *
      tauto
    rw [heq]
    have hn : 2 * (n + 1) + m = (2 * n + (m + 1)) + 1 := by omega
    rw [hn]
    exact ⟨F ∪ E, hU F hF E hE, _, hp, rfl⟩

private theorem inter_and_diff_mem_differenceHierarchy
    (hU : ∀ E ∈ C, ∀ F ∈ C, E ∪ F ∈ C)
    (hI : ∀ E ∈ C, ∀ F ∈ C, E ∩ F ∈ C) {n m : ℕ} {A B : Set α}
    (hA : A ∈ differenceHierarchy C n) (hB : B ∈ differenceHierarchy C m) :
    A ∩ B ∈ differenceHierarchy C (n * m) ∧
      A \ B ∈ differenceHierarchy C (n * (m + 1)) := by
  induction m generalizing A B with
  | zero =>
    have h : B = ∅ := hB
    subst h
    simpa using And.intro (show (∅ : Set α) ∈ differenceHierarchy C 0 from rfl) hA
  | succ m ih =>
    obtain ⟨E, hE, D, hD, rfl⟩ := hB
    constructor
    · have h := (ih (inter_mem_differenceHierarchy_right hI hA hE) hD).2
      have heq : A ∩ (E \ D) = (A ∩ E) \ D := by
        ext a
        simp only [Set.mem_inter_iff, Set.mem_sdiff]
        tauto
      rwa [heq]
    · have h := inter_mem_differenceHierarchy_right hI (ih hA hD).1 hE
      have hp := paste_mem_differenceHierarchy hU hA h hE Set.inter_subset_right
      have heq : A \ (E \ D) = (A \ E) ∪ ((A ∩ D) ∩ E) := by
        ext a
        simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_union]
        tauto
      rw [heq]
      simpa only [Nat.mul_add, Nat.mul_one, two_mul, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hp

/-- Intersecting levels `n` and `m` over a lattice of sets costs at most `n * m` levels. -/
theorem inter_mem_differenceHierarchy
    (hU : ∀ E ∈ C, ∀ F ∈ C, E ∪ F ∈ C)
    (hI : ∀ E ∈ C, ∀ F ∈ C, E ∩ F ∈ C) {n m : ℕ} {A B : Set α}
    (hA : A ∈ differenceHierarchy C n) (hB : B ∈ differenceHierarchy C m) :
    A ∩ B ∈ differenceHierarchy C (n * m) :=
  (inter_and_diff_mem_differenceHierarchy hU hI hA hB).1

/-- Subtracting level `m` from level `n` costs at most `n * (m + 1)` levels. -/
theorem diff_mem_differenceHierarchy
    (hU : ∀ E ∈ C, ∀ F ∈ C, E ∪ F ∈ C)
    (hI : ∀ E ∈ C, ∀ F ∈ C, E ∩ F ∈ C) {n m : ℕ} {A B : Set α}
    (hA : A ∈ differenceHierarchy C n) (hB : B ∈ differenceHierarchy C m) :
    A \ B ∈ differenceHierarchy C (n * (m + 1)) :=
  (inter_and_diff_mem_differenceHierarchy hU hI hA hB).2

/-- Union has a finite level bound when the base lattice contains the universe. -/
theorem union_mem_differenceHierarchy (h1 : Set.univ ∈ C)
    (hU : ∀ E ∈ C, ∀ F ∈ C, E ∪ F ∈ C)
    (hI : ∀ E ∈ C, ∀ F ∈ C, E ∩ F ∈ C) {n m : ℕ} {A B : Set α}
    (hA : A ∈ differenceHierarchy C n) (hB : B ∈ differenceHierarchy C m) :
    A ∪ B ∈ differenceHierarchy C ((n + 1) * (m + 1) + 1) := by
  have h := compl_mem_differenceHierarchy_succ h1
    (inter_mem_differenceHierarchy hU hI
      (compl_mem_differenceHierarchy_succ h1 hA) (compl_mem_differenceHierarchy_succ h1 hB))
  simpa only [Set.compl_inter, compl_compl] using h

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α} {n m : ℕ}

/-- Intersecting `BH` levels `n` and `m` costs at most `n * m` levels. -/
theorem inter_mem_BH (hA : A ∈ BH enc n) (hB : B ∈ BH enc m) :
    A ∩ B ∈ BH enc (n * m) :=
  inter_mem_differenceHierarchy (fun _ h₁ _ h₂ => union_mem_NP h₁ h₂)
    (fun _ h₁ _ h₂ => inter_mem_NP h₁ h₂) hA hB

/-- Subtracting `BH` level `m` from level `n` costs at most `n * (m + 1)` levels. -/
theorem diff_mem_BH (hA : A ∈ BH enc n) (hB : B ∈ BH enc m) :
    A \ B ∈ BH enc (n * (m + 1)) :=
  diff_mem_differenceHierarchy (fun _ h₁ _ h₂ => union_mem_NP h₁ h₂)
    (fun _ h₁ _ h₂ => inter_mem_NP h₁ h₂) hA hB

/-- The union of two finite `BH` levels stays at a finite level. -/
theorem union_mem_BH (hA : A ∈ BH enc n) (hB : B ∈ BH enc m) :
    A ∪ B ∈ BH enc ((n + 1) * (m + 1) + 1) :=
  union_mem_differenceHierarchy univ_mem_NP
    (fun _ h₁ _ h₂ => union_mem_NP h₁ h₂) (fun _ h₁ _ h₂ => inter_mem_NP h₁ h₂) hA hB

/-- The Boolean hierarchy is closed under intersection. -/
theorem inter_mem_BooleanHierarchy (hA : A ∈ BooleanHierarchy enc)
    (hB : B ∈ BooleanHierarchy enc) : A ∩ B ∈ BooleanHierarchy enc := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hA
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hB
  exact Set.mem_iUnion.mpr ⟨n * m, inter_mem_BH hn hm⟩

/-- `BooleanHierarchy` as a Boolean subalgebra of `Set α`. -/
def BooleanHierarchy.booleanSubalgebra (enc : α ↪ List Bool) : BooleanSubalgebra (Set α) :=
  .ofComplInf (BooleanHierarchy enc) (NP_subset_BooleanHierarchy empty_mem_NP)
    (fun _ => compl_mem_BooleanHierarchy) (fun _ _ => inter_mem_BooleanHierarchy)

@[simp]
theorem BooleanHierarchy.coe_booleanSubalgebra :
    (BooleanHierarchy.booleanSubalgebra enc : Set (Set α)) = BooleanHierarchy enc := rfl

@[simp]
theorem BooleanHierarchy.mem_booleanSubalgebra :
    A ∈ BooleanHierarchy.booleanSubalgebra enc ↔ A ∈ BooleanHierarchy enc := Iff.rfl

/-- The Boolean hierarchy is closed under difference. -/
theorem diff_mem_BooleanHierarchy (hA : A ∈ BooleanHierarchy enc)
    (hB : B ∈ BooleanHierarchy enc) : A \ B ∈ BooleanHierarchy enc :=
  (BooleanHierarchy.booleanSubalgebra enc).sdiff_mem hA hB

/-- The Boolean hierarchy is closed under union. -/
theorem union_mem_BooleanHierarchy (hA : A ∈ BooleanHierarchy enc)
    (hB : B ∈ BooleanHierarchy enc) : A ∪ B ∈ BooleanHierarchy enc :=
  (BooleanHierarchy.booleanSubalgebra enc).sup_mem hA hB

/-- The Boolean hierarchy is closed under symmetric difference. -/
theorem symmDiff_mem_BooleanHierarchy (hA : A ∈ BooleanHierarchy enc)
    (hB : B ∈ BooleanHierarchy enc) : symmDiff A B ∈ BooleanHierarchy enc :=
  (BooleanHierarchy.booleanSubalgebra enc).symmDiff_mem hA hB

end Cslib.Complexity
