/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.DP
import CslibFrontier.Computability.Complexity.Classes.NP.Witness

/-!
# The Boolean hierarchy over NP

The difference hierarchy iterates `A ∖ B`, with `A` in a base class and `B` at the previous
level. Level zero is the singleton class containing the empty language. Over NP, level one is
NP and level two is DP. This is the difference-hierarchy presentation of the Boolean hierarchy
[Cai et al.][CaiEtAl1988]. We develop the dual hierarchy `coBH`, right-hand Boolean closure with
`NP` languages, and the standard level-by-level collapse equivalences [Cai et al.][CaiEtAl1988];
[Kadin][Kadin1988]: if `coBH k ⊆ BH k` at some level `k`, then every higher level `BH m` and
`coBH m` (and the full `BooleanHierarchy`) collapses to `BH k`.

## Main definitions

* `differenceHierarchy`: finite nested differences over an arbitrary class of sets.
* `BH`, `coBH`, `BooleanHierarchy`: the levels over NP, their dual levels, and their union.

## Main results

* `BH_one`, `BH_two`, `coBH_one`, `coBH_two`: the first two levels of `BH` and `coBH` are
  `NP`/`DP` and `coNP`/`coDP`.
* `BH_mono`, `coBH_mono`, `BH_subset_coBH_succ`, `coBH_subset_BH_succ`,
  `iUnion_coBH_eq_BooleanHierarchy`: monotonicity, alternation between `BH` and `coBH`, and
  equality of their unions.
* `inter_mem_BH_of_mem_NP`, `diff_mem_BH_of_mem_NP`, `union_mem_BH_of_mem_NP`: right-hand
  closure of `BH` levels under intersection, difference, and union with `NP` languages.
* `PolyTimeReducible.mem_BH`, `PolyTimeReducible.mem_coBH`,
  `PolyTimeReducible.mem_BooleanHierarchy`: many-one reduction closure.
* `BH_succ_subset_iff_coBH_subset`, `BH_succ_eq_iff_coBH_subset`, `BH_eq_coBH_iff_BH_succ_eq`,
  `BH_eq_of_coBH_subset`, `coBH_eq_BH_of_coBH_subset`, `BooleanHierarchy_eq_BH_of_coBH_subset`,
  `BooleanHierarchy_eq_NP_of_NP_eq_coNP`: Boolean-hierarchy collapse equivalences.

## References

* [J.-Y. Cai et al., *The Boolean Hierarchy I: Structural Properties*][CaiEtAl1988]
* [J. Kadin, *The Polynomial Time Hierarchy Collapses if the Boolean Hierarchy
  Collapses*][Kadin1988]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α β : Type*}

/-- Nested differences over `C`, starting with just the empty set. -/
def differenceHierarchy (C : Set (Set α)) : ℕ → Set (Set α)
  | 0 => {∅}
  | n + 1 => {A | ∃ B ∈ C, ∃ D ∈ differenceHierarchy C n, A = B \ D}

/-- Level zero of the difference hierarchy is the singleton containing `∅`. -/
@[simp]
theorem differenceHierarchy_zero (C : Set (Set α)) : differenceHierarchy C 0 = {∅} := rfl

/-- At level one, taking a difference with the empty set recovers the base class. -/
@[simp]
theorem differenceHierarchy_one (C : Set (Set α)) : differenceHierarchy C 1 = C := by
  ext A
  simp [differenceHierarchy]

/-- Every level lies in a difference-closed class containing the base class and the empty set. -/
theorem differenceHierarchy_subset {C D : Set (Set α)} (hC : C ⊆ D) (h0 : ∅ ∈ D)
    (hD : ∀ A ∈ D, ∀ B ∈ D, A \ B ∈ D) (n : ℕ) :
    differenceHierarchy C n ⊆ D := by
  induction n with
  | zero =>
    rintro A (rfl : A = ∅)
    exact h0
  | succ n ih =>
    rintro A ⟨B, hB, E, hE, rfl⟩
    exact hD B (hC hB) E (ih hE)

/-- Inverse images preserve every level whenever they preserve the base classes. -/
theorem preimage_mem_differenceHierarchy {C : Set (Set α)} {D : Set (Set β)}
    {f : α → β} (hf : ∀ B ∈ D, f ⁻¹' B ∈ C) {n : ℕ} {A : Set β}
    (hA : A ∈ differenceHierarchy D n) : f ⁻¹' A ∈ differenceHierarchy C n := by
  induction n generalizing A with
  | zero =>
    have h : A = ∅ := hA
    subst h
    exact Set.preimage_empty
  | succ n ih =>
    obtain ⟨B, hB, E, hE, rfl⟩ := hA
    exact ⟨f ⁻¹' B, hf B hB, f ⁻¹' E, ih hE, rfl⟩

/-- Empty membership makes the levels increasing. -/
theorem differenceHierarchy_subset_succ {C : Set (Set α)} (hC : ∅ ∈ C) (n : ℕ) :
    differenceHierarchy C n ⊆ differenceHierarchy C (n + 1) := by
  induction n with
  | zero =>
    intro A hA
    have h : A = ∅ := hA
    subst h
    exact ⟨∅, hC, ∅, rfl, by simp⟩
  | succ n ih =>
    rintro A ⟨B, hB, D, hD, rfl⟩
    exact ⟨B, hB, D, ih hD, rfl⟩

/-- If the universe belongs to the base class, complementation costs one level. -/
theorem compl_mem_differenceHierarchy_succ {C : Set (Set α)} (hC : Set.univ ∈ C)
    {n : ℕ} {A : Set α} (hA : A ∈ differenceHierarchy C n) :
    Aᶜ ∈ differenceHierarchy C (n + 1) :=
  ⟨Set.univ, hC, A, hA, by ext a; simp⟩

/-- Intersecting on the right with a member of the base class preserves the level when the base
class is closed under intersection. -/
theorem inter_mem_differenceHierarchy_right {C : Set (Set α)}
    (hC : ∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ∩ B₂ ∈ C) {n : ℕ} {A B : Set α}
    (hA : A ∈ differenceHierarchy C n) (hB : B ∈ C) :
    A ∩ B ∈ differenceHierarchy C n := by
  cases n with
  | zero =>
    have h : A = ∅ := hA
    subst h
    simp [differenceHierarchy]
  | succ n =>
    obtain ⟨E, hE, D, hD, rfl⟩ := hA
    exact ⟨E ∩ B, hC E hE B hB, D, hD, by ext a; simp [and_right_comm]⟩

private theorem diff_and_union_mem_differenceHierarchy_right {C : Set (Set α)} (h0 : ∅ ∈ C)
    (hU : ∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ∪ B₂ ∈ C) :
    ∀ {n : ℕ} {A B : Set α}, A ∈ differenceHierarchy C n → B ∈ C →
      A \ B ∈ differenceHierarchy C (n + 1) ∧ A ∪ B ∈ differenceHierarchy C (n + 1)
  | 0, A, B, hA, hB => by
    have h : A = ∅ := hA
    subst h
    exact ⟨⟨∅, h0, ∅, rfl, by simp⟩, ⟨B, hB, ∅, rfl, by simp⟩⟩
  | n + 1, _, B, ⟨E, hE, D, hD, rfl⟩, hB => by
    obtain ⟨hdiff, hunion⟩ := diff_and_union_mem_differenceHierarchy_right h0 hU hD hB
    refine ⟨⟨E, hE, D ∪ B, hunion, ?_⟩, ⟨E ∪ B, hU E hE B hB, D \ B, hdiff, ?_⟩⟩
    · ext a
      simp only [Set.mem_sdiff, Set.mem_union]
      tauto
    · ext a
      simp only [Set.mem_sdiff, Set.mem_union]
      tauto

/-- Subtracting a member of the base class costs at most one level when the base class contains `∅`
and is closed under union. -/
theorem diff_mem_differenceHierarchy_right {C : Set (Set α)} (h0 : ∅ ∈ C)
    (hU : ∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ∪ B₂ ∈ C) {n : ℕ} {A B : Set α}
    (hA : A ∈ differenceHierarchy C n) (hB : B ∈ C) :
    A \ B ∈ differenceHierarchy C (n + 1) :=
  (diff_and_union_mem_differenceHierarchy_right h0 hU hA hB).1

/-- Taking the union with a member of the base class costs at most one level when the base class
contains `∅` and is closed under union. -/
theorem union_mem_differenceHierarchy_right {C : Set (Set α)} (h0 : ∅ ∈ C)
    (hU : ∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ∪ B₂ ∈ C) {n : ℕ} {A B : Set α}
    (hA : A ∈ differenceHierarchy C n) (hB : B ∈ C) :
    A ∪ B ∈ differenceHierarchy C (n + 1) :=
  (diff_and_union_mem_differenceHierarchy_right h0 hU hA hB).2

/-- If level `k` is closed under complement and the base class is closed under intersection,
level `k + 1` collapses to level `k`. -/
theorem differenceHierarchy_succ_subset_of_compl {C : Set (Set α)}
    (hI : ∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ∩ B₂ ∈ C) {k : ℕ}
    (hcompl : ∀ D ∈ differenceHierarchy C k, Dᶜ ∈ differenceHierarchy C k) :
    differenceHierarchy C (k + 1) ⊆ differenceHierarchy C k := by
  rintro A ⟨B, hB, D, hD, rfl⟩
  have h : B \ D = Dᶜ ∩ B := by
    ext a
    simp [Set.mem_inter_iff, and_comm]
  rw [h]
  exact inter_mem_differenceHierarchy_right hI (hcompl D hD) hB

/-- Once a successor level is contained in the previous level, all higher levels coincide with
that level. -/
theorem differenceHierarchy_eq_of_succ_subset {C : Set (Set α)} (h0 : ∅ ∈ C) {k : ℕ}
    (h : differenceHierarchy C (k + 1) ⊆ differenceHierarchy C k) {m : ℕ} (hm : k ≤ m) :
    differenceHierarchy C m = differenceHierarchy C k := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m _ ih =>
    apply Set.Subset.antisymm
    · rintro A ⟨B, hB, D, hD, rfl⟩
      rw [ih] at hD
      exact h ⟨B, hB, D, hD, rfl⟩
    · rw [← ih]
      exact differenceHierarchy_subset_succ h0 m

variable {α β : Type} {enc : α ↪ List Bool} {A : Set α}

/-- The `n`th level of the Boolean hierarchy over NP, with level zero containing only `∅`
[Cai et al.][CaiEtAl1988]. -/
def BH (enc : α ↪ List Bool) (n : ℕ) : Set (Set α) := differenceHierarchy (NP enc) n

/-- The complement of the `n`th level of the Boolean hierarchy over NP. -/
def coBH (enc : α ↪ List Bool) (n : ℕ) : Set (Set α) := {A | Aᶜ ∈ BH enc n}

/-- The union of all finite levels of the Boolean hierarchy over NP [Cai et al.][CaiEtAl1988]. -/
def BooleanHierarchy (enc : α ↪ List Bool) : Set (Set α) := ⋃ n, BH enc n

/-- Every finite level belongs to the full Boolean hierarchy. -/
theorem BH_subset_BooleanHierarchy (n : ℕ) : BH enc n ⊆ BooleanHierarchy enc :=
  Set.subset_iUnion (BH enc) n

/-- NP is the first level of the Boolean hierarchy. -/
theorem NP_subset_BooleanHierarchy : NP enc ⊆ BooleanHierarchy enc := by
  simpa only [BH, differenceHierarchy_one] using BH_subset_BooleanHierarchy (enc := enc) 1

/-- A difference-closed class containing NP contains its entire Boolean hierarchy. -/
theorem BooleanHierarchy_subset {D : Set (Set α)} (hNP : NP enc ⊆ D)
    (hD : ∀ A ∈ D, ∀ B ∈ D, A \ B ∈ D) : BooleanHierarchy enc ⊆ D :=
  Set.iUnion_subset (differenceHierarchy_subset hNP (hNP empty_mem_NP) hD)

/-- For a difference-closed target, containing NP is equivalent to containing the full
Boolean hierarchy over NP. -/
theorem BooleanHierarchy_subset_iff {D : Set (Set α)}
    (hD : ∀ A ∈ D, ∀ B ∈ D, A \ B ∈ D) :
    BooleanHierarchy enc ⊆ D ↔ NP enc ⊆ D :=
  ⟨NP_subset_BooleanHierarchy.trans, fun h => BooleanHierarchy_subset h hD⟩

@[simp]
theorem mem_coBH {n : ℕ} : A ∈ coBH enc n ↔ Aᶜ ∈ BH enc n := Iff.rfl

theorem compl_mem_coBH_iff {n : ℕ} : Aᶜ ∈ coBH enc n ↔ A ∈ BH enc n := by
  simp [coBH]

theorem compl_mem_BH_iff {n : ℕ} : Aᶜ ∈ BH enc n ↔ A ∈ coBH enc n := Iff.rfl

@[simp]
theorem BH_zero : BH enc 0 = {∅} := rfl

@[simp]
theorem coBH_zero : coBH enc 0 = {Set.univ} := by
  ext A
  simp [coBH, BH_zero, Set.compl_empty_iff]

/-- The first level is precisely NP. -/
@[simp]
theorem BH_one : BH enc 1 = NP enc := differenceHierarchy_one _

/-- The first dual level is precisely coNP. -/
@[simp]
theorem coBH_one : coBH enc 1 = coNP enc := by
  ext A
  simp [coBH, coNP]

/-- The second level is precisely DP. -/
theorem BH_two : BH enc 2 = DP enc := by
  ext A
  change (∃ B ∈ NP enc, ∃ D ∈ differenceHierarchy (NP enc) 1, A = B \ D) ↔ _
  rw [differenceHierarchy_one, mem_DP_iff_diff]

/-- The second dual level is precisely coDP. -/
theorem coBH_two : coBH enc 2 = coDP enc := by
  ext A
  rw [mem_coBH, mem_coDP, BH_two]

/-- The levels of the Boolean hierarchy are increasing. -/
theorem BH_mono : Monotone (BH enc) := by
  apply monotone_nat_of_le_succ
  exact differenceHierarchy_subset_succ empty_mem_NP

/-- The dual levels of the Boolean hierarchy are increasing. -/
theorem coBH_mono : Monotone (coBH enc) :=
  fun _ _ hmn _ hA => BH_mono hmn hA

/-- Complementation moves a language at most one level up. -/
theorem compl_mem_BH_succ {n : ℕ} (hA : A ∈ BH enc n) : Aᶜ ∈ BH enc (n + 1) :=
  compl_mem_differenceHierarchy_succ univ_mem_NP hA

/-- Every level of `BH` is contained in the next level of `coBH`. -/
theorem BH_subset_coBH_succ (n : ℕ) : BH enc n ⊆ coBH enc (n + 1) :=
  fun _ hA => compl_mem_BH_succ hA

/-- Every level of `coBH` is contained in the next level of `BH`. -/
theorem coBH_subset_BH_succ (n : ℕ) : coBH enc n ⊆ BH enc (n + 1) :=
  fun A hA => compl_compl A ▸ compl_mem_BH_succ hA

/-- Complementation moves a language in `coBH` at most one level up. -/
theorem compl_mem_coBH_succ {n : ℕ} (hA : A ∈ coBH enc n) : Aᶜ ∈ coBH enc (n + 1) :=
  compl_mem_coBH_iff.mpr (coBH_subset_BH_succ n hA)

/-- The union of the dual levels `coBH` coincides with `BooleanHierarchy`. -/
theorem iUnion_coBH_eq_BooleanHierarchy : (⋃ n, coBH enc n) = BooleanHierarchy enc :=
  Set.Subset.antisymm
    (Set.iUnion_subset fun n _ hA => Set.mem_iUnion.mpr ⟨n + 1, coBH_subset_BH_succ n hA⟩)
    (Set.iUnion_subset fun n _ hA => Set.mem_iUnion.mpr ⟨n + 1, BH_subset_coBH_succ n hA⟩)

/-- The union of the finite levels is closed under complement. -/
theorem compl_mem_BooleanHierarchy (hA : A ∈ BooleanHierarchy enc) :
    Aᶜ ∈ BooleanHierarchy enc := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hA
  exact Set.mem_iUnion.mpr ⟨n + 1, compl_mem_BH_succ hn⟩

/-- Intersecting a `BH enc n` language with an `NP` language stays in `BH enc n`. -/
theorem inter_mem_BH_of_mem_NP {n : ℕ} {B : Set α}
    (hA : A ∈ BH enc n) (hB : B ∈ NP enc) : A ∩ B ∈ BH enc n :=
  inter_mem_differenceHierarchy_right (fun _ h₁ _ h₂ => inter_mem_NP h₁ h₂) hA hB

/-- Subtracting an `NP` language from a `BH enc n` language stays in `BH enc (n + 1)`. -/
theorem diff_mem_BH_of_mem_NP {n : ℕ} {B : Set α}
    (hA : A ∈ BH enc n) (hB : B ∈ NP enc) : A \ B ∈ BH enc (n + 1) :=
  diff_mem_differenceHierarchy_right empty_mem_NP (fun _ h₁ _ h₂ => union_mem_NP h₁ h₂) hA hB

/-- Taking the union of a `BH enc n` language with an `NP` language stays in `BH enc (n + 1)`. -/
theorem union_mem_BH_of_mem_NP {n : ℕ} {B : Set α}
    (hA : A ∈ BH enc n) (hB : B ∈ NP enc) : A ∪ B ∈ BH enc (n + 1) :=
  union_mem_differenceHierarchy_right empty_mem_NP (fun _ h₁ _ h₂ => union_mem_NP h₁ h₂) hA hB

/-- Many-one reductions preserve each finite level. -/
theorem PolyTimeReducible.mem_BH {encB : β ↪ List Bool} {B : Set β} {n : ℕ}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ BH encB n) : A ∈ BH enc n := by
  obtain ⟨f, hf, hAB⟩ := h
  have h := preimage_mem_differenceHierarchy
    (fun D hD => PolyTimeReducible.mem_NP ⟨f, hf, fun _ => Iff.rfl⟩ hD) hB
  rwa [show f ⁻¹' B = A from Set.ext fun a => (hAB a).symm] at h

/-- Many-one reductions preserve each finite dual level. -/
theorem PolyTimeReducible.mem_coBH {encB : β ↪ List Bool} {B : Set β} {n : ℕ}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ coBH encB n) : A ∈ coBH enc n :=
  h.mem_compl PolyTimeReducible.mem_BH hB

/-- Many-one reductions preserve `BooleanHierarchy`. -/
theorem PolyTimeReducible.mem_BooleanHierarchy {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ BooleanHierarchy encB) :
    A ∈ BooleanHierarchy enc := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hB
  exact Set.mem_iUnion.mpr ⟨n, h.mem_BH hn⟩

/-- **Boolean-hierarchy step collapse** [Cai et al., Section 2][CaiEtAl1988]: level `k + 1` is
contained in level `k` if and only if `coBH enc k ⊆ BH enc k`. -/
theorem BH_succ_subset_iff_coBH_subset {k : ℕ} :
    BH enc (k + 1) ⊆ BH enc k ↔ coBH enc k ⊆ BH enc k :=
  ⟨(coBH_subset_BH_succ k).trans, fun h =>
    differenceHierarchy_succ_subset_of_compl (fun _ h₁ _ h₂ => inter_mem_NP h₁ h₂)
      (fun _ hD => h (compl_mem_coBH_iff.mpr hD))⟩

/-- Level `k + 1` equals level `k` if and only if `coBH enc k ⊆ BH enc k`. -/
theorem BH_succ_eq_iff_coBH_subset {k : ℕ} :
    BH enc (k + 1) = BH enc k ↔ coBH enc k ⊆ BH enc k :=
  ⟨fun h => BH_succ_subset_iff_coBH_subset.mp h.subset,
    fun h => Set.Subset.antisymm (BH_succ_subset_iff_coBH_subset.mpr h) (BH_mono (Nat.le_succ k))⟩

/-- Level `k` is closed under complement (`BH enc k = coBH enc k`) if and only if
`BH enc (k + 1) = BH enc k` [Cai et al., Section 2][CaiEtAl1988]. -/
theorem BH_eq_coBH_iff_BH_succ_eq {k : ℕ} :
    BH enc k = coBH enc k ↔ BH enc (k + 1) = BH enc k := by
  rw [BH_succ_eq_iff_coBH_subset]
  exact ⟨fun h => h.symm.subset,
    fun h => Set.Subset.antisymm (fun _ hA => h (compl_mem_coBH_iff.mpr hA)) h⟩

/-- If `BH enc (k + 1) ⊆ BH enc k`, then every higher level `BH enc m` (`k ≤ m`) equals
`BH enc k`. -/
theorem BH_eq_of_BH_succ_subset {k m : ℕ} (h : BH enc (k + 1) ⊆ BH enc k) (hm : k ≤ m) :
    BH enc m = BH enc k :=
  differenceHierarchy_eq_of_succ_subset empty_mem_NP h hm

/-- **Upward collapse of `BH`** [Cai et al., Section 2][CaiEtAl1988]; [Kadin][Kadin1988]: if
`coBH enc k ⊆ BH enc k`, then `BH enc m = BH enc k` for every `m ≥ k`. -/
theorem BH_eq_of_coBH_subset {k m : ℕ} (h : coBH enc k ⊆ BH enc k) (hm : k ≤ m) :
    BH enc m = BH enc k :=
  BH_eq_of_BH_succ_subset (BH_succ_subset_iff_coBH_subset.mpr h) hm

/-- **Upward collapse of `coBH`** [Cai et al., Section 2][CaiEtAl1988]; [Kadin][Kadin1988]: if
`coBH enc k ⊆ BH enc k`, then `coBH enc m = BH enc k` for every `m ≥ k`. -/
theorem coBH_eq_BH_of_coBH_subset {k m : ℕ} (h : coBH enc k ⊆ BH enc k) (hm : k ≤ m) :
    coBH enc m = BH enc k := by
  have hm_eq : coBH enc m = coBH enc k := by
    ext A
    simp only [mem_coBH, BH_eq_of_coBH_subset h hm]
  rw [hm_eq, ← BH_eq_coBH_iff_BH_succ_eq.mpr (BH_succ_eq_iff_coBH_subset.mpr h)]

/-- **Full Boolean-hierarchy collapse** [Cai et al., Section 2][CaiEtAl1988]; [Kadin][Kadin1988]:
if `coBH enc k ⊆ BH enc k`, then the entire Boolean hierarchy collapses to `BH enc k`. -/
theorem BooleanHierarchy_eq_BH_of_coBH_subset {k : ℕ} (h : coBH enc k ⊆ BH enc k) :
    BooleanHierarchy enc = BH enc k := by
  apply Set.Subset.antisymm
  · refine Set.iUnion_subset fun m => ?_
    rcases le_total m k with hmk | hkm
    · exact BH_mono hmk
    · exact (BH_eq_of_coBH_subset h hkm).subset
  · exact Set.subset_iUnion (BH enc) k

/-- If `NP = coNP`, the entire Boolean hierarchy collapses to `NP`. -/
theorem BooleanHierarchy_eq_NP_of_NP_eq_coNP (h : NP enc = coNP enc) :
    BooleanHierarchy enc = NP enc := by
  rw [← BH_one]
  refine BooleanHierarchy_eq_BH_of_coBH_subset ?_
  rw [coBH_one, BH_one]
  exact h.symm.subset

end Cslib.Complexity
