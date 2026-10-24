/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.Closure
public import Complexity.Computability.Complexity.Classes.PP.Characterization

/-!
# Exact counting: C=P

`CeqP` consists of zero sets of `GapP` functions, the gap characterization of `C=P`
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994]. These are verifier-based counts; no counting
machine characterization is assumed.

## Main definitions

* `Cslib.Complexity.coCeqP`: complements of exact-counting languages.
* `Cslib.Complexity.CeqP`: the exact counting class `C=P`.

## Main results

* `Cslib.Complexity.mem_CeqP_iff_exists_SharpP`: equality of two `#P` functions.
* `Cslib.Complexity.inter_mem_CeqP`, `Cslib.Complexity.union_mem_CeqP`.
* `Cslib.Complexity.coNP_subset_CeqP`, `Cslib.Complexity.CeqP_subset_PP`.
* `Cslib.Complexity.PolyTimeReducible.mem_CeqP`.

## References

* [L. Fortnow, *Counting Complexity*][Fortnow1997], Classifications 4.5 and 4.8–4.9,
  Corollaries 4.10–4.11.

* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- `C=P`, the zero sets of integer-valued `GapP` functions
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994],
[Fortnow, Classification 4.5][Fortnow1997]. -/
def CeqP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ g ∈ GapP enc, ∀ a, a ∈ A ↔ g a = 0}

/-- A language is in `C=P` iff membership is equality of two accepting counts. -/
theorem mem_CeqP_iff_exists_SharpP : A ∈ CeqP enc ↔
    ∃ f ∈ SharpP enc, ∃ g ∈ SharpP enc, ∀ a, a ∈ A ↔ f a = g a := by
  constructor
  · rintro ⟨h, ⟨f, hf, g, hg, hh⟩, hA⟩
    exact ⟨f, hf, g, hg, fun a => by simpa [hh a, sub_eq_zero] using hA a⟩
  · rintro ⟨f, hf, g, hg, hA⟩
    exact ⟨_, GapP.natCast_sub_natCast_mem hf hg, fun a => by simpa [sub_eq_zero] using hA a⟩

/-- A coNP language is the zero set of the accepting count for its complement. -/
theorem coNP_subset_CeqP : coNP enc ⊆ CeqP enc := by
  intro A hA
  obtain ⟨f, hf, hA⟩ := mem_NP_iff_exists_SharpP.mp hA
  refine ⟨fun a => (f a : ℤ), SharpP.natCast_mem_GapP hf, fun a => ?_⟩
  simpa only [Set.mem_compl_iff, not_not, not_lt, Nat.le_zero, Int.natCast_eq_zero] using
    not_congr (hA a)

/-- A product vanishes exactly when one of its factors vanishes. -/
theorem union_mem_CeqP (hA : A ∈ CeqP enc) (hB : B ∈ CeqP enc) : A ∪ B ∈ CeqP enc := by
  obtain ⟨f, hf, hA⟩ := hA
  obtain ⟨g, hg, hB⟩ := hB
  exact ⟨f * g, GapP.mul_mem hf hg, fun a => by simp [hA a, hB a]⟩

/-- A sum of two integer squares vanishes exactly when both vanish. -/
theorem inter_mem_CeqP (hA : A ∈ CeqP enc) (hB : B ∈ CeqP enc) : A ∩ B ∈ CeqP enc := by
  obtain ⟨f, hf, hA⟩ := hA
  obtain ⟨g, hg, hB⟩ := hB
  refine ⟨f * f + g * g, GapP.add_mem (GapP.mul_mem hf hf) (GapP.mul_mem hg hg), fun a => ?_⟩
  simp only [Set.mem_inter_iff, hA a, hB a, Pi.add_apply, Pi.mul_apply]
  constructor
  · rintro ⟨h₁, h₂⟩
    simp [h₁, h₂]
  · intro h
    have h₁ := sq_nonneg (f a)
    have h₂ := sq_nonneg (g a)
    constructor <;> nlinarith

/-- `C=P ⊆ PP`: for integer `g`, the gap `1 - g²` is positive precisely at its zeros. -/
theorem CeqP_subset_PP : CeqP enc ⊆ PP enc := by
  rintro A ⟨g, hg, hA⟩
  refine mem_PP_iff_exists_GapP.mpr
    ⟨1 - g * g, GapP.sub_mem' GapP.one_mem (GapP.mul_mem hg hg), fun a => ?_⟩
  simp only [hA a, Pi.sub_apply, Pi.one_apply, Pi.mul_apply]
  constructor
  · intro h
    simp [h]
  · intro h
    have := sq_nonneg (g a)
    nlinarith [sq_nonneg (g a - 1), sq_nonneg (g a + 1)]

/-- `C=P` is closed under polynomial-time many-one reductions. -/
theorem PolyTimeReducible.mem_CeqP {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ CeqP encB) : A ∈ CeqP enc := by
  obtain ⟨g, hg, hAB⟩ := h
  obtain ⟨f, hf, hB⟩ := hB
  exact ⟨f ∘ g, GapP.comp_mem hf hg, fun a => (hAB a).trans (hB (g a))⟩

/-- The complement class coC=P. See [Fortnow, Classifications 4.8–4.9][Fortnow1997]. -/
def coCeqP (enc : α ↪ List Bool) : Set (Set α) := {A | Aᶜ ∈ CeqP enc}

theorem mem_coCeqP : A ∈ coCeqP enc ↔ Aᶜ ∈ CeqP enc := Iff.rfl

@[simp]
theorem compl_mem_coCeqP : Aᶜ ∈ coCeqP enc ↔ A ∈ CeqP enc := by simp [coCeqP]

/-- coC=P consists of the nonzero sets of GapP functions. This is the complement of the
zero-set characterization [Fortnow, Classifications 4.5 and 4.9][Fortnow1997]. -/
theorem mem_coCeqP_iff_exists_GapP :
    A ∈ coCeqP enc ↔ ∃ g ∈ GapP enc, ∀ a, a ∈ A ↔ g a ≠ 0 :=
  exists_forall_mem_compl_iff fun _ _ => Iff.rfl

/-- NP is contained in coC=P [Fortnow, Corollary 4.11][Fortnow1997]. -/
theorem NP_subset_coCeqP : NP enc ⊆ coCeqP enc := by
  intro A hA
  exact coNP_subset_CeqP (by simpa [mem_coNP] using hA)

/-- coC=P is contained in PP [Fortnow, Corollary 4.10][Fortnow1997]. -/
theorem coCeqP_subset_PP : coCeqP enc ⊆ PP enc := by
  intro A hA
  obtain ⟨g, hg, hA⟩ := mem_coCeqP_iff_exists_GapP.mp hA
  exact mem_PP_iff_exists_GapP.mpr ⟨g * g, GapP.mul_mem hg hg, fun a => by
    simpa [pow_two] using (hA a).trans (sq_pos_iff).symm⟩

/-- Union closure is dual to intersection closure of C=P. -/
theorem union_mem_coCeqP (hA : A ∈ coCeqP enc) (hB : B ∈ coCeqP enc) :
    A ∪ B ∈ coCeqP enc :=
  compl_union_mem inter_mem_CeqP hA hB

/-- Intersection closure is dual to union closure of C=P. -/
theorem inter_mem_coCeqP (hA : A ∈ coCeqP enc) (hB : B ∈ coCeqP enc) :
    A ∩ B ∈ coCeqP enc :=
  compl_inter_mem union_mem_CeqP hA hB

/-- Polynomial-time reductions preserve coC=P. -/
theorem PolyTimeReducible.mem_coCeqP {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ coCeqP encB) : A ∈ coCeqP enc :=
  h.mem_compl PolyTimeReducible.mem_CeqP hB

end Cslib.Complexity
