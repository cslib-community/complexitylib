/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.UP
public import Complexity.Computability.Complexity.Classes.CeqP

/-!
# Unique-solution polynomial time

US tests whether a polynomial-time verifier has exactly one accepting witness
[Blass and Gurevich][BlassGurevich1982]. Unlike UP, a no-instance may have multiple witnesses.
This uses the existing verifier-based #P; no counting-machine characterization is asserted.
The containments and closure below are elementary count identities.

## Main definitions

* `Cslib.Complexity.US`: languages defined by an accepting count equal to one.

## Main results

* `UP_subset_US`, `coNP_subset_US`, `US_subset_CeqP`: basic containments.
* `inter_mem_US`, `PolyTimeReducible.mem_US`: intersection and reduction closure.

## References

* [A. Blass, Y. Gurevich, *On the unique satisfiability problem*][BlassGurevich1982]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- Exactly one accepting witness, with no ambiguity restriction on no-instances
[Blass and Gurevich][BlassGurevich1982]. -/
def US (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpP enc, ∀ a, a ∈ A ↔ f a = 1}

/-- Globally unambiguous verifiers are special cases of unique-solution verifiers. -/
theorem UP_subset_US : UP enc ⊆ US enc := by
  rintro A ⟨f, hf, -, hA⟩
  exact ⟨f, hf, hA⟩

/-- Adding one to the accepting count of the complement recognizes a coNP language. -/
theorem coNP_subset_US : coNP enc ⊆ US enc := by
  intro A hA
  obtain ⟨f, hf, hA⟩ := mem_NP_iff_exists_SharpP.mp hA
  refine ⟨f + 1, SharpP.add_one_mem hf, fun a => ?_⟩
  simpa only [Set.mem_compl_iff, not_not, not_lt, Nat.le_zero, Pi.add_apply, Pi.one_apply,
    Nat.add_eq_right] using not_congr (hA a)

/-- Subtracting one from the count gives a GapP zero test. -/
theorem US_subset_CeqP : US enc ⊆ CeqP enc := by
  rintro A ⟨f, hf, hA⟩
  refine ⟨(fun a => (f a : ℤ)) - 1,
    GapP.sub_mem' (SharpP.natCast_mem_GapP hf) GapP.one_mem, fun a => ?_⟩
  simpa [sub_eq_zero] using hA a

/-- A product of natural counts is one precisely when both factors are one. -/
theorem inter_mem_US (hA : A ∈ US enc) (hB : B ∈ US enc) : A ∩ B ∈ US enc := by
  obtain ⟨f, hf, hA⟩ := hA
  obtain ⟨g, hg, hB⟩ := hB
  exact ⟨f * g, SharpP.mul_mem hf hg, fun a => by simp [hA a, hB a]⟩

/-- Exact-count precomposition preserves US membership. -/
theorem PolyTimeReducible.mem_US {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ US encB) : A ∈ US enc := by
  obtain ⟨g, hg, hAB⟩ := h
  obtain ⟨f, hf, hB⟩ := hB
  exact ⟨f ∘ g, SharpP.comp_mem hf hg, fun a => (hAB a).trans (hB (g a))⟩

end Cslib.Complexity
