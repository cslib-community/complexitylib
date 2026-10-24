/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.UP
public import Complexity.Computability.Complexity.Classes.CeqP
public import Complexity.Foundations.Order.BooleanSubalgebra

/-!
# Small-gap polynomial time

`SPP` consists of languages whose characteristic function belongs to `GapP`, following
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994] and [Fortnow, Classification 4.4][Fortnow1997].
We use the library's verifier-based counting functions, without claiming a counting-machine
characterization. The Boolean closure proofs below are elementary consequences of the GapP
ring operations: complement uses `1 - f`, intersection `f * g`, and union De Morgan's law.

## Main definitions

* `Cslib.Complexity.SPP`: characteristic functions in `GapP`.

## Main results

* `Cslib.Complexity.UP_subset_SPP`, `Cslib.Complexity.SPP_subset_CeqP`.
* `Cslib.Complexity.compl_mem_SPP`, `Cslib.Complexity.inter_mem_SPP`,
  `Cslib.Complexity.union_mem_SPP`, `Cslib.Complexity.diff_mem_SPP`,
  `Cslib.Complexity.symmDiff_mem_SPP`, `Cslib.Complexity.PolyTimeReducible.mem_SPP`.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]
* [L. Fortnow, *Counting Complexity*][Fortnow1997]
-/

@[expose] public section

namespace Cslib.Complexity

open scoped symmDiff

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- Small-gap polynomial time: a GapP function is one on members and zero on nonmembers
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994], [Fortnow, Classification 4.4][Fortnow1997]. -/
def SPP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ GapP enc, (∀ a, f a = 0 ∨ f a = 1) ∧ ∀ a, a ∈ A ↔ f a = 1}

/-- `UP ⊆ SPP` [Fortnow, Corollary 4.11][Fortnow1997]. -/
theorem UP_subset_SPP : UP enc ⊆ SPP enc := by
  rintro A ⟨f, hf, hle, hA⟩
  refine ⟨fun a => (f a : ℤ), SharpP.natCast_mem_GapP hf, fun a => ?_, fun a => ?_⟩
  · have := hle a
    rcases (show f a = 0 ∨ f a = 1 by omega) with h | h <;> simp [h]
  · simpa using hA a

/-- Boolean complement corresponds to subtracting the characteristic function from one. -/
theorem compl_mem_SPP (hA : A ∈ SPP enc) : Aᶜ ∈ SPP enc := by
  obtain ⟨f, hf, hr, hA⟩ := hA
  refine ⟨1 - f, GapP.sub_mem' GapP.one_mem hf, fun a => ?_, fun a => ?_⟩
  · rcases hr a with h | h <;> simp [h]
  · rcases hr a with h | h <;> simp [hA a, h]

/-- Intersection multiplies two characteristic functions. -/
theorem inter_mem_SPP (hA : A ∈ SPP enc) (hB : B ∈ SPP enc) : A ∩ B ∈ SPP enc := by
  obtain ⟨f, hf, hr, hA⟩ := hA
  obtain ⟨g, hg, hs, hB⟩ := hB
  refine ⟨f * g, GapP.mul_mem hf hg, fun a => ?_, fun a => ?_⟩
  · rcases hr a with h | h <;> rcases hs a with k | k <;> simp [h, k]
  · rcases hr a with h | h <;> rcases hs a with k | k <;> simp [hA a, hB a, h, k]

/-- `SPP` as a Boolean subalgebra of `Set α`. -/
def SPP.booleanSubalgebra (enc : α ↪ List Bool) : BooleanSubalgebra (Set α) :=
  .ofComplInf (SPP enc) (UP_subset_SPP (P_subset_UP empty_mem_P)) (fun _ => compl_mem_SPP)
    (fun _ _ => inter_mem_SPP)

@[simp]
theorem SPP.coe_booleanSubalgebra : (SPP.booleanSubalgebra enc : Set (Set α)) = SPP enc := rfl

@[simp]
theorem SPP.mem_booleanSubalgebra : A ∈ SPP.booleanSubalgebra enc ↔ A ∈ SPP enc := Iff.rfl

/-- Union follows from intersection and complement. -/
theorem union_mem_SPP (hA : A ∈ SPP enc) (hB : B ∈ SPP enc) : A ∪ B ∈ SPP enc :=
  (SPP.booleanSubalgebra enc).sup_mem hA hB

/-- `SPP` is closed under set difference. -/
theorem diff_mem_SPP (hA : A ∈ SPP enc) (hB : B ∈ SPP enc) : A \ B ∈ SPP enc :=
  (SPP.booleanSubalgebra enc).sdiff_mem hA hB

/-- `SPP` is closed under symmetric difference. -/
theorem symmDiff_mem_SPP (hA : A ∈ SPP enc) (hB : B ∈ SPP enc) : A ∆ B ∈ SPP enc :=
  (SPP.booleanSubalgebra enc).symmDiff_mem hA hB

/-- Subtracting one turns the characteristic function into an exact-zero test. -/
theorem SPP_subset_CeqP : SPP enc ⊆ CeqP enc := by
  rintro A ⟨f, hf, -, hA⟩
  exact ⟨f - 1, GapP.sub_mem' hf GapP.one_mem, fun a => by simpa [sub_eq_zero] using hA a⟩

/-- Since SPP is closed under complement, coUP is also contained in SPP. -/
theorem coUP_subset_SPP : coUP enc ⊆ SPP enc := by
  intro A hA
  simpa using compl_mem_SPP (UP_subset_SPP hA)

/-- SPP is contained in coC=P by complement closure and its C=P containment. -/
theorem SPP_subset_coCeqP : SPP enc ⊆ coCeqP enc :=
  fun _ h => SPP_subset_CeqP (compl_mem_SPP h)

/-- Polynomial-time many-one reductions preserve the zero-or-one gap. -/
theorem PolyTimeReducible.mem_SPP {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ SPP encB) : A ∈ SPP enc := by
  obtain ⟨g, hg, hAB⟩ := h
  obtain ⟨f, hf, hr, hB⟩ := hB
  exact ⟨f ∘ g, GapP.comp_mem hf hg, fun a => hr (g a), fun a => (hAB a).trans (hB (g a))⟩

end Cslib.Complexity
