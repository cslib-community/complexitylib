/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Fusion.Semifilter

/-!
# Extending consistent semi-ultrafilter certificates

A family of rejected sets determines the largest upward family that rejects all of them:
a set is accepted exactly when it is contained in no rejected set. If the empty set is rejected
and no two rejected sets cover the universe, this family is a semi-ultrafilter. The condition
includes equal pairs and the empty set, so it also handles the empty carrier without an implicit
nonemptiness assumption.

## Main definitions

* `Cslib.Circuits.Fusion.Semifilter.ofRejected`: the maximal extension avoiding rejected sets.

## Main results

* `Cslib.Circuits.Fusion.Semifilter.isUltra_ofRejected`: the extension is a semi-ultrafilter.
* `Cslib.Circuits.Fusion.Semifilter.ofRejected_apply_iff`: its exact acceptance criterion.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*][CavalarOliveira2025], Theorem 45, credited there to Karchmer. This elementary
  extension construction is used to verify a finite certificate for the converse direction.
-/

@[expose] public section

namespace Cslib.Circuits.Fusion.Semifilter

variable {U : Type*} (rejected : Set (Set U)) (hempty : ∅ ∈ rejected)
    (hunion : ∀ s ∈ rejected, ∀ t ∈ rejected, s ∪ t ≠ Set.univ)

/-- The maximal upward family avoiding each rejected set, under the conditions that make it
proper and nonempty. The union condition includes a rejected set paired with itself. -/
def ofRejected : Semifilter U where
  toFun s := ∀ t ∈ rejected, ¬ s ⊆ t
  monotone' _ _ h hs t ht hsub := hs t ht (h.trans hsub)
  map_top' := propext ⟨fun _ => trivial, fun _ t ht hsub =>
    hunion t ht t ht (by simpa only [Set.union_self] using Set.eq_univ_of_univ_subset hsub)⟩
  map_bot' := propext ⟨fun h => h ∅ hempty (Set.Subset.refl _), False.elim⟩

/-- Acceptance is exactly the absence of a rejected superset. -/
@[simp] theorem ofRejected_apply_iff (s : Set U) :
    ofRejected rejected hempty hunion s ↔ ∀ t ∈ rejected, ¬ s ⊆ t := Iff.rfl

/-- Two rejected supersets of complementary sets would cover the universe. -/
theorem isUltra_ofRejected : (ofRejected rejected hempty hunion).IsUltra := by
  classical
  intro s
  by_cases hs : ofRejected rejected hempty hunion s
  · exact Or.inl hs
  · right
    obtain ⟨t, ht, hst⟩ := by simpa only [ofRejected_apply_iff, not_forall, not_not] using hs
    intro r hr hsr
    apply hunion t ht r hr
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ s
    · exact Or.inl (hst hx)
    · exact Or.inr (hsr hx)

/-- Every prescribed rejection is respected. -/
theorem not_ofRejected_of_mem {s : Set U} (hs : s ∈ rejected) :
    ¬ ofRejected rejected hempty hunion s :=
  fun h => h s hs (Set.Subset.refl _)

/-- Consistent acceptance labels extend to a semi-ultrafilter. The index includes a prescribed
empty rejected set; no finiteness or nonempty-carrier assumption is needed. -/
theorem exists_isUltra_of_labels {ι : Type*} (sets : ι → Set U) (labels : ι → Bool)
    (zero : ι) (hzero : sets zero = ∅) (hlabel : labels zero = false)
    (hmono : ∀ i j, sets i ⊆ sets j → labels i = true → labels j = true)
    (hcover : ∀ i j, sets i ∪ sets j = Set.univ → labels i = true ∨ labels j = true) :
    ∃ F : Semifilter U, F.IsUltra ∧ (∀ i, F (sets i) ↔ labels i = true) ∧
      ∀ s, F s ↔ ∀ i, labels i = false → ¬ s ⊆ sets i := by
  classical
  let rejected : Set (Set U) := {s | ∃ i, labels i = false ∧ sets i = s}
  have hempty : ∅ ∈ rejected := ⟨zero, hlabel, hzero⟩
  have hunion : ∀ s ∈ rejected, ∀ t ∈ rejected, s ∪ t ≠ Set.univ := by
    rintro s ⟨i, hi, rfl⟩ t ⟨j, hj, rfl⟩ h
    rcases hcover i j h with h | h <;> simp_all
  refine ⟨ofRejected rejected hempty hunion, isUltra_ofRejected rejected hempty hunion, ?_, ?_⟩
  · intro i
    constructor
    · intro h
      by_contra hi
      exact h _ ⟨i, by simpa using hi, rfl⟩ (Set.Subset.refl _)
    · rintro hi s ⟨j, hj, rfl⟩ hsub
      have := hmono i j hsub hi
      simp_all
  · intro s
    constructor
    · intro h i hi
      exact h _ ⟨i, hi, rfl⟩
    · rintro h t ⟨i, hi, rfl⟩
      exact h i hi

end Cslib.Circuits.Fusion.Semifilter
