/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Semifilter

/-!
# Exact consistency and the approximation interpretation of Fusion

The witnesses used for general set constructions require only acceptance of inputs true at
the reference point. Oliveira's nonmonotone Fusion model instead requires exact agreement on
both positive and negative literals [Oliveira2018Approximation, Definition 6]. These conditions
are different even when both polarities are supplied.

The observation of a set at a witness changes membership only at the distinguished point.
Under exact consistency it preserves supplied inputs. Unions have no positive error and
intersections have no negative error; the positive intersection error is precisely failure
to preserve the restricted pair. This is the local model bridge in Oliveira's Theorem 3.
It does not prove the random-pair lemma or the fixed-distribution counting barrier.

## Main definitions

* `Cslib.Circuits.Fusion.Semifilter.IsConsistentWith`: exact agreement with a bit vector on both
  literal polarities.
* `Cslib.Circuits.Fusion.SemifilterWitness.IsExact`: exact agreement on the supplied input family.
* `Cslib.Circuits.Fusion.SemifilterWitness.observe`: the set observed in one witness fiber of the
  extended model.

## Main results

* `Cslib.Circuits.Fusion.Semifilter.IsConsistentWith.unique`: literals determine the consistent
  bit vector.
* `Cslib.Circuits.Fusion.SemifilterWitness.observe_input`: exact witnesses preserve all supplied
  inputs.
* `Cslib.Circuits.Fusion.SemifilterWitness.inter_error`: intersection errors are exactly the
  covering pairs.

## References

* [Igor Carboni Oliveira, *Notes on the Method of Approximations and the Emergence of the
  Fusion Method*][Oliveira2018Approximation], Definition 6 and Theorem 3.
* [Alexander A. Razborov, *On the method of approximations*][Razborov1989].
-/

@[expose] public section

namespace Cslib.Circuits.Fusion

variable {U ι : Type*}

/-- Exact agreement on positive and negative coordinate literals. The carrier `U` can be the
negative inputs, while `point` is a positive input outside this carrier. -/
def Semifilter.IsConsistentWith (F : Semifilter U) (coordinates : U → ι → Bool)
    (point : ι → Bool) : Prop :=
  ∀ i b, F {x | coordinates x i = b} ↔ point i = b

/-- A semifilter consistent with two bit vectors determines the same vector. -/
theorem Semifilter.IsConsistentWith.unique {F : Semifilter U}
    {coordinates : U → ι → Bool} {point₁ point₂ : ι → Bool}
    (h₁ : F.IsConsistentWith coordinates point₁)
    (h₂ : F.IsConsistentWith coordinates point₂) : point₁ = point₂ := by
  funext i
  exact ((h₂ i (point₁ i)).mp ((h₁ i (point₁ i)).mpr rfl)).symm

variable {n : ℕ} {target : Set U} {input : Fin n → Set U}
  {admissible : Semifilter ↥(targetᶜ) → Prop}

/-- Exact consistency strengthens the one-sided `above` field of a semifilter witness. -/
def SemifilterWitness.IsExact (w : SemifilterWitness target input admissible) : Prop :=
  ∀ i, w.filter (Subtype.val ⁻¹' input i) ↔ w.point.val ∈ input i

/-- Since acceptance of true inputs is already required, exactness is equivalent to rejection
of every false input. -/
theorem SemifilterWitness.isExact_iff (w : SemifilterWitness target input admissible) :
    w.IsExact ↔ ∀ i, w.point.val ∉ input i → ¬ w.filter (Subtype.val ⁻¹' input i) := by
  constructor
  · exact fun h i hi hF => hi ((h i).mp hF)
  · intro h i
    exact ⟨fun hF => Classical.byContradiction fun hi => h i hi hF, w.above i⟩

/-- Exact coordinate consistency gives exactness for every supplied family of literals.
The family can contain both polarities, repetitions, or only selected literals. -/
theorem SemifilterWitness.isExact_of_isConsistentWith {ι : Type*}
    {target : Set (ι → Bool)} (indices : Fin n → ι) (polarities : Fin n → Bool)
    {admissible : Semifilter ↥(targetᶜ) → Prop}
    (w : SemifilterWitness target (fun j => {x | x (indices j) = polarities j}) admissible)
    (h : w.filter.IsConsistentWith Subtype.val w.point.val) : w.IsExact :=
  fun j => h (indices j) (polarities j)

/-- Observation in a single witness fiber of the extended approximation model. Away from its
distinguished point, membership is unchanged. -/
def SemifilterWitness.observe (w : SemifilterWitness target input admissible)
    (s : Set U) : Set U :=
  open Classical in
  {x | if x = w.point.val then w.filter (Subtype.val ⁻¹' s) else x ∈ s}

/-- At `w.point.val`, membership in `w.observe s` is acceptance of `Subtype.val ⁻¹' s` by
`w.filter`. -/
@[simp] theorem SemifilterWitness.mem_observe_point
    (w : SemifilterWitness target input admissible) (s : Set U) :
    w.point.val ∈ w.observe s ↔ w.filter (Subtype.val ⁻¹' s) := by
  simp [observe]

/-- Exact consistency makes every supplied input unchanged by observation. -/
theorem SemifilterWitness.observe_input (w : SemifilterWitness target input admissible)
    (h : w.IsExact) (i : Fin n) : w.observe (input i) = input i := by
  ext x
  by_cases hx : x = w.point.val
  · subst x
    exact w.mem_observe_point _ |>.trans (h i)
  · simp [observe, hx]

/-- Observation accepts no more points of an intersection than the intersection of observations.
Thus the approximation model has no negative intersection error. -/
theorem SemifilterWitness.observe_inter_subset
    (w : SemifilterWitness target input admissible) (s t : Set U) :
    w.observe (s ∩ t) ⊆ w.observe s ∩ w.observe t := by
  intro x hx
  by_cases heq : x = w.point.val
  · subst x
    simp only [mem_observe_point, Set.mem_inter_iff] at hx ⊢
    exact ⟨w.filter.monotone (a := Subtype.val ⁻¹' (s ∩ t)) (fun _ h => h.1) hx,
      w.filter.monotone (a := Subtype.val ⁻¹' (s ∩ t)) (fun _ h => h.2) hx⟩
  · simpa [observe, heq] using hx

/-- Unions have no positive error in the observation model. -/
theorem SemifilterWitness.union_subset_observe
    (w : SemifilterWitness target input admissible) (s t : Set U) :
    w.observe s ∪ w.observe t ⊆ w.observe (s ∪ t) := by
  intro x hx
  by_cases heq : x = w.point.val
  · subst x
    simp only [Set.mem_union, mem_observe_point] at hx ⊢
    exact hx.elim (w.filter.monotone fun _ h => Or.inl h)
      (w.filter.monotone fun _ h => Or.inr h)
  · simpa [observe, heq] using hx

/-- Positive intersection errors occur exactly at the distinguished point and exactly when
the restricted pair covers the witness semifilter. -/
theorem SemifilterWitness.inter_error (w : SemifilterWitness target input admissible)
    (s t : Set U) (x : U) :
    x ∈ (w.observe s ∩ w.observe t) \ w.observe (s ∩ t) ↔
      x = w.point.val ∧
        ¬ w.filter.PreservesPair (Subtype.val ⁻¹' s, Subtype.val ⁻¹' t) := by
  classical
  by_cases hx : x = w.point.val
  · subst x
    simp [Semifilter.PreservesPair, observe, not_imp, and_assoc]
  · simp [observe, hx]

/-- The target's distinguished positive point is always an observation error. -/
theorem SemifilterWitness.not_mem_observe_target
    (w : SemifilterWitness target input admissible) :
    w.point.val ∉ w.observe target := by
  rw [w.mem_observe_point]
  exact fun h => w.not_predicate_target fun _ => h

end Cslib.Circuits.Fusion
