/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Selecting original rows of a consistent linear system

The algebraic part of [ChenJiangZhu2027], Lemma 3.1 (PDF pp. 10–11): select
linearly independent original coefficient rows of a consistent rational system,
without changing its solutions. The result is over any field. Consistency is an
explicit witnessed hypothesis; no assumption about the desired selected rows is made.
This module does not implement elimination or certify a bit-operation bound.

## Main results

* `exists_original_rows`: original rows with the same solutions and at most as many
  equations as variables.
* `exists_original_rows_of_two_solutions`: in the nonunique case, strictly fewer rows
  than columns suffice, with selected size equal to the row-space dimension.

## References

* [ChenJiangZhu2027], Lemma 3.1, PDF pp. 10–11 (credits Jansen–Pieterse).
-/

public section

namespace Cslib.LinearSystem

open Submodule Matrix

variable {K ι d : Type*} [Field K] [Finite ι] [Fintype d]

/-- A consistent finite system has an equivalent subsystem of linearly independent
original rows. The selected number of rows is bounded by the number of columns. -/
theorem exists_original_rows (A : ι → d → K) (b : ι → K)
    (x₀ : d → K) (hx₀ : ∀ i, A i ⬝ᵥ x₀ = b i) :
    ∃ s : Finset ι, s.card ≤ Fintype.card d ∧
      LinearIndependent K (fun i : s => A i) ∧
      span K (Set.range (fun i : s => A i)) = span K (Set.range A) ∧
      s.card = Module.finrank K (span K (Set.range A)) ∧
      ∀ x : d → K, (∀ i ∈ s, A i ⬝ᵥ x = b i) ↔ ∀ i, A i ⬝ᵥ x = b i := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A
  let : Finite κ := Finite.of_injective a ha
  let := Fintype.ofFinite κ
  let s := Finset.univ.image a
  have hscard : s.card = Fintype.card κ := Finset.card_image_of_injective _ ha
  have hbound : s.card ≤ Fintype.card d := by
    rw [hscard]
    simpa using hli.fintype_card_le_finrank
  have hsrange : Set.range (fun i : s => A i) = Set.range (A ∘ a) := by
    ext v
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨a j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩, rfl⟩
  have hsel : LinearIndependent K (fun i : s => A i) := by
    let f : s → κ := fun i => Classical.choose (Finset.mem_image.mp i.property)
    have hf (i : s) : a (f i) = i := (Classical.choose_spec
      (Finset.mem_image.mp i.property)).2
    have hfi : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      rw [← hf i, ← hf j, hij]
    convert hli.comp f hfi using 1
    ext i j
    change A i j = A (a (f i)) j
    rw [hf]
  have hsp : span K (Set.range (fun i : s => A i)) = span K (Set.range A) := by
    rw [hsrange, hspan]
  have hrank : s.card = Module.finrank K (span K (Set.range A)) := by
    rw [← hsp, finrank_span_eq_card hsel, Fintype.card_coe]
  refine ⟨s, hbound, hsel, hsp, hrank, fun x => ⟨?_, fun h i _ => h i⟩⟩
  intro hx i
  let L : (d → K) →ₗ[K] K :=
    { toFun := fun v => v ⬝ᵥ x - v ⬝ᵥ x₀
      map_add' := by intro u v; simp [add_dotProduct]; ring
      map_smul' := by intro c v; simp [smul_dotProduct, mul_sub] }
  have hs : span K (Set.range (fun j : s => A j)) ≤ L.ker := by
    apply span_le.mpr
    rintro _ ⟨j, rfl⟩
    change A j ⬝ᵥ x - A j ⬝ᵥ x₀ = 0
    rw [hx j j.property, hx₀, sub_self]
  rw [hsrange, hspan] at hs
  have hi := hs (subset_span (Set.mem_range_self i))
  change A i ⬝ᵥ x - A i ⬝ᵥ x₀ = 0 at hi
  rw [hx₀] at hi
  exact sub_eq_zero.mp hi

omit [Finite ι] in
/-- Two solutions agree when the coefficient rows span all column vectors. -/
theorem solution_eq_of_span_eq_top (A : ι → d → K) (b : ι → K)
    (hspan : span K (Set.range A) = ⊤) {x z : d → K}
    (hx : ∀ i, A i ⬝ᵥ x = b i) (hz : ∀ i, A i ⬝ᵥ z = b i) : x = z := by
  let L : (d → K) →ₗ[K] K :=
    { toFun := fun v => v ⬝ᵥ (x - z)
      map_add' := by intro u v; exact add_dotProduct u v (x - z)
      map_smul' := by intro c v; exact smul_dotProduct c v (x - z) }
  have hs : span K (Set.range A) ≤ L.ker := by
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    change A i ⬝ᵥ (x - z) = 0
    rw [dotProduct_sub, hx, hz, sub_self]
  rw [hspan] at hs
  have hzero : x - z = 0 := dotProduct_eq_zero_iff.mp (fun v => by
    rw [dotProduct_comm]
    exact hs (Submodule.mem_top))
  exact sub_eq_zero.mp hzero

/-- In the nonunique consistent case, row selection actually leaves at most
`r - 1` original rows. Combined with the two-boundary path, this is the algebraic
source of the `2r - 2` variable budget in STOC submission 1575, Theorem 1.2.
No runtime guarantee or elimination algorithm is asserted here. -/
theorem exists_original_rows_of_two_solutions (A : ι → d → K) (b : ι → K)
    (x z : d → K) (hx : ∀ i, A i ⬝ᵥ x = b i) (hz : ∀ i, A i ⬝ᵥ z = b i)
    (hne : x ≠ z) :
    ∃ s : Finset ι, s.card < Fintype.card d ∧
      s.card = Module.finrank K (span K (Set.range A)) ∧
      ∀ u : d → K, (∀ i ∈ s, A i ⬝ᵥ u = b i) ↔ ∀ i, A i ⬝ᵥ u = b i := by
  obtain ⟨s, hbound, _, _, hrank, hsol⟩ := exists_original_rows A b x hx
  refine ⟨s, lt_of_le_of_ne hbound ?_, hrank, hsol⟩
  intro heq
  have hfull : span K (Set.range A) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← hrank, heq, Module.finrank_pi]
  exact hne (solution_eq_of_span_eq_top A b hfull hx hz)

end Cslib.LinearSystem
