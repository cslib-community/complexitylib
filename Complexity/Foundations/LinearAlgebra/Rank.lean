/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, rank bounds for finite spans of linear maps)

public import Complexity.Init
public import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# Rank bounds for finite spans of linear maps

Rank subadditivity bounds the rank of a linear combination by the sum of rank budgets for
its generators. The linear maps need not have finite-dimensional domains or codomains. Also
extracts a `Fin`-indexed linearly independent spanning subfamily from any `Fin`-indexed family over
a division ring.

## Main results

* `LinearMap.rank_smul_le`: scalar multiplication does not increase rank.
* `LinearMap.rank_le_sum_of_mem_span`: a rank budget for a finite span.
* `Submodule.exists_linearIndependent_fin_comp`: every `Fin`-indexed family over a division ring
  contains a `Fin`-indexed linearly independent subfamily with the same span.

## References

* The linear-map span lemmas are ported from LinearAlgebra/Rank.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
* [OpenAI2026RationalHitting]
-/

@[expose] public section

namespace LinearMap

variable {K A B : Type*} [Field K] [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]

/-- Scalar multiplication does not increase the rank of a linear map. -/
theorem rank_smul_le (c : K) (f : A →ₗ[K] B) : (c • f).rank ≤ f.rank :=
  Submodule.rank_mono (f.range_smul_le_range c)

/-- A linear map in the span of a finite family has rank at most the sum of any rank budgets
for its generators. -/
theorem rank_le_sum_of_mem_span {ι : Type*} [Fintype ι] (f : A →ₗ[K] B)
    (family : ι → A →ₗ[K] B) (budget : ι → ℕ)
    (hmem : f ∈ Submodule.span K (Set.range family))
    (hbound : ∀ i, (family i).rank ≤ budget i) : f.rank ≤ ∑ i, (budget i : Cardinal) := by
  classical
  obtain ⟨coefficients, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
  exact (rank_finsetSum_le Finset.univ _).trans
    (Finset.sum_le_sum fun i _ => (rank_smul_le (coefficients i) (family i)).trans (hbound i))

end LinearMap

/-- Every finite family `v : Fin h → V` over a division ring contains a `Fin`-indexed linearly
independent subfamily `v ∘ a` with the same span. -/
theorem Submodule.exists_linearIndependent_fin_comp (K : Type*) {V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] {h : ℕ} (v : Fin h → V) :
    ∃ (k : ℕ) (a : Fin k → Fin h), Function.Injective a ∧
      Submodule.span K (Set.range (v ∘ a)) = Submodule.span K (Set.range v) ∧
      LinearIndependent K (v ∘ a) := by
  classical
  obtain ⟨κ, a, ha, hs, hi⟩ := exists_linearIndependent' K v
  let : Fintype κ := Fintype.ofInjective a ha
  let e := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ, a ∘ e, ha.comp e.injective, ?_, hi.comp e e.injective⟩
  have he : Set.range (v ∘ a ∘ e) = Set.range (v ∘ a) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨e j, rfl⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨r, rfl⟩ := e.surjective j
      exact ⟨r, rfl⟩
  change Submodule.span K (Set.range (v ∘ a ∘ e)) = _
  rw [he, hs]
