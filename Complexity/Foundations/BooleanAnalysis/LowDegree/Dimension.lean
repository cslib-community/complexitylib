/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.LowDegree
public import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Exact dimensions of low-degree functions on the Boolean cube

The squarefree monomials form a basis over any field: they span all functions, and their number
equals the dimension of the function space. Restricting this basis gives the exact dimension of
`BitString.lowDegree`. Complementing coordinate sets bounds the codimension by another
low-degree dimension, which is useful when a polynomial-method argument budgets exceptional
outputs by codimension.

## Main results

* `Cslib.BitString.linearIndependent_monomial`: squarefree monomials are independent.
* `Cslib.BitString.finrank_lowDegree`: the exact dimension, including degrees above the dimension
  of the cube.
* `Cslib.BitString.card_sub_finrank_lowDegree_le`: a complementary-degree codimension bound.
-/

public section

namespace Cslib.BitString

open Finset Module

variable {K ι : Type*} [Field K]

/-- The squarefree monomials on a finite Boolean cube are linearly independent over any field. -/
theorem linearIndependent_monomial [Finite ι] : LinearIndependent K (monomial K (ι := ι)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · intro f _
    exact (Submodule.span_mono (Set.image_subset_range _ _)) (mem_lowDegree_self f)
  · simp [Module.finrank_fintype_fun_eq_card]

variable [Fintype ι]

/-- The dimension of the functions of degree at most `D` is exactly the number of coordinate
sets of cardinality at most `D`. -/
theorem finrank_lowDegree (D : ℕ) :
    finrank K (lowDegree K ι D) = #{S : Finset ι | #S ≤ D} := by
  classical
  have hli := (linearIndependent_monomial (K := K) (ι := ι)).comp
    (fun S : {S : Finset ι // #S ≤ D} => S.1) Subtype.val_injective
  have hrange : Set.range (fun S : {S : Finset ι // #S ≤ D} => monomial K S.1) =
      monomial K '' {S | #S ≤ D} := by
    ext f
    simp
  change LinearIndependent K (fun S : {S : Finset ι // #S ≤ D} => monomial K S.1) at hli
  have hdim := (linearIndependent_iff_card_eq_finrank_span.mp hli).symm
  rw [Set.finrank, hrange, ← lowDegree] at hdim
  simpa only [Fintype.card_subtype] using hdim

/-- Complementing sets of size greater than `D` injects them into the sets of size at most `E`
when `n ≤ D + E + 1`. Equivalently, the codimension of degree `D` is at most the dimension of
degree `E`. -/
theorem card_sub_finrank_lowDegree_le {D E : ℕ} (h : Fintype.card ι ≤ D + E + 1) :
    2 ^ Fintype.card ι - finrank K (lowDegree K ι D) ≤
      #{S : Finset ι | #S ≤ E} := by
  classical
  rw [finrank_lowDegree]
  have hpartition := card_filter_add_card_filter_not (s := (univ : Finset (Finset ι)))
    (p := fun S => #S ≤ D)
  have htotal : 2 ^ Fintype.card ι = Fintype.card (Finset ι) := by
    simp
  rw [htotal, ← card_univ, ← hpartition, Nat.add_sub_cancel_left]
  apply card_le_card_of_injOn (fun S => Sᶜ)
  · intro S hS
    have hlarge : ¬ #S ≤ D := (mem_filter.1 hS).2
    have hSle := card_le_univ S
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rw [card_compl]
    omega
  · intro S hS T hT hST
    exact compl_injective hST

end Cslib.BitString
