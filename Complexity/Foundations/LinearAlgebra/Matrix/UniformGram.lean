/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/DotProduct.lean`)

public import Complexity.Init
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.LinearCombination

/-!
# Families with a uniform Gram matrix

Vectors `v i ∈ K^κ` whose Gram matrix `(v i ⬝ᵥ v j)` is `(d - c) I + c J`, with `d` on the diagonal
and `c` off it, are linearly independent when `d ≠ c` and `d - c + m c ≠ 0`, where `m` is the
number of vectors: these are the two eigenvalues of `(d - c) I + c J`. So there are at most `|κ|`
such vectors. This is the linear algebra bound behind the oddtown theorem and Fisher's inequality
(`Complexity.Foundations.Combinatorics.SetFamily.Oddtown`). The proof is direct: dotting a
vanishing combination `∑ g i • v i` with `v j` gives `c ∑ g + (d - c) g j = 0` for every `j`, and
summing over `j` forces `∑ g = 0`.

## Main results

* `linearIndependent_of_dotProduct_eq_ite`: linear independence.
* `Fintype.card_le_of_dotProduct_eq_ite`: the resulting bound on the number of vectors.
-/

public section

open Finset

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

/-- Vectors whose Gram matrix is `(d - c) I + c J` are linearly independent when `d ≠ c` and
`d - c + |ι| c ≠ 0`. -/
theorem linearIndependent_of_dotProduct_eq_ite [DecidableEq ι] (v : ι → κ → K) (d c : K)
    (hv : ∀ i j, v i ⬝ᵥ v j = if i = j then d else c) (hdc : d ≠ c)
    (hm : d - c + (Fintype.card ι : K) * c ≠ 0) : LinearIndependent K v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set S := ∑ i, g i with hS
  have hrow : ∀ j, S * c + g j * (d - c) = 0 := by
    intro j
    have h := congrArg (fun w => w ⬝ᵥ v j) hg
    simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, hv, zero_dotProduct] at h
    have key : ∀ i, g i * (if i = j then d else c) =
        g i * c + if i = j then g i * (d - c) else 0 := by
      intro i; split_ifs <;> ring
    rw [sum_congr rfl fun i _ => key i, sum_add_distrib, sum_ite_eq' univ j, ← sum_mul] at h
    simpa only [mem_univ, ite_true] using h
  have hS0 : S = 0 := by
    have h := sum_congr rfl fun j (_ : j ∈ (univ : Finset ι)) => hrow j
    rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← sum_mul, ← hS, sum_const_zero]
      at h
    have : S * (d - c + (Fintype.card ι : K) * c) = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_right hm
  intro j
  have h := hrow j
  rw [hS0, zero_mul, zero_add] at h
  exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hdc)

/-- The rank bound: a family of vectors in `K^κ` with Gram matrix `(d - c) I + c J`, `d ≠ c` and
`d - c + |ι| c ≠ 0`, has at most `|κ|` members. -/
theorem Fintype.card_le_of_dotProduct_eq_ite [DecidableEq ι] (v : ι → κ → K) (d c : K)
    (hv : ∀ i j, v i ⬝ᵥ v j = if i = j then d else c) (hdc : d ≠ c)
    (hm : d - c + (Fintype.card ι : K) * c ≠ 0) : Fintype.card ι ≤ Fintype.card κ := by
  have h := (linearIndependent_of_dotProduct_eq_ite v d c hv hdc hm).fintype_card_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card] at h

end
