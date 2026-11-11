/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.LineCode.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Line codes spanned by line-parity functions

Line parity is a linear condition, so every linear combination of functions with line parity has
line parity. If `f : ι → (Fin ℓ → K) → K` is linearly independent, its evaluation rows
`x ↦ (f i x)_i` span `ι → K`, so some set of points has rows forming a basis of `ι → K`. This set
is the information set: data on it is extended by applying, to the row of every point, the linear
functional that takes the given values on the basis rows. The extension is a linear combination of
the `f i`, so it inherits their line parity.

## Main results

* `Cslib.LineCode.exists_card_info_eq_of_linearIndependent`: linearly independent functions with
  line parity span a line code with `Fintype.card ι` information symbols.

## References

* Adapted from MassProduction/HighRate/Systematic.lean and MassProduction/HighRate/Code.lean
  in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.LineCode

open Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ : ℕ}

/-- If `f : ι → (Fin ℓ → K) → K` is linearly independent and every `f i` has line parity, there
is a line code on `K ^ ℓ` with exactly `Fintype.card ι` information symbols. (The code built in
the proof is spanned by the `f i`; the statement records only its size.) -/
theorem exists_card_info_eq_of_linearIndependent {ι : Type*} [Fintype ι]
    (f : ι → (Fin ℓ → K) → K) (hf : LinearIndependent K f)
    (hsum : ∀ i u v, v ≠ 0 → ∑ c ∈ (univ : Finset K).erase 0, f i (u + c • v) = f i u) :
    ∃ C : LineCode K ℓ, C.info.card = Fintype.card ι := by
  classical
  let row : (Fin ℓ → K) → ι → K := fun x i => f i x
  have hrow : Submodule.span K (Set.range row) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hf
  obtain ⟨S, -, -, hS, hli⟩ :=
    exists_linearIndepOn_extension (linearIndepOn_empty K row) (Set.empty_subset Set.univ)
  have hspan : ⊤ ≤ Submodule.span K (Set.range fun x : S => row x) := by
    rw [← hrow, ← Set.image_eq_range, ← Set.image_univ]
    exact Submodule.span_le.mpr hS
  -- The rows of the points of `S` form a basis `B`; a codeword is a functional applied to rows.
  let B := Module.Basis.mk hli hspan
  refine ⟨{ info := S.toFinset
            extend := fun data y => B.constr K (fun x => data x) (row y)
            extend_eq := fun data u hu => ?_
            sum_extend := fun data u v hv => ?_ }, ?_⟩
  · rw [← Module.Basis.mk_apply hli hspan ⟨u, Set.mem_toFinset.mp hu⟩, Module.Basis.constr_basis]
  · have hrow_sum : row u = ∑ c ∈ (univ : Finset K).erase 0, row (u + c • v) := by
      funext i
      rw [Finset.sum_apply]
      exact (hsum i u v hv).symm
    rw [hrow_sum, map_sum]
  · rw [Set.toFinset_card, ← Module.finrank_eq_card_basis B, Module.finrank_fintype_fun_eq_card]

end Cslib.LineCode
