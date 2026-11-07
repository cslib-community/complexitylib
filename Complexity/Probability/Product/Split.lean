/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Product
import Complexity.Probability.PMF.Map

/-!
# Splitting the coordinates of a finite product

Split the coordinates of an independent product by a predicate `P`, along Mathlib's
`Equiv.piEquivPiSubtypeProd`. The coordinates satisfying `P` and the remaining coordinates form two
independent products.

## Main results

* `Cslib.Probability.PMF.pi_map_piEquivPiSubtypeProd`: the two parts of a split product are
  independent products.
-/

public section

namespace Cslib.Probability.PMF

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Finite (α i)]

/-- Splitting the coordinates of an independent product by a predicate `P` gives two independent
products: one over the coordinates satisfying `P`, one over the rest. -/
theorem pi_map_piEquivPiSubtypeProd (P : ι → Prop) [DecidablePred P] (p : ∀ i, PMF (α i)) :
    (pi p).map (Equiv.piEquivPiSubtypeProd P α) =
      (pi fun i : {i // P i} => p i).bind fun a =>
        (pi fun i : {i // ¬P i} => p i).map (a, ·) := by
  ext ⟨a, b⟩
  rw [map_equiv_apply, bind_map_prodMk_apply, pi_apply, pi_apply, pi_apply,
    ← Fintype.prod_subtype_mul_prod_subtype P]
  congr 1 <;> refine Finset.prod_congr rfl fun i _ => ?_
  · simp [Equiv.piEquivPiSubtypeProd_symm_apply, i.2]
  · simp [Equiv.piEquivPiSubtypeProd_symm_apply, i.2]

end Cslib.Probability.PMF
