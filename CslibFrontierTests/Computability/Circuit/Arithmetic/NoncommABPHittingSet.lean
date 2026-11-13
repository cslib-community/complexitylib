/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.NoncommABP

/-!
# Hitting sets of matrices for non-commutative branching programs

The non-commutative polynomial `x₀ x₁` over the rationals is computed by the branching program of
degree two with one vertex in each layer, whose edge after layer `k` is labelled by the variable
`x_k`. So it is nonzero at a pair of `3 × 3` matrices of the hitting set for degree two and width
one in two variables.
-/

public section

namespace CslibFrontierTests.NoncommABPHittingSet

open Cslib.Circuits.Arithmetic FreeAlgebra

/-- The width-one program of degree two whose edge after layer `k` is labelled `x_k`. -/
def prog : NoncommABP ℚ (Fin 2) 2 where
  width := fun _ => 1
  width_zero := rfl
  width_deg := rfl
  weight := fun k x => Matrix.of fun _ _ => if (x : ℕ) = k then 1 else 0

/-- The program computes `x₀ x₁`. -/
theorem polynomial_prog : prog.polynomial = ι ℚ 0 * ι ℚ 1 := by
  have h : ∀ (k : ℕ) (j : Fin (prog.width k)), Finset.univ = {j} := fun k j =>
    Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_univ _, fun i _ =>
      Fin.ext ((Nat.lt_one_iff.1 i.2).trans (Nat.lt_one_iff.1 j.2).symm)⟩
  have h2 : (Finset.univ : Finset (Fin (prog.width 2))) = {⟨0, Nat.one_pos⟩} := h 2 _
  have h1 : (Finset.univ : Finset (Fin (prog.width 1))) = {⟨0, Nat.one_pos⟩} := h 1 _
  have h0 : (Finset.univ : Finset (Fin (prog.width 0))) = {⟨0, Nat.one_pos⟩} := h 0 _
  rw [NoncommABP.polynomial, h2, Finset.sum_singleton, NoncommABP.pre_succ, h1,
    Finset.sum_singleton, NoncommABP.pre_succ, h0, Finset.sum_singleton, NoncommABP.pre_zero]
  simp [NoncommABP.edge, prog, Fin.sum_univ_two]

/-- `x₀ x₁` is not zero: it is `1` when both variables are `1`. -/
theorem polynomial_prog_ne_zero : prog.polynomial ≠ 0 := fun h => by
  have h' := congrArg (lift ℚ fun _ : Fin 2 => (1 : ℚ)) h
  simp [polynomial_prog] at h'

/-- The hitting set contains a pair of matrices where `x₀ x₁` is nonzero. -/
theorem exists_lift_ne_zero :
    ∃ P ∈ noncommABPHittingSet ℚ 2 2 1, lift ℚ P prog.polynomial ≠ 0 :=
  exists_mem_noncommABPHittingSet_lift_ne_zero prog (fun _ _ => le_rfl) polynomial_prog_ne_zero

/-- The hitting set is no larger than the one for read-once oblivious programs in two variables,
of width one, with layers of degree at most one. -/
example : (noncommABPHittingSet ℚ 2 2 1).card ≤ (roabpHittingSet ℚ 2 1 1).card :=
  card_noncommABPHittingSet_le 2 2 1

end CslibFrontierTests.NoncommABPHittingSet
