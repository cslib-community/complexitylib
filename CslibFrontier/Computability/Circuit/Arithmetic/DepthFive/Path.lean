/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.WordPolynomial
import CslibFrontier.Foundations.LinearAlgebra.Matrix.ListProd

/-!
# Paths of iterated matrix multiplication

The polynomial `IMM_{n,n}` is the sum, over the paths `0 = P 0, P 1, …, P n = 0` through `n`
layers of `n` vertices, of the product of the variables `(t, P t, P (t + 1))` on the edges of
the path [OpenAI, §4][OpenAI2026DepthFive]. The edges of a path lie in distinct layers, so the
monomial of a path is multilinear. `Path.part P T` is the exponent vector of the product of the
edge variables in the layers `T`.

## Main definitions

* `Cslib.Circuits.DepthFive.Path`: the paths from vertex `0` to vertex `0`.
* `Path.edge`: the variable of a path in a layer.
* `Path.part`: the exponent vector of the edges of a path in a set of layers.

## Main results

* `imm_eq_sum_paths`: `IMM_{n,n}` is the sum of the monomials of the paths.
* `card_path`: there are `n ^ (n - 1)` paths.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §4 (unrefereed preprint)
-/

@[expose] public section

open MvPolynomial Cslib.Circuits.Arithmetic

namespace Cslib.Circuits.DepthFive

variable {n : ℕ} [NeZero n]

/-- The paths `0 = P 0, P 1, …, P n = 0` through the `n` matrix layers. -/
abbrev Path (n : ℕ) [NeZero n] := {P : Fin (n + 1) → Fin n // P 0 = 0 ∧ P (Fin.last n) = 0}

namespace Path

variable (P : Path n)

/-- The variable of the path in layer `t`: the entry `(P t, P (t + 1))` of the `t`-th matrix. -/
def edge (t : Fin n) : Fin n × Fin n × Fin n := (t, P.1 t.castSucc, P.1 t.succ)

@[simp] theorem edge_fst (t : Fin n) : (P.edge t).1 = t := rfl

theorem edge_injective : Function.Injective P.edge := fun _ _ h => congrArg Prod.fst h

/-- The exponent vector of the product of the edge variables in the layers `T`. -/
noncomputable def part (T : Finset (Fin n)) : Fin n × Fin n × Fin n →₀ ℕ :=
  ∑ t ∈ T, Finsupp.single (P.edge t) 1

theorem part_apply (T : Finset (Fin n)) (x : Fin n × Fin n × Fin n) :
    P.part T x = if x.1 ∈ T ∧ P.edge x.1 = x then 1 else 0 := by
  rw [part, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single_of_mem x.1 h.1 fun t _ ht => ite_eq_right fun h' => ht ?_,
      ite_eq_left h.2]
    rw [← h', edge_fst]
  · refine Finset.sum_eq_zero fun t ht => ite_eq_right fun h' => h ?_
    rw [← h', edge_fst]
    exact ⟨ht, rfl⟩

theorem monomial_part {R : Type*} [CommSemiring R] (T : Finset (Fin n)) :
    monomial (P.part T) (1 : R) = ∏ t ∈ T, X (P.edge t) :=
  monomial_sum_one T _

end Path

/-- `IMM_{n,n}` is the sum of the monomials of the paths. -/
theorem imm_eq_sum_paths (K : Type*) [CommSemiring K] :
    imm K n n = ∑ P : Path n, ∏ t, X (P.edge t) := by
  rw [imm, Matrix.list_prod_ofFn_apply, ← Finset.sum_filter,
    Finset.sum_subtype (p := fun P : Fin (n + 1) → Fin n => P 0 = 0 ∧ P (Fin.last n) = 0) _
      (by simp)]
  rfl

/-- The polynomial `IMM_{n,n}` does not depend on the coefficient ring. -/
theorem map_imm {K L : Type*} [CommSemiring K] [CommSemiring L] (f : K →+* L) :
    map f (imm K n n) = imm L n n := by
  simp [imm_eq_sum_paths]

/-- There are `n ^ (n - 1)` paths. -/
theorem card_path : Fintype.card (Path n) = n ^ (n - 1) := by
  have h0 : (0 : Fin (n + 1)) ≠ Fin.last n := (Fin.last_pos' (n := n)).ne
  rw [Fintype.card_of_subtype (Fintype.piFinset fun j : Fin (n + 1) =>
      if j = 0 ∨ j = Fin.last n then {0} else Finset.univ)]
  · rw [Fintype.card_piFinset]
    simp only [apply_ite Finset.card, Finset.card_singleton, Finset.card_univ, Fintype.card_fin,
      Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
      Finset.card_univ, Fintype.card_fin, Finset.filter_or, Finset.filter_eq', Finset.filter_eq',
      ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _), ← Finset.insert_eq,
      Finset.card_pair h0]
    rfl
  · intro P
    simp only [Fintype.mem_piFinset]
    refine ⟨fun h => ⟨by simpa using h 0, by simpa using h (Fin.last n)⟩, fun h j => ?_⟩
    split_ifs with hj
    · rcases hj with rfl | rfl <;> simp [h.1, h.2]
    · exact Finset.mem_univ _

end Cslib.Circuits.DepthFive
