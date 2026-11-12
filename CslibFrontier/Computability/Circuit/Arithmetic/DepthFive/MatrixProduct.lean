/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.OfFintype
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.ListProd

/-!
# A depth-five circuit for an entry of a product of matrices

Let `B 0, …, B (r - 1)` be `ν × ν` matrices of polynomials such that every entry of `B j` is a
linear combination of monomials of one degree `e j`, the monomials being indexed by a finite type
`Λ` and shared by all entries. Entry `(0, 0)` of the product `B 0 * ⋯ * B (r - 1)` is the sum over
index tuples `P : Fin (r + 1) → Fin ν` with `P 0 = P r = 0` of the products
`∏ j, B j (P j) (P (j + 1))`. This is a homogeneous depth-five circuit: the monomials are the
lower product gates, the entries of the matrices are the middle sum gates, and the index tuples
are the upper product gates. It has `r * |Λ|` lower products, `r * ν ^ 2` middle sums and
`ν ^ (r + 1)` upper products; the endpoint condition is a coefficient of the output.

This is the circuit of the block construction of [OpenAI, §6][OpenAI2026DepthFive], stated for
any matrices rather than for blocks of `IMM`.

## Main results

* `Cslib.Circuits.DepthFive.exists_circuit_list_prod`: the circuit and its size.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §6 (unrefereed preprint)
-/

public section

namespace Cslib.Circuits.DepthFive

open MvPolynomial

variable {K σ : Type*} [CommSemiring K] [Fintype σ]

/-- Entry `(0, 0)` of a product of `r` matrices whose entries are combinations of monomials of
one degree, indexed by `Λ`, is computed by a homogeneous depth-five circuit with `r * |Λ|` lower
product gates, `r * ν ^ 2` middle sum gates and `ν ^ (r + 1)` upper product gates. -/
theorem exists_circuit_list_prod {ν r : ℕ} [NeZero ν] {Λ : Type*} [Fintype Λ] (e : Fin r → ℕ)
    (c : Fin r → Fin ν → Fin ν → Λ → K) (x : (j : Fin r) → Λ → Fin (e j) → σ) :
    ∃ d : Circuit K σ,
      d.polynomial = (List.ofFn fun j => (Matrix.of fun a b =>
        ∑ q, C (c j a b q) * ∏ i, X (x j q i) :
          Matrix (Fin ν) (Fin ν) (MvPolynomial σ K))).prod 0 0 ∧
      d.size = r * Fintype.card Λ + r * ν ^ 2 + ν ^ (r + 1) := by
  classical
  refine ⟨Circuit.ofFintype (L := Fin r × Λ) (M := Fin r × Fin ν × Fin ν)
      (U := Fin (r + 1) → Fin ν) (∑ j, e j) (fun (j, _) => e j)
      (fun (j, q) b v => if v = x j q b then 1 else 0) (fun (j, _, _) => e j)
      (fun (j, a, b) (j', q) => if j' = j then c j a b q else 0)
      (fun (j, a, b) (j', q) h => by
        by_cases hj : j' = j
        · rw [hj]
        · simp [hj] at h)
      (fun _ => r) (fun P j => (j, P j.castSucc, P j.succ))
      (fun P => if P 0 = 0 ∧ P (Fin.last r) = 0 then 1 else 0) (fun _ _ => rfl), ?_, ?_⟩
  · rw [Circuit.polynomial_ofFintype, Matrix.list_prod_ofFn_apply]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hprod : ∀ j : Fin r, (∑ l : Fin r × Λ,
        C (if l.1 = j then c j (P j.castSucc) (P j.succ) l.2 else 0) *
          ∏ b, ∑ v, C (if v = x l.1 l.2 b then (1 : K) else 0) * X v) =
        ∑ q, C (c j (P j.castSucc) (P j.succ) q) * ∏ i, X (x j q i) := fun j => by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
      · simp
      · intro j' _ hj
        simp [hj]
      · simp
    by_cases h : P 0 = 0 ∧ P (Fin.last r) = 0
    · simp only [h, and_self, ↓reduceIte, map_one, one_mul, Matrix.of_apply]
      exact Finset.prod_congr rfl fun j _ => hprod j
    · simp [h]
  · rw [Circuit.size_ofFintype]
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi, Finset.prod_const,
      Finset.card_univ]
    ring

end Cslib.Circuits.DepthFive
