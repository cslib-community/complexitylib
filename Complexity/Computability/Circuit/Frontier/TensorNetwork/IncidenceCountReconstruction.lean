/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceArraySum
public import Complexity.Foundations.BooleanAnalysis.SparseIncidence
import Mathlib.Data.List.GetD

/-!
# Exact incidence-polynomial reconstruction for actual sparse input lists

Instantiate the source incidence expansion on the actual normalized list input, not a supplied
finite system or supplied coefficients. The degree bound follows from the listed monomial
lengths, the cap is computed as `k*(sys.length+2*n)`, and the least nonnegative residue modulo
`2^(n+1)` is the exact declared-variable solution count, including free variables.

This proves the target value for the global network-decomposition step of [OpenAI2026ETH],
Lemma D.2 (PDF pp.55–56). It does not assert that the native degree-array contractions already
sum to this polynomial: that global correspondence remains to be proved.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.systemIncidencePolynomial`: the source incidence
  polynomial at the computed cap, from the original listed system.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.rootCount_eq_incidenceResidue`: exact count recovery
  from this input-derived polynomial, without supplied coefficients or an answer premise.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, equations (D.1)–(D.2), PDF pp.55–56.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.BitString Cslib.GenericRAM Polynomial

/-- The incidence polynomial of the actual listed system. This is a mathematical specification,
not an alternative evaluator that enumerates its exponentially many monomials. -/
noncomputable def systemIncidencePolynomial (k : ℕ) (p : ArrayInput) : ℤ[X] :=
  let eqs := fun i : Fin p.2.length => HeavyBranchFold.toFinsetEquation p.1 p.2[i]
  incidenceSum (fun i => equationScope (eqs i)) (fun i => parityCoeff (p.1 + 1) (eqs i))
    (degreeCap k p)

private theorem card_list_monomial_le (n : ℕ) (m : List ℕ) :
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ m)).card ≤ m.length := by
  let S := Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ m)
  calc S.card = (S.image Fin.val).card :=
        (Finset.card_image_of_injective S Fin.val_injective).symm
    _ ≤ m.toFinset.card := Finset.card_le_card (by
        intro v hv
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
        exact List.mem_toFinset.mpr (Finset.mem_filter.mp hi).2)
    _ ≤ m.length := List.toFinset_card_le m

/-- The listed degree bound implies the finite equation degree bound. -/
private theorem degree_toFinsetEquation_le {n k : ℕ} {eq : List (List ℕ)}
    (hk : ∀ m ∈ eq, m.length ≤ k) :
    ∀ M ∈ HeavyBranchFold.toFinsetEquation n eq, M.card ≤ k := by
  intro M hM
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hM)
  exact (card_list_monomial_le n m).trans (hk m hm)

/-- The least nonnegative residue of the actual input-derived incidence polynomial is the exact
number of common zeros. No native output equality or coefficient congruence is assumed. -/
theorem rootCount_eq_incidenceResidue {k n : ℕ} {sys : List (List (List ℕ))}
    (hcan : ∀ eq ∈ sys, Cslib.Complexity.IsCanonicalEquation eq)
    (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (hdegree : ∀ eq ∈ sys, ∀ m ∈ eq, m.length ≤ k) :
    (sumCoeffsBelow (n + 1) (systemIncidencePolynomial k (n, sys)) %
      (2 : ℤ) ^ (n + 1)).toNat = HeavyBranchFold.rootCount n sys := by
  let eqs := fun i : Fin sys.length => HeavyBranchFold.toFinsetEquation n sys[i]
  have hk : ∀ i, ∀ M ∈ eqs i, M.card ≤ k := fun i =>
    degree_toFinsetEquation_le (hdegree sys[i] (List.getElem_mem i.isLt))
  have he := emod_sum_eq_commonZeroCount_of_modEq eqs
    (I := fun i => equationScope (eqs i)) (fun _ => Finset.Subset.refl _) hk
    (ℓ := n + 1) (K := degreeCap k (n, sys)) (by simp)
    (by simp [degreeCap])
    (fun j => (systemIncidencePolynomial k (n, sys)).coeff j)
    (fun j _ => Int.ModEq.refl _)
  change sumCoeffsBelow (n + 1) (systemIncidencePolynomial k (n, sys)) %
    (2 : ℤ) ^ (n + 1) = _ at he
  rw [he, Int.toNat_natCast, ← HeavyBranchFold.rootCount_eq_commonZeroCount hcan hvars]

end Cslib.Circuits.Frontier.IncidenceNetwork
