/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceRankSum

/-! # Finite-sum reconstruction: unused ranks, empty capacities and actual native readback -/

public section

namespace CslibFrontierTests.TensorNetworkIncidenceRankSum

open Cslib Cslib.BitString Cslib.GenericRAM Cslib.Complexity Cslib.Circuits.Frontier
open Cslib.Circuits.Frontier.IncidenceNetwork Polynomial

/-- Three singleton subsets occupy only three of the four two-bit encodings. -/
abbrev sys : List (List (List ℕ)) := [[[0], [1], [2]]]

example : numWires 1 sys [1] = 2 ∧ (pairInc 1 sys 0 0).length.choose 1 = 3 := by decide
example : blockIndices (rowBlocks 1 sys [1] 0) [true, true] = [3] ∧
    incEntry (rowVertex 4 2 1 sys [1] 0).2 [true, true] = [] := by decide
example : Fintype.card (CombinationRanks 1 sys [1]) = 3 := by
  simp only [CombinationRanks, Fintype.card_pi, Fintype.card_fin]
  norm_num [Fin.prod_univ_one]
  decide

/-- An impossible capacity gives zero without evaluating an oracle. -/
example : rankPolynomial 4 2 1 7 3 sys [4] = 0 := by
  rw [← polyContraction_eq_rankPolynomial 4 2 1 7 0 3 sys [4]]
  exact polyContraction_eq_zero_of_capacity _ _ _ _ _ _ _ _ 0 0 (by decide) (by decide)
    (by decide)
example : rankPolynomial 4 2 1 0 3 sys [1] = 0 := by
  rw [← polyContraction_eq_rankPolynomial 4 2 1 0 0 3 sys [1]]
  exact polyContraction_eq_zero_of_dead _ _ _ _ _ _ _ _ (by decide)

/-- The empty assignment space has one term, not zero; the natural contraction is one. -/
example : rankPolynomial 4 2 0 0 0 [] [] = 1 := by
  rw [← polyContraction_eq_rankPolynomial 4 2 0 0 0 0 [] []]
  have hn : (network 4 2 0 0 0 0 [] []).2 = ⟨0, []⟩ := rfl
  rw [hn]
  simp [DescribedNetwork.polyContraction, DescribedNetwork.contraction]

/-- Padding is included in the actual polynomial-to-incidence identity on non-power-of-two ranks. -/
example : truncNatHom 4 2 ((network 4 2 1 7 9 3 sys [1]).2.polyContraction incEntry) =
    truncRingHom 4 2 (rankIncidencePolynomial 2 1 7 3 sys [1]) :=
  truncNatHom_polyContraction_eq_rankIncidencePolynomial _ _ _ _ _ _ (by decide) _ _

/-- The original encoded input determines cap, groups, arrays and every coefficient in readback. -/
example : (sumCoeffsBelow 3
    (∑ i ∈ Finset.range (degreeCount 1 (2, [[[0]]])),
      rankIncidencePolynomial 3 (Nat.ceilQuarter 2) (degreeCap 1 (2, [[[0]]])) 2 [[[0]]]
        (arrayAt (degreeCap 1 (2, [[[0]]])) (Nat.ceilQuarter 2) i)) % 8).toNat =
          sumArrays 1 (2, [[[0]]]) := by
  exact sumArrays_eq_rankIncidenceResidue 1 (2, [[[0]]]) (by decide)

/-- The same actual machine has the proved grouped-sum semantics and original-input resource
bounds on a genuine sparse family. No output, rank or runtime budget is supplied. -/
example : ∃ (cs : NativeCertificate (sumArrays 1) encArrayInput Turing.MultiTapeTM.encNat)
    (A n₀ : ℕ), ∀ n, n₀ ≤ n →
    (sumCoeffsBelow (n + 1)
      (∑ i ∈ Finset.range (degreeCount 1 (n, [])),
        rankIncidencePolynomial (n + 1) (Nat.ceilQuarter n) (degreeCap 1 (n, [])) n []
          (arrayAt (degreeCap 1 (n, [])) (Nat.ceilQuarter n) i)) %
            (2 : ℤ) ^ (n + 1)).toNat = sumArrays 1 (n, []) ∧
    let L := (encArrayInput (n, [])).length
    cs.time (n, []) ≤ (degreeCount 1 (n, []) + 1) *
        (A * (L + 1) ^ A * 2 ^ (A * sizeParam n / Nat.sqrt (Nat.log 2 (sizeParam n)))) ∧
      cs.space (n, []) ≤ A * (L + 1) ^ A := by
  obtain ⟨cs, A, n₀, hA⟩ := exists_sumArrays_certificate 1 1 (by decide)
  refine ⟨cs, A, n₀ + 1, fun n hn => ⟨sumArrays_eq_rankIncidenceResidue 1 (n, []) (by omega),
    hA n (by omega) [] ?_⟩⟩
  exact {
    vars_lt := by simp
    canonical := by simp
    length_le := by simp
    monomials_le := by simp
    degree_le := by simp
    scope_le := by simp
    varDegree_le := by simp [varDegree] }

end CslibFrontierTests.TensorNetworkIncidenceRankSum
