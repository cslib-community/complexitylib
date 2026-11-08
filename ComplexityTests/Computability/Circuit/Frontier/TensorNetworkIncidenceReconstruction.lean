/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceArraySupport
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceCountReconstruction
import all Complexity.Computability.GenericRAM.Native.HeavyBranchFold

/-! # Actual incidence decoding, zero contributions and count reconstruction clients -/

public section

namespace ComplexityTests.TensorNetworkIncidenceReconstruction

open Cslib.BitString Cslib.Complexity Cslib.GenericRAM Cslib.Circuits.Frontier
open Cslib.Circuits.Frontier.IncidenceNetwork Polynomial

example : unrankCombination 3 2 0 = [false, true, true] ∧
    unrankCombination 3 2 2 = [true, true, false] := by decide

example : ∃! r : Fin ((3).choose 2), unrankCombination 3 2 r = [true, false, true] := by
  convert unrankCombination_coverage [true, false, true] using 1 <;> rfl

example : ∃! r : Fin ((0).choose 0), unrankCombination 0 0 r = [] := by
  simpa using unrankCombination_coverage []

/-- These are the actual deduplicated incidences; repeated raw variables do not duplicate ranks. -/
example : pairInc 1 [[[0, 0], [1]], [[1]]] 0 0 = [(0, 0), (0, 1), (1, 1)] := by decide
example : ∃! r : Fin ((3).choose 2),
    selectBlock (pairInc 1 [[[0, 0], [1]], [[1]]] 0 0, 2) r = [(0, 1), (1, 1)] := by
  exact selectBlock_coverage (pairInc 1 [[[0, 0], [1]], [[1]]] 0 0)
    (nodup_pairInc 1 [[[0, 0], [1]], [[1]]] 0 0) [(0, 1), (1, 1)] (by decide)

/-- A zero-bit block with one unique subset is valid; an impossible degree is still rejected. -/
example : blockWires ([(0, 0)], 1) = 0 ∧
    validIndices [([(0, 0)], 1)] (blockIndices [([(0, 0)], 1)] []) = true := by decide
example : blockWires ([(0, 0)], 2) = 0 ∧
    validIndices [([(0, 0)], 2)] (blockIndices [([(0, 0)], 2)] []) = false := by decide
example : incEntry (rowVertex 4 3 1 [[[0]]] [2] 0).2 [] = [] := by decide

example : FeasibleArray 1 1 [[[0]]] [1] := by
  constructor
  · decide
  · intro g hg h hh
    have hg0 : g = 0 := by omega
    have hh0 : h = 0 := by omega
    subst g
    subst h
    decide
example : ¬ FeasibleArray 1 9 [[[0]]] [2] := by
  intro hs
  have hbad := hs.2 0 (by decide) 0 (by decide)
  change 2 ≤ 1 at hbad
  omega

/-- Cap overflow and capacity overflow annihilate actual networks, with padding present. -/
example : (network 4 3 1 1 7 3 [[[0]]] [2]).2.polyContraction incEntry = 0 := by
  exact polyContraction_eq_zero_of_dead _ _ _ _ _ _ _ _ (by decide)
example : (network 4 3 1 9 7 3 [[[0]]] [2]).2.polyContraction incEntry = 0 := by
  exact polyContraction_eq_zero_of_capacity _ _ _ _ _ _ _ _ 0 0 (by decide) (by decide)
    (by decide)

example : ∃! i : Fin (arrayCount 2 1), arrayAt 2 1 i = [2] ∧
    ∃! r : Fin ((3).choose ((arrayAt 2 1 i).getD 0 0)),
      selectBlock (pairInc 1 [[[0], [1]], [[1]]] 0 0, (arrayAt 2 1 i).getD 0 0) r =
        [(0, 1), (1, 1)] := by
  have h := array_and_ranks_coverage 2 1 [[[0], [1]], [[1]]] [[(0, 1), (1, 1)]]
    (by decide) (by decide) (by
      intro b hb
      have hb0 : b = 0 := by simpa using hb
      subst b
      decide)
  obtain ⟨i, ⟨hi, hr⟩, hu⟩ := h
  refine ⟨i, ⟨hi, ?_⟩, ?_⟩
  · convert hr 0 (by decide) using 1 <;> rfl
  · intro j hj
    exact arrayAt_injective 2 1 (hj.1.trans hi.symm)

open Classical in
/-- The native output admits the proved feasible-array restriction on a concrete original input. -/
example : sumArrays 1 (2, [[[0]]]) =
    (∑ i ∈ (Finset.range (degreeCount 1 (2, [[[0]]]))).filter (fun i =>
      FeasibleArray (Nat.ceilQuarter 2) (degreeCap 1 (2, [[[0]]])) [[[0]]]
        (arrayAt (degreeCap 1 (2, [[[0]]])) (Nat.ceilQuarter 2) i)),
      Cslib.Complexity.CountingSimulation.truncCoeffSum incEntry
        (buildArray 1 ((2, [[[0]]]), i))) % 8 := by
  exact sumArrays_eq_feasible 1 (2, [[[0]]])

/-- Counts retain declared free variables, and distinguish no equations from a constant one. -/
example : (sumCoeffsBelow 3 (systemIncidencePolynomial 1 (2, [])) % (2 : ℤ) ^ 3).toNat = 4 := by
  rw [rootCount_eq_incidenceResidue (by simp) (by simp) (by simp)]
  decide
example : (sumCoeffsBelow 1 (systemIncidencePolynomial 1 (0, [])) % (2 : ℤ)).toNat = 1 := by
  rw [show (2 : ℤ) = 2 ^ (0 + 1) by norm_num,
    rootCount_eq_incidenceResidue (by simp) (by simp) (by simp)]
  decide
example : (sumCoeffsBelow 1 (systemIncidencePolynomial 1 (0, [[[]]])) % (2 : ℤ)).toNat = 0 := by
  rw [show (2 : ℤ) = 2 ^ (0 + 1) by norm_num,
    rootCount_eq_incidenceResidue (by simp [IsCanonicalEquation, IsCanonicalMonomial])
      (by simp) (by simp)]
  decide
example : (sumCoeffsBelow 3 (systemIncidencePolynomial 1 (2, [[[0]]])) %
    (2 : ℤ) ^ 3).toNat = 2 := by
  rw [rootCount_eq_incidenceResidue (by simp [IsCanonicalEquation, IsCanonicalMonomial])
    (by decide) (by decide)]
  decide

/-- The normalized-input hypothesis is material: duplicate monomials would cancel over F₂. -/
example : ¬ IsCanonicalEquation [[0], [0]] := by simp [IsCanonicalEquation]

end ComplexityTests.TensorNetworkIncidenceReconstruction
