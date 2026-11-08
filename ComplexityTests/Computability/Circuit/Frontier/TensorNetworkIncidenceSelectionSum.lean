/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceSelectionSum

/-! # Complete native readback after capped incidence-family reindexing -/

public section

namespace ComplexityTests.TensorNetworkIncidenceSelectionSum

open Cslib Cslib.BitString Cslib.GenericRAM Cslib.Complexity
open Cslib.Circuits.Frontier.IncidenceNetwork Polynomial

/-- Repeated equations retain distinct local test positions. The original row identity has not
been replaced by a set of equations. -/
example : (fun _ : Fin (1 * 1) => [(0, 0), (1, 0)]) ∈ selectionFamilies 1 [[[0]], [[0]]] := by
  rw [mem_selectionFamilies]
  intro b
  fin_cases b
  decide

/-- One of three singleton choices is covered at degree one but excluded at degree zero. -/
example : (fun _ : Fin (1 * 1) => [(0, 1)]) ∈
    (selectionFamilies 1 [[[0], [1], [2]]]).filter (fun parts => ∑ b, (parts b).length ≤ 1) ∧
    (fun _ : Fin (1 * 1) => [(0, 1)]) ∉
      (selectionFamilies 1 [[[0], [1], [2]]]).filter (fun parts => ∑ b, (parts b).length ≤ 0) := by
  have hm : (fun _ : Fin (1 * 1) => [(0, 1)]) ∈ selectionFamilies 1 [[[0], [1], [2]]] := by
    rw [mem_selectionFamilies]
    intro b
    fin_cases b
    decide
  simp [Finset.mem_filter, hm]

/-- Actual output correspondence on a nonconstant equation, with no output premise. -/
example : (sumCoeffsBelow 2 (selectionPolynomial 2 1 3 1 [[[0]]]) % 4).toNat =
    sumArrays 1 (1, [[[0]]]) := by
  have h := sumArrays_eq_selectionResidue 1 (1, [[[0]]]) (by decide)
  norm_num [Nat.ceilQuarter_eq_sqrt, degreeCap] at h
  exact h

/-- No equations: readback still includes both declared variables in the weight. -/
example : (sumCoeffsBelow 3
    (selectionPolynomial 3 (Nat.ceilQuarter 2) 0 2 []) % 8).toNat =
      sumArrays 0 (2, []) := by
  have h := sumArrays_eq_selectionResidue 0 (2, []) (by decide)
  norm_num [degreeCap] at h
  exact h

/-- The correspondence includes the constant contradictory equation and a zero cap. -/
example : (sumCoeffsBelow 2 (selectionPolynomial 2 1 0 1 [[[]]]) % 4).toNat =
    sumArrays 0 (1, [[[]]]) := by
  have h := sumArrays_eq_selectionResidue 0 (1, [[[]]]) (by decide)
  norm_num [Nat.ceilQuarter_eq_sqrt, degreeCap] at h
  exact h

/-- The reindexed semantics belongs to the existing certified machine, preserving the actual
binary time (including array traversal) and original-input polynomial peak workspace. -/
example (k c : ℕ) (hk : 1 ≤ k) :
    ∃ (cs : NativeCertificate (sumArrays k) encArrayInput Turing.MultiTapeTM.encNat)
      (A n₀ : ℕ), ∀ n, n₀ ≤ n → ∀ sys,
      SubexponentialSAT.IncidenceBranching.IsSparseBranch k c n sys →
      (sumCoeffsBelow (n + 1)
        (selectionPolynomial (n + 1) (Nat.ceilQuarter n) (degreeCap k (n, sys)) n sys) %
          (2 : ℤ) ^ (n + 1)).toNat = sumArrays k (n, sys) ∧
      let L := (encArrayInput (n, sys)).length
      cs.time (n, sys) ≤ (degreeCount k (n, sys) + 1) *
        (A * (L + 1) ^ A * 2 ^ (A * sizeParam n / Nat.sqrt (Nat.log 2 (sizeParam n)))) ∧
        cs.space (n, sys) ≤ A * (L + 1) ^ A := by
  obtain ⟨cs, A, n₀, hA⟩ := exists_sumArrays_certificate k c hk
  exact ⟨cs, A, n₀ + 1, fun n hn sys hs =>
    ⟨sumArrays_eq_selectionResidue k (n, sys) (by omega), hA n (by omega) sys hs⟩⟩

end ComplexityTests.TensorNetworkIncidenceSelectionSum
