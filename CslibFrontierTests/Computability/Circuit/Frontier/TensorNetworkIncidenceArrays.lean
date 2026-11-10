/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceArraySum
import Mathlib.Data.Nat.Sqrt

/-! # Actual degree arrays, computed networks and the native streamed sum -/

public section

namespace CslibFrontierTests.TensorNetworkIncidenceArrays

open Cslib.GenericRAM Cslib.Complexity Cslib.Circuits.Frontier
open Cslib.Circuits.Frontier.IncidenceNetwork

example : arrayCount 0 3 = 1 := by decide
example : arrayAt 0 2 0 = [0, 0, 0, 0] := by decide
example : arrayCount 9 0 = 1 ∧ arrayAt 9 0 0 = [] := by decide
example : arrayAt 2 2 14 = [2, 1, 1, 0] := by decide
example : arrayAt 2 2 80 = [2, 2, 2, 2] := by decide

/-- The selected incidences determine one index, without caller-supplied coordinate bounds. -/
example : ∃! i : Fin (arrayCount 3 2),
    arrayAt 3 2 i = [1, 0, 2, 0] := by
  exact selected_degrees_coverage 3 2 [[(0, 0)], [], [(0, 1), (1, 1)], []]
    (by decide) (by decide)

example : Nat.ceilQuarter 0 = 0 ∧ Nat.ceilQuarter 1 = 1 ∧
    Nat.ceilQuarter 16 = 2 ∧ Nat.ceilQuarter 17 = 3 := by
  have h15 : Nat.sqrt 15 = 3 := by
    have := Nat.le_sqrt.mpr (show 3 * 3 ≤ 15 by decide)
    have := Nat.sqrt_lt.mpr (show 15 < 4 * 4 by decide)
    omega
  have h3 : Nat.sqrt 3 = 1 := by
    have := Nat.le_sqrt.mpr (show 1 * 1 ≤ 3 by decide)
    have := Nat.sqrt_lt.mpr (show 3 < 2 * 2 by decide)
    omega
  norm_num [Nat.ceilQuarter_eq_sqrt, h15, h3,
    show Nat.sqrt 16 = 4 from Nat.sqrt_eq 4, show Nat.sqrt 4 = 2 from Nat.sqrt_eq 2]

/-- Cap, number of arrays and the entire network are computed from the actual system. -/
example : degreeCap 1 (2, [[[0], [1]]]) = 5 ∧
    degreeCount 1 (2, [[[0], [1]]]) = 1296 := by
  norm_num [degreeCap, degreeCount, Nat.ceilQuarter_eq_sqrt, arrayCount]
example : buildArray 1 ((2, [[[0], [1]]]), 14) =
    (3, 3, network 3 3 2 5 (sizeParam 2) 2 [[[0], [1]]] [2, 2, 0, 0]) := by
  norm_num [buildArray, degreeCap, Nat.ceilQuarter_eq_sqrt, lemmaNetwork]
  rfl

/-- A genuine family of original inputs meets the resource theorem. The loop count is computed;
no entry budget, decomposition, answer or faster counter is supplied by the client. -/
example : ∃ (cs : NativeCertificate (sumArrays 1) encArrayInput Turing.MultiTapeTM.encNat)
    (A n₀ : ℕ), ∀ n, n₀ ≤ n →
    let L := (encArrayInput (n, [])).length
    cs.time (n, []) ≤ (degreeCount 1 (n, []) + 1) *
        (A * (L + 1) ^ A * 2 ^ (A * sizeParam n / Nat.sqrt (Nat.log 2 (sizeParam n)))) ∧
      cs.space (n, []) ≤ A * (L + 1) ^ A := by
  obtain ⟨cs, A, n₀, hA⟩ := exists_sumArrays_certificate 1 1 (by decide)
  refine ⟨cs, A, n₀, fun n hn => hA n hn [] ?_⟩
  exact {
    vars_lt := by simp
    canonical := by simp
    length_le := by simp
    monomials_le := by simp
    degree_le := by simp
    scope_le := by simp
    varDegree_le := by simp [varDegree] }

end CslibFrontierTests.TensorNetworkIncidenceArrays
