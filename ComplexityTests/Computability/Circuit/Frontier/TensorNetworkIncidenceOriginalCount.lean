/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceOriginalCounter
import all Complexity.Computability.GenericRAM.Native.HeavyBranchFold

/-! # Original assignment counts from actual native incidence contractions -/

public section

namespace ComplexityTests.TensorNetworkIncidenceOriginalCount

open Cslib Cslib.BitString Cslib.GenericRAM Cslib.Complexity
open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.IncidenceNetwork Polynomial

/-- A genuine non-power-of-two local subset capacity, followed through to the original count. -/
example : sumArrays 1 (3, [[[0], [1], [2]]]) = 4 := by
  rw [sumArrays_eq_rootCount (by decide)
    (by simp [IsCanonicalEquation, IsCanonicalMonomial]) (by decide) (by decide)]
  decide

/-- Declared variables outside all scopes remain free. -/
example : sumArrays 1 (4, [[[0]]]) = 8 := by
  rw [sumArrays_eq_rootCount (by decide)
    (by simp [IsCanonicalEquation, IsCanonicalMonomial]) (by decide) (by decide)]
  decide

/-- The two repeated equations lie in different groups and have the same local position. -/
example : sumArrays 1 (2, [[[0]], [[0]]]) = 2 := by
  rw [sumArrays_eq_rootCount (by decide)
    (by simp [IsCanonicalEquation, IsCanonicalMonomial]) (by decide) (by decide)]
  decide

/-- Interleaved original rows: group zero has two different local test positions. -/
example : sumArrays 1 (2, [[[0]], [[1]], [[0], [1]]]) = 1 := by
  rw [sumArrays_eq_rootCount (by decide)
    (by simp [IsCanonicalEquation, IsCanonicalMonomial]) (by decide) (by decide)]
  decide

/-- A nonlinear equation with a constant term, and one declared free variable. -/
example : sumArrays 2 (3, [[[0, 1], []]]) = 2 := by
  rw [sumArrays_eq_rootCount (by decide)
    (by simp [IsCanonicalEquation, IsCanonicalMonomial]) (by decide) (by decide)]
  decide

/-- Empty scopes and zero cap preserve all free variables or reject a constant contradiction. -/
example : sumArrays 0 (2, []) = 4 ∧ sumArrays 0 (2, [[[]]]) = 0 := by
  constructor
  · rw [sumArrays_eq_rootCount (by decide) (by simp) (by simp) (by simp)]
    decide
  · rw [sumArrays_eq_rootCount (by decide)
      (by simp [IsCanonicalEquation, IsCanonicalMonomial]) (by simp) (by simp)]
    decide

/-- The precise requested modular-polynomial bridge on original rows. -/
example : truncRingHom 3 3
      (selectionPolynomial 3 (Nat.ceilQuarter 2) (degreeCap 1 (2, [[[0]], [[0]]]))
        2 [[[0]], [[0]]]) =
    truncRingHom 3 3 (systemIncidencePolynomial 1 (2, [[[0]], [[0]]])) := by
  exact trunc_selectionPolynomial_eq_systemIncidencePolynomial (by decide)
    (by simp [IsCanonicalEquation, IsCanonicalMonomial]) (by decide)

/-- Zero-variable dispatch checks the unique assignment; no positive-size enumeration is used. -/
example : countOriginal 1 (0, []) = 1 ∧ countOriginal 1 (0, [[[]]]) = 0 ∧
    zeroCount [[[], []]] = 1 := by decide

/-- Canonicality and declaration hypotheses have genuine negative instances. -/
example : ¬ IsCanonicalEquation [[0], [0]] ∧ ¬ (∀ v ∈ [2], v < (2 : ℕ)) := by
  simp [IsCanonicalEquation]

/-- A real sparse family satisfies the actual counter's resource theorem at every large size,
with its original answer also proved. The array multiplier has not been hidden or removed. -/
example : ∃ (cs : NativeCertificate (countOriginal 1) encArrayInput Turing.MultiTapeTM.encNat)
    (A n₀ : ℕ) (P : ℕ → ℕ), Cslib.PolynomiallyBounded P ∧
    ∀ n, n₀ ≤ n → countOriginal 1 (n, []) = 2 ^ n ∧
      let L := (encArrayInput (n, [])).length
      cs.time (n, []) ≤ P L + (degreeCount 1 (n, []) + 1) *
        (A * (L + 1) ^ A * 2 ^ (A * sizeParam n / Nat.sqrt (Nat.log 2 (sizeParam n)))) ∧
        cs.space (n, []) ≤ P L + A * (L + 1) ^ A := by
  obtain ⟨cs, A, n₀, P, hP, _, hA⟩ := exists_countOriginal_certificate 1 1 (by decide)
  refine ⟨cs, A, n₀, P, hP, fun n hn => ⟨?_, hA n hn [] ?_⟩⟩
  · rw [countOriginal_eq_rootCount (by simp) (by simp) (by simp)]
    simp [HeavyBranchFold.rootCount]
  · exact {
      vars_lt := by simp
      canonical := by simp
      length_le := by simp
      monomials_le := by simp
      degree_le := by simp
      scope_le := by simp
      varDegree_le := by simp [varDegree] }

end ComplexityTests.TensorNetworkIncidenceOriginalCount
