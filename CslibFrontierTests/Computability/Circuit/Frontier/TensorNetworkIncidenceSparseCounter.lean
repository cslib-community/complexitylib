/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceSparseCounter
import all CslibFrontier.Computability.GenericRAM.Native.HeavyBranchFold

/-! # Actual high-incidence branching and the single-loglog native resource bound -/

public section

namespace CslibFrontierTests.TensorNetworkIncidenceSparseCounter

open Cslib Cslib.BitString Cslib.GenericRAM Cslib.Complexity
open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.IncidenceNetwork
open SubexponentialSAT

/-- Variable zero is genuinely heavy, while variable one remains in a reduced branch. -/
abbrev heavySystem : List (List (List ℕ)) := List.replicate 10 [[0]] ++ [[[1]]]

example : IncidenceBranching.branchVars 4 heavySystem = [0] := by decide
example : HeavyBranchFold.prepareBranch 4 [0] [false] heavySystem = .reduced 3 [[[0]]] ∧
    HeavyBranchFold.prepareBranch 4 [0] [true] heavySystem = .contradiction := by decide

/-- This computes an original answer through the new composed correctness theorem, not an oracle. -/
example : countSparse 1 (4, heavySystem) = 4 := by
  rw [countSparse_eq_rootCount
    (by simp [heavySystem, IsCanonicalEquation, IsCanonicalMonomial]) (by decide) (by decide)]
  decide

/-- The actual domain guard supplies the global output bound, including invalid encodings. -/
example : validSystem 1 (4, heavySystem) = true ∧
    countChecked 1 (2, [[[2]]]) = 0 ∧ countChecked 1 (2, [[[0], [0]]]) = 0 := by decide

/-- Empty and zero-variable contradictory systems retain their direct semantics. -/
example : countSparse 1 (0, []) = 1 ∧ countSparse 1 (0, [[[]]]) = 0 := by
  constructor
  · rw [countSparse_eq_rootCount (by simp) (by simp) (by simp)]
    decide
  · rw [countSparse_eq_rootCount
      (by simp [IsCanonicalEquation, IsCanonicalMonomial]) (by simp) (by simp)]
    decide

/-- A concrete rounding instance: one iterated logarithm, no square of that factor. -/
example : Nat.logLogSqrtLogScale 16 = 16 := by
  norm_num [Nat.logLogSqrtLogScale,
    show Nat.clog 2 16 = 4 from Nat.clog_pow 2 4 (by decide),
    show Nat.clog 2 4 = 2 from Nat.clog_pow 2 2 (by decide),
    show Nat.log 2 16 = 4 from Nat.log_pow (by decide) 4,
    show Nat.sqrt 4 = 2 from Nat.sqrt_eq' 2]

/-- The linear-size query enlargement used in the weighted plan changes only a constant.
This numerical fact is not an assumed faster CNF counting algorithm. -/
example (n N : ℕ) (hn : 16 ≤ n) (hN : N ≤ 2 * n - 2) :
    (Nat.logLogSqrtLogScale N : ℝ) ≤ 240 * Real.logLogSqrtLogScale n := by
  have h := Nat.cast_logLogSqrtLogScale_le_of_le_mul 2
    (by omega : N ≤ 2 * n) (by omega : max 16 2 ≤ n)
  norm_num only [Nat.cast_ofNat] at h
  exact h

/-- A nonempty sparse family has an actual native certificate, original count semantics and
real source-scale time/polynomial-space bounds at every sufficiently large declared size. -/
example : ∃ (cs : NativeCertificate (countSparse 1) encArrayInput Turing.MultiTapeTM.encNat)
    (D n₀ : ℕ), ∀ n, n₀ ≤ n →
      countSparse 1 (n, List.replicate n [[0]]) =
        HeavyBranchFold.rootCount n (List.replicate n [[0]]) ∧
      let L := (encArrayInput (n, List.replicate n [[0]])).length
      (cs.time (n, List.replicate n [[0]]) : ℝ) ≤ (D : ℝ) * (L + 1 : ℕ) ^ D *
        (2 : ℝ) ^ (((6 * D : ℕ) : ℝ) * Real.logLogSqrtLogScale n) ∧
      cs.space (n, List.replicate n [[0]]) ≤ D * (L + 1) ^ D := by
  obtain ⟨cs, D, n₀, hcs⟩ := exists_countSparse_real_sharp_certificate 1 1 (by decide)
  refine ⟨cs, D, max n₀ 4, fun n hn => ?_⟩
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  have hlog : 1 ≤ Nat.clog 2 n := by
    exact Nat.clog_pos Nat.one_lt_two (by omega : 1 < n)
  have hs : IncidenceBranching.IsSparseSystem 1 1 n (List.replicate n [[0]]) := by
    refine {
      vars_lt := ?_
      canonical := ?_
      length_le := by simp
      monomials_le := ?_
      degree_le := ?_ }
    · intro eq heq m hm v hv
      have he := List.eq_of_mem_replicate heq
      subst eq
      simp only [List.mem_singleton] at hm
      subst m
      simp only [List.mem_singleton] at hv
      subst v
      omega
    · simp [IsCanonicalEquation, IsCanonicalMonomial]
    · intro eq heq
      have he := List.eq_of_mem_replicate heq
      subst eq
      simpa using hlog
    · simp
  exact ⟨countSparse_eq_rootCount hs.canonical hs.vars_lt hs.degree_le,
    hcs n ((le_max_left _ _).trans hn) _ hs⟩

end CslibFrontierTests.TensorNetworkIncidenceSparseCounter
