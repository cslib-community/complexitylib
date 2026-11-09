/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceGeneralCounter
import CslibFrontier.Foundations.Data.Nat.LogLogSqrtLogPolylog
import all CslibFrontier.Computability.Complexity.FineGrained.CountingSparsification

/-! # Sharp actual parity resources and unrestricted-density original-count composition -/

public section

namespace CslibFrontierTests.TensorNetworkIncidenceSharpParity

open Cslib Cslib.BitString Cslib.GenericRAM Cslib.Complexity
open Cslib.Circuits.Frontier.IncidenceNetwork Cslib.Logic.PL Cslib.Logic.PL.CNF
open CountingSparsify Turing.MultiTapeTM

/-- The source schedule rounds square roots up, without the old iterated-log denominator. -/
example : sharpSearchDivisor 256 = 3 ∧ sharpSearchDivisor 1024 = 4 := by
  norm_num [sharpSearchDivisor,
    show Nat.clog 2 256 = 8 from Nat.clog_pow 2 8 (by decide),
    show Nat.clog 2 1024 = 10 from Nat.clog_pow 2 10 (by decide),
    show Nat.sqrt 7 = 2 from
      ((Nat.eq_sqrt').mpr (show 2 ^ 2 ≤ 7 ∧ 7 < (2 + 1) ^ 2 from by decide)).symm,
    show Nat.sqrt 9 = 3 from Nat.sqrt_eq' 3]

/-- Actual binary traversal clocks retain unused declared variables in the input support bound. -/
example : rounds (sharpSearchDivisor 4) ([[(0, true)]] : CNF ℕ) = 4 ∧
    rounds (sharpSearchDivisor 4) ([[(0, true)]] : CNF ℕ) ≤
      4 * 2 ^ Nat.logLogSqrtLogScale 4 := by
  have hc : Nat.clog 2 4 = 2 := Nat.clog_pow 2 2 (by decide)
  have hr : rounds (sharpSearchDivisor 4) ([[(0, true)]] : CNF ℕ) = 4 := by
    rw [rounds, CNF.length_distinctVars,
      show CNF.numVars ([[(0, true)]] : CNF ℕ) = 1 from by decide]
    norm_num [sharpSearchDivisor, hc]
  exact ⟨hr, sharp_rounds_le (by decide) (by decide)⟩

/-- Arbitrarily high fixed powers are absorbed with a constant that also covers zero. -/
example : ∃ A : ℕ, ∀ n,
    (Nat.clog 2 n) ^ 7 + 3 * (Nat.clog 2 n) ^ 2 ≤ Nat.logLogSqrtLogScale n + A := by
  exact Nat.exists_polynomial_clog_le_logLogSqrtLogScale_add
    (show Cslib.PolynomiallyBounded (fun t => t ^ 7 + 3 * t ^ 2) by fun_prop)

/-- One actual machine counts original sparse assignments and has the sharp real bound.
This combines semantic correctness with the certificate, rather than supplying desired runtime. -/
example : ∃ N₀ : ℕ, ∃ (cs : NativeCertificate (countParity 1 0 N₀)
    (encPair encUnary encCNF) encNat) (A : ℕ), ∀ n, 16 ≤ n → ∀ ψ : CNF ℕ,
    (∀ clause ∈ ψ, clause.length ≤ 1) → ψ.vars.toFinset ⊆ Finset.range n → ψ.length ≤ n →
    countParity 1 0 N₀ (n, ψ) = ψ.modelCountOn (Finset.range n) ∧
    let L := (encPair encUnary encCNF (n, ψ)).length
    (cs.time (n, ψ) : ℝ) ≤ (A : ℝ) * (L + 1 : ℕ) ^ A *
      (2 : ℝ) ^ (((6 * A : ℕ) : ℝ) * Real.logLogSqrtLogScale n) ∧
    cs.space (n, ψ) ≤ A * (L + 1) ^ A := by
  obtain ⟨N₀, cs, A, h⟩ := exists_countParity_real_sharp_certificate 1 0 (by decide)
  refine ⟨N₀, cs, A, fun n hn ψ hw hv hm => ?_⟩
  exact ⟨countParity_eq_modelCountOn hw hv (Or.inl (by simpa using hm)), h n hn ψ⟩

/-- Dense repeated clauses, unused bits, no clauses and contradiction all use the same
parameter choices derived from the actual source schedule. No density/counter oracle is assumed. -/
example : ∃ β Ncut : ℕ, ∀ N₀,
    countGeneralParity 2 β N₀ Ncut (2, List.replicate 5 [(0, true)]) = 2 ∧
    countGeneralParity 2 β N₀ Ncut (0, []) = 1 ∧
    countGeneralParity 2 β N₀ Ncut (0, [[]]) = 0 := by
  obtain ⟨β, Ncut, h⟩ := exists_countGeneralParity_eq_modelCountOn 2 (by decide)
  refine ⟨β, Ncut, fun N₀ => ?_⟩
  constructor
  · rw [h N₀ 2 (List.replicate 5 [(0, true)]) (by decide) (by decide)]
    decide
  constructor
  · rw [h N₀ 0 [] (by simp) (by decide)]
    decide
  · rw [h N₀ 0 [[]] (by simp) (by decide)]
    decide

/-- A nonempty family reaches the new tree schedule beyond every bounded-size cutoff.
The general-density endpoint here is correctness; its whole-machine resources remain open. -/
example : ∃ β Ncut : ℕ, ∀ N₀ n, Ncut ≤ n → 1 ≤ n →
    countGeneralParity 2 β N₀ Ncut (n, [[(0, true)]]) =
      CNF.modelCountOn ([[(0, true)]] : CNF ℕ) (Finset.range n) := by
  obtain ⟨β, Ncut, h⟩ := exists_countGeneralParity_eq_modelCountOn 2 (by decide)
  refine ⟨β, Ncut, fun N₀ n _hn hn1 => ?_⟩
  apply h N₀ n [[(0, true)]] (by simp)
  intro v hv
  have hv0 : v = 0 := by simpa [CNF.mem_vars] using hv
  exact Finset.mem_range.mpr (by omega)

end CslibFrontierTests.TensorNetworkIncidenceSharpParity
