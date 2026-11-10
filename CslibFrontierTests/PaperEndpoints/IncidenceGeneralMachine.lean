/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceGeneralMachine

/-!
# A single sharp finite counter with original unused-variable and rejection behavior

The twenty free variables are counted by the declared-count identity, without enumerating their
cube. The same actual counter handles an empty clause, no variables and an out-of-range index.
-/

public section
namespace IncidenceGeneralMachineTests
open Cslib.Circuits.Frontier.IncidenceNetwork Cslib.Logic.PL Cslib.Logic.PL.CNF
open Turing.MultiTapeTM

/-- The source machine is uniform in both declaration and arbitrary clause list, and its
original-variable counts are witnessed simultaneously on representative boundary inputs. -/
theorem machine_cases :
    ∃ (β N₀ Ncut C e A tapes : ℕ) (State : Type) (_ : Finite State)
      (tm : Turing.MultiTapeTM tapes Bool State),
      (∀ N, 20 ≤ N → ∀ φ : CNF ℕ, validDeclaredInput 2 N φ = true →
        ∃ t, tm.ComputesInTimeAndSpace (encCounter (N, φ))
          (encNat (countGeneralParity 2 β N₀ Ncut (N, φ))) t (C * (N + φ.length + 1) ^ e) ∧
          (t : ℝ) ≤ (C : ℝ) * (N + φ.length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale N) ∧
          (encNat (countGeneralParity 2 β N₀ Ncut (N, φ))).length ≤
            C * (N + φ.length + 1) ^ e) ∧
      countGeneralParity 2 β N₀ Ncut (20, []) = 2 ^ 20 ∧
      countGeneralParity 2 β N₀ Ncut (20, [[]]) = 0 ∧
      countGeneralParity 2 β N₀ Ncut (0, []) = 1 ∧
      countGeneralParity 2 β N₀ Ncut (1, [[(1, true)]]) = 0 := by
  obtain ⟨β, N₀, Ncut, C, e, A, tapes, State, hfinite, tm, hc, ht⟩ :=
    exists_countGeneralParity_source_machine 2 (by decide)
  refine ⟨β, N₀, Ncut, C, e, A, tapes, State, hfinite, tm, ht, ?_, ?_, ?_, ?_⟩
  · rw [hc]
    have hv : validDeclaredInput 2 20 [] = true := by decide
    simp [hv]
  · rw [hc]
    simp [validDeclaredInput, CNF.modelCountOn_eq_zero_of_nil_mem (by simp : [] ∈ [[]])]
  · rw [hc]
    have hv : validDeclaredInput 2 0 [] = true := by decide
    simp [hv]
  · rw [hc]
    have hv : validDeclaredInput 2 1 [[(1, true)]] = false := by decide
    simp [hv]

end IncidenceGeneralMachineTests
