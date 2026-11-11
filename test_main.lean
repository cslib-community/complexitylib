import Mathlib
import CslibFrontier.Algorithms.Lean.Simplex.TwoPhase

open Cslib.Algorithms.Lean.Simplex
open Matrix
open Dictionary

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}

theorem twoPhase_spec_proof (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K) :
    match twoPhase A b c with
    | TwoPhaseResult.infeasible y => 0 ≤ y ∧ 0 ≤ y ᵥ* A ∧ y ⬝ᵥ b < 0
    | TwoPhaseResult.unbounded x d => 0 ≤ x ∧ A *ᵥ x ≤ b ∧ 0 ≤ d ∧ A *ᵥ d ≤ 0 ∧ 0 < c ⬝ᵥ d
    | TwoPhaseResult.optimal x y => 0 ≤ x ∧ A *ᵥ x ≤ b ∧ 0 ≤ y ∧ c ≤ y ᵥ* A ∧ c ⬝ᵥ x = y ⬝ᵥ b := by
  sorry
