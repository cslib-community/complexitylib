import Mathlib
import CslibFrontier.Algorithms.Lean.Simplex.TwoPhase

open Cslib.Algorithms.Lean.Simplex
open Matrix
open Dictionary

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}

theorem phaseOneOpt_le_zero (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (D : Dictionary (Fin (n + 1 + m)) K)
    (hopt : (phaseOneDict A b).simplex = .optimal D) : D.objConst ≤ 0 := by
  have hF := phaseOneDict_feasible A b
  obtain ⟨D', hrun, hequiv, hD', hgreat⟩ | ⟨hrun, hunb⟩ :=
    Dictionary.simplex_spec (phaseOneDict A b) hF
  · rw [hrun] at hopt
    cases hopt
    -- D' is D
    have hmem : D.basicSolution ∈ D.feasibleSet := ⟨D.isSolution_basicSolution, (D.feasible_iff_nonneg_basicSolution).1 hD'⟩
    have heq : D.objConst = D.value D.basicSolution := D.value_basicSolution.symm
    rw [heq]
    have hval : D.value D.basicSolution = (phaseOneDict A b).value D.basicSolution :=
      (hequiv.value_eq _ hmem.1).symm
    rw [hval]
    sorry
