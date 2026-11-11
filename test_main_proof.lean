import Mathlib
import CslibFrontier.Algorithms.Lean.Simplex.TwoPhase

open Cslib.Algorithms.Lean.Simplex
open Matrix
open Dictionary

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}

theorem phaseOneOpt_le_zero (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (D : Dictionary (Fin (n + 1 + m)) K)
    (hopt : (phaseOneDict A b).simplex = .optimal D) : D.objConst ≤ 0 := by
  have hfeas := phaseOneDict_feasible A b
  obtain ⟨D', hrun, hequiv, hD', hgreat⟩ | ⟨hrun, hunb⟩ :=
    Dictionary.simplex_spec (phaseOneDict A b) hfeas
  · rw [hopt] at hrun
    cases hrun
    have hmem : D.basicSolution ∈ D.feasibleSet := ⟨D.isSolution_basicSolution, (D.feasible_iff_nonneg_basicSolution).1 hD'⟩
    have hmem_orig : D.basicSolution ∈ (phaseOneDict A b).feasibleSet := ⟨(hequiv.isSolution_iff _).2 hmem.1, hmem.2⟩
    have heq : D.objConst = D.value D.basicSolution := D.value_basicSolution.symm
    rw [heq, ← hequiv.value_eq _ hmem_orig.1]
    -- Now we must prove that for any z in (phaseOneDict A b).feasibleSet, value z ≤ 0.
    sorry
  · rcases hrun with ⟨D', s, h⟩
    rw [hopt] at h
    cases h

theorem phaseOneDict_equivalent_aux (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    (auxDictionary A b).Equivalent (phaseOneDict A b) := by
  unfold phaseOneDict
  rcases minRhsIndex b with _ | r
  · exact .refl _
  · split_ifs with hneg
    · refine Dictionary.equivalent_pivot (natAdd_mem_slackDictionary_basis _ _ _ _) (castAdd_notMem_slackDictionary_basis _ _ _ _) ?_
      -- coeff is 1
      sorry
    · exact .refl _
