/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import ComplexityTests.PaperEndpoints.RoundingExecution
public import Complexity.Statistics.LeastSquares.AffinePreprocessing
import all Complexity.Statistics.LeastSquares.AffinePreprocessing
import Mathlib.Tactic

/-! Affine-target conversion: negative/nonfirst pivot, output tables, singular
normal equations and a complete real solver instance with nonzero affine threshold. -/

open Matrix Cslib.LeastSquares Cslib.LeastSquares.AffineTarget Cslib.Algorithms.Lean

namespace ComplexityTests.AffineTarget1326

private def e : Fin 3 → ℚ := ![0, -2, 3]
private def x : Fin 2 → Fin 3 → ℚ := ![![1, 4, -1], ![2, -2, 7]]
private def y : Fin 2 → ℚ := ![6, -3]

example : (pivot e).ret = some 1 ∧ (pivot e).time = 2 := by decide +kernel
example : (pivot (fun _ : Fin 3 => (0 : ℚ))).ret = none ∧
    (pivot (fun _ : Fin 3 => (0 : ℚ))).time = 4 := by decide +kernel

-- The output contains every row/coordinate and the shifted responses.
example : (preprocess e 1 5 x y).ret = [([1, -2, 5], 16), ([2, 1, 4], -8)] := by
  rw [preprocess_ret]
  decide +kernel

-- Kernel evaluation of the program counter, beyond the asymptotic upper bound.
example : (preprocess e 1 5 x y).time = 31 := by decide +kernel

-- An arbitrary (non-coordinate) target and negative pivot preserve its sign.
example (γ : Fin 3 → ℝ) :
    (![0, -2, 3] : Fin 3 → ℝ) ⬝ᵥ
      (origin ![0, -2, 3] 1 5 + coeff ![0, -2, 3] 1 γ) = 5 + γ 1 := by
  apply target
  norm_num

-- Singularity is allowed by the equality-normal decision; no inverse is used here.
example : EqualityNormalDecision (fun _ : Fin 2 => ![0, 0]) (fun _ => 7)
    (![2, 3] : Fin 2 → ℝ) 5 0 := by
  refine ⟨fun _ => 1, ![1, 1], by simp, ?_, by norm_num [dotProduct, Fin.sum_univ_two],
    by norm_num [Fin.sum_univ_two]⟩
  ext j; fin_cases j <;> norm_num [dotProduct, Fin.sum_univ_two]

public def realX : Fin 4 → Fin 1 → ℝ := fun _ _ => 1
public def realY : Fin 4 → ℝ := ![0, 0, 4, 6]
private noncomputable def changedX : Fin 4 → Fin 1 → ℝ := fun _ _ => 1/2
private def changedY : Fin 4 → ℝ := ![-1, -1, 3, 5]
private noncomputable def eqWeights : Fin 4 → ℝ := ![1, 1, 2/3, 0]
public def oracle (_ : Fin 1) (_ : List (List ℝ × ℝ)) (k : ℕ) : TimeM ℕ Bool :=
  ⟨decide (2 ≤ k), 7⟩

private theorem oracle_correct (data : List (List ℝ × ℝ)) :
    ExternalSolver.NormalOracle (oracle 0 data) changedX changedY 0 := by
  intro k
  simp only [oracle, decide_eq_true_eq]
  constructor
  · intro hk
    refine ⟨eqWeights, 0, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num [eqWeights]
    · ext j; fin_cases j
      norm_num [eqWeights, changedX, changedY, dotProduct, Fin.sum_univ_one,
        Fin.sum_univ_four]
    · simp
    · have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
      norm_num [eqWeights, Fin.sum_univ_four]
      linarith
  · rintro ⟨v, b, hv, hn, hb, hm⟩
    by_contra hk
    have hk' : (k : ℝ) ≤ 1 := by exact_mod_cast (show k ≤ 1 by omega)
    have hb0 : b 0 = 0 := by simpa [dotProduct, Fin.sum_univ_one] using hb
    have heq := congrFun hn 0
    norm_num [changedX, changedY, dotProduct, Fin.sum_univ_one,
      Fin.sum_univ_four, hb0] at heq
    have hbsum : (∑ l : Fin 1, (1/2 : ℝ) * b l) = 0 := by
      simp [hb0]
    rw [hbsum] at heq
    have hb1 := (hv 0).2
    have hb2 := (hv 1).2
    have hb3 := (hv 3).1
    norm_num [Fin.sum_univ_four] at hm
    linarith

private theorem realGP : GeneralPosition realX :=
  ComplexityTests.RoundingExecution.design_generalPosition

-- Feasibility and full-data strict violation are independently checked from real OLS.
private noncomputable def inputWeights : Fin 4 → ℝ := ![1, 1, 1/2, 0]
private theorem input_feasible : Feasible realX realY (fun _ => 2) 2 inputWeights := by
  refine ⟨?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num [inputWeights]
  · apply realGP.weightedGram_posDef
    · intro i; fin_cases i <;> norm_num [inputWeights]
    · norm_num [inputWeights, Fin.sum_univ_four]
  · have hG := realGP.weightedGram_posDef realX inputWeights
      (by intro i; fin_cases i <;> norm_num [inputWeights])
      (by norm_num [inputWeights, Fin.sum_univ_four])
    rw [weightedEstimate_eq_of_normal realX realY inputWeights (fun _ => 4/5) hG (by
      ext j; fin_cases j
      norm_num [realX, realY, inputWeights, dotProduct, Fin.sum_univ_one, Fin.sum_univ_four])]
    norm_num [dotProduct, Fin.sum_univ_one]

public theorem affine_solver_example :
    (solve oracle (fun _ : Fin 1 => 2) 2 realX realY).ret = some 2 := by
  have hs (j : Fin 1) (_ : (2 : ℝ) ≠ 0) : ExternalSolver.NormalOracle
      (oracle j (List.ofFn (fun i =>
        (List.ofFn (AffineTarget.row (fun _ => 2) j (realX i)),
          response (fun _ => 2) j 2 realX realY i))))
      (fun i => AffineTarget.row (fun _ => 2) j (realX i))
      (response (fun _ => 2) j 2 realX realY) j := by
    fin_cases j
    have hx : (fun i => AffineTarget.row (fun _ : Fin 1 => (2 : ℝ)) 0 (realX i)) =
        changedX := by
      ext i l; fin_cases l; norm_num [AffineTarget.row, realX, changedX]
    have hy : response (fun _ : Fin 1 => (2 : ℝ)) 0 2 realX realY = changedY := by
      ext i; fin_cases i <;> norm_num [response, realY, realX, changedY]
    change ExternalSolver.NormalOracle (oracle 0 _)
      (fun i => AffineTarget.row (fun _ : Fin 1 => (2 : ℝ)) 0 (realX i))
      (response (fun _ : Fin 1 => (2 : ℝ)) 0 2 realX realY) 0
    rw [hx, hy]
    exact oracle_correct _
  have h := solve_correct oracle (fun _ : Fin 1 => 2) 2 realX realGP realY inputWeights hs
    input_feasible (by norm_num [inputWeights, Fin.sum_univ_four]) (by
      have hG := realGP.weightedGram_posDef realX (fun _ => 1) (by simp)
        (by norm_num [Fin.sum_univ_four])
      rw [weightedEstimate_eq_of_normal realX realY (fun _ => 1) (fun _ => 5/2) hG (by
        ext j; fin_cases j
        norm_num [realX, realY, dotProduct, Fin.sum_univ_one, Fin.sum_univ_four])]
      norm_num [dotProduct, Fin.sum_univ_one])
  have hvalue : (solve oracle (fun _ : Fin 1 => 2) 2 realX realY).ret = some 2 := by
    norm_num [solve, pivot, oracle, ExternalSolver.search, TimeM.ret_bind, TimeM.ret_pure]
  have hceil : ⌈fractionalStability realX realY (fun _ => 2) 2⌉₊ = 2 :=
    Option.some.inj (h.symm.trans hvalue)
  -- The full semantic theorem and direct computation agree.
  rwa [hceil] at h

end ComplexityTests.AffineTarget1326
