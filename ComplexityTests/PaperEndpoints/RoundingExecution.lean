/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.RoundingExecution
public import Complexity.Statistics.LeastSquares.ExternalSolver
import Mathlib.Tactic

/-! Executed rational rounding, both endpoint branches and threshold searches. -/

open Matrix Matrix.RankOne Cslib.LeastSquares Cslib.LeastSquares.RoundingExecution

namespace ComplexityTests.RoundingExecution

private def design : Fin 4 → Fin 1 → ℚ := fun _ _ => 1
private def response : Fin 4 → ℚ := ![-1, -1, 1, 2]
private def input : Fin 4 → ℚ := ![1, 1, 1/2, 1/4]
private def sparse : Fin 4 → ℚ := ![1, 1, 14/15, 0]

-- The genuinely unsparse input has two fractional coordinates in dimension one.
example : (fractionalList input).length = 2 := by decide +kernel
example : (∑ i, input i) = (11/4 : ℚ) := by decide +kernel

-- The residual equations are constructed from the computed fit, not supplied.
example : solve (∑ i, input i • vecMulVec (design i) (design i))
    (∑ i, (input i * response i) • design i) 0 = (-4/11 : ℚ) := by decide +kernel
example : (∑ i, sparse i * (response i - (-4/11))) = (0 : ℚ) := by decide +kernel

-- Execute the entire caller using this concrete LP answer. This example checks
-- the caller and its actual arithmetic; it does not certify a generic LP solver.
private def result := execute (fun _ _ => sparse) design response input (fun _ => 1)
example : result.ret.weights 0 = 1 ∧ result.ret.weights 1 = 1 ∧
    result.ret.weights 2 = 0 ∧ result.ret.weights 3 = 0 := by decide +kernel
example : result.ret.inv 0 0 = (1/2 : ℚ) ∧ result.ret.response 0 = -2 := by decide +kernel
example : result.ret.coordinates = 1 ∧ result.ret.rankChanges = 1 := by decide +kernel
example : result.time = (1, 1, 1) := by decide +kernel

-- Negating the target chooses the other branch, including restoration to one.
private def reverseResult := roundSparse design response sparse (fun _ => -1)
example : reverseResult.weights 2 = 1 ∧ reverseResult.coordinates = 1 ∧
    reverseResult.rankChanges = 2 := by decide +kernel
example : reverseResult.inv 0 0 = (1/3 : ℚ) ∧ reverseResult.response 0 = -1 := by decide +kernel

-- The signed denominator can genuinely vanish if the changed matrix is singular.
example : 1 + (-1 : ℚ) * ((fun _ : Fin 1 => (1 : ℚ)) ⬝ᵥ
    ((1 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ (fun _ => 1))) = 0 := by decide +kernel

open Cslib.LeastSquares.ExternalSolver Cslib.Algorithms.Lean

private def query (k : ℕ) : TimeM ℕ Bool := ⟨decide (3 ≤ k), 7⟩
example : (search query 10).ret = 3 ∧ (search query 10).time = 39 := by decide +kernel
example : (search query 1).ret = 2 ∧ (search query 1).time = 16 := by decide +kernel
example : (search (fun _ => ⟨true, 7⟩) 0).ret = 0 := by decide +kernel

-- A real semantic client checks the positive-definite backbone and target
-- contract for an actually fractional input, separately from rational execution.
public theorem design_generalPosition :
    GeneralPosition (fun _ : Fin 4 => fun _ : Fin 1 => (1 : ℝ)) := by
  intro s hs
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hcard : Fintype.card s = 1 := by simpa using hs
  have : Subsingleton s := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  have hsum : (∑ j : s, c j) = c i := by
    let : Unique s := ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩
    simpa only [Finset.univ_unique, Finset.sum_singleton] using
      congrArg c (Subsingleton.elim (default : s) i)
  have h := congrFun hc 0
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_one, Pi.zero_apply] at h
  exact hsum ▸ h

example :
    let x := fun _ : Fin 4 => fun _ : Fin 1 => (1 : ℝ)
    let y : Fin 4 → ℝ := ![-1, -1, 1, 2]
    let w : Fin 4 → ℝ := ![1, 1, 14/15, 0]
    let z := roundSparse x y w (fun _ => 1)
    (∀ i, z.weights i = 0 ∨ z.weights i = 1) ∧
      (∑ i, w i) - (∑ i, z.weights i) < 1 ∧
      (weightedGram 0 Finset.univ x z.weights).PosDef := by
  let x := fun _ : Fin 4 => fun _ : Fin 1 => (1 : ℝ)
  let y : Fin 4 → ℝ := ![-1, -1, 1, 2]
  let w : Fin 4 → ℝ := ![1, 1, 14/15, 0]
  obtain ⟨hu, _, hloss, hG, _⟩ := roundSparse_correct x design_generalPosition y w (fun _ => 1)
    (by intro i; fin_cases i <;> norm_num [w])
    (by
      have h : (Finset.univ.filter fun i => 0 < w i ∧ w i < 1) = {2} := by
        ext i; fin_cases i <;> norm_num [w]
      rw [h]; norm_num)
    (by norm_num [w, Fin.sum_univ_four])
  exact ⟨hu, by simpa using hloss, hG⟩

private def realDesign : Fin 4 → Fin 1 → ℝ := fun _ _ => 1
private def realResponse : Fin 4 → ℝ := ![-1, -1, 1, 2]
private noncomputable def equalityWeights : Fin 4 → ℝ := ![1, 1, 1, 1/2]
private def scalarOracle (k : ℕ) : TimeM ℕ Bool := ⟨decide (1 ≤ k), 7⟩

-- A complete, nonvacuous normal-equation oracle instance: the exact fractional
-- deletion threshold is one half, so the first successful integer query is one.
private theorem scalarOracle_correct : NormalOracle scalarOracle realDesign realResponse 0 := by
  intro k
  simp only [scalarOracle, decide_eq_true_eq]
  constructor
  · intro hk
    refine ⟨equalityWeights, 0, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num [equalityWeights]
    · ext j
      fin_cases j
      norm_num [equalityWeights, realResponse, realDesign, Fin.sum_univ_four,
        dotProduct, Fin.sum_univ_one]
    · simp
    · have hcast : (1 : ℝ) ≤ k := by exact_mod_cast hk
      norm_num [equalityWeights, Fin.sum_univ_four]
      linarith
  · rintro ⟨v, b, hv, hn, hb, hm⟩
    by_contra hk
    have hk0 : k = 0 := by omega
    subst k
    have hb0 : b 0 = 0 := by simpa [dotProduct, Fin.sum_univ_one] using hb
    have heq := congrFun hn 0
    norm_num [realDesign, realResponse, dotProduct, Fin.sum_univ_one,
      Fin.sum_univ_four, hb0] at heq
    have hbsum : (∑ i : Fin (0 + 1), b i) = 0 := by
      simpa using hb0
    rw [hbsum] at heq
    norm_num [Fin.sum_univ_four] at hm
    have h0 := (hv 0).2
    have h1 := (hv 1).2
    have h2 := (hv 2).2
    have h3 := (hv 3).2
    linarith

example : (search scalarOracle 3).ret = 1 ∧ (search scalarOracle 3).time = 18 := by
  decide +kernel

end ComplexityTests.RoundingExecution
