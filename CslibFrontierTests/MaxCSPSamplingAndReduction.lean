/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.FineGrained.BruteForce
import CslibFrontier.Computability.Complexity.FineGrained.MaxSAT.Reduction
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Verification tests for `Max-CSP`, constraint subsampling, and fixed-width SAT reductions

Exercises `MaxCSP`, `MaxCSPSampling`, and `MaxSAT.Reduction` across the strict `module` boundary:
* finite-domain (`Fin 3`) and Boolean unweighted/weighted `Max-CSP` scores, optima, and clamped
  binary compilation (`toClampedBoolean`);
* exact affine score and optimum shifts under forbidden-pattern `CSP.toCNF` compilation;
* nonvacuous instantiations of the `2 ^ (n + 1) * exp (-2 * s * δ ^ 2)` and
  `|D| ^ n * 2 * exp (-2 * s * δ ^ 2)` subsampling bounds, existence of sparse approximators, and
  tightness of the `2 * δ * m` optimality-loss bound;
* concrete `thresholdToCNF` compilation, `O(log m)`-query `TimeM` binary-search optimization
  (`optimumByBinarySearchM`), and native resource transfer (`FixedWidthSATSolver`).
-/

set_option linter.privateModule false

namespace Cslib.Tests.MaxCSPSamplingAndReduction

open Cslib.Algorithms.Lean Cslib.Complexity Cslib.Complexity.MaxSAT Cslib.Logic.PL
  Turing.MultiTapeTM

/-! ### 1. Finite-domain `Max-CSP` (`Fin 3` 3-coloring on `K₃` and `K₄`) and clamped compilation -/

/-- Disequality relation on `Fin 3` for proper 3-coloring edges. -/
def neqFin3 (_ : Unit) : List (Fin 3) → Bool
  | [u, v] => decide (u ≠ v)
  | _ => false

/-- Triangle `K₃` has 3 edges and is 3-colorable (`optimum = 3`). -/
def k3ColorCSP : MaxCSPInstance Unit ℕ where
  numVars := 3
  constraints := [⟨(), [0, 1]⟩, ⟨(), [1, 2]⟩, ⟨(), [0, 2]⟩]

/-- Equality (`true`) or disequality (`false`) relation on `Fin 3`. -/
def eqOrNeqFin3 (wantEq : Bool) : List (Fin 3) → Bool
  | [u, v] => if wantEq then decide (u = v) else decide (u ≠ v)
  | _ => false

/-- Unsatisfiable `Fin 3` triangle `x₀ = x₁`, `x₁ = x₂`, `x₀ ≠ x₂` (`3` constraints, `optimum = 2`).
-/
def frustratedFin3CSP : MaxCSPInstance Bool ℕ where
  numVars := 3
  constraints := [⟨true, [0, 1]⟩, ⟨true, [1, 2]⟩, ⟨false, [0, 2]⟩]

/-- Complete graph `K₄` on `Fin 3` (`4` variables, `6` edges). -/
def k4ColorCSP : MaxCSPInstance Unit ℕ where
  numVars := 4
  constraints :=
    [⟨(), [0, 1]⟩, ⟨(), [0, 2]⟩, ⟨(), [0, 3]⟩, ⟨(), [1, 2]⟩, ⟨(), [1, 3]⟩, ⟨(), [2, 3]⟩]

example : k3ColorCSP.optimum neqFin3 = 3 := by decide
example : frustratedFin3CSP.optimum eqOrNeqFin3 = 2 := by decide

/-- Clamped Boolean compilation of `frustratedFin3CSP` on `3 * 2 = 6` Boolean variables preserves
the exact optimum `2` without penalty weights. -/
theorem frustratedFin3_clampedBoolean_optimum :
    (frustratedFin3CSP.toClampedBoolean 3).optimum
      (MaxCSP.clampedSem 3 (by decide) eqOrNeqFin3) = 2 := by
  rw [frustratedFin3CSP.optimum_toClampedBoolean (by decide) eqOrNeqFin3 (by decide)]
  decide

/-! ### 2. Weighted `Max-CSP`, zero-variable & repeated-scope edge cases -/

/-- Concrete weighted `Max-CSP` over `ℕ` with asymmetric weights `3, 5, 7`. -/
def asymWeightedCSP : WeightedMaxCSP Bool ℕ ℕ where
  numVars := 1
  constraints := [⟨true, [0], 3⟩, ⟨false, [0], 5⟩, ⟨false, [0], 7⟩]

def litSem (pol : Bool) : List Bool → Bool
  | [b] => pol == b
  | _ => false

/-- Setting `x₀ = false` earns `5 + 7 = 12`, beating `x₀ = true` (`3`). -/
example : asymWeightedCSP.optimum litSem = 12 := by decide

/-- Zero-variable (`numVars = 0`) edge case with a nullary true constraint and a repeated-variable
scope `[0, 0]` reading the default `false` value outside `Fin 0`. -/
def zeroVarCSP : MaxCSPInstance Bool ℕ where
  numVars := 0
  constraints := [⟨true, []⟩, ⟨false, [0, 0]⟩]

def eqAllSem (target : Bool) (bs : List Bool) : Bool :=
  bs.all (· == target)

example : zeroVarCSP.optimum eqAllSem = 2 := by decide

/-! ### 3. Forbidden-pattern `CSP.toCNF` exact affine score and optimum shift -/

/-- Concrete unsatisfiable XOR cycle `x₀ ≠ x₁`, `x₁ ≠ x₂`, `x₀ ≠ x₂` (`3` constraints,
`optimum = 2`). -/
def xorCycleCSP : MaxCSPInstance Unit ℕ where
  numVars := 3
  constraints := [⟨(), [0, 1]⟩, ⟨(), [1, 2]⟩, ⟨(), [0, 2]⟩]

def xor2Sem (_ : Unit) : List Bool → Bool
  | [a, b] => a != b
  | _ => false

example : xorCycleCSP.optimum xor2Sem = 2 := by decide
example : (maxCSPToStruct 2 xor2Sem xorCycleCSP).clauses.length = 6 := by decide
example : (maxCSPToStruct 2 xor2Sem xorCycleCSP).optimum = 5 := by decide

/-- Verifies `5 + 3 = 6 + 2` via `optimum_maxCSPToStruct_add_length`. -/
theorem xorCycle_affine_shift :
    (maxCSPToStruct 2 xor2Sem xorCycleCSP).optimum + xorCycleCSP.constraints.length =
      (maxCSPToStruct 2 xor2Sem xorCycleCSP).clauses.length + xorCycleCSP.optimum xor2Sem :=
  optimum_maxCSPToStruct_add_length xor2Sem (by decide)

/-! ### 4. Tightness of the `2 * δ * m` optimality loss and nonvacuous subsampling bounds -/

/-- Instance on `1` variable with `4` clauses: `x₀` three times and `¬x₀` once (`m = 4`,
`optimum = 3` at `x₀ = true`, while `x₀ = false` has score `1`, losing `2 = 2 * (1 / 4) * 4` when a
`2`-sample picks `[x₀, ¬x₀]`). -/
abbrev tightLossInst : StructInstance :=
  ⟨1, [[(0, true)], [(0, true)], [(0, true)], [(0, false)]]⟩

example : tightLossInst.optimum = 3 := by decide

/-- Sample `ω = ![0, 3]` selects `x₀` and `¬x₀` (`s = 2`, `m = 4`). Rescaled score `(4 / 2) * 1 = 2`
is within `δ * m = (1 / 4) * 4 = 1` of the true scores `3` and `1` on *both* assignments, and the
sampled maximizer `xHat = fun _ => false` achieves true score `1 = 3 - 2 * (1 / 4) * 4`, attaining
the `2 * δ * m` loss bound with exact equality! -/
def tightSample : Fin 2 → Fin tightLossInst.clauses.length
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨3, by decide⟩

abbrev falseAssign : BitString 1 := fun _ => false
abbrev trueAssign : BitString 1 := fun _ => true

theorem tight_two_delta_m_attained :
    (tightLossInst.optimum : ℝ) - (tightLossInst.score falseAssign : ℝ) =
      2 * (1 / 4 : ℝ) * (tightLossInst.clauses.length : ℝ) ∧
    (∀ x : BitString tightLossInst.numVars,
      |(tightLossInst.clauses.length : ℝ) / (2 : ℝ) *
          ((tightLossInst.sample tightSample).score x : ℝ) -
        (tightLossInst.score x : ℝ)| ≤
      (1 / 4 : ℝ) * (tightLossInst.clauses.length : ℝ)) ∧
    (∀ x : BitString tightLossInst.numVars,
      (tightLossInst.sample tightSample).score x ≤
        (tightLossInst.sample tightSample).score falseAssign) := by
  have hopt : tightLossInst.optimum = 3 := by decide
  have hfalse_full : tightLossInst.score falseAssign = 1 := by decide
  have hfalse_samp : (tightLossInst.sample tightSample).score falseAssign = 1 := by decide
  have htrue_full : tightLossInst.score trueAssign = 3 := by decide
  have htrue_samp : (tightLossInst.sample tightSample).score trueAssign = 1 := by decide
  have hlen : tightLossInst.clauses.length = 4 := rfl
  refine ⟨by rw [hopt, hfalse_full, hlen]; norm_num, fun x => ?_, fun x => ?_⟩
  · by_cases hx : x 0 = true
    · have hxeq : x = trueAssign := funext fun i => by fin_cases i; exact hx
      rw [hxeq, htrue_samp, htrue_full, hlen]
      norm_num
    · have hxeq : x = falseAssign := funext fun i => by
        fin_cases i
        exact Bool.eq_false_iff.mpr hx
      rw [hxeq, hfalse_samp, hfalse_full, hlen]
      norm_num
  · by_cases hx : x 0 = true
    · have hxeq : x = trueAssign := funext fun i => by fin_cases i; exact hx
      rw [hxeq, htrue_samp, hfalse_samp]
    · have hxeq : x = falseAssign := funext fun i => by
        fin_cases i
        exact Bool.eq_false_iff.mpr hx
      rw [hxeq]

/-- Nonvacuous instantiation of `exists_boolean_sample_approx` on `xorCycleCSP` (`n = 3`,
`δ = 1 / 2`, `s = 6`: `(3 + 1) * log 2 < 4 * 0.7 = 2.8 < 3 = 2 * 6 * (1 / 2) ^ 2`). -/
theorem nonvacuous_exists_boolean_sample :
    ∃ ω : Fin 6 → Fin xorCycleCSP.constraints.length,
      (∀ xHat : BitString xorCycleCSP.numVars,
        (∀ x, (xorCycleCSP.sample ω).score xor2Sem x ≤
          (xorCycleCSP.sample ω).score xor2Sem xHat) →
        (xorCycleCSP.optimum xor2Sem : ℝ) - (xorCycleCSP.score xor2Sem xHat : ℝ) ≤
          2 * (1 / 2 : ℝ) * (xorCycleCSP.constraints.length : ℝ)) := by
  have hlog : (xorCycleCSP.numVars + 1 : ℝ) * Real.log 2 < 2 * (6 : ℝ) * (1 / 2 : ℝ) ^ 2 := by
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hn : (xorCycleCSP.numVars : ℝ) = 3 := rfl
    rw [hn]
    linarith
  obtain ⟨ω, -, hloss, -⟩ :=
    xorCycleCSP.exists_boolean_sample_approx xor2Sem (by decide) (by norm_num) hlog
  exact ⟨ω, hloss⟩

/-- Nonvacuous instantiation of `[0, 1]`-weighted subsampling concentration over `Fin 3`. -/
theorem nonvacuous_fin3_weighted_sampling :
    let F : WeightedMaxCSP Unit ℕ ℝ := k4ColorCSP.toRealWeighted
    ((F.samplePMF (by decide) 20).toOuterMeasure
      {ω | ∃ x : Fin F.numVars → Fin 3,
        (1 / 2 : ℝ) * (F.constraints.length : ℝ) ≤
          |(F.constraints.length : ℝ) / (20 : ℝ) * (F.sample ω).score neqFin3 x -
            F.score neqFin3 x|}).toReal ≤
      (3 : ℝ) ^ 4 * 2 * Real.exp (-2 * (20 : ℝ) * (1 / 2 : ℝ) ^ 2) := by
  intro F
  have hw : ∀ c ∈ F.constraints, c.weight ∈ Set.Icc (0 : ℝ) 1 := by
    intro c hc
    simp only [F, MaxCSPInstance.toRealWeighted, List.mem_map] at hc
    obtain ⟨_, _, rfl⟩ := hc
    exact ⟨zero_le_one, le_rfl⟩
  have hnv : F.numVars = 4 := rfl
  simpa only [Fintype.card_fin, hnv, Nat.cast_ofNat] using
    F.exists_sample_score_abs_sub_ge_le neqFin3 (by decide) 20 hw (by norm_num)

/-! ### 5. Fixed-width SAT reduction, `O(log m)` binary search, and native solver transfer -/

/-- Unsatisfiable 4-clause 2-CNF instance (`optimum = 3`). -/
def fourClauseInst : StructInstance where
  numVars := 2
  clauses := [[(0, true)], [(0, false)], [(0, true), (1, true)], [(0, false), (1, false)]]

example : fourClauseInst.optimum = 3 := by decide

/-- Executable unit-cost `TimeM` SAT oracle backed by `BruteForce.search`. -/
def bruteSolveM (φ : CNF ℕ) : TimeM ℕ Bool :=
  ⟨BruteForce.search φ, 1⟩

theorem bruteSolveM_spec (φ : CNF ℕ) (_ : ∀ c ∈ φ, c.length ≤ 3) :
    (bruteSolveM φ).ret = true ↔ φ.Satisfiable :=
  BruteForce.search_eq_true_iff φ

/-- `optimumByBinarySearchM` finds the exact optimum `3` of `fourClauseInst` in at most
`⌊log₂ 4⌋ + 1 = 3` oracle calls, and makes `0` calls on an empty formula. -/
example : (optimumByBinarySearchM bruteSolveM fourClauseInst).ret = 3 :=
  (optimumByBinarySearchM_ret (k := 3) le_rfl bruteSolveM_spec fourClauseInst).trans (by decide)

example : (optimumByBinarySearchM bruteSolveM fourClauseInst).time ≤ 3 := by
  have h := optimumByBinarySearchM_time_le fourClauseInst (solveM := bruteSolveM) (C := 1)
    (fun _ _ _ => le_rfl)
  have hlog : Nat.log 2 fourClauseInst.clauses.length + 1 = 3 := by decide
  exact h.trans_eq (by rw [one_mul, hlog])

example : (optimumByBinarySearchM bruteSolveM ⟨2, []⟩).ret = 0 :=
  (optimumByBinarySearchM_ret (k := 3) le_rfl bruteSolveM_spec ⟨2, []⟩).trans (by decide)

/-- Nonvacuous instantiation of the `η = 1 / 4` failure-probability sample-size bound on
`xorCycleCSP` (`n = 3`, `δ = 1 / 2`, `s = 9`: `(3 + 1) * log 2 + log 4 = 6 * log 2 < 4.2 ≤ 4.5`). -/
theorem nonvacuous_sample_size_eta :
    (3 / 4 : ℝ) ≤
      ((xorCycleCSP.samplePMF (by decide) 9).toOuterMeasure
        {ω | (∀ xHat : BitString xorCycleCSP.numVars,
            (∀ x, (xorCycleCSP.sample ω).score xor2Sem x ≤
              (xorCycleCSP.sample ω).score xor2Sem xHat) →
              (xorCycleCSP.optimum xor2Sem : ℝ) -
                (xorCycleCSP.score xor2Sem xHat : ℝ) ≤
                2 * (1 / 2 : ℝ) * (xorCycleCSP.constraints.length : ℝ)) ∧
          |(xorCycleCSP.constraints.length : ℝ) / (9 : ℝ) *
              ((xorCycleCSP.sample ω).optimum xor2Sem : ℝ) -
            (xorCycleCSP.optimum xor2Sem : ℝ)| ≤
              (1 / 2 : ℝ) * (xorCycleCSP.constraints.length : ℝ)}).toReal := by
  have hs : (xorCycleCSP.numVars + 1 : ℝ) * Real.log 2 + Real.log (1 / (1 / 4 : ℝ)) ≤
      2 * (9 : ℝ) * (1 / 2 : ℝ) ^ 2 := by
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hn : (xorCycleCSP.numVars : ℝ) = 3 := rfl
    have h4 : (1 : ℝ) / (1 / 4 : ℝ) = 2 ^ 2 := by norm_num
    rw [hn, h4, Real.log_pow]
    push_cast
    linarith
  have h := xorCycleCSP.one_sub_le_boolean_sample_good_of_sample_size xor2Sem (by decide)
    (s := 9) (by norm_num) (by norm_num) hs
  linarith

/-- Witness recovery (`optimizeByBinarySearchM`) finds both `optimum = 3` and an assignment `xHat`
scoring `3` on `fourClauseInst` within `⌊log₂ 4⌋ + 1 + 2 = 5` oracle calls. -/
theorem fourClause_optimize_witness :
    (optimizeByBinarySearchM bruteSolveM fourClauseInst).ret.1 = 3 ∧
      fourClauseInst.score (optimizeByBinarySearchM bruteSolveM fourClauseInst).ret.2 = 3 ∧
      (optimizeByBinarySearchM bruteSolveM fourClauseInst).time ≤ 5 := by
  obtain ⟨hopt, hscore⟩ :=
    optimizeByBinarySearchM_ret (k := 3) le_rfl bruteSolveM_spec fourClauseInst
  have h3 : fourClauseInst.optimum = 3 := by decide
  have ht := optimizeByBinarySearchM_time_le fourClauseInst (solveM := bruteSolveM) (C := 1)
    (fun _ _ _ => le_rfl)
  have h5 : Nat.log 2 fourClauseInst.clauses.length + 1 + fourClauseInst.numVars = 5 := by decide
  exact ⟨hopt.trans h3, hscore.trans h3, ht.trans_eq (by rw [one_mul, h5])⟩

/-- End-to-end subsampled witness-recovery guarantee under the `η = 1 / 2` sample-size bound on
`fourClauseInst` (`n = 2`, `w = 2`, `δ = 1 / 2`, `s = 8`: `4 * log 2 < 2.8 ≤ 4`). -/
theorem fourClause_sample_optimize_eta_spec :
    (∀ ω : Fin 8 → Fin fourClauseInst.clauses.length,
      (optimizeByBinarySearchM bruteSolveM (fourClauseInst.sample ω)).time ≤ 6) ∧
    (1 / 2 : ℝ) ≤
      ((fourClauseInst.samplePMF (by decide) 8).toOuterMeasure
        {ω | (fourClauseInst.optimum : ℝ) -
              (fourClauseInst.score
                (optimizeByBinarySearchM bruteSolveM (fourClauseInst.sample ω)).ret.2 : ℝ) ≤
              2 * (1 / 2 : ℝ) * (fourClauseInst.clauses.length : ℝ) ∧
          |(fourClauseInst.clauses.length : ℝ) / (8 : ℝ) *
              ((optimizeByBinarySearchM bruteSolveM (fourClauseInst.sample ω)).ret.1 : ℝ) -
            (fourClauseInst.optimum : ℝ)| ≤
              (1 / 2 : ℝ) * (fourClauseInst.clauses.length : ℝ)}).toReal := by
  have hs : (fourClauseInst.numVars + 1 : ℝ) * Real.log 2 + Real.log (1 / (1 / 2 : ℝ)) ≤
      2 * (8 : ℝ) * (1 / 2 : ℝ) ^ 2 := by
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hn : (fourClauseInst.numVars : ℝ) = 2 := rfl
    have hdiv : (1 : ℝ) / (1 / 2 : ℝ) = 2 := by norm_num
    rw [hn, hdiv]
    linarith
  obtain ⟨ht, hprob⟩ := sample_optimizeByBinarySearchM_spec_of_sample_size (k := 3) (w := 2)
    le_rfl bruteSolveM_spec (F := fourClauseInst) (by decide) (by decide) (s := 8) (C := 1)
    (fun _ _ _ => le_rfl) (by norm_num) (η := 1 / 2) (by norm_num) hs
  have h6 : Nat.log 2 8 + 1 + fourClauseInst.numVars = 6 := by decide
  exact ⟨fun ω => (ht ω).trans_eq (by rw [one_mul, h6]), by linarith⟩

/-- Exponential-time decision transfer instantiated from `KSAT_decidableInExpTime_one 3`. -/
theorem thresholdLanguage_expTime_bruteForce :
    DecidableInExpTime ThresholdLanguage encThresholdQuery ThresholdQuery.workSize 957 := by
  simpa only [mul_one] using
    decidableInExpTime_thresholdLanguage_of_KSAT (k := 3) le_rfl zero_le_one
      (KSAT_decidableInExpTime_one 3)

/-- Native `FixedWidthSATSolver 3` instantiated via `FixedWidthSATSolver.exists_bruteForce` to
verify `FixedWidthSATSolver.exists_optimum_algorithm` end-to-end in `2 ^ (957 * workSize + 957)`
time and polynomial space. -/
theorem exists_bruteForce_optimum_from_solver :
    ∃ d : ℕ,
      ComputableInO StructInstance.optimum encStructInstance encNat
        (fun F => 2 ^ (957 * F.workSize + 957) * ((encStructInstance F).length + 1) ^ d)
        (fun F => ((encStructInstance F).length + 1) ^ d) := by
  obtain ⟨solver, -, hrate⟩ := FixedWidthSATSolver.exists_bruteForce 3
  obtain ⟨d, hinO⟩ := solver.exists_optimum_algorithm (k := 3) le_rfl
  rw [hrate] at hinO
  exact ⟨d, hinO⟩

/-- Binary-search `Max-CSP` optimization instantiated on `xorCycleCSP` (`optimum = 2`). -/
example : (optimumMaxCSPByBinarySearchM 2 xor2Sem bruteSolveM xorCycleCSP).ret = 2 :=
  (optimumMaxCSPByBinarySearchM_ret (w := 2) (k := 3) le_rfl xor2Sem bruteSolveM_spec
    (by decide)).trans (by decide)

end Cslib.Tests.MaxCSPSamplingAndReduction
