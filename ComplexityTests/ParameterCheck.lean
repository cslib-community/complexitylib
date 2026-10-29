/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Choose
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.PolyTime.FineGrained.ParameterCheck
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt

/-!
# Concrete tests for polynomial-time parameter computation and exact Binomial-tail checks

Exercises `Nat.clog 2`, `Nat.sqrt`, `Nat.choose`, `ReplacementParams`, and
`Cslib.Complexity.SubexponentialSAT.ParameterCheck` on boundary/power-of-two/square inputs
`(0, 1, 2, 3, 4, 15, 16, 17, 1024)`, positive/negative/guard `checkBinomTail` witnesses bridged to
real `Bin(4, 1 / 4)` tail sums, `checkReplacementFeasible` witnesses, schedule evaluation
(`n = 20`, `chooseBeta`, `ReplacementParams.numGroups` at `4` and `2 ^ (2 ^ 20)`), eventual
feasibility via `exists_checkScheduleFeasible_eq_true` + round-trip soundness to
`ReplacementParams.Feasible`, and plain `ComputableInPolyTime` compositions via `fun_prop`.
-/

namespace ComplexityTests.ParameterCheck

open Cslib.Complexity.SubexponentialSAT Cslib.Complexity.SubexponentialSAT.ParameterCheck Finset
  Turing.MultiTapeTM

/-! ### 1. Boundary, power-of-two, and square tests for `Nat.clog 2`, `Nat.sqrt`, `rowBound` -/

example : [0, 1, 2, 3, 4, 15, 16, 17, 1024].map (Nat.clog 2) = [0, 0, 1, 2, 2, 4, 4, 5, 10] := by
  decide

example : [0, 1, 2, 3, 4, 15, 16, 17, 1024].map Nat.sqrt = [0, 1, 1, 1, 2, 3, 4, 4, 32] := by
  simp only [List.map_cons, List.map_nil]
  norm_num

example : [0, 1, 2, 3, 4, 15, 16, 17, 1024].map (ReplacementParams.rowBound 1) =
    [0, 0, 4, 8, 8, 8, 8, 12, 16] := by
  simp only [List.map_cons, List.map_nil, ReplacementParams.rowBound]
  norm_num

/-! ### 2. `checkBinomTail` positive, negative, and guard witnesses bridged to real probabilities -/

/-- For `Q = 4, r = 2` (`W ~ Bin(4, 1 / 4)`) and interval `[0, 3) = {0, 1, 2}`, the complement
`{3, 4}` has cleared-denominator numerator `4 * 1 * 3 + 1 * 1 * 1 = 13` over `4 ^ 4 = 256`. -/
example : binomTailNumerator 4 2 0 3 = 13 := by decide

/-- At `b = 1, r = 2, lam = 4`, the budget `1 / 16 = 16 / 256` exceeds `13 / 256`, so
`checkBinomTail 4 2 0 3 1 4 = true` and the real tail inequality holds. -/
example :
    let tail := ∑ w ∈ (Finset.range 5).filter (fun w => ¬(0 ≤ w ∧ w < 3)),
      ((4 : ℕ).choose w : ℝ) * (((2 : ℝ) - 1) / (2 * 2)) ^ w *
        (1 - ((2 : ℝ) - 1) / (2 * 2)) ^ (4 - w)
    checkBinomTail 4 2 0 3 1 4 = true ∧ tail = 13 / 256 ∧
      tail ≤ 1 / ((1 : ℝ) * (2 : ℝ) ^ 2 * 4) := by
  dsimp only
  have hchk : checkBinomTail 4 2 0 3 1 4 = true := by decide
  have hset : (Finset.range 5).filter (fun w => ¬(0 ≤ w ∧ w < 3)) = {3, 4} := by decide
  refine ⟨hchk, by rw [hset]; norm_num, ?_⟩
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one] using
    (checkBinomTail_eq_true_iff (Q := 4) (r := 2) (A₀ := 0) (R := 3) (b := 1)
      (lam := 4) (by decide) (by decide) (by decide)).mp hchk

/-- Tightening `lam` from `4` to `5` shrinks the budget to `1 / 20 < 13 / 256` (`260 > 256`), so
`checkBinomTail 4 2 0 3 1 5 = false` and the real tail inequality is refuted. -/
example :
    checkBinomTail 4 2 0 3 1 5 = false ∧
      ¬((∑ w ∈ (Finset.range 5).filter (fun w => ¬(0 ≤ w ∧ w < 3)),
          ((4 : ℕ).choose w : ℝ) * (((2 : ℝ) - 1) / (2 * 2)) ^ w *
            (1 - ((2 : ℝ) - 1) / (2 * 2)) ^ (4 - w)) ≤
          1 / ((1 : ℝ) * (2 : ℝ) ^ 2 * 5)) := by
  have hchk : checkBinomTail 4 2 0 3 1 5 = false := by decide
  refine ⟨hchk, fun hle => ?_⟩
  have hle' : (∑ w ∈ (Finset.range (4 + 1)).filter (fun w => ¬(0 ≤ w ∧ w < 0 + 3)),
      ((4 : ℕ).choose w : ℝ) * ((((2 : ℕ) : ℝ) - 1) / (2 * (2 : ℕ))) ^ w *
        (1 - (((2 : ℕ) : ℝ) - 1) / (2 * (2 : ℕ))) ^ (4 - w)) ≤
      1 / (((1 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) ^ 2 * (5 : ℕ)) := by
    simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one] using hle
  have htrue := (checkBinomTail_eq_true_iff (Q := 4) (r := 2) (A₀ := 0) (R := 3) (b := 1)
    (lam := 5) (by decide) (by decide) (by decide)).mpr hle'
  rw [hchk] at htrue; cases htrue

/-- Degenerate zero-denominator parameters are rejected by `checkBinomTail`'s positivity guards. -/
example :
    checkBinomTail 4 0 0 3 1 4 = false ∧ checkBinomTail 4 2 0 3 0 4 = false ∧
      checkBinomTail 4 2 0 3 1 0 = false := by decide

/-! ### 3. `checkReplacementFeasible` witnesses and `ReplacementParams.Feasible` round-trip -/

/-- Explicit feasible Lemma 4.7 witness `(n = 2 ^ 60, M = 2 ^ 60, b = 1, wmax = 1, lam = 10,
Q = 12, r = 2, A₀ = 0, R = 8)` verified in the kernel, with negative controls for each guard. -/
example :
    checkReplacementFeasible (2 ^ 60) (2 ^ 60) 1 1 10 12 2 0 8 = true ∧
      checkReplacementFeasible (2 ^ 60) 100 1 1 10 12 2 0 8 = false ∧
      checkReplacementFeasible 40 (2 ^ 60) 1 1 10 12 2 0 8 = false ∧
      checkReplacementFeasible (2 ^ 60) (2 ^ 60) 1 1 10 12 1 0 8 = false ∧
      checkReplacementFeasible (2 ^ 60) (2 ^ 60) 1 1 1000 12 2 0 8 = false := by decide

/-- Nonvacuous round-trip witness: for `β = 2`, there exists `n ≥ 20` where `chooseBeta` selects
`β = 2`, `checkScheduleFeasible` evaluates to `true`, and
`feasible_of_checkScheduleFeasible_chooseBeta_eq_true` reconstructs
`ReplacementParams.Feasible 2 n b b n`. -/
example :
    ∃ n ≥ 20,
      let b := Nat.clog 2 n ^ 2
      chooseBeta (Nat.clog 2 n) b b = 2 ∧
        checkScheduleFeasible n n b b 2 = true ∧
        ReplacementParams.Feasible 2 n b b n := by
  obtain ⟨n₀, hn₀, hpass⟩ := exists_checkScheduleFeasible_eq_true (β := 2) (by decide)
  refine ⟨n₀, hn₀, ?_⟩
  set lam := Nat.clog 2 n₀
  have hlam2 : 2 ≤ lam :=
    (show 2 = Nat.clog 2 (2 ^ 2) from (Nat.clog_pow 2 2 Nat.one_lt_two).symm).trans_le
      (Nat.clog_mono_right 2 (by omega))
  have hb1 : 1 ≤ lam ^ 2 := Nat.one_le_pow 2 lam (by omega)
  have hchk : checkScheduleFeasible n₀ n₀ (lam ^ 2) (lam ^ 2) 2 = true :=
    hpass le_rfl hb1 le_rfl hb1 le_rfl le_rfl (Nat.le_mul_of_pos_left n₀ hb1)
  obtain ⟨hβ1, _, _, hmin⟩ := chooseBeta_spec (b := lam ^ 2) (w := lam ^ 2) hlam2
  have hβ_le : chooseBeta lam (lam ^ 2) (lam ^ 2) ≤ 2 := by
    by_contra! hgt
    exact hmin 2 (by decide) hgt ⟨le_rfl, le_rfl⟩
  have hβ_ne1 : chooseBeta lam (lam ^ 2) (lam ^ 2) ≠ 1 := fun h1 => by
    obtain ⟨_, hb_le, _, _⟩ := chooseBeta_spec (b := lam ^ 2) (w := lam ^ 2) hlam2
    rw [h1, pow_one] at hb_le; nlinarith
  have hβ_eq : chooseBeta lam (lam ^ 2) (lam ^ 2) = 2 := by omega
  have hchk' : checkScheduleFeasible n₀ n₀ (lam ^ 2) (lam ^ 2)
      (chooseBeta lam (lam ^ 2) (lam ^ 2)) = true := by rw [hβ_eq]; exact hchk
  have hfeas := feasible_of_checkScheduleFeasible_chooseBeta_eq_true hchk'
  rw [hβ_eq] at hfeas
  exact ⟨hβ_eq, hchk, hfeas⟩

/-! ### 4. Schedule evaluation, `chooseBeta`, and Proposition 6.4 `numGroups` bounds -/

/-- Small-`n` fallback at `n = 20`: `λ = 5`, `ν = 3`, `r = 0`, `Q = 0`, `R = 12`, `A₀ = 0`. -/
example :
    computeScheduleParams 1 20 = (5, 3, 0, 0, 12, 0) ∧
      checkScheduleFeasible 20 20 1 1 1 = false := by
  simp only [computeScheduleParams, checkScheduleFeasible, checkReplacementFeasible,
    ReplacementParams.numGroups, ReplacementParams.numNodes, ReplacementParams.rowBound,
    ReplacementParams.intervalStart]
  norm_num

/-- Exact off-by-one power boundaries for `chooseBeta` at `lam = 4`. -/
example : chooseBeta 4 1 1 = 1 ∧ chooseBeta 4 5 16 = 2 ∧ chooseBeta 4 17 16 = 3 := by decide

/-- Concrete evaluation of `heavyDegreeCutoff`, `heavyIncidenceCutoff`, and `numGroups`. -/
example :
    heavyDegreeCutoff 16 = 1024 ∧ heavyIncidenceCutoff 25 10 = 6 ∧
      ReplacementParams.numGroups 4 = 1 := by
  simp only [heavyDegreeCutoff, heavyIncidenceCutoff, ReplacementParams.numGroups]
  norm_num

/-- Symbolic evaluation at `n = 2 ^ (2 ^ 20)` (`λ_n = 2 ^ 20`, `ν_n = 20`, `√λ_n = 1024`,
`ν_n ^ 2 = 400`), confirming `ReplacementParams.numGroups n = 2`, `numGroups_eq_findGreatest`, and
the strict integer-comparison sandwich `2 ^ 2 * 20 ^ 4 ≤ 2 ^ 20 < 3 ^ 2 * 20 ^ 4`. -/
example :
    let n := 2 ^ (2 ^ 20)
    ReplacementParams.numGroups n = 2 ∧
      Nat.findGreatest (fun s => s ^ 2 * Nat.clog 2 (Nat.clog 2 n) ^ 4 ≤ Nat.clog 2 n)
        (Nat.clog 2 n) = 2 ∧
      ReplacementParams.numGroups n ^ 2 * Nat.clog 2 (Nat.clog 2 n) ^ 4 ≤ Nat.clog 2 n ∧
      Nat.clog 2 n < (ReplacementParams.numGroups n + 1) ^ 2 * Nat.clog 2 (Nat.clog 2 n) ^ 4 := by
  dsimp only
  generalize hn_def : 2 ^ (2 ^ 20) = n
  have hlam : Nat.clog 2 n = 2 ^ 20 := by
    rw [← hn_def]; exact Nat.clog_pow 2 (2 ^ 20) Nat.one_lt_two
  clear hn_def
  have hnu : Nat.clog 2 (Nat.clog 2 n) = 20 := by
    rw [hlam, Nat.clog_pow 2 20 Nat.one_lt_two]
  have hsq : (Nat.clog 2 n).sqrt = 1024 := by rw [hlam]; norm_num
  have hg : ReplacementParams.numGroups n = 2 := by
    unfold ReplacementParams.numGroups; rw [hsq, hnu]; norm_num
  have hfg : Nat.findGreatest (fun s => s ^ 2 * Nat.clog 2 (Nat.clog 2 n) ^ 4 ≤ Nat.clog 2 n)
      (Nat.clog 2 n) = 2 := by
    have hnu0 : Nat.clog 2 (Nat.clog 2 n) ≠ 0 := by rw [hnu]; decide
    have heq := numGroups_eq_findGreatest n
    rw [hg, ite_eq_right_iff.mpr fun h => absurd h hnu0] at heq
    exact heq.symm
  exact ⟨hg, hfg, ReplacementParams.sq_mul_pow_four_le_clog n,
    ReplacementParams.clog_lt_succ_sq_mul_pow_four (by rw [hnu]; norm_num)⟩

/-! ### 5. Plain `ComputableInPolyTime` compositions via `fun_prop` -/

/-- Composing `ReplacementParams.{rowBound, intervalStart, auxDim}` from binary inputs is certified
directly by `fun_prop`. -/
example : ComputableInPolyTime (fun x : (ℕ × ℕ) × ℕ =>
      ReplacementParams.rowBound x.2 x.1.1 + ReplacementParams.intervalStart x.2 x.1.1 +
        ReplacementParams.auxDim x.1.1)
    (encPair (encPair encNat encNat) encNat) encNat := by fun_prop

/-- Composing `heavyIncidenceCutoff`, `ReplacementParams.numNodes`, and
`ReplacementParams.numGroups` from binary inputs is certified directly by `fun_prop`. -/
example : ComputableInPolyTime (fun x : (ℕ × ℕ) × ℕ =>
      heavyIncidenceCutoff x.1.2 x.1.1 + ReplacementParams.numNodes x.1.1 +
        ReplacementParams.numGroups x.1.1)
    (encPair (encPair encNat encNat) encNat) encNat := by fun_prop

/-- Composing `ReplacementParams.numGroups`, `heavyDegreeCutoff`, `chooseBeta`, and `Nat.clog 2`
from binary inputs is certified directly by `fun_prop`. -/
example : ComputableInPolyTime (fun x : (ℕ × ℕ) × ℕ =>
      ReplacementParams.numGroups x.1.1 + heavyDegreeCutoff x.1.2 +
        chooseBeta (Nat.clog 2 x.1.1) x.1.2 x.2)
    (encPair (encPair encNat encNat) encNat) encNat := by fun_prop

/-- Capping a binary `Q` by a unary bound `Q_cap` via `min` and computing `binomTailNumerator`,
`Nat.choose`, `Nat.sqrt`, and `Nat.clog 2` composes cleanly via `fun_prop`. -/
example : ComputableInPolyTime (fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      let Q := min x.1.1 x.1.2
      binomTailNumerator Q x.2.1.sqrt 1 (x.2.1.sqrt + 1) + Q.choose x.1.1 + Nat.clog 2 x.2.2)
    (encPair (encPair encUnary encNat) (encPair encNat encNat)) encNat := by fun_prop

end ComplexityTests.ParameterCheck
