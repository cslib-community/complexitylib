/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.ReplacementParams
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Tactic.PolyTime.Init
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Nat.Sqrt
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Choose
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial-time parameter schedule and exact feasibility checks for subexponential `#k-SAT`

In Section 4.7 (Lemma 4.8, pp. 34–35), Section 5.5 (pp. 38–39), and Section 6.4 (Proposition 6.4,
pp. 43–44) of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], a uniform
algorithm computes the discrete replacement and sparsification parameters from input sizes and
verifies the numerical hypotheses of Lemma 4.7 and Lemma 4.8 in exact integer arithmetic, falling
back to direct evaluation on the finitely many small inputs where those checks fail rather than
referencing any noncomputable threshold constant `N₀`.

This module certifies the schedule parameters of `ReplacementParams` (`numGroups`, `numNodes`,
`rowBound`, `auxDim`, `intervalStart`) directly under plain `ComputableInPolyTime` (including
Proposition 6.4's integer-comparison characterization of `numGroups` via `s ^ 2 * ν_n ^ 4 ≤ λ_n`),
adds the Section 5.5 parameter selectors (`heavyDegreeCutoff`, `heavyIncidenceCutoff`,
`chooseBeta`), and proves exact cleared-denominator natural-number decision procedures
(`checkBinomTail`, `checkReplacementFeasible`, `checkScheduleFeasible`) with bidirectional
soundness/completeness and eventual-feasibility bridges to `ReplacementParams`.

## Main definitions

* `Cslib.Complexity.SubexponentialSAT.ParameterCheck.heavyDegreeCutoff`,
  `Cslib.Complexity.SubexponentialSAT.ParameterCheck.heavyIncidenceCutoff`,
  `Cslib.Complexity.SubexponentialSAT.ParameterCheck.chooseBeta`,
  `Cslib.Complexity.SubexponentialSAT.ParameterCheck.computeScheduleParams`: Section 5.5 and full
  Section 4.7 parameter selectors.
* `Cslib.Complexity.SubexponentialSAT.ParameterCheck.binomTailTerm`,
  `Cslib.Complexity.SubexponentialSAT.ParameterCheck.binomTailNumerator`,
  `Cslib.Complexity.SubexponentialSAT.ParameterCheck.checkBinomTail`,
  `Cslib.Complexity.SubexponentialSAT.ParameterCheck.checkReplacementFeasible`,
  `Cslib.Complexity.SubexponentialSAT.ParameterCheck.checkScheduleFeasible`: cleared-denominator
  natural-number Binomial-tail and Lemma 4.7 / Lemma 4.8 feasibility decision procedures.

## Main results

* `Cslib.Complexity.SubexponentialSAT.ParameterCheck.numGroups_eq_findGreatest`: Proposition 6.4
  `Nat.findGreatest` characterization of
  `Cslib.Complexity.SubexponentialSAT.ReplacementParams.numGroups` (from
  `ReplacementParams.sq_mul_pow_four_le_clog` and
  `ReplacementParams.clog_lt_succ_sq_mul_pow_four`).
* `Cslib.Complexity.SubexponentialSAT.ParameterCheck.checkBinomTail_eq_true_iff`,
  `checkBinomTail_schedule_eq_true_iff`, `checkScheduleFeasible_eq_true_iff`: exact equivalences
  with real Binomial tail probabilities and schedule balance bounds.
* `Cslib.Complexity.SubexponentialSAT.ParameterCheck.checkScheduleFeasible_eq_true_of_feasible`,
  `exists_checkScheduleFeasible_eq_true`, `feasible_of_checkScheduleFeasible_eq_true`,
  `feasible_of_checkScheduleFeasible_chooseBeta_eq_true`: completeness, eventual feasibility, and
  soundness against `Cslib.Complexity.SubexponentialSAT.ReplacementParams.Feasible`.
* `Cslib.Complexity.SubexponentialSAT.ParameterCheck.computableInPolyTime_numGroups`,
  `computableInPolyTime_numNodes`, `computableInPolyTime_rowBound`, `computableInPolyTime_auxDim`,
  `computableInPolyTime_intervalStart`, `computableInPolyTime_scheduleAndCheck_binary`,
  `computableInPolyTime_scheduleAndCheck_unary`: plain
  `Turing.MultiTapeTM.ComputableInPolyTime` certificates for the schedule and checkers.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 4.6 (Lemma 4.7,
  pp. 33–34), Section 4.7 (Lemma 4.8, pp. 34–35), Section 5.5 (pp. 38–39), and Section 6.4
  (Proposition 6.4, pp. 43–44).
-/

@[expose] public section

namespace Cslib.Complexity.SubexponentialSAT.ParameterCheck

open Finset Turing.MultiTapeTM

/-! ### 1. Section 5.5 / Section 6.4 Parameter Selectors and Full Schedule Tuple -/

/-- Auxiliary fifth-power polylogarithmic cutoff `λ_n ^ 5` on `n` variables, where
`λ_n = Nat.clog 2 n`. -/
def heavyDegreeCutoff (n : ℕ) : ℕ :=
  Nat.clog 2 n ^ 5

/-- Heavy-incidence threshold `b₀ = ⌈M / n⌉ ⌈√λ_n⌉` of Section 5.5 (`[OpenAI2026ETH]`, p. 38) for a
system of total scope size `M` on `n` variables. -/
def heavyIncidenceCutoff (M n : ℕ) : ℕ :=
  ((M + n - 1) / n) * (if Nat.clog 2 n = 0 then 0 else (Nat.clog 2 n - 1).sqrt + 1)

/-- Selector for the smallest integer `β ≥ 1` satisfying `b ≤ lam ^ β` and `w ≤ lam ^ β` in
Section 5.5 (`[OpenAI2026ETH]`, pp. 38–39), defaulting to `1` when `lam ≤ 1` and `max b w > 1`. -/
def chooseBeta (lam b w : ℕ) : ℕ :=
  (((List.range (max b.size w.size + 1)).map (· + 1)).find? fun β =>
    decide (b ≤ lam ^ β) && decide (w ≤ lam ^ β)).getD 1

/-- Full discrete parameter schedule `(λ, ν, r, Q, R, A₀)` of Section 4.7 equation (4.17) and
Lemma 4.8 (`[OpenAI2026ETH]`, p. 34), reusing `ReplacementParams` directly. -/
def computeScheduleParams (β n : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (Nat.clog 2 n, Nat.clog 2 (Nat.clog 2 n), ReplacementParams.numGroups n,
    ReplacementParams.numNodes n, ReplacementParams.rowBound β n,
    ReplacementParams.intervalStart β n)

/-- For `1 ≤ n`, `heavyIncidenceCutoff M n` agrees with `⌈(M : ℝ) / n⌉₊ * ⌈√λ_n⌉₊` (§5.5, p. 38). -/
theorem heavyIncidenceCutoff_eq_ceil_mul {M n : ℕ} (hn : 1 ≤ n) :
    heavyIncidenceCutoff M n = ⌈(M : ℝ) / n⌉₊ * ⌈Real.sqrt (Nat.clog 2 n)⌉₊ := by
  have hcsqrt : (if Nat.clog 2 n = 0 then 0 else (Nat.clog 2 n - 1).sqrt + 1) =
      ⌈Real.sqrt (Nat.clog 2 n)⌉₊ :=
    Nat.eq_of_mul_eq_mul_left (by decide : 0 < 0 + 3) (ReplacementParams.rowBound_eq_mul_ceil 0 n)
  rw [heavyIncidenceCutoff, hcsqrt]; congr 1
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp only [zero_add, Nat.cast_zero, zero_div, Nat.ceil_zero]
    exact Nat.div_eq_of_lt (by omega)
  · rw [show M + n - 1 = (M - 1) + n by omega, Nat.add_div_right _ (by omega : 0 < n)]
    set q := (M - 1) / n
    symm; rw [Nat.ceil_eq_iff (Nat.succ_ne_zero q), Nat.succ_sub_one]
    have hn_rpos : (0 : ℝ) < n := by positivity
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hn_rpos]
      have hmul : q * n ≤ M - 1 := Nat.div_mul_le_self (M - 1) n
      exact_mod_cast (by omega : q * n < M)
    · rw [div_le_iff₀ hn_rpos]
      have hdiv : n * q + (M - 1) % n = M - 1 := Nat.div_add_mod (M - 1) n
      have hmod := Nat.mod_lt (M - 1) (by omega : 0 < n)
      have hle : M ≤ (q + 1) * n := by rw [add_mul, one_mul, mul_comm q]; omega
      exact_mod_cast hle

/-- Whenever `2 ≤ lam`, `chooseBeta lam b w` returns the smallest integer `β ≥ 1` satisfying
`b ≤ lam ^ β` and `w ≤ lam ^ β` (§5.5, pp. 38–39). -/
theorem chooseBeta_spec {lam b w : ℕ} (hlam : 2 ≤ lam) :
    1 ≤ chooseBeta lam b w ∧
      b ≤ lam ^ chooseBeta lam b w ∧
      w ≤ lam ^ chooseBeta lam b w ∧
      ∀ β, 1 ≤ β → β < chooseBeta lam b w → ¬(b ≤ lam ^ β ∧ w ≤ lam ^ β) := by
  unfold chooseBeta
  set B := max b.size w.size + 1
  set l := (List.range B).map (· + 1)
  set pred : ℕ → Bool := fun β => decide (b ≤ lam ^ β) && decide (w ≤ lam ^ β)
  have hB_mem : B ∈ l := List.mem_map.mpr ⟨max b.size w.size, List.mem_range.mpr (by omega), rfl⟩
  have hB_pred : pred B = true := by
    have hb : b < lam ^ B := (Nat.lt_size_self b).trans_le
      ((Nat.pow_le_pow_right Nat.zero_lt_two
        ((le_max_left b.size w.size).trans (Nat.le_succ _))).trans (Nat.pow_le_pow_left hlam B))
    have hw : w < lam ^ B := (Nat.lt_size_self w).trans_le
      ((Nat.pow_le_pow_right Nat.zero_lt_two
        ((le_max_right b.size w.size).trans (Nat.le_succ _))).trans (Nat.pow_le_pow_left hlam B))
    simp only [pred, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hb.le, hw.le⟩
  obtain ⟨β₀, hfind⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨B, hB_mem, hB_pred⟩)
  rw [hfind, Option.getD_some]
  have hmem := List.mem_of_find?_eq_some hfind
  have hp := List.find?_some hfind
  simp only [l, List.mem_map, List.mem_range] at hmem
  obtain ⟨i, hi, rfl⟩ := hmem
  simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at hp
  refine ⟨by omega, hp.1, hp.2, fun β hβ₁ hβ_lt hβ_ok => ?_⟩
  have htake_eq : l.take i = (List.range i).map (· + 1) := by
    simp only [l, ← List.map_take, List.take_range, min_eq_left hi.le]
  have hβ_in_take : β ∈ l.take i := by
    rw [htake_eq, List.mem_map]; exact ⟨β - 1, List.mem_range.mpr (by omega), by omega⟩
  rw [(List.take_append_drop i l).symm, List.find?_append] at hfind
  cases htake : (l.take i).find? pred with
  | none =>
    have hnot : ¬pred β = true := List.find?_eq_none.mp htake β hβ_in_take
    simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at hnot; exact hnot hβ_ok
  | some y =>
    rw [htake, Option.some_or] at hfind; injection hfind with hy
    have hy_mem := List.mem_of_find?_eq_some htake
    rw [htake_eq, List.mem_map] at hy_mem
    obtain ⟨j, hj, hj_eq⟩ := hy_mem
    have hj_lt := List.mem_range.mp hj
    omega

/-- Proposition 6.4 integer-comparison characterization (`[OpenAI2026ETH]`, pp. 43–44):
`ReplacementParams.numGroups n` equals the `Nat.findGreatest` search for the largest `s ≤ λ_n`
satisfying `s ^ 2 * ν_n ^ 4 ≤ λ_n` (and `0` when `ν_n = 0`). -/
theorem numGroups_eq_findGreatest (n : ℕ) :
    ReplacementParams.numGroups n =
      if Nat.clog 2 (Nat.clog 2 n) = 0 then 0
      else Nat.findGreatest
        (fun s => s ^ 2 * Nat.clog 2 (Nat.clog 2 n) ^ 4 ≤ Nat.clog 2 n) (Nat.clog 2 n) := by
  set lam := Nat.clog 2 n; set nu := Nat.clog 2 lam
  rcases Nat.eq_zero_or_pos nu with hnu | hnu
  · simp only [ReplacementParams.numGroups, lam, nu, hnu, ↓reduceIte,
      zero_pow (by positivity : 2 ≠ 0), Nat.div_zero]
  · simp only [nu, Nat.ne_of_gt hnu, ↓reduceIte]
    have hs_le_lam : ReplacementParams.numGroups n ≤ lam :=
      (Nat.div_le_self _ _).trans (Nat.sqrt_le_self lam)
    have hle_fg := Nat.le_findGreatest
      (P := fun s => s ^ 2 * nu ^ 4 ≤ lam) hs_le_lam (ReplacementParams.sq_mul_pow_four_le_clog n)
    refine le_antisymm hle_fg ?_
    by_contra! hgt
    have hfg_spec : Nat.findGreatest (fun s => s ^ 2 * nu ^ 4 ≤ lam) lam ^ 2 * nu ^ 4 ≤ lam :=
      Nat.findGreatest_spec (P := fun s => s ^ 2 * nu ^ 4 ≤ lam) (Nat.zero_le lam)
        (by simp only [zero_pow (by positivity : 2 ≠ 0), zero_mul, Nat.zero_le])
    have hstep : (ReplacementParams.numGroups n + 1) ^ 2 * nu ^ 4 ≤ lam :=
      (Nat.mul_le_mul_right (nu ^ 4) (Nat.pow_le_pow_left hgt 2)).trans hfg_spec
    exact (not_le_of_gt (ReplacementParams.clog_lt_succ_sq_mul_pow_four hnu)) hstep

/-! ### 2. Cleared-Denominator `ℕ` Binomial-Tail and Feasibility Checkers -/

/-- Cleared-denominator integer summand `Q.choose w * (r - 1) ^ w * (r + 1) ^ (Q - w)` of
`(2 r) ^ Q * Pr[W = w]` for `W ~ Bin(Q, (r - 1) / (2 r))`. -/
def binomTailTerm (Q r w : ℕ) : ℕ :=
  Q.choose w * (r - 1) ^ w * (r + 1) ^ (Q - w)

/-- Exact cleared-denominator integer numerator `(2 r) ^ Q * Pr[W ∉ [A₀, A₀ + R))` for
`W ~ Bin(Q, (r - 1) / (2 r))`, summing `binomTailTerm Q r w` over `w ∈ {0, …, Q}` outside
`[A₀, A₀ + R)`. -/
def binomTailNumerator (Q r A₀ R : ℕ) : ℕ :=
  (((List.range (Q + 1)).filter fun w => !(decide (A₀ ≤ w) && decide (w < A₀ + R))).map
    (binomTailTerm Q r)).sum

/-- Exact integer decision procedure for the biased Binomial tail bound
`Pr[W ∉ [A₀, A₀ + R)) ≤ 1 / (b * r ^ 2 * lam)` under `W ~ Bin(Q, (r - 1) / (2 r))`, including
positivity guards `1 ≤ r`, `1 ≤ b`, and `1 ≤ lam`. -/
def checkBinomTail (Q r A₀ R b lam : ℕ) : Bool :=
  decide (1 ≤ r) && decide (1 ≤ b) && decide (1 ≤ lam) &&
    decide (binomTailNumerator Q r A₀ R * b * r ^ 2 * lam ≤ (2 * r) ^ Q)

/-- Exact integer decision procedure for the numerical hypotheses of Lemma 4.7
(`[OpenAI2026ETH]`, pp. 33–34): checks `2 ≤ r`, `1 ≤ R`, `R < Q`, `A₀ + R ≤ Q + 1`,
`2 * (b + wmax) * (r ^ (2 * Q)) ^ 2 ≤ M`, `2 * Q * r ^ 2 ≤ n`, and `checkBinomTail`. -/
def checkReplacementFeasible (n M b wmax lam Q r A₀ R : ℕ) : Bool :=
  decide (2 ≤ r) && decide (1 ≤ R) && decide (R < Q) && decide (A₀ + R ≤ Q + 1) &&
    decide (2 * (b + wmax) * (r ^ (2 * Q)) ^ 2 ≤ M) && decide (2 * Q * r ^ 2 ≤ n) &&
    checkBinomTail Q r A₀ R b lam

/-- Compute the full Section 4.7 schedule `(λ, ν, r, Q, R, A₀)` and verify in exact integer
arithmetic both the Lemma 4.8 regime conditions (`20 ≤ n`, `32 ≤ R`, `6 * R ≤ Q`) and
`checkReplacementFeasible`, deciding whether to run the subexponential replacement branch or the
small-`n` direct-evaluation fallback of Theorem 2.2 / §5.5 (`[OpenAI2026ETH]`, p. 39). -/
def checkScheduleFeasible (n M b wmax β : ℕ) : Bool :=
  let s := computeScheduleParams β n
  decide (20 ≤ n) && decide (32 ≤ s.2.2.2.2.1) && decide (6 * s.2.2.2.2.1 ≤ s.2.2.2.1) &&
    checkReplacementFeasible n M b wmax s.1 s.2.2.2.1 s.2.2.1 s.2.2.2.2.2 s.2.2.2.2.1

/-! #### Bridges to `Finset` sums, real probabilities, and `ReplacementParams` -/

private theorem sum_map_filter_range (n : ℕ) (p : ℕ → Bool) (f : ℕ → ℕ) :
    (((List.range n).filter p).map f).sum =
      ∑ w ∈ (Finset.range n).filter (fun w => p w = true), f w := by
  induction n with
  | zero =>
    simp only [List.range_zero, List.filter_nil, List.map_nil, List.sum_nil, Finset.range_zero,
      Finset.filter_empty, Finset.sum_empty]
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      Finset.range_add_one, Finset.filter_insert]
    by_cases h : p n = true
    · have hnot : n ∉ (Finset.range n).filter (fun w => p w = true) := fun hm =>
        (Finset.mem_range.mp (Finset.mem_filter.mp hm).1).ne rfl
      rw [List.filter_cons_of_pos h, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      simp only [h, ↓reduceIte, Finset.sum_insert hnot, add_comm]
    · rw [List.filter_cons_of_neg h, List.filter_nil, List.map_nil, List.sum_nil, add_zero]
      simp only [Bool.eq_false_iff.mpr h, Bool.false_eq_true, ↓reduceIte]

/-- `binomTailNumerator` as a `Finset` sum over `{0, …, Q}` outside `[A₀, A₀ + R)`. -/
theorem binomTailNumerator_eq_sum (Q r A₀ R : ℕ) :
    binomTailNumerator Q r A₀ R =
      ∑ w ∈ (Finset.range (Q + 1)).filter (fun w => ¬(A₀ ≤ w ∧ w < A₀ + R)),
        Q.choose w * (r - 1) ^ w * (r + 1) ^ (Q - w) := by
  unfold binomTailNumerator binomTailTerm
  rw [sum_map_filter_range]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext w; simp only [Finset.mem_filter]
  exact and_congr_right fun _ => by
    by_cases h1 : A₀ ≤ w <;> by_cases h2 : w < A₀ + R <;>
      simp only [h1, h2, decide_true, decide_false, Bool.and_self, Bool.and_false, Bool.false_and,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, and_self, and_false, false_and,
        not_true_eq_false, not_false_eq_true]

private theorem real_binomTailTerm_mul_two_mul_pow {Q r w : ℕ} (hr : 1 ≤ r) (hw : w ≤ Q) :
    (Q.choose w : ℝ) * (((r : ℝ) - 1) / (2 * r)) ^ w *
        (1 - ((r : ℝ) - 1) / (2 * r)) ^ (Q - w) * (2 * (r : ℝ)) ^ Q =
      ((Q.choose w * (r - 1) ^ w * (r + 1) ^ (Q - w) : ℕ) : ℝ) := by
  have h2r_ne : (2 * (r : ℝ)) ≠ 0 := by positivity
  have h1mp : 1 - ((r : ℝ) - 1) / (2 * r) = ((r : ℝ) + 1) / (2 * r) := by field_simp; ring
  have hpow : (2 * (r : ℝ)) ^ Q = (2 * (r : ℝ)) ^ w * (2 * (r : ℝ)) ^ (Q - w) := by
    rw [← pow_add, Nat.add_sub_of_le hw]
  have hfac1 : (((r : ℝ) - 1) / (2 * r)) ^ w * (2 * (r : ℝ)) ^ w = ((r : ℝ) - 1) ^ w := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero w h2r_ne)]
  have hfac2 : (((r : ℝ) + 1) / (2 * r)) ^ (Q - w) * (2 * (r : ℝ)) ^ (Q - w) =
      ((r : ℝ) + 1) ^ (Q - w) := by rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero (Q - w) h2r_ne)]
  rw [h1mp, hpow, show (Q.choose w : ℝ) * (((r : ℝ) - 1) / (2 * r)) ^ w *
      (((r : ℝ) + 1) / (2 * r)) ^ (Q - w) * ((2 * (r : ℝ)) ^ w * (2 * (r : ℝ)) ^ (Q - w)) =
      (Q.choose w : ℝ) * ((((r : ℝ) - 1) / (2 * r)) ^ w * (2 * (r : ℝ)) ^ w) *
        ((((r : ℝ) + 1) / (2 * r)) ^ (Q - w) * (2 * (r : ℝ)) ^ (Q - w)) by ring, hfac1, hfac2,
    Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hr, Nat.cast_add,
    Nat.cast_one]

/-- **Exact bridge from `checkBinomTail` to real `Bin(Q, (r - 1) / (2 r))` tail probabilities**:
for `1 ≤ r`, `1 ≤ b`, and `1 ≤ lam`, `checkBinomTail Q r A₀ R b lam = true` holds if and only if
the real Binomial tail outside `[A₀, A₀ + R)` is at most `1 / (b * r ^ 2 * lam)`. -/
theorem checkBinomTail_eq_true_iff {Q r A₀ R b lam : ℕ}
    (hr : 1 ≤ r) (hb : 1 ≤ b) (hlam : 1 ≤ lam) :
    checkBinomTail Q r A₀ R b lam = true ↔
      ∑ w ∈ (Finset.range (Q + 1)).filter (fun w => ¬(A₀ ≤ w ∧ w < A₀ + R)),
        (Q.choose w : ℝ) * (((r : ℝ) - 1) / (2 * r)) ^ w *
          (1 - ((r : ℝ) - 1) / (2 * r)) ^ (Q - w) ≤
        1 / ((b : ℝ) * (r : ℝ) ^ 2 * lam) := by
  unfold checkBinomTail
  simp only [Bool.and_eq_true, decide_eq_true_eq, hr, hb, hlam, true_and]
  set S := (Finset.range (Q + 1)).filter fun w => ¬(A₀ ≤ w ∧ w < A₀ + R)
  have hsum_mul : (∑ w ∈ S, (Q.choose w : ℝ) * (((r : ℝ) - 1) / (2 * r)) ^ w *
        (1 - ((r : ℝ) - 1) / (2 * r)) ^ (Q - w)) * (2 * (r : ℝ)) ^ Q =
      (binomTailNumerator Q r A₀ R : ℝ) := by
    rw [Finset.sum_mul, binomTailNumerator_eq_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    exact real_binomTailTerm_mul_two_mul_pow hr
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hw).1))
  have h2r_pos : (0 : ℝ) < (2 * (r : ℝ)) ^ Q := by positivity
  have hden_pos : (0 : ℝ) < (b : ℝ) * (r : ℝ) ^ 2 * lam := by positivity
  have hcast_iff : binomTailNumerator Q r A₀ R * b * r ^ 2 * lam ≤ (2 * r) ^ Q ↔
      (binomTailNumerator Q r A₀ R : ℝ) * ((b : ℝ) * (r : ℝ) ^ 2 * lam) ≤ (2 * (r : ℝ)) ^ Q := by
    rw [← Nat.cast_le (α := ℝ)]; push_cast; ring_nf
  rw [hcast_iff, ← hsum_mul, le_div_iff₀ hden_pos]
  set lhs := ∑ w ∈ S, (Q.choose w : ℝ) * (((r : ℝ) - 1) / (2 * r)) ^ w *
    (1 - ((r : ℝ) - 1) / (2 * r)) ^ (Q - w)
  set den := (b : ℝ) * (r : ℝ) ^ 2 * lam
  exact ⟨fun h => le_of_mul_le_mul_right (by linarith : lhs * den * (2 * (r : ℝ)) ^ Q ≤
      1 * (2 * (r : ℝ)) ^ Q) h2r_pos,
    fun h => by linarith [mul_le_mul_of_nonneg_right h h2r_pos.le]⟩

/-- Closed-interval (`Finset.Icc A₀ (A₀ + R - 1)`) form of `checkBinomTail_eq_true_iff` whenever
`1 ≤ R`, matching the interval `I = {A₀, …, A₀ + R - 1}` of Lemma 4.8. -/
theorem checkBinomTail_eq_true_iff_notMem_Icc {Q r A₀ R b lam : ℕ}
    (hr : 1 ≤ r) (hR : 1 ≤ R) (hb : 1 ≤ b) (hlam : 1 ≤ lam) :
    checkBinomTail Q r A₀ R b lam = true ↔
      ∑ w ∈ (Finset.range (Q + 1)).filter (fun w => w ∉ Finset.Icc A₀ (A₀ + R - 1)),
        (Q.choose w : ℝ) * (((r : ℝ) - 1) / (2 * r)) ^ w *
          (1 - ((r : ℝ) - 1) / (2 * r)) ^ (Q - w) ≤
        1 / ((b : ℝ) * (r : ℝ) ^ 2 * lam) := by
  rw [checkBinomTail_eq_true_iff hr hb hlam]
  refine Eq.to_iff (congrArg₂ (· ≤ ·) (Finset.sum_congr ?_ fun _ _ => rfl) rfl)
  ext w; simp only [Finset.mem_filter, Finset.mem_Icc]
  exact and_congr_right fun _ => not_congr ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega⟩,
    fun ⟨h1, h2⟩ => ⟨h1, by omega⟩⟩

/-- Schedule specialization of `checkBinomTail_eq_true_iff_notMem_Icc`: on equation (4.17)'s
schedule, `checkBinomTail` decides
`ReplacementParams.binomTail β n ≤ ReplacementParams.tailBudget b n` exactly. -/
theorem checkBinomTail_schedule_eq_true_iff {β n b : ℕ}
    (hr : 1 ≤ ReplacementParams.numGroups n) (hR : 1 ≤ ReplacementParams.rowBound β n)
    (hb : 1 ≤ b) (hlam : 1 ≤ Nat.clog 2 n) :
    checkBinomTail (ReplacementParams.numNodes n) (ReplacementParams.numGroups n)
        (ReplacementParams.intervalStart β n) (ReplacementParams.rowBound β n) b
        (Nat.clog 2 n) = true ↔
      ReplacementParams.binomTail β n ≤ ReplacementParams.tailBudget b n :=
  checkBinomTail_eq_true_iff_notMem_Icc hr hR hb hlam

/-- Soundness and completeness characterization of `checkReplacementFeasible`, unpacking all
numerical balance bounds and the exact real Binomial tail inequality. -/
theorem checkReplacementFeasible_eq_true_iff (n M b wmax lam Q r A₀ R : ℕ) :
    checkReplacementFeasible n M b wmax lam Q r A₀ R = true ↔
      2 ≤ r ∧ 1 ≤ R ∧ R < Q ∧ A₀ + R ≤ Q + 1 ∧
        2 * (b + wmax) * (r ^ (2 * Q)) ^ 2 ≤ M ∧ 2 * Q * r ^ 2 ≤ n ∧
        1 ≤ b ∧ 1 ≤ lam ∧
        ∑ w ∈ (Finset.range (Q + 1)).filter (fun w => ¬(A₀ ≤ w ∧ w < A₀ + R)),
          (Q.choose w : ℝ) * (((r : ℝ) - 1) / (2 * r)) ^ w *
            (1 - ((r : ℝ) - 1) / (2 * r)) ^ (Q - w) ≤
          1 / ((b : ℝ) * (r : ℝ) ^ 2 * lam) := by
  constructor
  · intro h
    unfold checkReplacementFeasible at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hr2, hR1⟩, hRQ⟩, hAR⟩, hbalM⟩, hbaln⟩, htail⟩ := h
    have htail_guards : 1 ≤ b ∧ 1 ≤ lam := by
      unfold checkBinomTail at htail
      simp only [Bool.and_eq_true, decide_eq_true_eq] at htail
      exact ⟨htail.1.1.2, htail.1.2⟩
    exact ⟨hr2, hR1, hRQ, hAR, hbalM, hbaln, htail_guards.1, htail_guards.2,
      (checkBinomTail_eq_true_iff (by omega) htail_guards.1 htail_guards.2).mp htail⟩
  · rintro ⟨hr2, hR1, hRQ, hAR, hbalM, hbaln, hb1, hlam1, htail_real⟩
    have htail := (checkBinomTail_eq_true_iff (by omega) hb1 hlam1).mpr htail_real
    unfold checkReplacementFeasible
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨hr2, hR1⟩, hRQ⟩, hAR⟩, hbalM⟩, hbaln⟩, htail⟩

/-- Exact characterization of `checkScheduleFeasible` in terms of `ReplacementParams`. -/
theorem checkScheduleFeasible_eq_true_iff (n M b w β : ℕ) :
    checkScheduleFeasible n M b w β = true ↔
      20 ≤ n ∧ 2 ≤ ReplacementParams.numGroups n ∧ 32 ≤ ReplacementParams.rowBound β n ∧
        6 * ReplacementParams.rowBound β n ≤ ReplacementParams.numNodes n ∧ 1 ≤ b ∧
        2 * (b + w) * ReplacementParams.auxDim n ^ 2 ≤ M ∧
        2 * ReplacementParams.numNodes n * ReplacementParams.numGroups n ^ 2 ≤ n ∧
        ReplacementParams.binomTail β n ≤ ReplacementParams.tailBudget b n := by
  constructor
  · intro h
    unfold checkScheduleFeasible computeScheduleParams checkReplacementFeasible at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h20, hR32⟩, hRQ6⟩, ⟨⟨⟨⟨⟨⟨hr2, _⟩, _⟩, _⟩, hbalM⟩, hbaln⟩, htail⟩⟩ := h
    have hguards : 1 ≤ b ∧ 1 ≤ Nat.clog 2 n := by
      unfold checkBinomTail at htail
      simp only [Bool.and_eq_true, decide_eq_true_eq] at htail
      exact ⟨htail.1.1.2, htail.1.2⟩
    exact ⟨h20, hr2, hR32, hRQ6, hguards.1, hbalM, hbaln,
      (checkBinomTail_schedule_eq_true_iff (by omega) (by omega) hguards.1 hguards.2).mp htail⟩
  · rintro ⟨h20, hr2, hR32, hRQ6, hb1, haux_bal, hvar_bal, htail_le⟩
    have hlam1 : 1 ≤ Nat.clog 2 n := Nat.clog_pos Nat.one_lt_two (by omega : 1 < n)
    have hR1 : 1 ≤ ReplacementParams.rowBound β n := by omega
    have hsub := ReplacementParams.interval_subset_range (β := β) hr2 hR1 (by omega)
    have hk_mem : ReplacementParams.intervalStart β n + ReplacementParams.rowBound β n - 1 ∈
        ReplacementParams.interval β n := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
    have hk_lt := Finset.mem_range.mp (hsub hk_mem)
    have htail := (checkBinomTail_schedule_eq_true_iff (by omega) hR1 hb1 hlam1).mpr htail_le
    unfold checkScheduleFeasible computeScheduleParams checkReplacementFeasible
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨h20, hR32⟩, hRQ6⟩,
      ⟨⟨⟨⟨⟨⟨hr2, hR1⟩, by omega⟩, by omega⟩, haux_bal⟩, hvar_bal⟩, htail⟩⟩

/-- **Completeness of `checkScheduleFeasible` against `ReplacementParams.Feasible`**: every feasible
instance passes the exact integer-arithmetic feasibility checker. -/
theorem checkScheduleFeasible_eq_true_of_feasible {β n b w M : ℕ}
    (h : ReplacementParams.Feasible β n b w M) :
    checkScheduleFeasible n M b w β = true := by
  have hr_r : (2 : ℝ) ≤ ReplacementParams.numGroups n := by exact_mod_cast h.two_le_numGroups
  have hp0 : 0 ≤ ReplacementParams.binomProb n := by
    unfold ReplacementParams.binomProb; exact div_nonneg (by linarith) (by positivity)
  have hp1 : 0 ≤ 1 - ReplacementParams.binomProb n := by
    unfold ReplacementParams.binomProb
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have htail_nn : 0 ≤ ReplacementParams.binomTail β n :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hbud_pos : 0 < ReplacementParams.tailBudget b n := lt_of_le_of_lt htail_nn h.binomTail_lt
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb_pos
    · simp only [ReplacementParams.tailBudget, Nat.cast_zero, zero_mul, div_zero,
        lt_self_iff_false] at hbud_pos
    · omega
  exact (checkScheduleFeasible_eq_true_iff n M b w β).mpr
    ⟨h.twenty_le, h.two_le_numGroups, h.thirtyTwo_le_rowBound, h.six_mul_rowBound_le_numNodes,
      hb1, h.aux_balance, h.var_balance, h.binomTail_lt.le⟩

/-- **Eventual passage of `checkScheduleFeasible` (Lemma 4.8, `[OpenAI2026ETH]`, p. 34:
"For fixed `β`, only finitely many `n` fail these checks")**: for every `1 ≤ β`, there exists
`n₀ ≥ 20` above which `checkScheduleFeasible n M b w β = true` holds for all valid `(b, w, M)`. -/
theorem exists_checkScheduleFeasible_eq_true {β : ℕ} (hβ : 1 ≤ β) :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧ ∀ ⦃n b w M : ℕ⦄, n₀ ≤ n →
      1 ≤ b → b ≤ Nat.clog 2 n ^ β →
      1 ≤ w → w ≤ Nat.clog 2 n ^ β →
      n ≤ M → M ≤ b * n → checkScheduleFeasible n M b w β = true := by
  obtain ⟨n₀, hn₀, hfeas⟩ := ReplacementParams.exists_feasible hβ
  exact ⟨n₀, hn₀, fun ⦃_ _ _ _⦄ hn hb₁ hb₂ hw₁ hw₂ hnM hMbn =>
    checkScheduleFeasible_eq_true_of_feasible (hfeas hn hb₁ hb₂ hw₁ hw₂ hnM hMbn)⟩

/-- **Soundness of `checkScheduleFeasible` against `ReplacementParams.Feasible`**: when `1 ≤ β` and
`b ≤ λ_n ^ β`, passing `checkScheduleFeasible n M b w β` implies the full
`ReplacementParams.Feasible` bundle, including the strict Binomial tail bound and equation (4.18)'s
`rowCost` bound. -/
theorem feasible_of_checkScheduleFeasible_eq_true {β n b w M : ℕ}
    (hβ : 1 ≤ β) (hb₂ : b ≤ Nat.clog 2 n ^ β)
    (hchk : checkScheduleFeasible n M b w β = true) :
    ReplacementParams.Feasible β n b w M := by
  obtain ⟨h20, hr, hR, hRQ, hb₁, haux_bal, hvar_bal, _⟩ :=
    (checkScheduleFeasible_eq_true_iff n M b w β).mp hchk
  have hlam_pos : 1 ≤ Nat.clog 2 n := Nat.clog_pos Nat.one_lt_two (by omega : 1 < n)
  have htau_pos : 0 < ReplacementParams.tau n := by unfold ReplacementParams.tau; positivity
  have htau_le : ReplacementParams.tau n ≤ 1 / 2 := by
    unfold ReplacementParams.tau
    exact one_div_le_one_div_of_le zero_lt_two
      (by exact_mod_cast (by nlinarith : 2 ≤ ReplacementParams.numGroups n * Nat.clog 2 n))
  have hsub := ReplacementParams.interval_subset_range (β := β) hr (by omega) (by omega)
  exact
    { twenty_le := h20, two_le_numGroups := hr, thirtyTwo_le_rowBound := hR,
      six_mul_rowBound_le_numNodes := hRQ, tau_pos := htau_pos, tau_le_half := htau_le,
      auxDim_le := ReplacementParams.auxDim_le_two_pow n, aux_balance := haux_bal,
      var_balance := hvar_bal, card_interval_eq := ReplacementParams.card_interval (by omega),
      interval_subset := hsub,
      mem_interval_of_close := fun k hk =>
        let hmem := ReplacementParams.mem_interval_of_abs_sub_le hr hR (by omega) hk
        ⟨hmem, Nat.lt_succ_iff.mp (Finset.mem_range.mp (hsub hmem))⟩,
      binomTail_lt := ReplacementParams.binomTail_lt_tailBudget hβ hr hR hRQ hb₁ hb₂,
      rowCost_bound := ReplacementParams.rowCost_le hr hR hRQ }

/-- Automatic soundness of `checkScheduleFeasible` when `β = chooseBeta (Nat.clog 2 n) b w`
(§5.5, pp. 38–39), needing no external `1 ≤ β` or `b ≤ λ_n ^ β` hypotheses. -/
theorem feasible_of_checkScheduleFeasible_chooseBeta_eq_true {n M b w : ℕ}
    (hchk : checkScheduleFeasible n M b w (chooseBeta (Nat.clog 2 n) b w) = true) :
    ReplacementParams.Feasible (chooseBeta (Nat.clog 2 n) b w) n b w M := by
  have h20 : 20 ≤ n := ((checkScheduleFeasible_eq_true_iff _ _ _ _ _).mp hchk).1
  have hlam2 : 2 ≤ Nat.clog 2 n :=
    (show 2 = Nat.clog 2 (2 ^ 2) from (Nat.clog_pow 2 2 Nat.one_lt_two).symm).trans_le
      (Nat.clog_mono_right 2 (by omega))
  obtain ⟨hβ1, hb₂, _, _⟩ := chooseBeta_spec (b := b) (w := w) hlam2
  exact feasible_of_checkScheduleFeasible_eq_true hβ1 hb₂ hchk

/-! ### 3. Plain Polynomial-Time Certificates (`ComputableInPolyTime`) -/

section PolyTime

open ComputableInPolyTime

/-! #### Internal plain building blocks -/

private theorem clog_two_le_size (n : ℕ) : Nat.clog 2 n ≤ n.size :=
  (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr (Nat.lt_size_self n).le

private theorem bAdd {α : Type} {ei : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableInPolyTime f ei encNat) (hg : ComputableInPolyTime g ei encNat) :
    ComputableInPolyTime (fun x => f x + g x) ei encNat :=
  binary_add.comp (hf.prod hg)

private theorem bDiv {α : Type} {ei : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableInPolyTime f ei encNat) (hg : ComputableInPolyTime g ei encNat) :
    ComputableInPolyTime (fun x => f x / g x) ei encNat :=
  binary_div.comp (hf.prod hg)

private theorem bLe {α : Type} {ei : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableInPolyTime f ei encNat) (hg : ComputableInPolyTime g ei encNat) :
    ComputableInPolyTime (fun x => decide (f x ≤ g x)) ei encBool :=
  (show ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
    (encPair encNat encNat) encBool by fun_prop).comp (hf.prod hg)

private theorem uToB : ComputableInPolyTime (fun n : ℕ => n) encUnary encNat := by fun_prop

private theorem uMax :
    ComputableInPolyTime (fun p : ℕ × ℕ => max p.1 p.2) (encPair encUnary encUnary) encUnary := by
  fun_prop

private theorem bSum : ComputableInPolyTime List.sum (encList encNat) encNat := by fun_prop

private theorem clog2_pt : ComputableInPolyTime (Nat.clog 2) encNat encNat :=
  binary_clog_two_nat

private theorem nu_pt :
    ComputableInPolyTime (fun n : ℕ => Nat.clog 2 (Nat.clog 2 n)) encNat encNat :=
  clog2_pt.comp clog2_pt

/-- `ReplacementParams.numGroups` (`r`) is polynomial-time over binary naturals. -/
@[fun_prop, program_certificate]
theorem computableInPolyTime_numGroups :
    ComputableInPolyTime ReplacementParams.numGroups encNat encNat :=
  bDiv (binary_sqrt.comp clog2_pt) (binary_pow' nu_pt (const 2))

/-- `ReplacementParams.numGroups` (`r`) is polynomial-time from binary naturals to unary. -/
theorem computableInPolyTime_numGroups_unary :
    ComputableInPolyTime ReplacementParams.numGroups encNat encUnary := by
  refine (binary_min_unary' binary_size computableInPolyTime_numGroups).of_enc_eq fun n =>
    congrArg encUnary ?_
  exact (Nat.min_eq_right
    (((Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)).trans (clog_two_le_size n))).symm

/-- `ReplacementParams.numNodes` (`Q`) is polynomial-time over binary naturals. -/
@[fun_prop, program_certificate]
theorem computableInPolyTime_numNodes :
    ComputableInPolyTime ReplacementParams.numNodes encNat encNat :=
  bDiv clog2_pt (binary_mul' (const 128) nu_pt)

/-- `ReplacementParams.numNodes` (`Q`) is polynomial-time from binary naturals to unary. -/
theorem computableInPolyTime_numNodes_unary :
    ComputableInPolyTime ReplacementParams.numNodes encNat encUnary := by
  refine (binary_min_unary' binary_size computableInPolyTime_numNodes).of_enc_eq fun n =>
    congrArg encUnary ?_
  exact (Nat.min_eq_right ((Nat.div_le_self _ _).trans (clog_two_le_size n))).symm

/-- `ReplacementParams.rowBound` (`R`) is polynomial-time over binary pairs `(β, n)`. -/
theorem computableInPolyTime_rowBound :
    ComputableInPolyTime (fun p : ℕ × ℕ => ReplacementParams.rowBound p.1 p.2)
      (encPair encNat encNat) encNat :=
  binary_mul' (bAdd (fst encNat encNat) (const 3))
    (binary_ceilSqrt.comp (clog2_pt.comp (snd encNat encNat)))

@[fun_prop, program_certificate]
theorem computableInPolyTime_rowBound_apply {α : Type} {encIn : α ↪ List Bool} {fβ fn : α → ℕ}
    (hβ : ComputableInPolyTime fβ encIn encNat) (hn : ComputableInPolyTime fn encIn encNat) :
    ComputableInPolyTime (fun x => ReplacementParams.rowBound (fβ x) (fn x)) encIn encNat :=
  (computableInPolyTime_rowBound.comp (hβ.prod hn)).of_enc_eq fun _ => rfl

/-- `ReplacementParams.auxDim` (`D = r ^ (2 Q) ≤ 2 ^ (λ / 128)`) is polynomial-time over binary
naturals (`encNat` to `encNat`). -/
@[fun_prop, program_certificate]
theorem computableInPolyTime_auxDim :
    ComputableInPolyTime ReplacementParams.auxDim encNat encNat :=
  binary_pow' computableInPolyTime_numGroups
    (unary_mul.comp ((const 2).prod computableInPolyTime_numNodes_unary))

/-- `ReplacementParams.intervalStart` (`A₀`) is polynomial-time over binary pairs `(β, n)`. -/
theorem computableInPolyTime_intervalStart :
    ComputableInPolyTime (fun p : ℕ × ℕ => ReplacementParams.intervalStart p.1 p.2)
      (encPair encNat encNat) encNat := by
  have hn := snd encNat encNat
  have hr := computableInPolyTime_numGroups.comp hn
  have hQ := computableInPolyTime_numNodes.comp hn
  have hR := computableInPolyTime_rowBound
  exact bDiv
    (binary_sub' (binary_mul' hQ (binary_sub' hr (const 1)))
      (binary_mul' hr (binary_sub' hR (const 1))))
    (binary_mul' (const 2) hr)

@[fun_prop, program_certificate]
theorem computableInPolyTime_intervalStart_apply {α : Type} {encIn : α ↪ List Bool} {fβ fn : α → ℕ}
    (hβ : ComputableInPolyTime fβ encIn encNat) (hn : ComputableInPolyTime fn encIn encNat) :
    ComputableInPolyTime (fun x => ReplacementParams.intervalStart (fβ x) (fn x)) encIn encNat :=
  (computableInPolyTime_intervalStart.comp (hβ.prod hn)).of_enc_eq fun _ =>
    congrArg encNat (congrArg₂ ReplacementParams.intervalStart rfl rfl)

/-- `heavyDegreeCutoff` (`λ_n ^ 5`) is polynomial-time over binary naturals. -/
@[fun_prop, program_certificate]
theorem computableInPolyTime_heavyDegreeCutoff :
    ComputableInPolyTime heavyDegreeCutoff encNat encNat :=
  binary_pow' clog2_pt (const 5)

/-- `heavyIncidenceCutoff` (`b₀ = ⌈M / n⌉ ⌈√λ_n⌉`) is polynomial-time over binary pairs `(M, n)`. -/
theorem computableInPolyTime_heavyIncidenceCutoff :
    ComputableInPolyTime (fun p : ℕ × ℕ => heavyIncidenceCutoff p.1 p.2)
      (encPair encNat encNat) encNat :=
  binary_mul'
    (bDiv (binary_sub' (bAdd (fst encNat encNat) (snd encNat encNat)) (const 1))
      (snd encNat encNat))
    (binary_ceilSqrt.comp (clog2_pt.comp (snd encNat encNat)))

@[fun_prop, program_certificate]
theorem computableInPolyTime_heavyIncidenceCutoff_apply {α : Type} {encIn : α ↪ List Bool}
    {fM fn : α → ℕ} (hM : ComputableInPolyTime fM encIn encNat)
    (hn : ComputableInPolyTime fn encIn encNat) :
    ComputableInPolyTime (fun x => heavyIncidenceCutoff (fM x) (fn x)) encIn encNat :=
  (computableInPolyTime_heavyIncidenceCutoff.comp (hM.prod hn)).of_enc_eq fun _ => rfl

/-- `chooseBeta` is polynomial-time over binary triples `(lam, b, w)`. -/
theorem computableInPolyTime_chooseBeta :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => chooseBeta p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encNat) encNat) encNat := by
  let encIn := encPair (encPair encNat encNat) encNat
  have hb_size : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.2.size) encIn encUnary :=
    binary_size.comp ((fst (encPair encNat encNat) encNat).snd')
  have hw_size : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.2.size) encIn encUnary :=
    binary_size.comp (snd (encPair encNat encNat) encNat)
  have hlist : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => (List.range (max p.1.2.size p.2.size + 1)).map (· + 1))
      encIn (encList encUnary) :=
    mapWithInput
      (range.comp (unary_add.comp ((uMax.comp (hb_size.prod hw_size)).prod (const 1))))
      (unary_add.comp ((snd encIn encUnary).prod (const 1)))
  have hpred : ComputableInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × ℕ) =>
        decide (q.1.1.2 ≤ q.1.1.1 ^ q.2) && decide (q.1.2 ≤ q.1.1.1 ^ q.2))
      (encPair encIn encUnary) encBool := by
    have hq1 := fst encIn encUnary
    have hpow := binary_pow' ((hq1.fst').fst') (snd encIn encUnary)
    exact bool_and' (bLe ((hq1.fst').snd') hpow) (bLe hq1.snd' hpow)
  exact uToB.comp ((findWithInput hlist hpred).optionGetDWithInput (const 1))

@[fun_prop, program_certificate]
theorem computableInPolyTime_chooseBeta_apply {α : Type} {encIn : α ↪ List Bool}
    {flam fb fw : α → ℕ} (hlam : ComputableInPolyTime flam encIn encNat)
    (hb : ComputableInPolyTime fb encIn encNat) (hw : ComputableInPolyTime fw encIn encNat) :
    ComputableInPolyTime (fun x => chooseBeta (flam x) (fb x) (fw x)) encIn encNat :=
  (computableInPolyTime_chooseBeta.comp ((hlam.prod hb).prod hw)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_binomTailTerm :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => binomTailTerm p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encNat) encUnary) encNat := by
  have h1 := fst (encPair encUnary encNat) encUnary
  have hQ := h1.fst'; have hr := h1.snd'; have hw := snd (encPair encUnary encNat) encUnary
  exact binary_mul'
    (binary_mul' (binary_choose.comp (hQ.prod hw)) (binary_pow' (binary_sub' hr (const 1)) hw))
    (binary_pow' (bAdd hr (const 1)) (unary_sub.comp (hQ.prod hw)))

/-- `binomTailNumerator` is polynomial-time with `Q` in `encUnary` and `(r, A₀, R)` in `encNat`. -/
theorem computableInPolyTime_binomTailNumerator :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × ℕ => binomTailNumerator p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary encNat) encNat) encNat) encNat := by
  let enc3 := encPair (encPair encUnary encNat) encNat; let encIn := encPair enc3 encNat
  have hlist : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × ℕ => List.range (p.1.1.1 + 1)) encIn (encList encUnary) :=
    range.comp (unary_add.comp ((((fst enc3 encNat).fst').fst').prod (const 1)))
  have hfilter : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × ℕ => (List.range (p.1.1.1 + 1)).filter fun w =>
        !(decide (p.1.2 ≤ w) && decide (w < p.1.2 + p.2))) encIn (encList encUnary) := by
    refine filterWithInput hlist ?_
    have hw_b := uToB.comp (snd encIn encUnary)
    have hA := ((fst encIn encUnary).fst').snd'; have hR := (fst encIn encUnary).snd'
    exact bool_not.comp (bool_and' (bLe hA hw_b) (binary_lt' hw_b (bAdd hA hR)))
  refine bSum.comp (mapWithInput (f := fun p w => binomTailTerm p.1.1.1 p.1.1.2 w) hfilter ?_)
  have hp := fst encIn encUnary
  exact computableInPolyTime_binomTailTerm.comp
    ((((((hp.fst').fst').fst').prod (((hp.fst').fst').snd')).prod (snd encIn encUnary)))

/-- `binomTailNumerator` is also polynomial-time when both `(Q, r)` are given in `encUnary`. -/
theorem computableInPolyTime_binomTailNumerator_unary :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × ℕ => binomTailNumerator p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary encUnary) encNat) encNat) encNat := by
  let enc3 := encPair (encPair encUnary encUnary) encNat
  have hp3 := fst enc3 encNat
  exact computableInPolyTime_binomTailNumerator.comp
    (((((hp3.fst').fst').prod (uToB.comp ((hp3.fst').snd'))).prod hp3.snd').prod
      (snd enc3 encNat))

@[fun_prop] theorem computableInPolyTime_binomTailNumerator_apply {α : Type}
    {encIn : α ↪ List Bool} {fQ fr fA fR : α → ℕ} (hQ : ComputableInPolyTime fQ encIn encUnary)
    (hr : ComputableInPolyTime fr encIn encNat) (hA : ComputableInPolyTime fA encIn encNat)
    (hR : ComputableInPolyTime fR encIn encNat) :
    ComputableInPolyTime (fun x => binomTailNumerator (fQ x) (fr x) (fA x) (fR x)) encIn encNat :=
  (computableInPolyTime_binomTailNumerator.comp (((hQ.prod hr).prod hA).prod hR)).of_enc_eq
    fun _ => rfl

/-- `checkBinomTail` is polynomial-time with `Q` in `encUnary` and `(r, A₀, R, b, lam)` in
`encNat`. -/
theorem computableInPolyTime_checkBinomTail :
    ComputableInPolyTime
      (fun p : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
        checkBinomTail p.1.1.1.1.1 p.1.1.1.1.2 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair (encPair (encPair encUnary encNat) encNat) encNat) encNat) encNat)
      encBool := by
  let enc4 := encPair (encPair (encPair encUnary encNat) encNat) encNat
  let enc5 := encPair enc4 encNat
  have hp5 := fst enc5 encNat; have hp4 := hp5.fst'
  have hQ := ((hp4.fst').fst').fst'; have hr := ((hp4.fst').fst').snd'
  have hb := hp5.snd'; have hlam := snd enc5 encNat
  have hnum := computableInPolyTime_binomTailNumerator.comp hp4
  have hlhs := binary_mul' (binary_mul' (binary_mul' hnum hb) (binary_pow' hr (const 2))) hlam
  have hrhs := binary_pow' (binary_mul' (const 2) hr) hQ
  exact bool_and'
    (bool_and' (bool_and' (bLe (const 1) hr) (bLe (const 1) hb)) (bLe (const 1) hlam))
    (bLe hlhs hrhs)

/-- `checkBinomTail` is also polynomial-time when both `(Q, r)` are given in `encUnary`. -/
theorem computableInPolyTime_checkBinomTail_unary :
    ComputableInPolyTime
      (fun p : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
        checkBinomTail p.1.1.1.1.1 p.1.1.1.1.2 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair (encPair (encPair encUnary encUnary) encNat) encNat) encNat)
        encNat) encBool := by
  let enc4 := encPair (encPair (encPair encUnary encUnary) encNat) encNat
  let enc5 := encPair enc4 encNat; have hp5 := fst enc5 encNat; have hp4 := hp5.fst'
  exact computableInPolyTime_checkBinomTail.comp
    ((((((((hp4.fst').fst').fst').prod (uToB.comp (((hp4.fst').fst').snd'))).prod
      ((hp4.fst').snd')).prod hp4.snd').prod hp5.snd').prod (snd enc5 encNat))

theorem computableInPolyTime_checkBinomTail_apply {α : Type} {encIn : α ↪ List Bool}
    {fQ fr fA fR fb flam : α → ℕ}
    (hQ : ComputableInPolyTime fQ encIn encUnary) (hr : ComputableInPolyTime fr encIn encNat)
    (hA : ComputableInPolyTime fA encIn encNat) (hR : ComputableInPolyTime fR encIn encNat)
    (hb : ComputableInPolyTime fb encIn encNat) (hlam : ComputableInPolyTime flam encIn encNat) :
    ComputableInPolyTime
      (fun x => checkBinomTail (fQ x) (fr x) (fA x) (fR x) (fb x) (flam x)) encIn encBool :=
  (computableInPolyTime_checkBinomTail.comp
    (((((hQ.prod hr).prod hA).prod hR).prod hb).prod hlam)).of_enc_eq fun _ => rfl

private abbrev FeasibleTuple := (((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ

private abbrev encFeasible8 : ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ ↪ List Bool :=
  encPair (encPair (encPair (encPair (encPair (encPair (encPair encNat encNat) encNat) encNat)
    encNat) encUnary) encNat) encNat

private abbrev encFeasibleTuple : FeasibleTuple ↪ List Bool := encPair encFeasible8 encNat

/-- `checkReplacementFeasible` is polynomial-time with `Q` in `encUnary` and
`(n, M, b, wmax, lam, r, A₀, R)` in `encNat`. -/
theorem computableInPolyTime_checkReplacementFeasible :
    ComputableInPolyTime
      (fun p : (((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
        checkReplacementFeasible p.1.1.1.1.1.1.1.1 p.1.1.1.1.1.1.1.2 p.1.1.1.1.1.1.2
          p.1.1.1.1.1.2 p.1.1.1.1.2 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair (encPair (encPair (encPair (encPair (encPair encNat encNat)
        encNat) encNat) encNat) encUnary) encNat) encNat) encNat) encBool := by
  have h8 := fst encFeasible8 encNat
  have h7 := h8.fst'; have h6 := h7.fst'; have h5 := h6.fst'
  have h4 := h5.fst'; have h3 := h4.fst'; have h2 := h3.fst'
  have hn := h2.fst'; have hM := h2.snd'; have hb := h3.snd'
  have hwmax := h4.snd'; have hlam := h5.snd'; have hQ := h6.snd'
  have hr := h7.snd'; have hA := h8.snd'; have hR := snd encFeasible8 encNat
  have hQb := uToB.comp hQ
  have hD2 := binary_pow' (binary_pow' hr (unary_mul.comp ((const 2).prod hQ))) (const 2)
  have hbalM := bLe (binary_mul' (binary_mul' (const 2) (bAdd hb hwmax)) hD2) hM
  have hbaln := bLe (binary_mul' (binary_mul' (const 2) hQb) (binary_pow' hr (const 2))) hn
  have htail := computableInPolyTime_checkBinomTail.comp
    (((((hQ.prod hr).prod hA).prod hR).prod hb).prod hlam)
  exact bool_and' (bool_and' (bool_and' (bool_and' (bool_and'
    (bool_and' (bLe (const 2) hr) (bLe (const 1) hR)) (binary_lt' hR hQb))
    (bLe (bAdd hA hR) (bAdd hQb (const 1)))) hbalM) hbaln) htail

/-- `checkReplacementFeasible` is also polynomial-time when both `(Q, r)` are given in
`encUnary`. -/
theorem computableInPolyTime_checkReplacementFeasible_unary :
    ComputableInPolyTime
      (fun p : (((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
        checkReplacementFeasible p.1.1.1.1.1.1.1.1 p.1.1.1.1.1.1.1.2 p.1.1.1.1.1.1.2
          p.1.1.1.1.1.2 p.1.1.1.1.2 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair (encPair (encPair (encPair (encPair (encPair encNat encNat)
        encNat) encNat) encNat) encUnary) encUnary) encNat) encNat) encBool := by
  let enc8 := encPair (encPair (encPair (encPair (encPair (encPair (encPair encNat encNat) encNat)
    encNat) encNat) encUnary) encUnary) encNat
  have h8 := fst enc8 encNat; have h7 := h8.fst'; have h6 := h7.fst'; have h5 := h6.fst'
  have h4 := h5.fst'; have h3 := h4.fst'; have h2 := h3.fst'
  exact computableInPolyTime_checkReplacementFeasible.comp
    ((((((((h2.fst'.prod h2.snd').prod h3.snd').prod h4.snd').prod h5.snd').prod h6.snd').prod
      (uToB.comp h7.snd')).prod h8.snd').prod (snd enc8 encNat))

theorem computableInPolyTime_checkReplacementFeasible_apply {α : Type} {encIn : α ↪ List Bool}
    {fn fM fb fwmax flam fQ fr fA fR : α → ℕ}
    (hn : ComputableInPolyTime fn encIn encNat) (hM : ComputableInPolyTime fM encIn encNat)
    (hb : ComputableInPolyTime fb encIn encNat) (hwmax : ComputableInPolyTime fwmax encIn encNat)
    (hlam : ComputableInPolyTime flam encIn encNat) (hQ : ComputableInPolyTime fQ encIn encUnary)
    (hr : ComputableInPolyTime fr encIn encNat) (hA : ComputableInPolyTime fA encIn encNat)
    (hR : ComputableInPolyTime fR encIn encNat) :
    ComputableInPolyTime (fun x => checkReplacementFeasible (fn x) (fM x) (fb x) (fwmax x) (flam x)
      (fQ x) (fr x) (fA x) (fR x)) encIn encBool :=
  (computableInPolyTime_checkReplacementFeasible.comp
    ((((((((hn.prod hM).prod hb).prod hwmax).prod hlam).prod hQ).prod hr).prod hA).prod
      hR)).of_enc_eq fun _ => rfl

private abbrev encScheduleOut : (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))

/-- Computing the full Section 4.7 schedule `(λ, ν, r, Q, R, A₀)` is polynomial-time over binary
pairs `(β, n)`. -/
theorem computableInPolyTime_computeScheduleParams :
    ComputableInPolyTime (fun p : ℕ × ℕ => computeScheduleParams p.1 p.2) (encPair encNat encNat)
      (encPair encNat (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))) :=
  let hn := snd encNat encNat
  (clog2_pt.comp hn).prod ((nu_pt.comp hn).prod
    ((computableInPolyTime_numGroups.comp hn).prod
      ((computableInPolyTime_numNodes.comp hn).prod
        (computableInPolyTime_rowBound.prod computableInPolyTime_intervalStart))))

theorem computableInPolyTime_computeScheduleParams_apply {α : Type} {encIn : α ↪ List Bool}
    {fβ fn : α → ℕ} (hβ : ComputableInPolyTime fβ encIn encNat)
    (hn : ComputableInPolyTime fn encIn encNat) :
    ComputableInPolyTime (fun x => computeScheduleParams (fβ x) (fn x)) encIn
      (encPair encNat (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))) :=
  (computableInPolyTime_computeScheduleParams.comp (hβ.prod hn)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_checkScheduleFeasible_binary :
    ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ =>
        checkScheduleFeasible p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair (encPair encNat encNat) encNat) encNat) encNat) encBool := by
  let enc4 := encPair (encPair (encPair encNat encNat) encNat) encNat
  have h4 := fst enc4 encNat; have h3 := h4.fst'; have h2 := h3.fst'
  have hn := h2.fst'; have hM := h2.snd'; have hb := h3.snd'
  have hwmax := h4.snd'; have hβ := snd enc4 encNat
  have hlam := clog2_pt.comp hn; have hr := computableInPolyTime_numGroups.comp hn
  have hQu := computableInPolyTime_numNodes_unary.comp hn
  have hQb := computableInPolyTime_numNodes.comp hn
  have hR := computableInPolyTime_rowBound.comp (hβ.prod hn)
  have hA := computableInPolyTime_intervalStart.comp (hβ.prod hn)
  have hfeas := computableInPolyTime_checkReplacementFeasible.comp
    ((((((((hn.prod hM).prod hb).prod hwmax).prod hlam).prod hQu).prod hr).prod hA).prod hR)
  exact bool_and' (bool_and' (bool_and' (bLe (const 20) hn) (bLe (const 32) hR))
    (bLe (binary_mul' (const 6) hR) hQb)) hfeas

theorem computableInPolyTime_checkScheduleFeasible_apply {α : Type} {encIn : α ↪ List Bool}
    {fn fM fb fwmax fβ : α → ℕ} (hn : ComputableInPolyTime fn encIn encNat)
    (hM : ComputableInPolyTime fM encIn encNat) (hb : ComputableInPolyTime fb encIn encNat)
    (hwmax : ComputableInPolyTime fwmax encIn encNat) (hβ : ComputableInPolyTime fβ encIn encNat) :
    ComputableInPolyTime
      (fun x => checkScheduleFeasible (fn x) (fM x) (fb x) (fwmax x) (fβ x)) encIn encBool :=
  (computableInPolyTime_checkScheduleFeasible_binary.comp
    ((((hn.prod hM).prod hb).prod hwmax).prod hβ)).of_enc_eq fun _ => rfl

/-- **Binary-`n` full-schedule and feasibility certificate (Lemma 4.8, p. 34)**: given
`(n, M, b, wmax, β)` all in binary (`encNat`), computing `(λ, ν, r, Q, R, A₀)` and deciding
`checkScheduleFeasible` runs in polynomial time in
`|encNat n| + |encNat M| + |encNat b| + |encNat wmax| + |encNat β|`. -/
theorem computableInPolyTime_scheduleAndCheck_binary :
    ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ =>
        (computeScheduleParams p.2 p.1.1.1.1,
          checkScheduleFeasible p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2))
      (encPair (encPair (encPair (encPair encNat encNat) encNat) encNat) encNat)
      (encPair
        (encPair encNat (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat)))))
        encBool) := by
  let enc4 := encPair (encPair (encPair encNat encNat) encNat) encNat
  exact (computableInPolyTime_computeScheduleParams.comp
    ((snd enc4 encNat).prod ((((fst enc4 encNat).fst').fst').fst'))).prod
    computableInPolyTime_checkScheduleFeasible_binary

/-- **Composed unary-`n` full-schedule and feasibility certificate (§5.5 / Theorem 2.2)**: given
`(n_unary, M, b, wmax, β)` with `n_unary` in `encUnary` and `(M, b, wmax, β)` in `encNat`,
computing `(λ, ν, r, Q, R, A₀)` and running both `checkReplacementFeasible` and
`checkScheduleFeasible` is polynomial-time. -/
theorem computableInPolyTime_scheduleAndCheck_unary :
    ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ =>
        let s := computeScheduleParams p.2 p.1.1.1.1
        (s,
          checkReplacementFeasible p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 s.1 s.2.2.2.1 s.2.2.1
            s.2.2.2.2.2 s.2.2.2.2.1,
          checkScheduleFeasible p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2))
      (encPair (encPair (encPair (encPair encUnary encNat) encNat) encNat) encNat)
      (encPair
        (encPair encNat (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat)))))
        (encPair encBool encBool)) := by
  let enc4 := encPair (encPair (encPair encUnary encNat) encNat) encNat
  have h4 := fst enc4 encNat; have h3 := h4.fst'; have h2 := h3.fst'
  have hn := uToB.comp h2.fst'; have hM := h2.snd'; have hb := h3.snd'
  have hwmax := h4.snd'; have hβ := snd enc4 encNat
  have hsched := computableInPolyTime_computeScheduleParams.comp (hβ.prod hn)
  have hlam := clog2_pt.comp hn; have hr := computableInPolyTime_numGroups.comp hn
  have hQu := computableInPolyTime_numNodes_unary.comp hn
  have hQb := computableInPolyTime_numNodes.comp hn
  have hR := computableInPolyTime_rowBound.comp (hβ.prod hn)
  have hA := computableInPolyTime_intervalStart.comp (hβ.prod hn)
  have hrep := computableInPolyTime_checkReplacementFeasible.comp
    ((((((((hn.prod hM).prod hb).prod hwmax).prod hlam).prod hQu).prod hr).prod hA).prod hR)
  have hchk := computableInPolyTime_checkScheduleFeasible_binary.comp
    ((((hn.prod hM).prod hb).prod hwmax).prod hβ)
  exact hsched.prod (hrep.prod hchk)

end PolyTime

end Cslib.Complexity.SubexponentialSAT.ParameterCheck
