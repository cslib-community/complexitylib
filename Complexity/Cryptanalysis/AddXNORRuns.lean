/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNOR
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Fixed-operator Add/XNOR correlations

[WangLvShenZhang2027], Theorem 3 (PDF pp. 15–16). Unlike the operator-averaged
formula, `fixedFrom` fixes every operator and averages only independent uniform
full-width operands. `runs` encodes addition runs separated by XNORs, allowing
zero-length runs for leading, trailing or consecutive XNORs. The run factor is
the real part of ((1+i)/2)^z, the algebraic form of 2^(-z/2) cos(z*pi/4).
The signed correlation factors over all runs, without assuming an independence
claim as a hypothesis. No hardness or adversarial search theorem follows.
-/

public section

open scoped BigOperators

namespace Cslib.Cryptanalysis.AddXNOR

variable {h : ℕ}

/-- Exact signed expectation with a fixed operator list and fresh uniform words. -/
@[expose] def fixedFrom (h : ℕ) : List Bool → BitVec (h + 2) → Bool → ℚ
  | [], s, ell => sign (s.getLsbD 1 ^^ ell)
  | b :: bs, s, ell =>
    𝔼 hi : Fin (2 ^ h), 𝔼 lo : Fin 4,
      fixedFrom h bs (step b s (word hi lo)) (ell ^^ (word hi lo).getLsbD 1 ^^ b)

/-- Correlation averaged over all operands, with operators held fixed. -/
@[expose] def fixedCorrelation (h : ℕ) (bs : List Bool) : ℚ :=
  𝔼 hi : Fin (2 ^ h), 𝔼 lo : Fin 4,
    fixedFrom h bs (word hi lo) ((word hi lo).getLsbD 1)

private def transfer (b : Bool) (p : ℚ × ℚ) : ℚ × ℚ :=
  if b then ((p.1 + p.2) / 2, (p.1 + p.2) / 2)
  else ((p.1 + p.2) / 2, (p.2 - p.1) / 2)

private def coefficients : List Bool → ℚ × ℚ
  | [] => (1, 1)
  | b :: bs => transfer b (coefficients bs)

private def statistic (p : ℚ × ℚ) (s : BitVec 2) (ell : Bool) : ℚ :=
  sign (s.getLsbD 1 ^^ ell) * (if s.getLsbD 0 then p.2 else p.1)

private theorem statistic_step (b : Bool) (p : ℚ × ℚ) (s : BitVec 2) (ell : Bool) :
    (𝔼 lo : Fin 4, statistic p (step b s (BitVec.ofNat 2 lo.val))
      (ell ^^ (BitVec.ofNat 2 lo.val).getLsbD 1 ^^ b)) =
      statistic (transfer b p) s ell := by
  rcases s with ⟨s⟩
  fin_cases s <;> cases ell <;> cases b <;>
    norm_num [Finset.expect_eq_sum_div_card, Fin.sum_univ_succ, statistic, transfer,
      step, sign, BitVec.getLsbD, BitVec.add_def, BitVec.not_def, Nat.testBit] <;> ring

private theorem fixedFrom_coefficients (h : ℕ) (bs : List Bool)
    (s : BitVec (h + 2)) (ell : Bool) :
    fixedFrom h bs s ell = statistic (coefficients bs) (s.setWidth 2) ell := by
  induction bs generalizing s ell with
  | nil => simp [fixedFrom, statistic, coefficients]
  | cons b bs ih =>
    have low (a : BitVec (h + 2)) : (a.setWidth 2).getLsbD 1 = a.getLsbD 1 := by simp
    simp only [fixedFrom, ih, step_low, word_low, ← low (word _ _), word_low]
    simp only [statistic_step, coefficients]
    exact Finset.expect_const Finset.univ_nonempty _

private theorem fixedCorrelation_coefficients (h : ℕ) (bs : List Bool) :
    fixedCorrelation h bs = ((coefficients bs).1 + (coefficients bs).2) / 2 := by
  unfold fixedCorrelation
  have low (a : BitVec (h + 2)) : (a.setWidth 2).getLsbD 1 = a.getLsbD 1 := by simp
  simp only [fixedFrom_coefficients, word_low, ← low (word _ _), word_low]
  have inner : (𝔼 lo : Fin 4, statistic (coefficients bs) (BitVec.ofNat 2 lo.val)
      ((BitVec.ofNat 2 lo.val).getLsbD 1)) =
      ((coefficients bs).1 + (coefficients bs).2) / 2 := by
    norm_num [Finset.expect_eq_sum_div_card, Fin.sum_univ_succ, statistic, sign,
      BitVec.getLsbD, Nat.testBit]
    ring
  simp only [inner]
  exact Finset.expect_const Finset.univ_nonempty _

/-- Addition runs separated by one XNOR, including a final XNOR.
The final XNOR does not change signed correlation; zero runs encode any extra separators. -/
@[expose] def runs : List ℕ → List Bool
  | [] => []
  | z :: zs => List.replicate z false ++ true :: runs zs

/-- Algebraic run factor, equal to the paper's damped cosine. -/
@[expose] def runFactor (z : ℕ) : ℚ :=
  let p := Nat.iterate (fun p : ℚ × ℚ => ((p.1 + p.2) / 2, (p.2 - p.1) / 2)) z (1, 1)
  (p.1 + p.2) / 2

private theorem coefficients_append (xs ys : List Bool) :
    coefficients (xs ++ ys) = xs.foldr transfer (coefficients ys) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append, coefficients, ih, List.foldr_cons]

private theorem transfer_scale (b : Bool) (c : ℚ) (p : ℚ × ℚ) :
    transfer b (c * p.1, c * p.2) =
      (c * (transfer b p).1, c * (transfer b p).2) := by
  cases b <;> ext <;> simp [transfer] <;> ring

private theorem repeat_scale (z : ℕ) (c : ℚ) (p : ℚ × ℚ) :
    Nat.iterate (transfer false) z (c * p.1, c * p.2) =
      (c * (Nat.iterate (transfer false) z p).1,
       c * (Nat.iterate (transfer false) z p).2) := by
  induction z with
  | zero => rfl
  | succ z ih =>
    simp only [Function.iterate_succ_apply', ih, transfer_scale]

private theorem replicate_fold (z : ℕ) (p : ℚ × ℚ) :
    (List.replicate z false).foldr transfer p = Nat.iterate (transfer false) z p := by
  induction z with
  | zero => rfl
  | succ z ih => simp only [List.replicate_succ, List.foldr_cons, ih,
      Function.iterate_succ_apply']

/-- The fixed-operator signed correlation factors over arbitrary addition runs.
There is no restriction on the number or lengths of runs or on the high bits. -/
theorem fixedCorrelation_runs (h : ℕ) (zs : List ℕ) :
    fixedCorrelation h (runs zs) = (zs.map runFactor).prod := by
  rw [fixedCorrelation_coefficients]
  induction zs with
  | nil => norm_num [runs, coefficients]
  | cons z zs ih =>
    simp only [runs, coefficients_append, coefficients, replicate_fold]
    let c := ((coefficients (runs zs)).1 + (coefficients (runs zs)).2) / 2
    have hs := repeat_scale z c (1, 1)
    simp only [mul_one] at hs
    change ((Nat.iterate (transfer false) z (c, c)).1 +
      (Nat.iterate (transfer false) z (c, c)).2) / 2 = _
    rw [hs]
    change (c * (Nat.iterate (transfer false) z (1, 1)).1 +
      c * (Nat.iterate (transfer false) z (1, 1)).2) / 2 = _
    change c = _ at ih
    rw [ih]
    simp only [List.map_cons, List.prod_cons, runFactor]
    change _ = (((Nat.iterate (transfer false) z (1, 1)).1 +
      (Nat.iterate (transfer false) z (1, 1)).2) / 2) * _
    ring

/-- Appending an XNOR with a fresh uniform operand preserves correlation. -/
theorem fixedCorrelation_append_xnor (h : ℕ) (bs : List Bool) :
    fixedCorrelation h (bs ++ [true]) = fixedCorrelation h bs := by
  have hc : coefficients [true] = coefficients [] := by norm_num [coefficients, transfer]
  simp only [fixedCorrelation_coefficients, coefficients_append, hc]
  rw [← coefficients_append, List.append_nil]

/-- Every operator string is represented by addition runs, up to an irrelevant
final XNOR. Zero-length runs account for adjacent or endpoint XNORs. -/
theorem exists_runs (bs : List Bool) : ∃ zs, runs zs = bs ++ [true] := by
  induction bs with
  | nil => exact ⟨[0], rfl⟩
  | cons b bs ih =>
    rcases ih with ⟨zs, hz⟩
    cases b with
    | true => exact ⟨0 :: zs, by simpa only [runs, List.replicate_zero,
        List.nil_append, List.cons_append] using congrArg (List.cons true) hz⟩
    | false =>
      cases zs with
      | nil => simp [runs] at hz
      | cons z zs =>
        refine ⟨(z + 1) :: zs, ?_⟩
        simpa only [runs, List.replicate_succ, List.cons_append] using
          congrArg (List.cons false) hz

/-- The run-product formula applies to every fixed operator string. -/
theorem fixedCorrelation_run_product (h : ℕ) (bs : List Bool) :
    ∃ zs, runs zs = bs ++ [true] ∧
      fixedCorrelation h bs = (zs.map runFactor).prod := by
  obtain ⟨zs, hz⟩ := exists_runs bs
  refine ⟨zs, hz, ?_⟩
  rw [← fixedCorrelation_append_xnor, ← hz, fixedCorrelation_runs]

private theorem run_complex (z : ℕ) :
    let p := Nat.iterate (transfer false) z (1, 1)
    (⟨((p.1 + p.2) / 2 : ℚ), ((p.1 - p.2) / 2 : ℚ)⟩ : ℂ) =
      (⟨1 / 2, 1 / 2⟩ : ℂ) ^ z := by
  induction z with
  | zero => apply Complex.ext <;> norm_num
  | succ z ih =>
    rw [pow_succ, ← ih]
    simp only [Function.iterate_succ_apply']
    apply Complex.ext <;> norm_num [transfer, Complex.mul_re, Complex.mul_im] <;> ring

/-- Exact closed form of each run factor as a complex power. This is the
algebraic damped-cosine formula, without numerical trigonometric evaluation. -/
theorem runFactor_complex (z : ℕ) :
    (runFactor z : ℝ) = ((⟨1 / 2, 1 / 2⟩ : ℂ) ^ z).re := by
  have h := congrArg Complex.re (run_complex z)
  exact h

/-- The source's closed form, written with an integer power of 1/sqrt(2).
This is exactly 2^(-z/2) cos(z*pi/4). -/
theorem runFactor_cos (z : ℕ) :
    (runFactor z : ℝ) = (1 / Real.sqrt 2) ^ z * Real.cos (z * (Real.pi / 4)) := by
  have trig (t : ℝ) :
      Complex.cos (t : ℂ) + Complex.sin (t : ℂ) * Complex.I =
        (⟨Real.cos t, Real.sin t⟩ : ℂ) := by
    apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have base : (⟨1 / 2, 1 / 2⟩ : ℂ) =
      (1 / Real.sqrt 2 : ℂ) *
        (Complex.cos (Real.pi / 4 : ℝ) + Complex.sin (Real.pi / 4 : ℝ) * Complex.I) := by
    rw [trig]
    apply Complex.ext <;> simp [Real.cos_pi_div_four, Real.sin_pi_div_four] <;>
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [runFactor_complex, base, mul_pow, Complex.cos_add_sin_mul_I_pow]
  norm_cast
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero, add_zero]

/-- The single-run decay bound from Theorem 3. -/
theorem abs_runFactor_le (z : ℕ) :
    |(runFactor z : ℝ)| ≤ (1 / Real.sqrt 2) ^ z := by
  rw [runFactor_cos, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

/-- A run of zero additions contributes no correlation loss. -/
theorem runFactor_zero : runFactor 0 = 1 := by norm_num [runFactor]

/-- Theorem 3's full fixed-operator formula, with explicit cosine factors.
Zero runs may be removed using `runFactor_zero`; they account only for separators. -/
theorem fixedCorrelation_runs_cos (h : ℕ) (zs : List ℕ) :
    (fixedCorrelation h (runs zs) : ℝ) =
      (zs.map fun z : ℕ => (1 / Real.sqrt 2) ^ z * Real.cos (z * (Real.pi / 4))).prod := by
  rw [fixedCorrelation_runs]
  push_cast
  rw [List.map_map]
  simp only [Function.comp_def, runFactor_cos]

/-- The number of actual additions is the sum of the run lengths. -/
theorem runs_addition_count (zs : List ℕ) : (runs zs).count false = zs.sum := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp [runs, ih]

/-- The full correlation decays by at least half a bit per actual addition. -/
theorem abs_fixedCorrelation_runs_le (h : ℕ) (zs : List ℕ) :
    |(fixedCorrelation h (runs zs) : ℝ)| ≤ (1 / Real.sqrt 2) ^ zs.sum := by
  rw [fixedCorrelation_runs]
  induction zs with
  | nil => norm_num
  | cons z zs ih =>
    simp only [List.map_cons, List.prod_cons, Rat.cast_mul, abs_mul, List.sum_cons, pow_add]
    exact mul_le_mul (abs_runFactor_le z) ih (abs_nonneg _) (by positivity)

/-- Each four extra additions multiply the signed factor by -1/4. -/
theorem runFactor_add_four (z : ℕ) : runFactor (z + 4) = -runFactor z / 4 := by
  have hp : (⟨1 / 2, 1 / 2⟩ : ℂ) ^ 4 = (-1 / 4 : ℂ) := by
    apply Complex.ext <;> norm_num [pow_succ, Complex.mul_re, Complex.mul_im]
  have hr : (runFactor (z + 4) : ℝ) = -(runFactor z : ℝ) / 4 := by
    rw [runFactor_complex, pow_add, hp, runFactor_complex]
    simp [Complex.mul_re]
    ring
  exact_mod_cast hr

private theorem runFactor_blocks (t r : ℕ) :
    runFactor (4 * t + r) = (-1 / 4 : ℚ) ^ t * runFactor r := by
  induction t with
  | zero => simp
  | succ t ih =>
    have he : 4 * (t + 1) + r = (4 * t + r) + 4 := by omega
    rw [he, runFactor_add_four, ih, pow_succ]
    ring

/-- Exactly the runs of length 2 modulo 4 have zero signed correlation. -/
theorem runFactor_eq_zero_iff (z : ℕ) : runFactor z = 0 ↔ z % 4 = 2 := by
  have he : z = 4 * (z / 4) + z % 4 := by omega
  conv_lhs => rw [he, runFactor_blocks]
  rw [mul_eq_zero, or_iff_right (pow_ne_zero _ (by norm_num : (-1 / 4 : ℚ) ≠ 0))]
  have hm : z % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases z % 4 <;> norm_num [runFactor, Function.iterate_succ_apply']

end Cslib.Cryptanalysis.AddXNOR
