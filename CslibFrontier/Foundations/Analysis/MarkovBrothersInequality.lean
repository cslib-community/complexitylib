/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/`)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Compact

/-!
# The Markov brothers' inequality

A real polynomial `p` of degree at most `n` with `|p| ≤ M` on `[-1, 1]` has `|p'| ≤ n² M` on
`[-1, 1]` (`Polynomial.abs_eval_derivative_le_sq_mul`), the inequality of A. A. Markov
([BorweinErdelyi1995], [Rivlin1990]). The proof combines two classical inequalities.

* **Schur's inequality**: a polynomial `q` of degree less than `n ≥ 1` with
  `√(1 - x²) |q(x)| ≤ M` on `[-1, 1]` has `|q| ≤ n M` there
  (`Polynomial.abs_eval_le_mul_of_sqrt_mul_abs_eval_le`). Where `√(1 - x²) ≥ sin (π / 2n) ≥ 1 / n`
  this is immediate. Beyond the largest zero `cos (π / 2n)` of the Chebyshev polynomial `T n`,
  interpolate `q` at the `n` zeros `ηₖ` of `T n`. There every Lagrange basis polynomial is
  `T n(x) / ((x - ηₖ) T n'(ηₖ))` with `T n(x) / (x - ηₖ) ≥ 0`, the identity
  `|T n'(ηₖ)| √(1 - ηₖ²) = n` turns the bound on `√(1 - ηₖ²) |q(ηₖ)|` into a bound on each term,
  and the terms add up to `M T n'(x) / n ≤ M T n'(1) / n = n M`.
* **Bernstein's inequality**: `√(1 - x²) |p'(x)| ≤ n M` on `[-1, 1]`
  (`Polynomial.sqrt_mul_abs_eval_derivative_le`). For `a ∈ [-1, 1]` and `b = √(1 - a²)`, the
  odd part `(p(ac + bs) - p(ac - bs)) / 2` of `p` along the circle `c² + s² = 1` is `s r(c)` for a
  polynomial `r` of degree less than `n` with `r(1) = b p'(a)`, read off the Taylor expansion of
  `p` at `ac`. Since `|ac ± bs| ≤ 1`, Schur's inequality at `1` bounds `r(1)`.

Schur's inequality applied to `p'` with Bernstein's bound gives Markov's.

Rescaled to an interval `[a, b]`, Markov's inequality reads `(b - a) |p'| ≤ 2 n² M`
(`Polynomial.sub_mul_abs_eval_derivative_le`). A polynomial of degree at most `d` whose values at
the integers `0, …, N` lie in `[b₁, b₂]` therefore has `(N - d²) |q'| ≤ d² (b₂ - b₁)` on `[0, N]`
(`Polynomial.sub_mul_abs_eval_derivative_le_of_forall_nat`): every point of `[0, N]` is within
`1/2` of an integer, so the largest value `c` of `|q'|` on `[0, N]` keeps `q` within `c / 2` of
`[b₁, b₂]`, and Markov's inequality gives `N c ≤ d² (b₂ - b₁ + c)`. The same argument bounds `q`
itself, `(N - d²) |q| ≤ N max |q(k)|` (`Polynomial.sub_mul_abs_eval_le_of_forall_nat`), the
bound of Ehlich and Zeller [EhlichZeller1964] (see also [CoppersmithRivlin1992]), and gives the
lemma behind the degree bounds of Nisan and Szegedy [NisanSzegedy1994]
(`Polynomial.mul_le_sq_mul_of_le_abs_eval_derivative`).

## Main results

* `Polynomial.abs_eval_le_mul_of_sqrt_mul_abs_eval_le`: Schur's inequality.
* `Polynomial.sqrt_mul_abs_eval_derivative_le`: Bernstein's inequality.
* `Polynomial.abs_eval_derivative_le_sq_mul`: **the Markov brothers' inequality**, `|p'| ≤ n² M`.
* `Polynomial.sub_mul_abs_eval_derivative_le`: Markov's inequality on an interval `[a, b]`.
* `Polynomial.sub_mul_abs_eval_derivative_le_of_forall_nat`,
  `Polynomial.sub_mul_abs_eval_le_of_forall_nat`: polynomials bounded at the integers of `[0, N]`.
* `Polynomial.mul_le_sq_mul_of_le_abs_eval_derivative`: the Nisan–Szegedy lemma: if moreover
  `|q'(ξ)| ≥ c ≥ 0` at some `ξ ∈ [0, N]`, then `c N ≤ d² (c + b₂ - b₁)`.

## References

* [P. Borwein, T. Erdélyi, *Polynomials and Polynomial Inequalities*][BorweinErdelyi1995]
* [T. J. Rivlin, *Chebyshev Polynomials*][Rivlin1990]
* [H. Ehlich, K. Zeller, *Schwankung von Polynomen zwischen Gitterpunkten*][EhlichZeller1964]
* [D. Coppersmith, T. J. Rivlin, *The growth of polynomials bounded at equally spaced
  points*][CoppersmithRivlin1992]
* [N. Nisan, M. Szegedy, *On the degree of Boolean functions as real polynomials*][NisanSzegedy1994]
-/

@[expose] public section

open Finset Real
open Set (Icc)

namespace Polynomial

/-! ### Schur's inequality -/

/-- The zeros `cos ((2k + 1) π / 2n)`, `k < n`, of the Chebyshev polynomial `T n`. -/
private noncomputable def chebyshevZero (n k : ℕ) : ℝ := cos ((2 * k + 1) * π / (2 * n))

private theorem injOn_chebyshevZero (n : ℕ) : Set.InjOn (chebyshevZero n) (range n) :=
  Finset.nodup_map_iff_injOn.1 (Chebyshev.roots_T_real_nodup n)

/-- The angle of a zero of `T n` lies in `[π / 2n, π]`. -/
private theorem angle_mem {n k : ℕ} (hk : k < n) :
    π / (2 * n) ≤ (2 * k + 1) * π / (2 * n) ∧ (2 * k + 1) * π / (2 * n) ≤ π := by
  have hn : (0 : ℝ) < 2 * n := by
    have : 0 < n := by omega
    positivity
  have hk' : (2 * k + 1 : ℝ) ≤ 2 * n := by exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * n)
  constructor
  · rw [div_le_div_iff_of_pos_right hn]
    nlinarith [pi_pos]
  · rw [div_le_iff₀ hn]
    nlinarith [pi_pos]

/-- `T n = 2ⁿ⁻¹ ∏ₖ (X - ηₖ)` over the zeros `ηₖ` of `T n`. -/
private theorem T_eq_C_mul_nodal (n : ℕ) :
    Chebyshev.T ℝ n = C (2 ^ (n - 1)) * Lagrange.nodal (range n) (chebyshevZero n) := by
  have hroots : (Chebyshev.T ℝ n).roots = ((range n).image (chebyshevZero n)).val :=
    Chebyshev.roots_T_real n
  have hcard : Multiset.card (Chebyshev.T ℝ n).roots = (Chebyshev.T ℝ n).natDegree := by
    rw [hroots, Chebyshev.natDegree_T, Finset.card_val,
      Finset.card_image_of_injOn (injOn_chebyshevZero n), card_range, Int.natAbs_natCast]
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
  rw [Chebyshev.leadingCoeff_T, Int.natAbs_natCast, hroots, ← Finset.prod_eq_multiset_prod,
    Finset.prod_image (injOn_chebyshevZero n), Lagrange.nodal]

/-- At a zero `η` of `T n`, `|T n'(η)| √(1 - η²) = n`. -/
private theorem abs_eval_derivative_T_mul_sqrt {n k : ℕ} (hk : k < n) :
    |(derivative (Chebyshev.T ℝ n)).eval (chebyshevZero n k)| *
      √(1 - chebyshevZero n k ^ 2) = n := by
  obtain ⟨h₁, h₂⟩ := angle_mem hk
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  set θ := (2 * k + 1) * π / (2 * n) with hθ
  have hθ0 : 0 ≤ θ := (by positivity : 0 ≤ π / (2 * n)).trans h₁
  rw [chebyshevZero, ← hθ, ← sin_eq_sqrt_one_sub_cos_sq hθ0 h₂, ← abs_of_nonneg
    (sin_nonneg_of_nonneg_of_le_pi hθ0 h₂), ← abs_mul, Chebyshev.T_derivative_eq_U, eval_mul,
    mul_assoc, Chebyshev.U_real_cos]
  have hnθ : ((((n : ℤ) - 1 : ℤ) : ℝ) + 1) * θ = k * π + π / 2 := by
    rw [hθ]
    push_cast
    field_simp
    ring
  rw [hnθ, sin_add_pi_div_two, cos_nat_mul_pi, eval_intCast, Int.cast_natCast, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, mul_one, Nat.abs_cast]

/-- Schur's inequality beyond the largest zero `cos (π / 2n)` of `T n`, by Lagrange interpolation at
the zeros of `T n`. -/
private theorem abs_eval_le_mul_of_cos_le {n : ℕ} (hn : 0 < n) {q : ℝ[X]} (hq : q.natDegree < n)
    {M : ℝ} (hM : ∀ y ∈ Icc (-1 : ℝ) 1, √(1 - y ^ 2) * |q.eval y| ≤ M) {x : ℝ}
    (hx₁ : cos (π / (2 * n)) ≤ x) (hx₂ : x ≤ 1) : |q.eval x| ≤ n * M := by
  classical
  set s := range n
  set v := chebyshevZero n
  set c : ℝ := 2 ^ (n - 1)
  have hc : 0 < c := by positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hM0 : 0 ≤ M := (mul_nonneg (sqrt_nonneg _) (abs_nonneg _)).trans (hM 0 (by simp))
  have hinj := injOn_chebyshevZero n
  -- every node lies at or below `x`
  have hvx (j : ℕ) (hj : j ∈ s) : v j ≤ x := by
    obtain ⟨h₁, h₂⟩ := angle_mem (mem_range.1 hj)
    exact (cos_le_cos_of_nonneg_of_le_pi (by positivity) h₂ h₁).trans hx₁
  have hv (j : ℕ) (hj : j ∈ s) : v j ∈ Icc (-1 : ℝ) 1 := ⟨neg_one_le_cos _, cos_le_one _⟩
  -- the derivative of `T n` is `c` times that of the node polynomial
  have hT' (y : ℝ) : (derivative (Chebyshev.T ℝ n)).eval y =
      c * (derivative (Lagrange.nodal s v)).eval y := by
    rw [T_eq_C_mul_nodal, derivative_C_mul, eval_mul, eval_C]
  -- interpolation at the zeros of `T n`
  have hdeg : q.degree < #s := by
    rw [card_range]
    exact (degree_le_natDegree).trans_lt (by exact_mod_cast hq)
  have heval : q.eval x = ∑ k ∈ s, q.eval (v k) *
      ((∏ j ∈ s.erase k, (x - v j)) / ∏ j ∈ s.erase k, (v k - v j)) := by
    conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
    rw [Lagrange.interpolate_apply, eval_finsetSum]
    refine sum_congr rfl fun k _ => ?_
    rw [eval_mul, eval_C, Lagrange.basis, eval_prod, ← prod_div_distrib]
    congr 1
    refine prod_congr rfl fun j _ => ?_
    rw [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C, div_eq_inv_mul]
  -- the weight of each node
  have hweight (k : ℕ) (hk : k ∈ s) :
      n * |q.eval (v k)| ≤ c * M * |∏ j ∈ s.erase k, (v k - v j)| := by
    have hd : (derivative (Lagrange.nodal s v)).eval (v k) = ∏ j ∈ s.erase k, (v k - v j) := by
      rw [Lagrange.eval_nodal_derivative_eval_node_eq hk, Lagrange.eval_nodal]
    have h := abs_eval_derivative_T_mul_sqrt (mem_range.1 hk)
    rw [hT', hd] at h
    calc (n : ℝ) * |q.eval (v k)|
        = |c * ∏ j ∈ s.erase k, (v k - v j)| * (√(1 - v k ^ 2) * |q.eval (v k)|) := by
          rw [← h]; ring
      _ ≤ |c * ∏ j ∈ s.erase k, (v k - v j)| * M := by gcongr; exact hM _ (hv k hk)
      _ = c * M * |∏ j ∈ s.erase k, (v k - v j)| := by rw [abs_mul, abs_of_pos hc]; ring
  have hsum : ∑ k ∈ s, ∏ j ∈ s.erase k, (x - v j) = (derivative (Lagrange.nodal s v)).eval x := by
    rw [Lagrange.derivative_nodal, eval_finsetSum]
    exact sum_congr rfl fun k _ => Lagrange.eval_nodal.symm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcos : 0 ≤ cos (π / (2 * n)) :=
    cos_nonneg_of_mem_Icc ⟨by linarith [(by positivity : 0 ≤ π / (2 * n)), pi_pos],
      div_le_div_of_nonneg_left pi_pos.le two_pos (by linarith)⟩
  have hx : |x| ≤ 1 := abs_le.2 ⟨by linarith, hx₂⟩
  have hTx : (derivative (Chebyshev.T ℝ n)).eval x ≤ n ^ 2 := by
    have h := Chebyshev.abs_iterate_derivative_T_real_le n 1 hx
    simp only [Function.iterate_one, Chebyshev.derivative_T_eval_one] at h
    exact_mod_cast (le_abs_self _).trans h
  calc |q.eval x|
      ≤ ∑ k ∈ s, |q.eval (v k) *
          ((∏ j ∈ s.erase k, (x - v j)) / ∏ j ∈ s.erase k, (v k - v j))| := by
        rw [heval]; exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ s, c * M / n * ∏ j ∈ s.erase k, (x - v j) := by
        refine sum_le_sum fun k hk => ?_
        have hw : 0 ≤ ∏ j ∈ s.erase k, (x - v j) :=
          prod_nonneg fun j hj => sub_nonneg.2 (hvx j (mem_of_mem_erase hj))
        have hd : ∏ j ∈ s.erase k, (v k - v j) ≠ 0 := prod_ne_zero_iff.2 fun j hj =>
          sub_ne_zero.2 fun h => (mem_erase.1 hj).1 (hinj (mem_of_mem_erase hj) hk h.symm)
        have h := mul_le_mul_of_nonneg_right (hweight k hk) hw
        rw [abs_mul, abs_div, abs_of_nonneg hw, mul_div_assoc', div_le_iff₀ (abs_pos.2 hd),
          div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hnR]
        linarith
    _ = M / n * (derivative (Chebyshev.T ℝ n)).eval x := by
        rw [← mul_sum, hsum, hT']; ring
    _ ≤ M / n * n ^ 2 := by gcongr
    _ = n * M := by field_simp

/-- **Schur's inequality**: a real polynomial `q` of degree less than `n ≥ 1` with
`√(1 - x²) |q(x)| ≤ M` on `[-1, 1]` satisfies `|q(x)| ≤ n M` on `[-1, 1]`. -/
theorem abs_eval_le_mul_of_sqrt_mul_abs_eval_le {n : ℕ} (hn : 0 < n) {q : ℝ[X]}
    (hq : q.natDegree < n) {M : ℝ} (hM : ∀ y ∈ Icc (-1 : ℝ) 1, √(1 - y ^ 2) * |q.eval y| ≤ M)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : |q.eval x| ≤ n * M := by
  rcases le_or_gt (cos (π / (2 * n))) x with h | h
  · exact abs_eval_le_mul_of_cos_le hn hq hM h hx.2
  rcases le_or_gt x (-cos (π / (2 * n))) with h' | h'
  · -- reflect `q` to `q(-x)`
    have hq' : (q.comp (-X)).natDegree < n := by
      rwa [natDegree_comp, natDegree_neg, natDegree_X, mul_one]
    have := abs_eval_le_mul_of_cos_le hn hq' (M := M) (fun y hy => by
      simpa [eval_comp] using hM (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩)
      (x := -x) (by linarith) (by linarith [hx.1])
    simpa [eval_comp] using this
  · -- here `√(1 - x²) ≥ sin (π / 2n) ≥ 1 / n`
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsin : 1 / n ≤ sin (π / (2 * n)) := by
      have h := mul_le_sin (x := π / (2 * n)) (by positivity)
        (div_le_div_of_nonneg_left pi_pos.le two_pos (by linarith [(by exact_mod_cast hn :
          (1 : ℝ) ≤ n)]))
      calc 1 / (n : ℝ) = 2 / π * (π / (2 * n)) := by field_simp
        _ ≤ _ := h
    have hsq : x ^ 2 < cos (π / (2 * n)) ^ 2 := sq_lt_sq' (by linarith) h
    have h1 : 1 / n ≤ √(1 - x ^ 2) := by
      rw [show (1 : ℝ) / n = √((1 / n) ^ 2) from (sqrt_sq (by positivity)).symm]
      refine sqrt_le_sqrt ?_
      have := sin_sq_add_cos_sq (π / (2 * n))
      nlinarith [hsin, (by positivity : (0 : ℝ) ≤ 1 / n)]
    calc |q.eval x| = n * (1 / n * |q.eval x|) := by field_simp
      _ ≤ n * (√(1 - x ^ 2) * |q.eval x|) := by gcongr
      _ ≤ n * M := by gcongr; exact hM x hx

/-! ### Bernstein's inequality -/

/-- `∑_{j < 2n} g j` groups into the pairs `g (2m) + g (2m + 1)`. -/
private theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∑ j ∈ range (2 * n), g j = ∑ m ∈ range n, (g (2 * m) + g (2 * m + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- The odd part of `p` along the circle through `a + b i`: the polynomial `r` with
`s r(c) = (p(ac + bs) - p(ac - bs)) / 2` whenever `c² + s² = 1`. -/
private noncomputable def oddPart (p : ℝ[X]) (n : ℕ) (a b : ℝ) : ℝ[X] :=
  ∑ m ∈ range n, (hasseDeriv (2 * m + 1) p).comp (C a * X) * C (b ^ (2 * m + 1)) *
    (1 - X ^ 2) ^ m

private theorem natDegree_oddPart_lt {p : ℝ[X]} {n : ℕ} (hn : 0 < n) (hp : p.natDegree ≤ n)
    (a b : ℝ) : (oddPart p n a b).natDegree < n := by
  refine (natDegree_sum_le_of_forall_le _ _ fun m _ => ?_).trans_lt (Nat.sub_lt hn one_pos)
  by_cases hm : p.natDegree < 2 * m + 1
  · simp [hasseDeriv_eq_zero_of_lt_natDegree p _ hm]
  refine (natDegree_mul_le.trans (add_le_add (natDegree_mul_le.trans (add_le_add
    natDegree_comp_le (natDegree_C _).le)) natDegree_pow_le)).trans ?_
  have hX : (C a * X).natDegree ≤ 1 := (natDegree_C_mul_le a X).trans natDegree_X_le
  have h2 : (1 - X ^ 2 : ℝ[X]).natDegree ≤ 2 :=
    natDegree_sub_le_of_le (natDegree_one.le.trans (Nat.zero_le 2)) (natDegree_X_pow_le 2)
  rw [natDegree_hasseDeriv]
  have := Nat.mul_le_mul_left (p.natDegree - (2 * m + 1)) hX
  have := Nat.mul_le_mul_left m h2
  omega

private theorem eval_oddPart_one {p : ℝ[X]} {n : ℕ} (hn : 0 < n) (a b : ℝ) :
    (oddPart p n a b).eval 1 = (derivative p).eval a * b := by
  rw [oddPart, eval_finsetSum, sum_eq_single_of_mem 0 (mem_range.2 hn) fun m _ hm => by
    simp [zero_pow hm]]
  simp [hasseDeriv_one]

/-- The defining identity of the odd part. -/
private theorem two_mul_mul_eval_oddPart {p : ℝ[X]} {n : ℕ} (hn : 0 < n) (hp : p.natDegree ≤ n)
    (a b c s : ℝ) (hs : s ^ 2 = 1 - c ^ 2) :
    2 * (s * (oddPart p n a b).eval c) = p.eval (a * c + b * s) - p.eval (a * c - b * s) := by
  have htaylor (y : ℝ) : p.eval (a * c + y) =
      ∑ j ∈ range (2 * n), (hasseDeriv j p).eval (a * c) * y ^ j := by
    rw [add_comm, ← taylor_eval, eval_eq_sum_range' (n := 2 * n) (by rw [natDegree_taylor]; omega)]
    simp only [taylor_coeff]
  rw [sub_eq_add_neg _ (b * s), htaylor, htaylor, ← sum_sub_distrib, sum_range_two_mul, oddPart,
    eval_finsetSum, mul_sum, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  have hodd : (-(b * s)) ^ (2 * m + 1) = -(b * s) ^ (2 * m + 1) := Odd.neg_pow ⟨m, rfl⟩ _
  have heven : (-(b * s)) ^ (2 * m) = (b * s) ^ (2 * m) := Even.neg_pow ⟨m, two_mul m⟩ _
  simp only [eval_mul, eval_comp, eval_C, eval_X, eval_pow, eval_sub, eval_one, hodd, heven]
  rw [← hs]
  ring

/-- **Bernstein's inequality**: a real polynomial `p` of degree at most `n` with `|p| ≤ M` on
`[-1, 1]` satisfies `√(1 - x²) |p'(x)| ≤ n M` on `[-1, 1]`. -/
theorem sqrt_mul_abs_eval_derivative_le {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ y ∈ Icc (-1 : ℝ) 1, |p.eval y| ≤ M) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    √(1 - x ^ 2) * |(derivative p).eval x| ≤ n * M := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [derivative_of_natDegree_zero (Nat.le_zero.1 hp)]
  set b := √(1 - x ^ 2)
  have hb : b ^ 2 = 1 - x ^ 2 := sq_sqrt (by nlinarith [hx.1, hx.2])
  -- the odd part of `p` along the circle is bounded by `M`
  have hr : ∀ c ∈ Icc (-1 : ℝ) 1, √(1 - c ^ 2) * |(oddPart p n x b).eval c| ≤ M := by
    intro c hc
    set s := √(1 - c ^ 2)
    have hs : s ^ 2 = 1 - c ^ 2 := sq_sqrt (by nlinarith [hc.1, hc.2])
    have hcirc (σ : ℝ) (hσ : σ ^ 2 = 1) : x * c + σ * b * s ∈ Icc (-1 : ℝ) 1 := by
      rw [Set.mem_Icc, ← abs_le, ← sq_le_one_iff_abs_le_one]
      have key : (x * c + σ * b * s) ^ 2 + (x * s - σ * b * c) ^ 2 = 1 := by
        have : (x * c + σ * b * s) ^ 2 + (x * s - σ * b * c) ^ 2 =
            (x ^ 2 + σ ^ 2 * b ^ 2) * (c ^ 2 + s ^ 2) := by ring
        rw [this, hσ, hb, hs]
        ring
      nlinarith [sq_nonneg (x * s - σ * b * c)]
    have h := two_mul_mul_eval_oddPart hn hp x b c s hs
    have h₁ := hM _ (by simpa only [one_mul] using hcirc 1 (one_pow 2))
    have h₂ := hM (x * c - b * s) (by
      have hm := hcirc (-1) (by norm_num)
      rwa [show x * c + -1 * b * s = x * c - b * s by ring] at hm)
    have hs0 : 0 ≤ s := sqrt_nonneg _
    have : |2 * (s * (oddPart p n x b).eval c)| ≤ 2 * M :=
      h ▸ (abs_sub _ _).trans (by linarith)
    rw [abs_mul, abs_two, abs_mul, abs_of_nonneg hs0] at this
    linarith
  have h := abs_eval_le_mul_of_sqrt_mul_abs_eval_le hn (natDegree_oddPart_lt hn hp x b) hr
    (x := 1) ⟨by norm_num, le_rfl⟩
  rwa [eval_oddPart_one hn, abs_mul, abs_of_nonneg (sqrt_nonneg _), mul_comm] at h

/-! ### Markov's inequality -/

/-- **The Markov brothers' inequality**: a real polynomial `p` of degree at most `n` with `|p| ≤ M`
on `[-1, 1]` satisfies `|p'| ≤ n² M` on `[-1, 1]`. -/
theorem abs_eval_derivative_le_sq_mul {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ y ∈ Icc (-1 : ℝ) 1, |p.eval y| ≤ M) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(derivative p).eval x| ≤ n ^ 2 * M := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [derivative_of_natDegree_zero (Nat.le_zero.1 hp)]
  have hq : (derivative p).natDegree < n := (natDegree_derivative_le p).trans_lt (by omega)
  have := abs_eval_le_mul_of_sqrt_mul_abs_eval_le hn hq
    (fun y hy => sqrt_mul_abs_eval_derivative_le hp hM hy) hx
  rwa [← mul_assoc, ← sq] at this

/-- **Markov's inequality on an interval**: a real polynomial `p` of degree at most `n` with
`|p| ≤ M` on `[a, b]` satisfies `(b - a) |p'| ≤ 2 n² M` on `[a, b]`. -/
theorem sub_mul_abs_eval_derivative_le {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) {a b M : ℝ}
    (hab : a < b) (hM : ∀ y ∈ Icc a b, |p.eval y| ≤ M) {x : ℝ} (hx : x ∈ Icc a b) :
    (b - a) * |(derivative p).eval x| ≤ 2 * n ^ 2 * M := by
  set L : ℝ[X] := C ((b - a) / 2) * X + C ((a + b) / 2)
  have hL (t : ℝ) : L.eval t = (b - a) / 2 * t + (a + b) / 2 := by simp [L]
  have hdeg : (p.comp L).natDegree ≤ n := by
    refine natDegree_comp_le.trans ?_
    have : L.natDegree ≤ 1 := natDegree_linear_le
    nlinarith
  have hbound : ∀ t ∈ Icc (-1 : ℝ) 1, |(p.comp L).eval t| ≤ M := fun t ht => by
    rw [eval_comp, hL]
    exact hM _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hba : 0 < b - a := sub_pos.2 hab
  set t := (2 * x - a - b) / (b - a)
  have ht : t ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · rw [le_div_iff₀ hba]; linarith [hx.1]
    · rw [div_le_iff₀ hba]; linarith [hx.2]
  have hLt : L.eval t = x := by
    rw [hL, show t = (2 * x - a - b) / (b - a) from rfl]
    field_simp
    ring
  have h := abs_eval_derivative_le_sq_mul hdeg hbound ht
  rw [derivative_comp, eval_mul, eval_comp, hLt, abs_mul] at h
  have hL' : (derivative L).eval t = (b - a) / 2 := by simp [L]
  rw [hL', abs_of_pos (by positivity)] at h
  linarith

/-! ### Polynomials bounded at the integers -/

/-- The largest value `c` of `|q'|` on `[0, N]` satisfies `N c ≤ d² (b₂ - b₁ + c)` when the
values of `q` at the integers of `[0, N]` lie in `[b₁, b₂]`, and `q` stays within `c / 2` of
`[b₁, b₂]` on `[0, N]`. -/
private theorem exists_max_abs_eval_derivative {d N : ℕ} {q : ℝ[X]} (hq : q.natDegree ≤ d)
    (hN : 0 < N) {b₁ b₂ : ℝ} (hb : ∀ k : ℕ, k ≤ N → q.eval (k : ℝ) ∈ Icc b₁ b₂) :
    ∃ c, (∀ y ∈ Icc (0 : ℝ) N, |(derivative q).eval y| ≤ c) ∧
      N * c ≤ d ^ 2 * (b₂ - b₁ + c) ∧
      ∀ y ∈ Icc (0 : ℝ) N, |q.eval y - (b₁ + b₂) / 2| ≤ (b₂ - b₁ + c) / 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨y₀, hy₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hNR.le)
    (continuous_abs.comp (derivative q).continuous).continuousOn
  set c := |(derivative q).eval y₀|
  have hc (y : ℝ) (hy : y ∈ Icc (0 : ℝ) N) : |(derivative q).eval y| ≤ c := hmax hy
  -- `q` is within `c / 2` of its value at the nearest integer
  have hval : ∀ y ∈ Icc (0 : ℝ) N, |q.eval y - (b₁ + b₂) / 2| ≤ (b₂ - b₁ + c) / 2 := by
    intro y hy
    set k := ⌊y + 1 / 2⌋₊
    have hk₁ : (k : ℝ) ≤ y + 1 / 2 := Nat.floor_le (by linarith [hy.1])
    have hk₂ : y + 1 / 2 < k + 1 := Nat.lt_floor_add_one _
    have hkN : k ≤ N := by
      have : (k : ℝ) < N + 1 := by linarith [hy.2]
      exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
    have hkI : (k : ℝ) ∈ Icc (0 : ℝ) N := ⟨k.cast_nonneg, by exact_mod_cast hkN⟩
    have hmvt := (convex_Icc (0 : ℝ) N).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun z => q.eval z) (fun z _ => (q.hasDerivAt z).hasDerivWithinAt) hc hkI hy
    simp only [Real.norm_eq_abs] at hmvt
    have hyk : |y - k| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have hqk := hb k hkN
    have h0 : 0 ≤ c := (abs_nonneg _).trans (hc y hy)
    rw [abs_le] at hmvt ⊢
    constructor <;> nlinarith [hqk.1, hqk.2, abs_nonneg (y - k)]
  refine ⟨c, hc, ?_, hval⟩
  -- Markov's inequality on `[0, N]` at the maximum
  have h := sub_mul_abs_eval_derivative_le (p := q - C ((b₁ + b₂) / 2))
    ((natDegree_sub_C).le.trans hq) hNR (fun y hy => by simpa using hval y hy) hy₀
  rw [derivative_sub, derivative_C, sub_zero, sub_zero] at h
  linarith

/-- **Polynomials bounded at the integers, derivative form**: a real polynomial `q` of degree at
most `d` whose values at the integers `0, …, N` lie in `[b₁, b₂]` satisfies
`(N - d²) |q'| ≤ d² (b₂ - b₁)` on `[0, N]`. -/
theorem sub_mul_abs_eval_derivative_le_of_forall_nat {d N : ℕ} {q : ℝ[X]} (hq : q.natDegree ≤ d)
    (hN : 0 < N) {b₁ b₂ : ℝ} (hb : ∀ k : ℕ, k ≤ N → q.eval (k : ℝ) ∈ Icc b₁ b₂) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) N) : (N - d ^ 2) * |(derivative q).eval x| ≤ d ^ 2 * (b₂ - b₁) := by
  obtain ⟨c, hc, hNc, -⟩ := exists_max_abs_eval_derivative hq hN hb
  have hB : 0 ≤ b₂ - b₁ := by linarith [(hb 0 (Nat.zero_le _)).1, (hb 0 (Nat.zero_le _)).2]
  rcases le_or_gt ((N : ℝ) - d ^ 2) 0 with h | h
  · nlinarith [abs_nonneg ((derivative q).eval x), sq_nonneg (d : ℝ)]
  · nlinarith [hc x hx]

/-- **The Ehlich–Zeller bound**: a real polynomial `q` of degree at most `d` with `|q| ≤ B` at the
integers `0, …, N` satisfies `(N - d²) |q| ≤ N B` on `[0, N]`; for `d² < N` this bounds `q` on the
whole interval [EhlichZeller1964], [CoppersmithRivlin1992]. -/
theorem sub_mul_abs_eval_le_of_forall_nat {d N : ℕ} {q : ℝ[X]} (hq : q.natDegree ≤ d) (hN : 0 < N)
    {B : ℝ} (hb : ∀ k : ℕ, k ≤ N → |q.eval (k : ℝ)| ≤ B) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) N) :
    (N - d ^ 2) * |q.eval x| ≤ N * B := by
  obtain ⟨c, hc, hNc, hval⟩ := exists_max_abs_eval_derivative hq hN (b₁ := -B) (b₂ := B)
    fun k hk => abs_le.1 (hb k hk)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb 0 (Nat.zero_le _))
  have hq' : |q.eval x| ≤ B + c / 2 := by
    have := hval x hx
    rw [neg_add_cancel, zero_div, sub_zero] at this
    linarith
  have h0 : 0 ≤ c := (abs_nonneg _).trans (hc x hx)
  rcases le_or_gt ((N : ℝ) - d ^ 2) 0 with h | h
  · nlinarith [abs_nonneg (q.eval x), (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  · nlinarith

/-- **The Nisan–Szegedy lemma**: a real polynomial `q` of degree at most `d` whose values at the
integers `0, …, N` lie in `[b₁, b₂]`, and with `|q'(ξ)| ≥ c ≥ 0` at some `ξ ∈ [0, N]`, satisfies
`c N ≤ d² (c + (b₂ - b₁))` [NisanSzegedy1994]. -/
theorem mul_le_sq_mul_of_le_abs_eval_derivative {d N : ℕ} {q : ℝ[X]} (hq : q.natDegree ≤ d)
    (hN : 0 < N) {b₁ b₂ : ℝ} (hb : ∀ k : ℕ, k ≤ N → q.eval (k : ℝ) ∈ Icc b₁ b₂) {ξ c : ℝ}
    (hξ : ξ ∈ Icc (0 : ℝ) N) (hc : 0 ≤ c) (hcξ : c ≤ |(derivative q).eval ξ|) :
    c * N ≤ d ^ 2 * (c + (b₂ - b₁)) := by
  have h := sub_mul_abs_eval_derivative_le_of_forall_nat hq hN hb hξ
  have hB : 0 ≤ b₂ - b₁ := by linarith [(hb 0 (Nat.zero_le _)).1, (hb 0 (Nat.zero_le _)).2]
  rcases le_or_gt ((N : ℝ) - d ^ 2) 0 with h' | h'
  · nlinarith
  · nlinarith

end Polynomial
