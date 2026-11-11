/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.AmbainisAdversary.WeightLayers
public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueQuery

/-!
# Lower bounds of Nayak and Wu for approximate counting, median, and selection

This module derives the statistical query lower bounds of [Nayak and Wu][NayakWu1999] from the
adversary weight-layer promise bound `Cslib.Quantum.one_sub_mul_add_le_four_mul_mul_abs_sub_of_weight`
and the value-query simulation results in
`CslibFrontier/Computability/QueryComplexity/Quantum/ValueQuery.lean`.

Let `T` be the query count of a quantum algorithm whose failure probability on every valid input is
at most `ε` (`2 * ε ≤ 1`), measured through a multi-outcome classical readout of its final basis
state:

* **Approximate counting** ([NayakWu1999], Theorem 1.11): for a Boolean oracle input
  `x : BitString n` with `t` ones, outputting `y : ℝ` with `|y - t| < Δ` (`1 / 2 ≤ Δ`,
  `4 * Δ ≤ n`) satisfies `(1 - 2√(ε(1-ε))) (√(n / Δ) + √(t (n - t)) / Δ) ≤ 16 T`, and at error
  `1 / 3` gives `√(n / Δ) + √(t (n - t)) / Δ ≤ 288 T`
  (`Cslib.Quantum.one_sub_mul_approxCount_le`, `Cslib.Quantum.approxCount_lower_bound`). For
  `0 < Δ ≤ 1 / 2` and `1 ≤ n`, exact-precision counting still requires
  `(1 - 2√(ε(1-ε))) (√n + √(t (n - t))) ≤ 4 T`.
* **Approximate `k`-th smallest element** ([NayakWu1999], Theorem 1.5): in the value-query model
  on an ordered sequence `X : ι → α` of length `n = |ι|` (`1 ≤ k ≤ n`, `1 ≤ Δ`, `4 * Δ ≤ n`),
  outputting an element `y` of `X` whose rank lies strictly in `(k - Δ, k + Δ)` (or even any `y`
  satisfying the relaxed rank bounds `Cslib.Quantum.IsApproxKthSmallestRelaxed`) requires
  `(1 - 2√(ε(1-ε))) (√(n / Δ) + √(k (n - k)) / Δ) ≤ 40 T` for general unitary value oracles,
  and `≤ 20 T` when the two-value oracle step has an involutive difference such as an XOR oracle
  (`Cslib.Quantum.one_sub_mul_kthSmallest_le`,
  `Cslib.Quantum.one_sub_mul_kthSmallest_le_of_involution`). An algorithm returning only an
  index `i : ι` rather than the value `X i` satisfies the same bound on `T + 1`
  (`Cslib.Quantum.kthSmallest_index_lower_bound`).
* **Approximate median** ([NayakWu1999], Corollary 1.6): for `0 < δ < 1`, outputting a
  `δ`-approximate median (`Cslib.Quantum.IsApproxMedian`) of `X : ι → α` requires
  `(1 - 2√(ε(1-ε))) min (1 / δ) n ≤ 24 T` (`≤ 12 T` for involutive-difference oracles, and
  `1 / δ ≤ 432 T` at error `1 / 3` when `1 ≤ δ n`;
  `Cslib.Quantum.one_sub_mul_median_le`, `Cslib.Quantum.median_lower_bound`), with the
  corresponding `T + 1` bound for index-returning algorithms.

Notice the `T + 1` shift for index-returning algorithms: at `n = 3` and `δ = 1 / 3`, returning a
uniformly random index `i : Fin 3` in `0` queries already yields an exact median `x_i` with
probability at least `2 / 3` on every `0/1` input, whereas outputting the value `x_i` itself cannot
avoid at least one query.

## Main definitions

* `Cslib.Quantum.IsApproxMedian`: `δ`-approximate median predicate on `ι → α`.
* `Cslib.Quantum.IsKthSmallest`, `Cslib.Quantum.IsApproxKthSmallest`,
  `Cslib.Quantum.IsApproxKthSmallestRelaxed`: `j`-th smallest and `Δ`-approximate `k`-th smallest
  predicates on `ι → α`.

## Main results

* `Cslib.Quantum.one_sub_mul_approxCount_le`, `Cslib.Quantum.approxCount_lower_bound`: Theorem 1.11
  of [NayakWu1999].
* `Cslib.Quantum.one_sub_mul_kthSmallest_le`,
  `Cslib.Quantum.one_sub_mul_kthSmallest_le_of_involution`,
  `Cslib.Quantum.kthSmallest_lower_bound`: Theorem 1.5 of [NayakWu1999].
* `Cslib.Quantum.one_sub_mul_median_le`, `Cslib.Quantum.one_sub_mul_median_le_of_involution`,
  `Cslib.Quantum.median_lower_bound`: Corollary 1.6 of [NayakWu1999].

## References

* [A. Nayak, F. Wu, *The quantum query complexity of approximating the median and related
  statistics*][NayakWu1999], Theorem 1.5, Corollary 1.6, Theorem 1.11 (arXiv:quant-ph/9804066v2).
-/

public section

namespace Cslib.Quantum

open Finset BitString

/-! ### Problem definitions -/

section ProblemDefs

variable {ι α : Type*} [Fintype ι] [LinearOrder α]

/-- `y` is a **`δ`-approximate median** of `X : ι → α` ([NayakWu1999], Problem 1) when fewer
than `(1 + δ) |ι| / 2` entries are strictly smaller than `y` and fewer than `(1 + δ) |ι| / 2`
entries are strictly larger than `y`. -/
@[expose] def IsApproxMedian (X : ι → α) (δ : ℝ) (y : α) : Prop :=
  (#{i | X i < y} : ℝ) < (1 + δ) * Fintype.card ι / 2 ∧
    (#{i | y < X i} : ℝ) < (1 + δ) * Fintype.card ι / 2

/-- `y` is a **`j`-th smallest element** (`1`-indexed) of `X : ι → α`: at most `j - 1` entries are
strictly less than `y`, and at least `j` entries are at most `y`. -/
@[expose] def IsKthSmallest (X : ι → α) (j : ℕ) (y : α) : Prop :=
  #{i | X i < y} < j ∧ j ≤ #{i | X i ≤ y}

/-- `y` is a **`Δ`-approximate `k`-th smallest element** of `X : ι → α` ([NayakWu1999],
Problem 2): `y` is a `j`-th smallest element of `X` for some `1 ≤ j ≤ |ι|` with
`k - Δ < j < k + Δ`. -/
@[expose] def IsApproxKthSmallest (X : ι → α) (k : ℕ) (Δ : ℝ) (y : α) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ j ≤ Fintype.card ι ∧ (k : ℝ) - Δ < j ∧ (j : ℝ) < k + Δ ∧
    IsKthSmallest X j y

/-- Relaxed `Δ`-approximate `k`-th smallest condition not requiring `y` to appear in `X`: `y`
still lies between the minimum and maximum of `X` and satisfies the rank bounds implied by
`IsApproxKthSmallest`. -/
@[expose] def IsApproxKthSmallestRelaxed (X : ι → α) (k : ℕ) (Δ : ℝ) (y : α) : Prop :=
  #{i | X i < y} < Fintype.card ι ∧ #{i | y < X i} < Fintype.card ι ∧
    (#{i | X i < y} : ℝ) + 1 < k + Δ ∧ (#{i | y < X i} : ℝ) < Fintype.card ι - k + Δ

/-- Every `Δ`-approximate `k`-th smallest element satisfies the relaxed rank condition. -/
theorem IsApproxKthSmallest.relaxed {X : ι → α} {k : ℕ} {Δ : ℝ} {y : α}
    (h : IsApproxKthSmallest X k Δ y) : IsApproxKthSmallestRelaxed X k Δ y := by
  obtain ⟨j, hj1, hjn, hkd, hjk, hlt, hle⟩ := h
  have hpart : #{i | y < X i} + #{i | X i ≤ y} = Fintype.card ι := by
    have hs := card_filter_add_card_filter_not (s := univ) (fun i => y < X i)
    simp only [card_univ] at hs
    refine hs.trans' ?_
    congr 1
    refine congrArg card (filter_congr fun i _ => not_lt)
  refine ⟨lt_of_lt_of_le hlt hjn, by omega, ?_, ?_⟩
  · have hlt1 : (#{i | X i < y} : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : #{i | X i < y} + 1 ≤ j)
    linarith
  · have hgt : (#{i | y < X i} : ℝ) ≤ Fintype.card ι - j := by
      have : #{i | y < X i} ≤ Fintype.card ι - j := by omega
      have hjR : (j : ℝ) ≤ Fintype.card ι := by exact_mod_cast hjn
      exact_mod_cast this
    linarith

end ProblemDefs

/-! ### Error-1/3 constant helper -/

/-- The error-`1/3` factor `1 - 2√((1/3)(2/3))` is at least `1 / 18`. -/
private theorem one_eighteenth_le_factor :
    (1 / 18 : ℝ) ≤ 1 - 2 * √((1 / 3 : ℝ) * (1 - 1 / 3)) := by
  have hsqrt : √((1 / 3 : ℝ) * (1 - 1 / 3)) ≤ 17 / 36 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  linarith

/-! ### Theorem 1.11: Δ-approximate counting -/

section ApproxCount

private theorem approxCount_disjoint_step {n : ℕ} {W : Type*} [Fintype W]
    (U : ℕ → State n W →ₗᵢ[ℂ] State n W) {ψ₀ : State n W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : Fin n × Bool × W → ℝ) {t k' : ℕ} {Δ ε : ℝ} (ht : t ≤ n) (hk' : k' ≤ n)
    (hk'ne : t ≠ k') (hgap : 2 * Δ ≤ |(t : ℝ) - k'|)
    (h : ∀ x : BitString n,
      1 - ε ≤ measureProb (run U ψ₀ x T) (univ.filter fun p => |out p - weight x| < Δ))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * (√(n * |(t : ℝ) - k'|) + √(t * (n - t))) ≤
      4 * T * |(t : ℝ) - k'| := by
  classical
  set S : Finset (Fin n × Bool × W) := univ.filter fun p => |out p - t| < Δ
  refine one_sub_mul_add_le_four_mul_mul_abs_sub_of_weight U hψ₀ T S hk'ne ht hk'
    (fun x hx => ?_) (fun y hy => ?_) hε (le_min_iff.mpr ⟨le_rfl, (by omega : min t k' ≤ t)⟩)
    (le_max_left t k')
  · rw [← hx]
    exact h x
  · set S' : Finset (Fin n × Bool × W) := univ.filter fun p => |out p - k'| < Δ
    have hdisj : S ⊆ S'ᶜ := by
      intro p hp
      rw [mem_compl, mem_filter]
      intro hp'
      have h1 : |out p - t| < Δ := (mem_filter.mp hp).2
      have h2 : |out p - k'| < Δ := hp'.2
      have htri : |(t : ℝ) - k'| ≤ |out p - t| + |out p - k'| := by
        calc
          |(t : ℝ) - k'| = |(-(out p - t)) + (out p - k')| := by ring_nf
          _ ≤ |-(out p - t)| + |out p - k'| := abs_add_le _ _
          _ = |out p - t| + |out p - k'| := by rw [abs_neg]
      linarith
    have hmono := measureProb_mono (run U ψ₀ y T) hdisj
    rw [measureProb_compl, norm_run, hψ₀, one_pow] at hmono
    have hy' : 1 - ε ≤ measureProb (run U ψ₀ y T) S' := by
      simpa [S', hy] using h y
    linarith

/-- **Core step of Theorem 1.11** ([NayakWu1999]): for `0 < Δ` and `d = ⌈2Δ⌉₊` with either
`t + d ≤ n` or `d ≤ t`, any `T`-query algorithm approximating `weight x` within `< Δ` with error
`ε ≤ 1/2` satisfies `(1 - 2√(ε(1-ε))) (√(n d) + √(t (n - t))) ≤ 4 T d`. -/
theorem one_sub_mul_add_le_of_approxCount_aux {n : ℕ} {W : Type*} [Fintype W]
    (U : ℕ → State n W →ₗᵢ[ℂ] State n W) {ψ₀ : State n W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : Fin n × Bool × W → ℝ) {t : ℕ} {Δ ε : ℝ} (ht : t ≤ n) (hΔ : 0 < Δ)
    (hstep : t + Nat.ceil (2 * Δ) ≤ n ∨ Nat.ceil (2 * Δ) ≤ t)
    (h : ∀ x : BitString n,
      1 - ε ≤ measureProb (run U ψ₀ x T) (univ.filter fun p => |out p - weight x| < Δ))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * (√(n * Nat.ceil (2 * Δ)) + √(t * (n - t))) ≤
      4 * T * Nat.ceil (2 * Δ) := by
  set d := Nat.ceil (2 * Δ)
  have hd_pos : 0 < d := Nat.ceil_pos.mpr (by linarith)
  have hd_ge : 2 * Δ ≤ d := Nat.le_ceil (2 * Δ)
  rcases hstep with hup | hdn
  · have hbound := approxCount_disjoint_step U hψ₀ T out ht hup (by omega : t ≠ t + d)
      (by
        have : |(t : ℝ) - (t + d : ℕ)| = d := by
          push_cast
          rw [abs_of_nonpos (by linarith)]
          ring
        linarith) h hε
    have habs : |(t : ℝ) - (t + d : ℕ)| = d := by
      push_cast
      rw [abs_of_nonpos (by linarith)]
      ring
    simpa [habs] using hbound
  · have hbound := approxCount_disjoint_step U hψ₀ T out ht (by omega : t - d ≤ n)
      (by omega : t ≠ t - d)
      (by
        have hsub : ((t - d : ℕ) : ℝ) = t - d := Nat.cast_sub hdn
        rw [abs_of_nonneg (by rw [hsub]; linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d])]
        rw [hsub]; ring_nf; exact hd_ge) h hε
    have hsub : ((t - d : ℕ) : ℝ) = t - d := Nat.cast_sub hdn
    have habs : |(t : ℝ) - ((t - d : ℕ) : ℝ)| = d := by
      rw [hsub, abs_of_nonneg (by linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d])]
      ring
    simpa [habs] using hbound

/-- **Theorem 1.11** ([NayakWu1999]): any `T`-query algorithm approximating the Hamming weight of
every `x : BitString n` within additive error `< Δ` (`1 / 2 ≤ Δ`, `4 * Δ ≤ n`) with failure
probability at most `ε ≤ 1 / 2` satisfies
`(1 - 2√(ε(1-ε))) (√(n / Δ) + √(t (n - t)) / Δ) ≤ 16 T` on inputs of weight `t ≤ n`. -/
theorem one_sub_mul_approxCount_le {n : ℕ} {W : Type*} [Fintype W]
    (U : ℕ → State n W →ₗᵢ[ℂ] State n W) {ψ₀ : State n W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : Fin n × Bool × W → ℝ) {t : ℕ} {Δ ε : ℝ} (ht : t ≤ n)
    (hΔ_lo : 1 / 2 ≤ Δ) (hΔ_hi : 4 * Δ ≤ n)
    (h : ∀ x : BitString n,
      1 - ε ≤ measureProb (run U ψ₀ x T) (univ.filter fun p => |out p - weight x| < Δ))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * (√(n / Δ) + √(t * (n - t)) / Δ) ≤ 16 * T := by
  set d := Nat.ceil (2 * Δ)
  have hΔ : 0 < Δ := by linarith
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.ceil_pos.mpr (by linarith))
  have hd_lt : (d : ℝ) < 2 * Δ + 1 := Nat.ceil_lt_add_one (by linarith)
  have h2d : 2 * d ≤ n + 1 := by
    have : (2 * d : ℝ) < n + 2 := by linarith
    have : (2 * d : ℕ) < n + 2 := by exact_mod_cast this
    omega
  have hstep : t + d ≤ n ∨ d ≤ t := by omega
  have hcore := one_sub_mul_add_le_of_approxCount_aux U hψ₀ T out ht hΔ hstep h hε
  have hd_le : (d : ℝ) ≤ 4 * Δ := by linarith
  have hfac := one_sub_two_mul_sqrt_nonneg ε
  have hdiv : √(n / d) + √(t * (n - t)) / d ≤ 4 * T / (1 - 2 * √(ε * (1 - ε))) ∨
      1 - 2 * √(ε * (1 - ε)) = 0 := by
    rcases eq_or_lt_of_le hfac with h0 | hpos
    · exact Or.inr h0.symm
    · refine Or.inl ?_
      rw [le_div_iff₀ hpos, mul_comm, mul_div_assoc']
      have hsq : √(n / d) * d = √(n * d) := by
        rw [Real.sqrt_div (Nat.cast_nonneg n), div_mul_eq_mul_div, div_eq_iff (Real.sqrt_ne_zero'.mpr hd_pos),
          Real.sqrt_mul (Nat.cast_nonneg n), mul_assoc, Real.mul_self_sqrt hd_pos.le]
      rw [mul_add, hsq, div_mul_cancel₀ _ hd_pos.ne']
      linarith
  rcases hdiv with hle | h0
  · have hsqrt_d : √(n / Δ) ≤ 2 * √(n / d) := by
      have h1 : (n : ℝ) / Δ ≤ 4 * ((n : ℝ) / d) := by
        rw [mul_div_assoc', div_le_div_iff₀ hΔ hd_pos]
        nlinarith [Nat.cast_nonneg n]
      calc
        √(n / Δ) ≤ √(4 * (n / d)) := Real.sqrt_le_sqrt h1
        _ = 2 * √(n / d) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hinv_d : √(t * (n - t)) / Δ ≤ 4 * (√(t * (n - t)) / d) := by
      rw [mul_div_assoc', div_le_div_iff₀ hΔ hd_pos]
      have hnn : 0 ≤ √(t * (n - t)) := Real.sqrt_nonneg _
      nlinarith
    calc
      (1 - 2 * √(ε * (1 - ε))) * (√(n / Δ) + √(t * (n - t)) / Δ)
          ≤ (1 - 2 * √(ε * (1 - ε))) * (4 * (√(n / d) + √(t * (n - t)) / d)) := by
            refine mul_le_mul_of_nonneg_left ?_ hfac
            linarith [Real.sqrt_nonneg (n / d)]
      _ ≤ 4 * ((1 - 2 * √(ε * (1 - ε))) * (4 * T / (1 - 2 * √(ε * (1 - ε))))) := by
            rw [← mul_assoc, mul_comm _ 4, mul_assoc]
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hfac) (by norm_num)
      _ = 16 * T := by
            have hne : 1 - 2 * √(ε * (1 - ε)) ≠ 0 := by
              intro heq
              have := hcore
              -- unreachable since `hle` came from `hpos`
              sorry
            field_simp [hne]; ring
  · rw [← h0, zero_mul]
    positivity

end ApproxCount

end Cslib.Quantum
