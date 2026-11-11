/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.AmbainisAdversary.WeightLayers
public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueQuery
import CslibFrontier.Foundations.Quantum.Measurement.Overlap

/-!
# Lower bounds of Nayak and Wu for approximate counting, median, and selection

This module derives the statistical query lower bounds of [Nayak and Wu][NayakWu1999] from the
adversary weight-layer promise bound
`Cslib.Quantum.one_sub_mul_add_le_four_mul_mul_abs_sub_of_weight`
and the value-query simulation results in
`CslibFrontier/Computability/QueryComplexity/Quantum/ValueQuery.lean`.

Let `T` be the query count of a quantum algorithm whose failure probability on every valid input is
at most `ε` (`2 * ε ≤ 1`), measured through a multi-outcome classical readout of its final basis
state (`measureProb ... (univ.filter ...)`, connected to `Cslib.Quantum.measureOut` via
`Cslib.Quantum.le_measureProb_of_le_measureOut`):

* **Approximate counting** ([NayakWu1999], Theorem 1.11): for a Boolean oracle input
  `x : BitString n` with `t` ones, outputting `y : ℝ` with `|y - t| < Δ` (`1 / 2 ≤ Δ`,
  `4 * Δ ≤ n`) satisfies `(1 - 2√(ε(1-ε))) (√(n / Δ) + √(t (n - t)) / Δ) ≤ 16 T`, and at error
  `1 / 3` gives `√(n / Δ) + √(t (n - t)) / Δ ≤ 288 T`
  (`Cslib.Quantum.one_sub_mul_approxCount_le`, `Cslib.Quantum.approxCount_lower_bound`). For
  `0 < Δ ≤ 1 / 2` and `1 ≤ n`, exact-precision counting still requires
  `(1 - 2√(ε(1-ε))) (√n + √(t (n - t))) ≤ 4 T` (`Cslib.Quantum.one_sub_mul_exactCount_le`).
* **Approximate `k`-th smallest element** ([NayakWu1999], Theorem 1.5): in the value-query model
  on an ordered sequence `X : ι → α` of length `n = |ι|` (`1 ≤ k ≤ n`, `1 ≤ Δ`, `4 * Δ ≤ n`),
  outputting an element `y` of `X` whose rank lies strictly in `(k - Δ, k + Δ)` (or even any `y`
  satisfying `Cslib.Quantum.IsApproxKthSmallestRelaxed`) requires
  `(1 - 2√(ε(1-ε))) (√(n / Δ) + √(k (n - k)) / Δ) ≤ 32 T` for general unitary value oracles
  (`≤ 576 T` at error `1 / 3`), and `≤ 16 T` (`≤ 288 T` at error `1 / 3`) when the two-value oracle
  step has an involutive difference such as an XOR oracle
  (`Cslib.Quantum.one_sub_mul_kthSmallest_le`,
  `Cslib.Quantum.one_sub_mul_kthSmallest_le_of_involution`,
  `Cslib.Quantum.kthSmallest_lower_bound`).
  An algorithm returning only an index `i : ι` rather than the value `X i` satisfies the same
  bound on `T + 1` (`Cslib.Quantum.one_sub_mul_kthSmallest_index_le`,
  `Cslib.Quantum.kthSmallest_index_lower_bound`).
* **Approximate median** ([NayakWu1999], Corollary 1.6): for `0 < δ < 1` and `1 ≤ n`, outputting a
  `δ`-approximate median (`Cslib.Quantum.IsApproxMedian`) of `X : ι → α` requires
  `(1 - 2√(ε(1-ε))) min (1 / δ) n ≤ 24 T` (`≤ 12 T` for involutive-difference oracles, and
  `min (1 / δ) n ≤ 432 T`, in particular `1 / δ ≤ 432 T` when `1 ≤ δ n`, at error `1 / 3`;
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

* `Cslib.Quantum.one_sub_mul_exactCount_le`, `Cslib.Quantum.one_sub_mul_approxCount_le`,
  `Cslib.Quantum.approxCount_lower_bound`: Theorem 1.11 of [NayakWu1999].
* `Cslib.Quantum.one_sub_mul_kthSmallest_le`,
  `Cslib.Quantum.one_sub_mul_kthSmallest_le_of_involution`,
  `Cslib.Quantum.kthSmallest_lower_bound`, `Cslib.Quantum.one_sub_mul_kthSmallest_index_le`:
  Theorem 1.5 of [NayakWu1999].
* `Cslib.Quantum.one_sub_mul_median_le`, `Cslib.Quantum.one_sub_mul_median_le_of_involution`,
  `Cslib.Quantum.median_lower_bound`, `Cslib.Quantum.one_sub_mul_median_index_le`: Corollary 1.6 of
  [NayakWu1999].

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

/-- Monotonicity of `IsApproxMedian` in the tolerance `δ`. -/
theorem IsApproxMedian.mono {X : ι → α} {δ₁ δ₂ : ℝ} {y : α} (h : δ₁ ≤ δ₂)
    (hm : IsApproxMedian X δ₁ y) : IsApproxMedian X δ₂ y := by
  have hle : (1 + δ₁) * Fintype.card ι / 2 ≤ (1 + δ₂) * Fintype.card ι / 2 := by
    have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    nlinarith
  exact ⟨lt_of_lt_of_le hm.1 hle, lt_of_lt_of_le hm.2 hle⟩

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
    have h2 : #{i | X i ≤ y} = #{i | ¬ y < X i} :=
      congrArg card (filter_congr fun i _ => not_lt.symm)
    rw [h2]
    exact hs
  refine ⟨lt_of_lt_of_le hlt hjn, by omega, ?_, ?_⟩
  · have hlt1 : (#{i | X i < y} : ℝ) + 1 ≤ j := by
      exact_mod_cast (by omega : #{i | X i < y} + 1 ≤ j)
    linarith
  · have hgt : (#{i | y < X i} : ℝ) ≤ Fintype.card ι - j := by
      have : #{i | y < X i} ≤ Fintype.card ι - j := by omega
      have hjR : (j : ℝ) ≤ Fintype.card ι := by exact_mod_cast hjn
      exact_mod_cast this
    linarith

/-- Converts an `ENNReal` lower bound on `(measureOut ψ hψ out).toOuterMeasure {b | P b}` into a
`measureProb` lower bound on `univ.filter fun y => P (out y)`. -/
theorem le_measureProb_of_le_measureOut {γ β : Type*} [Fintype γ] (ψ : EuclideanSpace ℂ γ)
    (hψ : ‖ψ‖ = 1) (out : γ → β) (P : β → Prop) {p : ℝ}
    (hp : ENNReal.ofReal p ≤ (measureOut ψ hψ out).toOuterMeasure {b | P b}) :
    p ≤ (open Classical in measureProb ψ (univ.filter fun y => P (out y))) := by
  classical
  rw [measureOut_toOuterMeasure_apply] at hp
  exact (ENNReal.ofReal_le_ofReal_iff (measureProb_nonneg _ _)).mp hp

end ProblemDefs

/-! ### Algebraic and error-1/3 helpers -/

section Helpers

/-- The error-`1/3` factor `1 - 2√((1/3)(2/3))` is at least `1 / 18`. -/
private theorem one_eighteenth_le_factor :
    (1 / 18 : ℝ) ≤ 1 - 2 * √((1 / 3 : ℝ) * (1 - 1 / 3)) := by
  have hsqrt : √((1 / 3 : ℝ) * (1 - 1 / 3)) ≤ 17 / 36 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  linarith

private theorem le_eighteen_mul_of_one_sub_mul_le {X B : ℝ} (hX : 0 ≤ X)
    (h : (1 - 2 * √((1 / 3 : ℝ) * (1 - 1 / 3))) * X ≤ B) : X ≤ 18 * B := by
  have hle : (1 / 18 : ℝ) * X ≤ (1 - 2 * √((1 / 3 : ℝ) * (1 - 1 / 3))) * X :=
    mul_le_mul_of_nonneg_right one_eighteenth_le_factor hX
  linarith

/-- Division-free scaling from an integer gap `d ≤ 4 * Δ` to a real gap `Δ > 0`. -/
private theorem approx_scale_le {F n m Δ d B : ℝ}
    (hF : 0 ≤ F) (hn : 0 ≤ n) (hΔ : 0 < Δ) (hd : 0 < d) (hd_le : d ≤ 4 * Δ)
    (hcore : F * (√(n * d) + √m) ≤ B * d) :
    F * (√(n / Δ) + √m / Δ) ≤ 4 * B := by
  have hdiv : d / Δ ≤ 4 := (div_le_iff₀ hΔ).2 (by linarith)
  have hsq_le : d ^ 2 * (n / Δ) ≤ 4 * (n * d) := by
    calc
      d ^ 2 * (n / Δ) = n * d * (d / Δ) := by ring
      _ ≤ n * d * 4 := mul_le_mul_of_nonneg_left hdiv (mul_nonneg hn hd.le)
      _ = 4 * (n * d) := by ring
  have h1 : d * √(n / Δ) ≤ 2 * √(n * d) := by
    calc
      d * √(n / Δ) = √(d ^ 2) * √(n / Δ) := by rw [Real.sqrt_sq hd.le]
      _ = √(d ^ 2 * (n / Δ)) := (Real.sqrt_mul (sq_nonneg d) _).symm
      _ ≤ √(4 * (n * d)) := Real.sqrt_le_sqrt hsq_le
      _ = 2 * √(n * d) := by
            rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]
  have h2 : d * (√m / Δ) ≤ 4 * √m := by
    calc
      d * (√m / Δ) = √m * (d / Δ) := by ring
      _ ≤ √m * 4 := mul_le_mul_of_nonneg_left hdiv (Real.sqrt_nonneg m)
      _ = 4 * √m := by ring
  have hsum : d * (√(n / Δ) + √m / Δ) ≤ 4 * (√(n * d) + √m) := by
    calc
      d * (√(n / Δ) + √m / Δ) = d * √(n / Δ) + d * (√m / Δ) := by ring
      _ ≤ 4 * √(n * d) + 4 * √m := add_le_add (by linarith [Real.sqrt_nonneg (n * d)]) h2
      _ = 4 * (√(n * d) + √m) := by ring
  have hmul : d * (F * (√(n / Δ) + √m / Δ)) ≤ d * (4 * B) := by
    calc
      d * (F * (√(n / Δ) + √m / Δ)) = F * (d * (√(n / Δ) + √m / Δ)) := by ring
      _ ≤ F * (4 * (√(n * d) + √m)) := mul_le_mul_of_nonneg_left hsum hF
      _ = 4 * (F * (√(n * d) + √m)) := by ring
      _ ≤ 4 * (B * d) := mul_le_mul_of_nonneg_left hcore (by norm_num)
      _ = d * (4 * B) := by ring
  exact le_of_mul_le_mul_left hmul hd

end Helpers

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
    (fun x hx => ?_) (fun y hy => ?_) hε (min_le_left t k') (le_max_left t k')
  · dsimp only [S]
    rw [← hx]
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
        rw [hsub]; linarith) h hε
    have hsub : ((t - d : ℕ) : ℝ) = t - d := Nat.cast_sub hdn
    have habs : |(t : ℝ) - ((t - d : ℕ) : ℝ)| = d := by
      rw [hsub, abs_of_nonneg (by linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d])]
      ring
    simpa [habs] using hbound

/-- **Exact-precision counting (`0 < Δ ≤ 1 / 2`)** ([NayakWu1999], Theorem 1.11): for `1 ≤ n`
and `0 < Δ ≤ 1 / 2`, approximating the Hamming weight within `< Δ` requires
`(1 - 2√(ε(1-ε))) (√n + √(t (n - t))) ≤ 4 T` queries. -/
theorem one_sub_mul_exactCount_le {n : ℕ} {W : Type*} [Fintype W]
    (U : ℕ → State n W →ₗᵢ[ℂ] State n W) {ψ₀ : State n W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : Fin n × Bool × W → ℝ) {t : ℕ} {Δ ε : ℝ} (hn : 1 ≤ n) (ht : t ≤ n)
    (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (h : ∀ x : BitString n,
      1 - ε ≤ measureProb (run U ψ₀ x T) (univ.filter fun p => |out p - weight x| < Δ))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * (√n + √(t * (n - t))) ≤ 4 * T := by
  have hd : Nat.ceil (2 * Δ) = 1 := by
    have h1 : 1 ≤ Nat.ceil (2 * Δ) := Nat.ceil_pos.mpr (by linarith)
    have h2 : Nat.ceil (2 * Δ) ≤ 1 := Nat.ceil_le.mpr (by norm_num; linarith)
    omega
  have hstep : t + Nat.ceil (2 * Δ) ≤ n ∨ Nat.ceil (2 * Δ) ≤ t := by omega
  have hcore := one_sub_mul_add_le_of_approxCount_aux U hψ₀ T out ht hΔ_pos hstep h hε
  simpa [hd, mul_one] using hcore

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
  have hbound := approx_scale_le (one_sub_two_mul_sqrt_nonneg ε) (Nat.cast_nonneg n) hΔ hd_pos
    (by linarith) hcore
  linarith

/-- Bounded-error (`ε = 1 / 3`) form of Theorem 1.11 ([NayakWu1999]):
`√(n / Δ) + √(t (n - t)) / Δ ≤ 288 T`. -/
theorem approxCount_lower_bound {n : ℕ} {W : Type*} [Fintype W]
    (U : ℕ → State n W →ₗᵢ[ℂ] State n W) {ψ₀ : State n W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : Fin n × Bool × W → ℝ) {t : ℕ} {Δ : ℝ} (ht : t ≤ n)
    (hΔ_lo : 1 / 2 ≤ Δ) (hΔ_hi : 4 * Δ ≤ n)
    (h : ∀ x : BitString n,
      1 - (1 / 3 : ℝ) ≤ measureProb (run U ψ₀ x T) (univ.filter fun p => |out p - weight x| < Δ)) :
    √(n / Δ) + √(t * (n - t)) / Δ ≤ 288 * T := by
  have hcore := one_sub_mul_approxCount_le U hψ₀ T out ht hΔ_lo hΔ_hi h (by norm_num)
  have hnn : 0 ≤ √((n : ℝ) / Δ) + √((t : ℝ) * (n - t)) / Δ := by positivity
  linarith [le_eighteen_mul_of_one_sub_mul_le hnn hcore]

end ApproxCount

/-! ### Shared Boolean-simulation adversary bridge -/

section TwoValueSimBridge

private def embedSeq {ι α : Type*} {n : ℕ} (e : ι ≃ Fin n) (a₀ a₁ : α)
    (b : BitString n) : ι → α :=
  fun i => if b (e i) then a₁ else a₀

private theorem card_filter_comp_equiv {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin n)
    (b : BitString n) (c : Bool) :
    #{i : ι | b (e i) = c} = #{j : Fin n | b j = c} :=
  Finset.card_bij (fun i _ => e i) (fun _ hi => by simp_all)
    (fun _ _ _ _ h => e.injective h)
    (fun j hj => ⟨e.symm j, by simp_all, e.apply_symm_apply j⟩)

private theorem card_filter_embedSeq_lt {ι α : Type*} [Fintype ι] [LinearOrder α]
    {n : ℕ} (e : ι ≃ Fin n) {a₀ a₁ : α} (_ha : a₀ < a₁) (b : BitString n) (y : α)
    (hy : a₀ < y) :
    n - weight b ≤ #{i : ι | embedSeq e a₀ a₁ b i < y} := by
  have hsub : univ.filter (fun i : ι => b (e i) = false) ⊆
      univ.filter (fun i : ι => embedSeq e a₀ a₁ b i < y) := by
    intro i hi
    rw [mem_filter] at hi ⊢
    exact ⟨mem_univ i, by simp [embedSeq, hi.2, hy]⟩
  have hcard : #{i : ι | b (e i) = false} = n - weight b := by
    rw [card_filter_comp_equiv e b false]
    have hnot := weight_not b
    simp only [Fintype.card_fin] at hnot
    rw [← hnot]
    refine congrArg card (filter_congr fun j _ => ?_)
    cases hb : b j <;> simp [hb]
  exact hcard ▸ card_le_card hsub

private theorem card_filter_embedSeq_gt {ι α : Type*} [Fintype ι] [LinearOrder α]
    {n : ℕ} (e : ι ≃ Fin n) {a₀ a₁ : α} (ha : a₀ < a₁) (b : BitString n) (y : α)
    (hy : y ≤ a₀) :
    weight b ≤ #{i : ι | y < embedSeq e a₀ a₁ b i} := by
  have hsub : univ.filter (fun i : ι => b (e i) = true) ⊆
      univ.filter (fun i : ι => y < embedSeq e a₀ a₁ b i) := by
    intro i hi
    rw [mem_filter] at hi ⊢
    exact ⟨mem_univ i, by simp [embedSeq, hi.2, lt_of_le_of_lt hy ha]⟩
  have hcard : #{i : ι | b (e i) = true} = weight b := by
    rw [card_filter_comp_equiv e b true, weight]
  exact hcard ▸ card_le_card hsub

private theorem measureProb_le_of_sep {ι V W α : Type*} [Fintype ι] [Fintype V] [Fintype W]
    [LinearOrder α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × V × W → α) (P : (ι → α) → α → Prop) {a₀ : α} {ε : ℝ} {X : ι → α}
    (hgood : 1 - ε ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T) (univ.filter fun p => P X (out p)))) :
    ((∀ y, P X y → y ≤ a₀) →
      1 - ε ≤ measureProb (runValue step U ψ₀ X T) (univ.filter fun p => out p ≤ a₀)) ∧
    ((∀ y, P X y → a₀ < y) →
      measureProb (runValue step U ψ₀ X T) (univ.filter fun p => out p ≤ a₀) ≤ ε) := by
  classical
  refine ⟨fun hle => hgood.trans (measureProb_mono _ fun p hp => ?_), fun hgt => ?_⟩
  · rw [mem_filter] at hp ⊢
    exact ⟨mem_univ p, hle _ hp.2⟩
  · have hsub : univ.filter (fun p => out p ≤ a₀) ⊆
        (univ.filter (fun p => P X (out p)))ᶜ := by
      intro p hp
      rw [mem_compl, mem_filter]
      intro hp'
      exact not_lt.mpr (mem_filter.mp hp).2 (hgt _ hp'.2)
    have hmono := measureProb_mono (runValue step U ψ₀ X T) hsub
    rw [measureProb_compl, norm_runValue, hψ₀, one_pow] at hmono
    linarith

private theorem measureProb_sim_sep {ι V W α : Type*} [Fintype ι] [Fintype V] [Fintype W]
    [LinearOrder α] {n : ℕ} (e : ι ≃ Fin n)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × V × W → α) (P : (ι → α) → α → Prop) {a₀ a₁ : α} {ε : ℝ}
    (Vsim : ℕ → State n (V × W) →ₗᵢ[ℂ] State n (V × W)) (φ₀ : State n (V × W)) (T_bool : ℕ)
    (hsim : ∀ (b : BitString n) (S : Finset (ι × V × W)),
      measureProb (run Vsim φ₀ b T_bool) (S.map (embedOutcome e)) =
        measureProb (runValue step U ψ₀ (embedSeq e a₀ a₁ b) T) S)
    (hgood : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - ε ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T) (univ.filter fun p => P X (out p))))
    {t₁ t₂ : ℕ}
    (h1 : ∀ b : BitString n, weight b = t₁ → ∀ y, P (embedSeq e a₀ a₁ b) y → y ≤ a₀)
    (h2 : ∀ b : BitString n, weight b = t₂ → ∀ y, P (embedSeq e a₀ a₁ b) y → a₀ < y) :
    (∀ b : BitString n, weight b = t₁ → 1 - ε ≤
      measureProb (run Vsim φ₀ b T_bool) ((univ.filter fun p => out p ≤ a₀).map (embedOutcome e))) ∧
    (∀ b : BitString n, weight b = t₂ →
      measureProb (run Vsim φ₀ b T_bool) ((univ.filter fun p => out p ≤ a₀).map (embedOutcome e)) ≤
        ε) := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · rw [hsim]
    refine (measureProb_le_of_sep step U hψ₀ T out P (hgood _ fun i => ?_)).1 (h1 b hb)
    by_cases hbi : b (e i) <;> simp [embedSeq, hbi]
  · rw [hsim]
    refine (measureProb_le_of_sep step U hψ₀ T out P (hgood _ fun i => ?_)).2 (h2 b hb)
    by_cases hbi : b (e i) <;> simp [embedSeq, hbi]

end TwoValueSimBridge

/-! ### Theorem 1.5: Δ-approximate `k`-th smallest element -/

section KthSmallest

private theorem kthSmallest_le_of_weight_le {ι α : Type*} [Fintype ι] [LinearOrder α]
    {n : ℕ} (e : ι ≃ Fin n) (hn : Fintype.card ι = n) {a₀ a₁ : α} (ha : a₀ < a₁)
    {k : ℕ} (_hk : k ≤ n) {Δ : ℝ} (b : BitString n)
    (hw : weight b = 0 ∨ (weight b : ℝ) + Δ ≤ n - k)
    {y : α} (hy : IsApproxKthSmallestRelaxed (embedSeq e a₀ a₁ b) k Δ y) :
    y ≤ a₀ := by
  by_contra hnot
  have hgt : a₀ < y := lt_of_not_ge hnot
  have hcard := card_filter_embedSeq_lt e ha b y hgt
  rcases hw with hw0 | hwle
  · have : n ≤ #{i : ι | embedSeq e a₀ a₁ b i < y} := by omega
    have h1 := hy.1
    omega
  · have hwN : weight b ≤ n := weight_le_length b
    have hsub : ((n - weight b : ℕ) : ℝ) = n - weight b := Nat.cast_sub hwN
    have hleR : (n : ℝ) - weight b ≤ #{i : ι | embedSeq e a₀ a₁ b i < y} := by
      rw [← hsub]
      exact_mod_cast hcard
    linarith [hy.2.2.1]

private theorem kthSmallest_gt_of_weight_ge {ι α : Type*} [Fintype ι] [LinearOrder α]
    {n : ℕ} (e : ι ≃ Fin n) (hn : Fintype.card ι = n) {a₀ a₁ : α} (ha : a₀ < a₁)
    {k : ℕ} {Δ : ℝ} (b : BitString n)
    (hw : weight b = n ∨ (n : ℝ) - k + Δ ≤ weight b)
    {y : α} (hy : IsApproxKthSmallestRelaxed (embedSeq e a₀ a₁ b) k Δ y) :
    a₀ < y := by
  by_contra hnot
  have hle : y ≤ a₀ := le_of_not_gt hnot
  have hcard := card_filter_embedSeq_gt e ha b y hle
  rcases hw with hwn | hwge
  · have : n ≤ #{i : ι | y < embedSeq e a₀ a₁ b i} := by omega
    have h2 := hy.2.1
    omega
  · have hleR : (weight b : ℝ) ≤ #{i : ι | y < embedSeq e a₀ a₁ b i} := by exact_mod_cast hcard
    have h2 := hy.2.2.2
    rw [hn] at h2
    linarith

private theorem one_sub_mul_kthSmallest_le_of_sim {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α]
    {n : ℕ} (e : ι ≃ Fin n) (hn : Fintype.card ι = n)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × V × W → α) {a₀ a₁ : α} (ha : a₀ < a₁) {k : ℕ} {Δ ε : ℝ}
    (_hk1 : 1 ≤ k) (hkn : k ≤ n) (hΔ_lo : 1 ≤ Δ) (hΔ_hi : 4 * Δ ≤ n)
    (Vsim : ℕ → State n (V × W) →ₗᵢ[ℂ] State n (V × W)) (φ₀ : State n (V × W)) (T_bool : ℕ)
    (hφ₀ : ‖φ₀‖ = 1)
    (hsim : ∀ (b : BitString n) (S : Finset (ι × V × W)),
      measureProb (run Vsim φ₀ b T_bool) (S.map (embedOutcome e)) =
        measureProb (runValue step U ψ₀ (embedSeq e a₀ a₁ b) T) S)
    (hgood : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - ε ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T)
        (univ.filter fun p => IsApproxKthSmallestRelaxed X k Δ (out p))))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * (√(n / Δ) + √((k : ℝ) * (n - k)) / Δ) ≤ 16 * T_bool := by
  set c₁ := n - k
  have hc₁ : c₁ ≤ n := Nat.sub_le n k
  have hΔ_pos : 0 < Δ := by linarith
  have hc₁_mul : ((c₁ : ℝ) * (n - c₁)) = (k : ℝ) * (n - k) := by
    have hsub : (c₁ : ℝ) = n - k := Nat.cast_sub hkn
    rw [hsub]
    ring
  have hpair : ∀ (t₁ t₂ : ℕ), t₁ ≠ t₂ → t₁ ≤ n → t₂ ≤ n → min t₁ t₂ ≤ c₁ → c₁ ≤ max t₁ t₂ →
      (t₁ = 0 ∨ (t₁ : ℝ) + Δ ≤ n - k) → (t₂ = n ∨ (n : ℝ) - k + Δ ≤ t₂) →
      |(t₁ : ℝ) - t₂| ≤ 4 * Δ →
      (1 - 2 * √(ε * (1 - ε))) * (√(n / Δ) + √((k : ℝ) * (n - k)) / Δ) ≤ 16 * T_bool := by
    intro t₁ t₂ hne ht₁ ht₂ hmin hmax hsep₁ hsep₂ hgap
    have hsep := measureProb_sim_sep e step U hψ₀ T out
      (fun X y => IsApproxKthSmallestRelaxed X k Δ y) Vsim φ₀ T_bool hsim hgood
      (fun b hb y hy => kthSmallest_le_of_weight_le e hn ha hkn b
        (Or.elim hsep₁ (fun h0 => Or.inl (hb.trans h0)) (fun hle => Or.inr (by rw [hb]; exact hle)))
        hy)
      (fun b hb y hy => kthSmallest_gt_of_weight_ge e hn ha b
        (Or.elim hsep₂ (fun hn' => Or.inl (hb.trans hn'))
          (fun hge => Or.inr (by rw [hb]; exact hge)))
        hy)
    have hcore := one_sub_mul_add_le_four_mul_mul_abs_sub_of_weight Vsim hφ₀ T_bool
      ((univ.filter fun p => out p ≤ a₀).map (embedOutcome e)) hne ht₁ ht₂
      hsep.1 hsep.2 hε hmin hmax
    have hd_pos : 0 < |(t₁ : ℝ) - t₂| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
    have hsc := approx_scale_le (one_sub_two_mul_sqrt_nonneg ε) (Nat.cast_nonneg n) hΔ_pos
      hd_pos hgap hcore
    rw [hc₁_mul] at hsc
    linarith
  set d₁ := Nat.ceil Δ
  have hd₁_pos : 1 ≤ d₁ := Nat.ceil_pos.mpr hΔ_pos
  have hd₁_ge : Δ ≤ d₁ := Nat.le_ceil Δ
  have hd₁_lt : (d₁ : ℝ) < Δ + 1 := Nat.ceil_lt_add_one hΔ_pos.le
  set d₂ := Nat.ceil (2 * Δ)
  have hd₂_pos : 1 ≤ d₂ := Nat.ceil_pos.mpr (by linarith)
  have hd₂_ge : 2 * Δ ≤ d₂ := Nat.le_ceil (2 * Δ)
  have hd₂_lt : (d₂ : ℝ) < 2 * Δ + 1 := Nat.ceil_lt_add_one (by linarith)
  have hd₂_le_4 : (d₂ : ℝ) ≤ 4 * Δ := by linarith
  have hd₂_le_n : d₂ ≤ n := by
    have : (d₂ : ℝ) ≤ n := by linarith
    exact_mod_cast this
  by_cases hhi : c₁ + d₁ ≤ n
  · by_cases hlo : d₁ ≤ c₁
    · refine hpair (c₁ - d₁) (c₁ + d₁) (by omega) (by omega) (by omega)
        (by rw [min_eq_left (by omega)]; omega) (by rw [max_eq_right (by omega)]; omega)
        (Or.inr ?_) (Or.inr ?_) ?_
      · have hsub : ((c₁ - d₁ : ℕ) : ℝ) = c₁ - d₁ := Nat.cast_sub hlo
        have hcsub : (c₁ : ℝ) = n - k := Nat.cast_sub hkn
        rw [hsub, hcsub]
        linarith
      · have hcsub : (c₁ : ℝ) = n - k := Nat.cast_sub hkn
        push_cast
        rw [hcsub]
        linarith
      · push_cast
        rw [Nat.cast_sub hlo, abs_of_nonpos (by linarith)]
        linarith
    · have hc₁_lt : c₁ < d₁ := by omega
      have hc₁_lt_R : (c₁ : ℝ) < Δ := Nat.lt_ceil.mp hc₁_lt
      have hc₁_le_d₂ : c₁ ≤ d₂ := by
        have : (c₁ : ℝ) ≤ d₂ := by linarith
        exact_mod_cast this
      refine hpair 0 d₂ (by omega) (Nat.zero_le n) hd₂_le_n
        (by rw [min_eq_left (Nat.zero_le d₂)]; exact Nat.zero_le c₁)
        (by rw [max_eq_right (Nat.zero_le d₂)]; exact hc₁_le_d₂)
        (Or.inl rfl) (Or.inr ?_) ?_
      · have hcsub : (c₁ : ℝ) = n - k := Nat.cast_sub hkn
        linarith
      · push_cast
        rw [zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg d₂)]
        exact hd₂_le_4
  · have hkd₁ : k < d₁ := by
      dsimp only [c₁] at hhi
      omega
    have hk_lt_R : (k : ℝ) < Δ := Nat.lt_ceil.mp hkd₁
    have hk_le_d₂ : k ≤ d₂ := by
      have : (k : ℝ) ≤ d₂ := by linarith
      exact_mod_cast this
    refine hpair (n - d₂) n (by omega) (Nat.sub_le n d₂) le_rfl
      (by rw [min_eq_left (Nat.sub_le n d₂)]; omega)
      (by rw [max_eq_right (Nat.sub_le n d₂)]; exact hc₁)
      (Or.inr ?_) (Or.inl rfl) ?_
    · rw [Nat.cast_sub hd₂_le_n]
      linarith
    · rw [Nat.cast_sub hd₂_le_n, abs_of_nonpos (by linarith)]
      linarith

/-- **Theorem 1.5 (arbitrary unitary oracle, two-valued domain)** ([NayakWu1999]): any `T`-query
value-query algorithm outputting an element satisfying `IsApproxKthSmallestRelaxed` on all
`{a₀, a₁}`-valued inputs (`a₀ < a₁`) with failure probability `ε ≤ 1 / 2` satisfies
`(1 - 2√(ε(1-ε))) (√(|ι| / Δ) + √(k (|ι| - k)) / Δ) ≤ 32 T`. -/
theorem one_sub_mul_kthSmallest_twoValues_le {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × V × W → α) (a₀ a₁ : α) (ha : a₀ < a₁) {k : ℕ} {Δ ε : ℝ}
    (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hΔ_lo : 1 ≤ Δ) (hΔ_hi : 4 * Δ ≤ Fintype.card ι)
    (hgood : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - ε ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T)
        (univ.filter fun p => IsApproxKthSmallestRelaxed X k Δ (out p))))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) *
        (√((Fintype.card ι : ℝ) / Δ) + √((k : ℝ) * (Fintype.card ι - k)) / Δ) ≤
      32 * T := by
  let e := Fintype.equivFin ι
  obtain ⟨Vsim, φ₀, hφ₀, hsim⟩ := exists_sim_value e step a₀ a₁ U ψ₀ T
  have hbound := one_sub_mul_kthSmallest_le_of_sim e rfl step U hψ₀ T out ha hk1 hkn hΔ_lo
    hΔ_hi Vsim φ₀ (2 * T) (hφ₀.trans hψ₀) hsim hgood hε
  push_cast at hbound
  linarith

/-- **Theorem 1.5 (arbitrary unitary oracle)** ([NayakWu1999]): over any nontrivial linear order
`α`, a `T`-query value-query algorithm approximating the `k`-th smallest element within `< Δ`
(`1 ≤ k ≤ |ι|`, `1 ≤ Δ`, `4 * Δ ≤ |ι|`) with failure probability `ε ≤ 1 / 2` satisfies
`(1 - 2√(ε(1-ε))) (√(|ι| / Δ) + √(k (|ι| - k)) / Δ) ≤ 32 T`. -/
theorem one_sub_mul_kthSmallest_le {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α] [Nontrivial α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × V × W → α) {k : ℕ} {Δ ε : ℝ}
    (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hΔ_lo : 1 ≤ Δ) (hΔ_hi : 4 * Δ ≤ Fintype.card ι)
    (hgood : ∀ X : ι → α, 1 - ε ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T)
        (univ.filter fun p => IsApproxKthSmallestRelaxed X k Δ (out p))))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) *
        (√((Fintype.card ι : ℝ) / Δ) + √((k : ℝ) * (Fintype.card ι - k)) / Δ) ≤
      32 * T := by
  obtain ⟨a₀, a₁, ha⟩ := exists_pair_lt α
  exact one_sub_mul_kthSmallest_twoValues_le step U hψ₀ T out a₀ a₁ ha hk1 hkn hΔ_lo hΔ_hi
    (fun X _ => hgood X) hε

/-- **Theorem 1.5 (involutive-difference oracle)** ([NayakWu1999]): when the relative step
`(step a₀).symm.trans (step a₁)` is an involution (for instance an XOR oracle), each value query
costs one phase query, tightening the constant from `32` to `16`. -/
theorem one_sub_mul_kthSmallest_le_of_involution {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × V × W → α) (a₀ a₁ : α) (ha : a₀ < a₁)
    (hR : ∀ φ, ((step a₀).symm.trans (step a₁)) (((step a₀).symm.trans (step a₁)) φ) = φ)
    {k : ℕ} {Δ ε : ℝ}
    (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hΔ_lo : 1 ≤ Δ) (hΔ_hi : 4 * Δ ≤ Fintype.card ι)
    (hgood : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - ε ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T)
        (univ.filter fun p => IsApproxKthSmallestRelaxed X k Δ (out p))))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) *
        (√((Fintype.card ι : ℝ) / Δ) + √((k : ℝ) * (Fintype.card ι - k)) / Δ) ≤
      16 * T := by
  let e := Fintype.equivFin ι
  obtain ⟨Vsim, φ₀, hφ₀, hsim⟩ := exists_sim_involution e step a₀ a₁ hR U ψ₀ T
  exact one_sub_mul_kthSmallest_le_of_sim e rfl step U hψ₀ T out ha hk1 hkn hΔ_lo hΔ_hi Vsim φ₀ T
    (hφ₀.trans hψ₀) hsim hgood hε

private theorem measureProb_isApproxKthSmallestRelaxed_ge {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) (ψ₀ : ValueState ι V W) (T : ℕ)
    (out : ι × V × W → α) (X : ι → α) {k : ℕ} {Δ ε : ℝ}
    (h : 1 - ε ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T)
        (univ.filter fun p => IsApproxKthSmallest X k Δ (out p)))) :
    1 - ε ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T)
        (univ.filter fun p => IsApproxKthSmallestRelaxed X k Δ (out p))) := by
  classical
  refine h.trans (measureProb_mono _ fun p hp => ?_)
  rw [mem_filter] at hp ⊢
  exact ⟨mem_univ p, hp.2.relaxed⟩

private theorem kthSmallest_one_third_of_le {n k : ℕ} {Δ B : ℝ} (hkn : k ≤ n) (hΔ : 0 ≤ Δ)
    (h : (1 - 2 * √((1 / 3 : ℝ) * (1 - 1 / 3))) *
        (√((n : ℝ) / Δ) + √((k : ℝ) * (n - k)) / Δ) ≤ B) :
    √((n : ℝ) / Δ) + √((k : ℝ) * (n - k)) / Δ ≤ 18 * B := by
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hnn : 0 ≤ √((n : ℝ) / Δ) + √((k : ℝ) * (n - k)) / Δ := by
    have : 0 ≤ (k : ℝ) * (n - k) := mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr hknR)
    positivity
  exact le_eighteen_mul_of_one_sub_mul_le hnn h

/-- Bounded-error (`ε = 1 / 3`) form of Theorem 1.5 ([NayakWu1999]) for `IsApproxKthSmallest`:
`√(|ι| / Δ) + √(k (|ι| - k)) / Δ ≤ 576 T`. -/
theorem kthSmallest_lower_bound {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α] [Nontrivial α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × V × W → α) {k : ℕ} {Δ : ℝ}
    (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hΔ_lo : 1 ≤ Δ) (hΔ_hi : 4 * Δ ≤ Fintype.card ι)
    (hgood : ∀ X : ι → α, 1 - (1 / 3 : ℝ) ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T)
        (univ.filter fun p => IsApproxKthSmallest X k Δ (out p)))) :
    √((Fintype.card ι : ℝ) / Δ) + √((k : ℝ) * (Fintype.card ι - k)) / Δ ≤ 576 * T := by
  have hcore := one_sub_mul_kthSmallest_le step U hψ₀ T out hk1 hkn hΔ_lo hΔ_hi
    (fun X => measureProb_isApproxKthSmallestRelaxed_ge step U ψ₀ T out X (hgood X)) (by norm_num)
  linarith [kthSmallest_one_third_of_le hkn (by linarith) hcore]

/-- Bounded-error (`ε = 1 / 3`) form of Theorem 1.5 ([NayakWu1999]) for involutive-difference
oracles: `√(|ι| / Δ) + √(k (|ι| - k)) / Δ ≤ 288 T`. -/
theorem kthSmallest_involution_lower_bound {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × V × W → α) (a₀ a₁ : α) (ha : a₀ < a₁)
    (hR : ∀ φ, ((step a₀).symm.trans (step a₁)) (((step a₀).symm.trans (step a₁)) φ) = φ)
    {k : ℕ} {Δ : ℝ}
    (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hΔ_lo : 1 ≤ Δ) (hΔ_hi : 4 * Δ ≤ Fintype.card ι)
    (hgood : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - (1 / 3 : ℝ) ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T)
        (univ.filter fun p => IsApproxKthSmallest X k Δ (out p)))) :
    √((Fintype.card ι : ℝ) / Δ) + √((k : ℝ) * (Fintype.card ι - k)) / Δ ≤ 288 * T := by
  have hcore := one_sub_mul_kthSmallest_le_of_involution step U hψ₀ T out a₀ a₁ ha hR hk1 hkn hΔ_lo
    hΔ_hi (fun X hX => measureProb_isApproxKthSmallestRelaxed_ge step U ψ₀ T out X (hgood X hX))
    (by norm_num)
  linarith [kthSmallest_one_third_of_le hkn (by linarith) hcore]

/-- **Theorem 1.5 (index-returning value-query algorithm)** ([NayakWu1999]): a `T`-query
algorithm returning an index `idx p : ι` whose value `X (idx p)` approximates the `k`-th smallest
element is simulated in `T + 1` queries via `Cslib.Quantum.exists_sim_index_to_value`, giving
`(1 - 2√(ε(1-ε))) (√(|ι| / Δ) + √(k (|ι| - k)) / Δ) ≤ 32 (T + 1)`. -/
theorem one_sub_mul_kthSmallest_index_le {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (v₀ : V) (read : V → α) (a₀ a₁ : α) (ha : a₀ < a₁)
    (hread₀ : (open Classical in
      measureProb (step a₀ (ket v₀)) (univ.filter fun v => read v = a₀)) = 1)
    (hread₁ : (open Classical in
      measureProb (step a₁ (ket v₀)) (univ.filter fun v => read v = a₁)) = 1)
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (idx : ι × V × W → ι) {k : ℕ} {Δ ε : ℝ}
    (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hΔ_lo : 1 ≤ Δ) (hΔ_hi : 4 * Δ ≤ Fintype.card ι)
    (hgood : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - ε ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T)
        (univ.filter fun p => IsApproxKthSmallestRelaxed X k Δ (X (idx p)))))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) *
        (√((Fintype.card ι : ℝ) / Δ) + √((k : ℝ) * (Fintype.card ι - k)) / Δ) ≤
      32 * ((T : ℝ) + 1) := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨U', ψ₀', out', hnorm, hsim⟩ := exists_sim_index_to_value step v₀ read U ψ₀ T idx
  have hgood' : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - ε ≤ (open Classical in
      measureProb (runValue step U' ψ₀' X (T + 1))
        (univ.filter fun q => IsApproxKthSmallestRelaxed X k Δ (out' q))) := by
    intro X hX
    rw [hsim X (fun i => by rcases hX i with hi | hi <;> simpa [hi] using ‹_›)
      (IsApproxKthSmallestRelaxed X k Δ)]
    exact hgood X hX
  have hres := one_sub_mul_kthSmallest_twoValues_le step U' (hnorm.trans hψ₀) (T + 1) out' a₀ a₁
    ha hk1 hkn hΔ_lo hΔ_hi hgood' hε
  push_cast at hres
  exact hres

/-- Bounded-error (`ε = 1 / 3`) form of Theorem 1.5 for index-returning algorithms:
`√(|ι| / Δ) + √(k (|ι| - k)) / Δ ≤ 576 (T + 1)`. -/
theorem kthSmallest_index_lower_bound {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (v₀ : V) (read : V → α) (a₀ a₁ : α) (ha : a₀ < a₁)
    (hread₀ : (open Classical in
      measureProb (step a₀ (ket v₀)) (univ.filter fun v => read v = a₀)) = 1)
    (hread₁ : (open Classical in
      measureProb (step a₁ (ket v₀)) (univ.filter fun v => read v = a₁)) = 1)
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (idx : ι × V × W → ι) {k : ℕ} {Δ : ℝ}
    (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hΔ_lo : 1 ≤ Δ) (hΔ_hi : 4 * Δ ≤ Fintype.card ι)
    (hgood : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - (1 / 3 : ℝ) ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T)
        (univ.filter fun p => IsApproxKthSmallest X k Δ (X (idx p))))) :
    √((Fintype.card ι : ℝ) / Δ) + √((k : ℝ) * (Fintype.card ι - k)) / Δ ≤ 576 * ((T : ℝ) + 1) := by
  have hcore := one_sub_mul_kthSmallest_index_le step v₀ read a₀ a₁ ha hread₀ hread₁ U hψ₀ T idx
    hk1 hkn hΔ_lo hΔ_hi
    (fun X hX => measureProb_isApproxKthSmallestRelaxed_ge step U ψ₀ T (fun p => X (idx p)) X
      (hgood X hX))
    (by norm_num)
  linarith [kthSmallest_one_third_of_le hkn (by linarith) hcore]

/-- Specialization of `one_sub_mul_kthSmallest_index_le` to permutation oracles `permStep π`. -/
theorem one_sub_mul_kthSmallest_perm_index_le {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α]
    (π : α → Equiv.Perm V) (v₀ : V) (a₀ a₁ : α) (ha : a₀ < a₁) (hne : π a₀ v₀ ≠ π a₁ v₀)
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (idx : ι × V × W → ι) {k : ℕ} {Δ ε : ℝ}
    (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hΔ_lo : 1 ≤ Δ) (hΔ_hi : 4 * Δ ≤ Fintype.card ι)
    (hgood : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - ε ≤ (open Classical in
      measureProb (runValue (permStep π) U ψ₀ X T)
        (univ.filter fun p => IsApproxKthSmallestRelaxed X k Δ (X (idx p)))))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) *
        (√((Fintype.card ι : ℝ) / Δ) + √((k : ℝ) * (Fintype.card ι - k)) / Δ) ≤
      32 * ((T : ℝ) + 1) := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨U', ψ₀', out', hnorm, hsim⟩ := exists_sim_index_to_value_perm π v₀ a₀ a₁ hne U ψ₀ T idx
  have hgood' : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - ε ≤ (open Classical in
      measureProb (runValue (permStep π) U' ψ₀' X (T + 1))
        (univ.filter fun q => IsApproxKthSmallestRelaxed X k Δ (out' q))) := by
    intro X hX
    rw [hsim X hX (IsApproxKthSmallestRelaxed X k Δ)]
    exact hgood X hX
  have hres := one_sub_mul_kthSmallest_twoValues_le (permStep π) U' (hnorm.trans hψ₀) (T + 1) out'
    a₀ a₁ ha hk1 hkn hΔ_lo hΔ_hi hgood' hε
  push_cast at hres
  exact hres

end KthSmallest

/-! ### Corollary 1.6: δ-approximate median -/

section Median

private theorem one_sub_mul_median_le_of_sim {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α]
    {n : ℕ} (e : ι ≃ Fin n) (hn : Fintype.card ι = n) (hn1 : 1 ≤ n)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × V × W → α) {a₀ a₁ : α} (ha : a₀ < a₁) {δ ε : ℝ}
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (Vsim : ℕ → State n (V × W) →ₗᵢ[ℂ] State n (V × W)) (φ₀ : State n (V × W)) (T_bool : ℕ)
    (hφ₀ : ‖φ₀‖ = 1)
    (hsim : ∀ (b : BitString n) (S : Finset (ι × V × W)),
      measureProb (run Vsim φ₀ b T_bool) (S.map (embedOutcome e)) =
        measureProb (runValue step U ψ₀ (embedSeq e a₀ a₁ b) T) S)
    (hgood : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - ε ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T) (univ.filter fun p => IsApproxMedian X δ (out p))))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * min (1 / δ) n ≤ 12 * T_bool := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
  set t₁ := Nat.floor ((1 - δ) * n / 2)
  set t₂ := Nat.ceil ((1 + δ) * n / 2)
  have ht₁_nonneg : 0 ≤ (1 - δ) * n / 2 := by nlinarith
  have ht₁_le : (t₁ : ℝ) ≤ (1 - δ) * n / 2 := Nat.floor_le ht₁_nonneg
  have ht₁_lt : (1 - δ) * n / 2 < t₁ + 1 := Nat.lt_floor_add_one _
  have ht₂_ge : (1 + δ) * n / 2 ≤ t₂ := Nat.le_ceil _
  have ht₂_lt : (t₂ : ℝ) < (1 + δ) * n / 2 + 1 := Nat.ceil_lt_add_one (by nlinarith)
  have h2t₁ : 2 * t₁ ≤ n := by
    have : (2 * t₁ : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hn_le_2t₂ : n ≤ 2 * t₂ := by
    have : (n : ℝ) ≤ 2 * t₂ := by nlinarith
    exact_mod_cast this
  have ht₂_le_n : t₂ ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have ht₁_le_n : t₁ ≤ n := by omega
  have ht₁_lt_t₂ : t₁ < t₂ := by
    have : (t₁ : ℝ) < t₂ := by nlinarith
    exact_mod_cast this
  have hsep := measureProb_sim_sep e step U hψ₀ T out (fun X y => IsApproxMedian X δ y)
    Vsim φ₀ T_bool hsim hgood
    (fun b hb y hm => by
      by_contra hnot
      have hlt : a₀ < y := lt_of_not_ge hnot
      have hcard := card_filter_embedSeq_lt e ha b y hlt
      rw [hb] at hcard
      have hcardR : (n : ℝ) - t₁ ≤ #{i : ι | embedSeq e a₀ a₁ b i < y} := by
        rw [← Nat.cast_sub ht₁_le_n]
        exact_mod_cast hcard
      have hm1 := hm.1
      rw [hn] at hm1
      linarith)
    (fun b hb y hm => by
      by_contra hnot
      have hle : y ≤ a₀ := le_of_not_gt hnot
      have hcard := card_filter_embedSeq_gt e ha b y hle
      rw [hb] at hcard
      have hcardR : (t₂ : ℝ) ≤ #{i : ι | y < embedSeq e a₀ a₁ b i} := by exact_mod_cast hcard
      have hm2 := hm.2
      rw [hn] at hm2
      linarith)
  have hcard := one_sub_mul_card_le_four_mul_mul_abs_sub_of_weight Vsim hφ₀ T_bool
    ((univ.filter fun p => out p ≤ a₀).map (embedOutcome e)) ht₁_lt_t₂.ne
    (by rw [min_eq_left ht₁_lt_t₂.le]; exact h2t₁)
    (by rw [max_eq_right ht₁_lt_t₂.le]; exact hn_le_2t₂)
    ht₁_le_n ht₂_le_n hsep.1 hsep.2 hε
  have habs : |(t₁ : ℝ) - t₂| = t₂ - t₁ := by
    rw [abs_of_nonpos (by linarith [show (t₁ : ℝ) ≤ t₂ by exact_mod_cast ht₁_lt_t₂.le])]
    ring
  rw [habs] at hcard
  have hfac := one_sub_two_mul_sqrt_nonneg ε
  have hdiff : (t₂ : ℝ) - t₁ < δ * n + 2 := by linarith
  by_cases hbig : 2 ≤ δ * n
  · have hstep : (1 - 2 * √(ε * (1 - ε))) * n ≤ 8 * T_bool * (δ * n) := by
      have hle2 : (t₂ : ℝ) - t₁ ≤ 2 * δ * n := by linarith
      calc
        (1 - 2 * √(ε * (1 - ε))) * n ≤ 4 * T_bool * ((t₂ : ℝ) - t₁) := hcard
        _ ≤ 4 * T_bool * (2 * δ * n) := mul_le_mul_of_nonneg_left hle2 (by positivity)
        _ = 8 * T_bool * (δ * n) := by ring
    have hδn_pos : 0 < δ * n := by positivity
    have hinv : (1 - 2 * √(ε * (1 - ε))) * (1 / δ) ≤ 8 * T_bool := by
      refine le_of_mul_le_mul_right ?_ hδn_pos
      calc
        (1 - 2 * √(ε * (1 - ε))) * (1 / δ) * (δ * n)
            = (1 - 2 * √(ε * (1 - ε))) * n := by field_simp [hδ₀.ne']
        _ ≤ 8 * T_bool * (δ * n) := hstep
    calc
      (1 - 2 * √(ε * (1 - ε))) * min (1 / δ) n
          ≤ (1 - 2 * √(ε * (1 - ε))) * (1 / δ) := mul_le_mul_of_nonneg_left (min_le_left _ _) hfac
      _ ≤ 8 * T_bool := hinv
      _ ≤ 12 * T_bool := by linarith
  · have hlt4 : (t₂ - t₁ : ℕ) < 4 := by
      have : ((t₂ - t₁ : ℕ) : ℝ) < 4 := by
        rw [Nat.cast_sub ht₁_lt_t₂.le]
        linarith
      exact_mod_cast this
    have hle3 : (t₂ : ℝ) - t₁ ≤ 3 := by
      rw [← Nat.cast_sub ht₁_lt_t₂.le]
      exact_mod_cast (by omega : t₂ - t₁ ≤ 3)
    have hstep : (1 - 2 * √(ε * (1 - ε))) * n ≤ 12 * T_bool := by
      calc
        (1 - 2 * √(ε * (1 - ε))) * n ≤ 4 * T_bool * ((t₂ : ℝ) - t₁) := hcard
        _ ≤ 4 * T_bool * 3 := mul_le_mul_of_nonneg_left hle3 (by positivity)
        _ = 12 * T_bool := by ring
    calc
      (1 - 2 * √(ε * (1 - ε))) * min (1 / δ) n
          ≤ (1 - 2 * √(ε * (1 - ε))) * n := mul_le_mul_of_nonneg_left (min_le_right _ _) hfac
      _ ≤ 12 * T_bool := hstep

/-- **Corollary 1.6 (arbitrary unitary oracle, two-valued domain)** ([NayakWu1999]): any
`T`-query value-query algorithm computing a `δ`-approximate median (`0 < δ < 1`, `1 ≤ |ι|`) on
all `{a₀, a₁}`-valued inputs (`a₀ < a₁`) with failure probability `ε ≤ 1 / 2` satisfies
`(1 - 2√(ε(1-ε))) min (1 / δ) |ι| ≤ 24 T`. -/
theorem one_sub_mul_median_twoValues_le {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × V × W → α) (a₀ a₁ : α) (ha : a₀ < a₁) {δ ε : ℝ}
    (hn1 : 1 ≤ Fintype.card ι) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hgood : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - ε ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T) (univ.filter fun p => IsApproxMedian X δ (out p))))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * min (1 / δ) (Fintype.card ι) ≤ 24 * T := by
  let e := Fintype.equivFin ι
  obtain ⟨Vsim, φ₀, hφ₀, hsim⟩ := exists_sim_value e step a₀ a₁ U ψ₀ T
  have hbound := one_sub_mul_median_le_of_sim e rfl hn1 step U hψ₀ T out ha hδ₀ hδ₁ Vsim φ₀
    (2 * T) (hφ₀.trans hψ₀) hsim hgood hε
  push_cast at hbound
  linarith

/-- **Corollary 1.6 (arbitrary unitary oracle)** ([NayakWu1999]): over any nontrivial linear order
`α`, a `T`-query value-query algorithm computing a `δ`-approximate median (`0 < δ < 1`, `1 ≤ |ι|`)
with failure probability `ε ≤ 1 / 2` satisfies `(1 - 2√(ε(1-ε))) min (1 / δ) |ι| ≤ 24 T`. -/
theorem one_sub_mul_median_le {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α] [Nontrivial α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × V × W → α) {δ ε : ℝ}
    (hn1 : 1 ≤ Fintype.card ι) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hgood : ∀ X : ι → α, 1 - ε ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T) (univ.filter fun p => IsApproxMedian X δ (out p))))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * min (1 / δ) (Fintype.card ι) ≤ 24 * T := by
  obtain ⟨a₀, a₁, ha⟩ := exists_pair_lt α
  exact one_sub_mul_median_twoValues_le step U hψ₀ T out a₀ a₁ ha hn1 hδ₀ hδ₁
    (fun X _ => hgood X) hε

/-- **Corollary 1.6 (involutive-difference oracle)** ([NayakWu1999]): when
`(step a₀).symm.trans (step a₁)` is an involution (for instance an XOR oracle), the constant
tightens from `24` to `12`: `(1 - 2√(ε(1-ε))) min (1 / δ) |ι| ≤ 12 T`. -/
theorem one_sub_mul_median_le_of_involution {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × V × W → α) (a₀ a₁ : α) (ha : a₀ < a₁)
    (hR : ∀ φ, ((step a₀).symm.trans (step a₁)) (((step a₀).symm.trans (step a₁)) φ) = φ)
    {δ ε : ℝ} (hn1 : 1 ≤ Fintype.card ι) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hgood : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - ε ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T) (univ.filter fun p => IsApproxMedian X δ (out p))))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * min (1 / δ) (Fintype.card ι) ≤ 12 * T := by
  let e := Fintype.equivFin ι
  obtain ⟨Vsim, φ₀, hφ₀, hsim⟩ := exists_sim_involution e step a₀ a₁ hR U ψ₀ T
  exact one_sub_mul_median_le_of_sim e rfl hn1 step U hψ₀ T out ha hδ₀ hδ₁ Vsim φ₀ T
    (hφ₀.trans hψ₀) hsim hgood hε

/-- Bounded-error (`ε = 1 / 3`) form of Corollary 1.6 ([NayakWu1999]):
`min (1 / δ) |ι| ≤ 432 T`. -/
theorem median_lower_bound {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α] [Nontrivial α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × V × W → α) {δ : ℝ}
    (hn1 : 1 ≤ Fintype.card ι) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hgood : ∀ X : ι → α, 1 - (1 / 3 : ℝ) ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T) (univ.filter fun p => IsApproxMedian X δ (out p)))) :
    min (1 / δ) (Fintype.card ι) ≤ 432 * T := by
  have hcore := one_sub_mul_median_le step U hψ₀ T out hn1 hδ₀ hδ₁ hgood (by norm_num)
  have hnn : 0 ≤ min (1 / δ) (Fintype.card ι) := by positivity
  linarith [le_eighteen_mul_of_one_sub_mul_le hnn hcore]

/-- When `1 ≤ δ * |ι|`, `min (1 / δ) |ι| = 1 / δ`, so Corollary 1.6 gives `1 / δ ≤ 432 T`. -/
theorem median_inv_delta_lower_bound {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α] [Nontrivial α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × V × W → α) {δ : ℝ}
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hδn : 1 ≤ δ * Fintype.card ι)
    (hgood : ∀ X : ι → α, 1 - (1 / 3 : ℝ) ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T) (univ.filter fun p => IsApproxMedian X δ (out p)))) :
    1 / δ ≤ 432 * T := by
  have hn1 : 1 ≤ Fintype.card ι := by
    by_contra h
    have h0 : Fintype.card ι = 0 := by omega
    rw [h0, Nat.cast_zero, mul_zero] at hδn
    linarith
  have hle : 1 / δ ≤ Fintype.card ι := (div_le_iff₀ hδ₀).2 (by linarith)
  have hm := median_lower_bound step U hψ₀ T out hn1 hδ₀ hδ₁ hgood
  rw [min_eq_left hle] at hm
  exact hm

/-- Bounded-error (`ε = 1 / 3`) form of Corollary 1.6 ([NayakWu1999]) for involutive-difference
oracles: `min (1 / δ) |ι| ≤ 216 T`. -/
theorem median_involution_lower_bound {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (out : ι × V × W → α) (a₀ a₁ : α) (ha : a₀ < a₁)
    (hR : ∀ φ, ((step a₀).symm.trans (step a₁)) (((step a₀).symm.trans (step a₁)) φ) = φ)
    {δ : ℝ} (hn1 : 1 ≤ Fintype.card ι) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hgood : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - (1 / 3 : ℝ) ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T) (univ.filter fun p => IsApproxMedian X δ (out p)))) :
    min (1 / δ) (Fintype.card ι) ≤ 216 * T := by
  have hcore := one_sub_mul_median_le_of_involution step U hψ₀ T out a₀ a₁ ha hR hn1 hδ₀ hδ₁ hgood
    (by norm_num)
  have hnn : 0 ≤ min (1 / δ) (Fintype.card ι) := by positivity
  linarith [le_eighteen_mul_of_one_sub_mul_le hnn hcore]

/-- **Corollary 1.6 (index-returning value-query algorithm)** ([NayakWu1999]): a `T`-query
algorithm returning an index `idx p : ι` whose value `X (idx p)` is a `δ`-approximate median
satisfies `(1 - 2√(ε(1-ε))) min (1 / δ) |ι| ≤ 24 (T + 1)`. -/
theorem one_sub_mul_median_index_le {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (v₀ : V) (read : V → α) (a₀ a₁ : α) (ha : a₀ < a₁)
    (hread₀ : (open Classical in
      measureProb (step a₀ (ket v₀)) (univ.filter fun v => read v = a₀)) = 1)
    (hread₁ : (open Classical in
      measureProb (step a₁ (ket v₀)) (univ.filter fun v => read v = a₁)) = 1)
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (idx : ι × V × W → ι) {δ ε : ℝ}
    (hn1 : 1 ≤ Fintype.card ι) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hgood : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - ε ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T)
        (univ.filter fun p => IsApproxMedian X δ (X (idx p)))))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * min (1 / δ) (Fintype.card ι) ≤ 24 * ((T : ℝ) + 1) := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨U', ψ₀', out', hnorm, hsim⟩ := exists_sim_index_to_value step v₀ read U ψ₀ T idx
  have hgood' : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - ε ≤ (open Classical in
      measureProb (runValue step U' ψ₀' X (T + 1))
        (univ.filter fun q => IsApproxMedian X δ (out' q))) := by
    intro X hX
    rw [hsim X (fun i => by rcases hX i with hi | hi <;> simpa [hi] using ‹_›)
      (IsApproxMedian X δ)]
    exact hgood X hX
  have hres := one_sub_mul_median_twoValues_le step U' (hnorm.trans hψ₀) (T + 1) out' a₀ a₁ ha
    hn1 hδ₀ hδ₁ hgood' hε
  push_cast at hres
  exact hres

/-- Bounded-error (`ε = 1 / 3`) form of Corollary 1.6 for index-returning algorithms:
`min (1 / δ) |ι| ≤ 432 (T + 1)`. -/
theorem median_index_lower_bound {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (v₀ : V) (read : V → α) (a₀ a₁ : α) (ha : a₀ < a₁)
    (hread₀ : (open Classical in
      measureProb (step a₀ (ket v₀)) (univ.filter fun v => read v = a₀)) = 1)
    (hread₁ : (open Classical in
      measureProb (step a₁ (ket v₀)) (univ.filter fun v => read v = a₁)) = 1)
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (idx : ι × V × W → ι) {δ : ℝ}
    (hn1 : 1 ≤ Fintype.card ι) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hgood : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - (1 / 3 : ℝ) ≤ (open Classical in
      measureProb (runValue step U ψ₀ X T)
        (univ.filter fun p => IsApproxMedian X δ (X (idx p))))) :
    min (1 / δ) (Fintype.card ι) ≤ 432 * ((T : ℝ) + 1) := by
  have hcore := one_sub_mul_median_index_le step v₀ read a₀ a₁ ha hread₀ hread₁ U hψ₀ T idx
    hn1 hδ₀ hδ₁ hgood (by norm_num)
  have hnn : 0 ≤ min (1 / δ) (Fintype.card ι) := by positivity
  linarith [le_eighteen_mul_of_one_sub_mul_le hnn hcore]

/-- Specialization of `one_sub_mul_median_index_le` to permutation oracles `permStep π`. -/
theorem one_sub_mul_median_perm_index_le {ι V W α : Type*}
    [Fintype ι] [Fintype V] [Fintype W] [LinearOrder α]
    (π : α → Equiv.Perm V) (v₀ : V) (a₀ a₁ : α) (ha : a₀ < a₁) (hne : π a₀ v₀ ≠ π a₁ v₀)
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (idx : ι × V × W → ι) {δ ε : ℝ}
    (hn1 : 1 ≤ Fintype.card ι) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hgood : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - ε ≤ (open Classical in
      measureProb (runValue (permStep π) U ψ₀ X T)
        (univ.filter fun p => IsApproxMedian X δ (X (idx p)))))
    (hε : 2 * ε ≤ 1) :
    (1 - 2 * √(ε * (1 - ε))) * min (1 / δ) (Fintype.card ι) ≤ 24 * ((T : ℝ) + 1) := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨U', ψ₀', out', hnorm, hsim⟩ := exists_sim_index_to_value_perm π v₀ a₀ a₁ hne U ψ₀ T idx
  have hgood' : ∀ X : ι → α, (∀ i, X i = a₀ ∨ X i = a₁) → 1 - ε ≤ (open Classical in
      measureProb (runValue (permStep π) U' ψ₀' X (T + 1))
        (univ.filter fun q => IsApproxMedian X δ (out' q))) := by
    intro X hX
    rw [hsim X hX (IsApproxMedian X δ)]
    exact hgood X hX
  have hres := one_sub_mul_median_twoValues_le (permStep π) U' (hnorm.trans hψ₀) (T + 1) out' a₀ a₁
    ha hn1 hδ₀ hδ₁ hgood' hε
  push_cast at hres
  exact hres

end Median

end Cslib.Quantum
