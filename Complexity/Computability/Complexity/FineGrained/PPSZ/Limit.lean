/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.PPSZ.Unique
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# PPSZ for unique 3-SAT: the limit of the depth recursion

For `k = 3` the depth recursion of PPSZ reads `Q 3 (d + 1) r = (r + (1 - r) * Q 3 d r) ^ 2`. For
fixed `r ∈ [0, 1]` the sequence `Q 3 d r` increases with `d` and is bounded by every nonnegative
fixed point of `x ↦ (r + (1 - r) * x) ^ 2`. The fixed points are the roots of
`((1 - r) ^ 2 * x - r ^ 2) * (x - 1)`, so the smallest one is `R3 r = (r / (1 - r)) ^ 2` for
`r < 1 / 2` and `R3 r = 1` otherwise (`R3_eq`, `R3_le_of_eq`), and `Q 3 d r` tends to it
(`tendsto_Q_three`) [Paturi, Pudlák, Saks, Zane, Claim 1 (p. 352) and
p. 354][PaturiPudlakSaksZane2005]. Its integral is `∫₀¹ R3 = 2 - 2 log 2` (`integral_R3`), and
by dominated convergence `qbar 3 d` tends to it (`tendsto_qbar_three`). Throughout, `log` is the
natural logarithm `Real.log`.

Combined with the bound `2^{-(1 - qbar 3 h) n}` for unique 3-SAT (`round_success_of_unique`),
this gives, for every `ε > 0`, a bound `w` such that one round of PPSZ with w-implication outputs
the unique satisfying assignment of every 3-CNF formula on `n` variables with probability at least
`2^{-(2 log 2 - 1 + ε) n}` (`round_success_unique_three_limit`). Here `2 log 2 - 1 ≈ 0.386`; this
is the `ε`-form of [Paturi, Pudlák, Saks, Zane, Theorem 1(ii)][PaturiPudlakSaksZane2005] for
`k = 3`, with w-implication in place of bounded resolution.

## Main definitions

* `Cslib.Complexity.PPSZ.R3`: the limit `R3 r` of `Q 3 d r` as `d → ∞`.

## Main results

* `Cslib.Complexity.PPSZ.R3_le_of_eq`: `R3 r` is the smallest fixed point of the recursion step.
* `Cslib.Complexity.PPSZ.tendsto_Q_three`: `Q 3 d r → R3 r` for `r ∈ [0, 1]`.
* `Cslib.Complexity.PPSZ.integral_R3`: `∫₀¹ R3 r dr = 2 - 2 log 2`.
* `Cslib.Complexity.PPSZ.tendsto_qbar_three`: `qbar 3 d → 2 - 2 log 2`.
* `Cslib.Complexity.PPSZ.round_success_unique_three_limit`: for every `ε > 0` there is `w` such
  that one round of PPSZ with w-implication solves unique 3-SAT with probability at least
  `2^{-(2 log 2 - 1 + ε) n}`.

## References

* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
* [D. Scheder, *PPSZ is better than you think*][Scheder2021]
-/

@[expose] public section

namespace Cslib.Complexity.PPSZ

open Cslib.Logic.PL Finset Filter Topology

/-! ### The limit of the depth recursion -/

/-- **The limit of the depth recursion for `k = 3`**
[Paturi, Pudlák, Saks, Zane, Claim 1 and p. 354][PaturiPudlakSaksZane2005]:
`R3 r = (r / (1 - r)) ^ 2` for `r < 1 / 2` and `R3 r = 1` otherwise. For `r ∈ [0, 1]` it is the
smallest root of `R = (r + (1 - r) * R) ^ 2` (`R3_eq`, `R3_le_of_eq`); the roots are `1` and, for
`r < 1`, `(r / (1 - r)) ^ 2`. -/
noncomputable def R3 (r : ℝ) : ℝ := if r < 1 / 2 then (r / (1 - r)) ^ 2 else 1

variable {r : ℝ}

/-- Both formulas give `1` at `r = 1 / 2`, so `R3 r = (r / (1 - r)) ^ 2` for `r ≤ 1 / 2`. -/
theorem R3_of_le (hr : r ≤ 1 / 2) : R3 r = (r / (1 - r)) ^ 2 := by
  unfold R3
  split_ifs with h
  · rfl
  · rw [le_antisymm hr (not_lt.1 h)]
    norm_num

/-- `R3 r = 1` for `r ≥ 1 / 2`. -/
theorem R3_of_ge (hr : 1 / 2 ≤ r) : R3 r = 1 := by
  unfold R3
  split_ifs with h
  · exact absurd h (not_lt.2 hr)
  · rfl

/-- `R3` is nonnegative. -/
theorem R3_nonneg (r : ℝ) : 0 ≤ R3 r := by
  unfold R3
  split_ifs
  · positivity
  · exact zero_le_one

/-- For `0 ≤ r < 1 / 2`, `R3 r < 1`. -/
theorem R3_lt_one (hr0 : 0 ≤ r) (hr : r < 1 / 2) : R3 r < 1 := by
  rw [R3_of_le hr.le]
  have h : r / (1 - r) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  exact pow_lt_one₀ (div_nonneg hr0 (by linarith)) h two_ne_zero

/-- `R3 r` is a fixed point of the recursion step. -/
theorem R3_eq (r : ℝ) : (r + (1 - r) * R3 r) ^ 2 = R3 r := by
  rcases lt_or_ge r (1 / 2) with h | h
  · rw [R3_of_le h.le]
    have : 1 - r ≠ 0 := by linarith
    field_simp
    ring
  · rw [R3_of_ge h]
    ring

/-- The fixed points of the recursion step are the roots of
`((1 - r) ^ 2 * x - r ^ 2) * (x - 1)`. -/
private theorem sq_add_one_sub_mul_sub (r x : ℝ) :
    (r + (1 - r) * x) ^ 2 - x = ((1 - r) ^ 2 * x - r ^ 2) * (x - 1) := by
  ring

/-- `R3 r` is the smallest fixed point of the recursion step on `[0, 1]`. -/
theorem R3_le_of_eq (hr : r ∈ Set.Icc (0 : ℝ) 1) {x : ℝ} (hx : (r + (1 - r) * x) ^ 2 = x) :
    R3 r ≤ x := by
  have h := sq_add_one_sub_mul_sub r x
  rw [hx, sub_self, eq_comm, mul_eq_zero] at h
  rcases lt_or_ge r (1 / 2) with hr2 | hr2
  · rcases h with h | h
    · have : 0 < (1 - r) ^ 2 := by
        have : 0 < 1 - r := by linarith
        positivity
      rw [R3_of_le hr2.le, div_pow, div_le_iff₀ this]
      linarith
    · linarith [R3_lt_one hr.1 hr2, sub_eq_zero.1 h]
  · rw [R3_of_ge hr2]
    rcases h with h | h
    · have h1 : (1 - r) ^ 2 * (1 - x) = 1 - 2 * r := by linear_combination -h
      by_contra hlt
      have : 0 ≤ (1 - r) ^ 2 * (1 - x) := mul_nonneg (sq_nonneg _) (by linarith)
      have hr' : r = 1 / 2 := by linarith
      rw [hr'] at h1
      linarith
    · linarith [sub_eq_zero.1 h]

/-- `Q 3 d r ≤ R3 r` on `[0, 1]`: the recursion step is monotone on `[0, ∞)` and fixes `R3 r`. -/
theorem Q_three_le_R3 {d : ℕ} (hr : r ∈ Set.Icc (0 : ℝ) 1) : Q 3 d r ≤ R3 r := by
  induction d with
  | zero => exact R3_nonneg r
  | succ d ih =>
    rw [Q_succ, ← R3_eq r]
    exact pow_le_pow_left₀ (add_one_sub_mul_mem_Icc hr (Q_mem_Icc hr)).1
      ((add_le_add_iff_left r).2 (mul_le_mul_of_nonneg_left ih (sub_nonneg.2 hr.2))) _

/-- A fixed point of the recursion step that is at most `R3 r` equals `R3 r`. -/
theorem eq_R3_of_eq (hr : r ∈ Set.Icc (0 : ℝ) 1) {x : ℝ} (hx : (r + (1 - r) * x) ^ 2 = x)
    (hxR : x ≤ R3 r) : x = R3 r :=
  le_antisymm hxR (R3_le_of_eq hr hx)

/-- **`Q 3 d r` tends to `R3 r`** [Paturi, Pudlák, Saks, Zane, p. 352 and
p. 354][PaturiPudlakSaksZane2005]: for `r ∈ [0, 1]` the sequence increases and is bounded by
`1`, so it converges; its limit is a fixed point of the recursion step at most `R3 r`, hence equal
to `R3 r`. -/
theorem tendsto_Q_three (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun d => Q 3 d r) atTop (𝓝 (R3 r)) := by
  have hbdd : BddAbove (Set.range fun d => Q 3 d r) := ⟨1, by
    rintro _ ⟨d, rfl⟩
    exact Q_le_one hr⟩
  have hT := tendsto_atTop_ciSup (monotone_Q hr) hbdd
  have hfix : (r + (1 - r) * ⨆ d, Q 3 d r) ^ 2 = ⨆ d, Q 3 d r := by
    refine tendsto_nhds_unique ?_ (hT.comp (tendsto_add_atTop_nat 1))
    exact ((hT.const_mul (1 - r)).const_add r).pow 2
  rwa [← eq_R3_of_eq hr hfix (ciSup_le fun _ => Q_three_le_R3 hr)]

/-! ### The integral of the limit -/

/-- `x ↦ (x / (1 - x)) ^ 2` is continuous on `[0, 1 / 2]`. -/
private theorem continuousOn_div_one_sub_sq :
    ContinuousOn (fun x : ℝ => (x / (1 - x)) ^ 2) (Set.uIcc 0 (1 / 2)) := by
  refine (continuousOn_id.div (by fun_prop) fun x hx => ?_).pow 2
  rw [Set.uIcc_of_le (by norm_num)] at hx
  linarith [hx.2]

/-- **The integral of the limit** [Paturi, Pudlák, Saks, Zane, p. 354][PaturiPudlakSaksZane2005]:
`∫₀¹ R3 r dr = 2 - 2 log 2`, since `1 / (1 - r) + 2 log (1 - r) + r` is an antiderivative of
`(r / (1 - r)) ^ 2`. -/
theorem integral_R3 : ∫ r in (0 : ℝ)..1, R3 r = 2 - 2 * Real.log 2 := by
  have hI : Set.uIcc (0 : ℝ) (1 / 2) = Set.Icc 0 (1 / 2) := Set.uIcc_of_le (by norm_num)
  have hJ : Set.uIcc (1 / 2 : ℝ) 1 = Set.Icc (1 / 2) 1 := Set.uIcc_of_le (by norm_num)
  have h1 : Set.EqOn R3 (fun x => (x / (1 - x)) ^ 2) (Set.uIcc 0 (1 / 2)) := fun x hx =>
    R3_of_le (hI ▸ hx).2
  have h2 : Set.EqOn R3 (fun _ => 1) (Set.uIcc (1 / 2) 1) := fun x hx => R3_of_ge (hJ ▸ hx).1
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) (1 / 2),
      HasDerivAt (fun y => (1 - y)⁻¹ + 2 * Real.log (1 - y) + y) ((x / (1 - x)) ^ 2) x := by
    intro x hx
    have hx1 : 1 - x ≠ 0 := by linarith [(hI ▸ hx).2]
    have hd : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    refine (((hd.inv hx1).add ((hd.log hx1).const_mul 2)).add (hasDerivAt_id' x)).congr_deriv ?_
    field_simp
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
      ((continuousOn_div_one_sub_sq.congr h1).intervalIntegrable)
      ((continuousOn_const.congr h2).intervalIntegrable),
    intervalIntegral.integral_congr h1, intervalIntegral.integral_congr h2,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      continuousOn_div_one_sub_sq.intervalIntegrable]
  have hlog : Real.log (1 - 1 / 2) = -Real.log 2 := by
    rw [← Real.log_inv]
    norm_num
  rw [hlog, intervalIntegral.integral_const, smul_eq_mul, sub_zero, Real.log_one]
  ring

/-! ### The limit of `qbar 3` and unique 3-SAT -/

/-- **`qbar 3 d` tends to `2 - 2 log 2`**, by dominated convergence from `tendsto_Q_three` and
`integral_R3` [Paturi, Pudlák, Saks, Zane, Lemma 8 and p. 354][PaturiPudlakSaksZane2005]. -/
theorem tendsto_qbar_three : Tendsto (qbar 3) atTop (𝓝 (2 - 2 * Real.log 2)) := by
  rw [← integral_R3]
  have hmem : ∀ x ∈ Set.uIoc (0 : ℝ) 1, x ∈ Set.Icc (0 : ℝ) 1 := fun x hx => by
    rw [Set.uIoc_of_le zero_le_one] at hx
    exact Set.Ioc_subset_Icc_self hx
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
    (Eventually.of_forall fun d => (continuous_Q 3 d).aestronglyMeasurable)
    (Eventually.of_forall fun d => MeasureTheory.ae_of_all _ fun x hx => ?_)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun x hx => tendsto_Q_three (hmem x hx))
  rw [Real.norm_eq_abs, abs_of_nonneg (Q_nonneg (hmem x hx))]
  exact Q_le_one (hmem x hx)

/-- `qbar 3 d ≤ 2 - 2 log 2` for every depth `d`. -/
theorem qbar_three_le (d : ℕ) : qbar 3 d ≤ 2 - 2 * Real.log 2 :=
  monotone_qbar.ge_of_tendsto tendsto_qbar_three d

/-- For every `ε > 0`, some depth `h` has `qbar 3 h ≥ 2 - 2 log 2 - ε`. -/
theorem exists_le_qbar_three {ε : ℝ} (hε : 0 < ε) : ∃ h, 2 - 2 * Real.log 2 - ε ≤ qbar 3 h :=
  ((tendsto_order.1 tendsto_qbar_three).1 _ (by linarith)).exists.imp fun _ => le_of_lt

/-- **PPSZ for unique 3-SAT** [Paturi, Pudlák, Saks, Zane, Theorem 1(ii)][PaturiPudlakSaksZane2005],
[Scheder, Theorem 1.3][Scheder2021], for PPSZ with w-implication. For every `ε > 0` there is a
bound `w` such that, for every `n`, one round of PPSZ with w-implication outputs the unique
satisfying assignment `σ` of any CNF formula `φ` on `n` variables whose clauses have at most `3`
literals with probability at least `2^{-(2 log 2 - 1 + ε) n}`, where `2 log 2 - 1 ≈ 0.386`.

For `k = 3`, [Paturi, Pudlák, Saks, Zane, Theorem 1(ii)][PaturiPudlakSaksZane2005] bounds the
success probability below by `2^{-(1 - μ₃ / 2) n - o(n)}`, where `μ₃ / 2 = 2 - 2 log 2`, so
`1 - μ₃ / 2 = 2 log 2 - 1`; the `o(n)` term comes from its resolution bound `s(n)` growing with
`n`. The form here, `2^{-(2 log 2 - 1 + ε) n}` for every `ε > 0` with `w` depending only on `ε`,
is the `ε`-form of that bound. Letting `w` grow slowly with `n` would turn it into a lower bound
`2^{-(2 log 2 - 1) n - o(n)}`, uniformly over all such formulas; that form is not formalized here.
The paper uses `s`-bounded resolution in place of w-implication; the per-variable analysis is the
same [Scheder, p. 3][Scheder2021]. -/
theorem round_success_unique_three_limit :
    ∀ ε > 0, ∃ w : ℕ, ∀ (n : ℕ) (φ : CNF (Fin n)) (σ : Fin n → Bool), φ.eval σ = true →
      (∀ τ, φ.eval τ = true → τ = σ) → (∀ c ∈ φ, c.length ≤ 3) →
      (2 : ℝ) ^ (-((2 * Real.log 2 - 1 + ε) * n)) ≤ ((round φ w) fun x => some (σ x)).toReal := by
  intro ε hε
  obtain ⟨h, hh⟩ := exists_le_qbar_three hε
  refine ⟨∑ i ∈ range h, (3 - 1) ^ i, fun n φ σ hσ huniq hlen => ?_⟩
  refine le_trans ?_ (round_success_of_unique hσ huniq hlen le_rfl)
  exact Real.rpow_le_rpow_of_exponent_le one_le_two
    (neg_le_neg (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)))

end Cslib.Complexity.PPSZ
