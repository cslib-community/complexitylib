/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.PPSZ.Limit
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# PPSZ for unique k-SAT: the limit of the depth recursion for general `k`

For `r ∈ [0, 1]` the depth recursion `Q k (d + 1) r = (r + (1 - r) * Q k d r) ^ (k - 1)` increases
with `d` and is bounded by `1`. Its limit `R k r` is the smallest nonnegative fixed point of
`x ↦ (r + (1 - r) * x) ^ (k - 1)` (`tendsto_Q`, `isLeast_R`). On `[0, 1)` the fixed-point
equation can be solved for `r`: `r = S k t` with `S k t = (t ^ (1 / (k - 1)) - t) / (1 - t)`
(`S_R`, `R_S`). For `k ≥ 3`, `R k = 1` on `[(k - 2) / (k - 1), 1]` and `R k` is a strictly
increasing continuous bijection from `[0, (k - 2) / (k - 1))` onto `[0, 1)` with inverse `S k`
[Paturi, Pudlák, Saks, Zane, Claim 1 (p. 352)][PaturiPudlakSaksZane2005].

The integral of the limit is `∫₀¹ R k = ∫₀¹ (1 - S k) = μ_k / (k - 1)`, where
`μ_k = ∑_{j ≥ 1} 1 / (j (j + 1 / (k - 1)))` (`integral_R`); the first equality is the layer-cake
formula, and the second integrates `1 - S k t = ∑_{i ≥ 0} (t ^ i - t ^ (i + 1 / (k - 1)))` term by
term [Paturi, Pudlák, Saks, Zane, p. 354][PaturiPudlakSaksZane2005]. By dominated convergence
`qbar k d → μ_k / (k - 1)` (`tendsto_qbar`). Combined with the bound `2^{-(1 - qbar k h) n}` for
unique k-SAT (`round_success_of_unique`), this gives, for every `ε > 0`, a bound `w` such that one
round of PPSZ with w-implication outputs the unique satisfying assignment of every k-CNF formula
on `n` variables with probability at least `2^{-(1 - μ_k / (k - 1) + ε) n}`
(`round_success_unique_limit`).

For `k = 3` the limit is the function `R3` of
`Complexity.Computability.Complexity.FineGrained.PPSZ.Limit` (`R_three`), and comparing the two
integrals gives `μ_3 = 4 - 4 log 2` (`mu_three`), that is
`∑_{j ≥ 1} 1 / (j (2 j + 1)) = 2 - 2 log 2` (`tsum_three`).

## Main definitions

* `Cslib.Complexity.PPSZ.R`: the limit `R k r` of `Q k d r` as `d → ∞`.
* `Cslib.Complexity.PPSZ.S`: the inverse `S k t = (t ^ (1 / (k - 1)) - t) / (1 - t)` of `R k`.
* `Cslib.Complexity.PPSZ.mu`: the constant `μ_k = ∑_{j ≥ 1} 1 / (j (j + 1 / (k - 1)))`.

## Main results

* `Cslib.Complexity.PPSZ.tendsto_Q`, `Cslib.Complexity.PPSZ.isLeast_R`: `Q k d r → R k r`, the
  smallest nonnegative fixed point of the recursion step.
* `Cslib.Complexity.PPSZ.S_R`, `Cslib.Complexity.PPSZ.R_S`, `Cslib.Complexity.PPSZ.R_eq_one`,
  `Cslib.Complexity.PPSZ.strictMonoOn_R`, `Cslib.Complexity.PPSZ.continuousOn_R`: Claim 1 of the
  paper.
* `Cslib.Complexity.PPSZ.integral_R`: `∫₀¹ R k r dr = μ_k / (k - 1)`.
* `Cslib.Complexity.PPSZ.mu_div_eq_tsum`: `μ_k / (k - 1) = ∑_{j ≥ 1} 1 / (j ((k - 1) j + 1))`.
* `Cslib.Complexity.PPSZ.tendsto_qbar`: `qbar k d → μ_k / (k - 1)`.
* `Cslib.Complexity.PPSZ.round_success_unique_limit`: for every `ε > 0` there is `w` such that one
  round of PPSZ with w-implication solves unique k-SAT with probability at least
  `2^{-(1 - μ_k / (k - 1) + ε) n}`.
* `Cslib.Complexity.PPSZ.mu_three`: `μ_3 = 4 - 4 log 2`.

## References

* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
* [D. Scheder, *PPSZ is better than you think*][Scheder2021]
-/

@[expose] public section

namespace Cslib.Complexity.PPSZ

open Cslib.Logic.PL Filter Topology MeasureTheory Set

variable {k d : ℕ} {r t x : ℝ}

/-! ### The limit of the depth recursion -/

/-- **The limit of the depth recursion**
[Paturi, Pudlák, Saks, Zane, p. 352][PaturiPudlakSaksZane2005]:
`R k r = sup_d Q k d r`. For `r ∈ [0, 1]` it is the limit of `Q k d r` as `d → ∞` (`tendsto_Q`)
and the smallest nonnegative fixed point of `x ↦ (r + (1 - r) * x) ^ (k - 1)` (`isLeast_R`), which
is how the paper defines it. Outside `[0, 1]` the value is not meaningful. -/
noncomputable def R (k : ℕ) (r : ℝ) : ℝ := ⨆ d, Q k d r

/-- If `x ≥ 0` is mapped below itself by the recursion step, then it bounds every `Q k d r`. -/
theorem Q_le_of_le (hr : r ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x)
    (hfx : (r + (1 - r) * x) ^ (k - 1) ≤ x) : Q k d r ≤ x := by
  induction d with
  | zero => exact hx
  | succ d ih =>
    rw [Q_succ]
    refine le_trans (pow_le_pow_left₀ (add_one_sub_mul_mem_Icc hr (Q_mem_Icc hr)).1 ?_ _) hfx
    exact (add_le_add_iff_left r).2 (mul_le_mul_of_nonneg_left ih (sub_nonneg.2 hr.2))

/-- The depth recursion is bounded on `[0, 1]`. -/
theorem bddAbove_range_Q (hr : r ∈ Icc (0 : ℝ) 1) : BddAbove (range fun d => Q k d r) :=
  ⟨1, by
    rintro _ ⟨d, rfl⟩
    exact Q_le_one hr⟩

/-- Each `Q k d r` is at most the limit. -/
theorem Q_le_R (hr : r ∈ Icc (0 : ℝ) 1) (d : ℕ) : Q k d r ≤ R k r :=
  le_ciSup (bddAbove_range_Q hr) d

/-- `R` is nonnegative on `[0, 1]`. -/
theorem R_nonneg (hr : r ∈ Icc (0 : ℝ) 1) : 0 ≤ R k r := Q_le_R hr 0

/-- `R` is at most `1` on `[0, 1]`. -/
theorem R_le_one (hr : r ∈ Icc (0 : ℝ) 1) : R k r ≤ 1 := ciSup_le fun _ => Q_le_one hr

/-- `R` takes values in `[0, 1]` on `[0, 1]`. -/
theorem R_mem_Icc (hr : r ∈ Icc (0 : ℝ) 1) : R k r ∈ Icc (0 : ℝ) 1 := ⟨R_nonneg hr, R_le_one hr⟩

/-- **`Q k d r` tends to `R k r`** [Paturi, Pudlák, Saks, Zane, p. 352][PaturiPudlakSaksZane2005]:
for `r ∈ [0, 1]` the sequence increases and is bounded by `1`. -/
theorem tendsto_Q (hr : r ∈ Icc (0 : ℝ) 1) : Tendsto (fun d => Q k d r) atTop (𝓝 (R k r)) :=
  tendsto_atTop_ciSup (monotone_Q hr) (bddAbove_range_Q hr)

/-- `R k r` is a fixed point of the recursion step. -/
theorem R_eq (hr : r ∈ Icc (0 : ℝ) 1) : (r + (1 - r) * R k r) ^ (k - 1) = R k r := by
  have hT := tendsto_Q (k := k) hr
  refine tendsto_nhds_unique ?_ (hT.comp (tendsto_add_atTop_nat 1))
  exact ((hT.const_mul (1 - r)).const_add r).pow (k - 1)

/-- If `x ≥ 0` is mapped below itself by the recursion step, then `R k r ≤ x`. -/
theorem R_le_of_le (hr : r ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x)
    (hfx : (r + (1 - r) * x) ^ (k - 1) ≤ x) : R k r ≤ x :=
  ciSup_le fun _ => Q_le_of_le hr hx hfx

/-- **`R k r` is the smallest nonnegative fixed point** of the recursion step, the definition of
[Paturi, Pudlák, Saks, Zane, p. 352][PaturiPudlakSaksZane2005]. -/
theorem isLeast_R (hr : r ∈ Icc (0 : ℝ) 1) :
    IsLeast {x | 0 ≤ x ∧ (r + (1 - r) * x) ^ (k - 1) = x} (R k r) :=
  ⟨⟨R_nonneg hr, R_eq hr⟩, fun _ hx => R_le_of_le hr hx.1 hx.2.le⟩

/-- `R k` is monotone on `[0, 1]`. -/
theorem monotoneOn_R : MonotoneOn (R k) (Icc 0 1) := fun _ hr _ hs hrs =>
  ciSup_mono (bddAbove_range_Q hs) fun _ => Q_le_Q_of_le hr.1 hrs hs.2

/-- `R k r ≤ x` if and only if some `y ∈ [0, x]` is mapped below itself by the recursion step. -/
theorem R_le_iff (hr : r ∈ Icc (0 : ℝ) 1) :
    R k r ≤ x ↔ ∃ y ∈ Icc 0 x, (r + (1 - r) * y) ^ (k - 1) ≤ y :=
  ⟨fun h => ⟨R k r, ⟨R_nonneg hr, h⟩, (R_eq hr).le⟩,
    fun ⟨_, hy, hfy⟩ => (R_le_of_le hr hy.1 hfy).trans hy.2⟩

/-! ### The inverse of the limit -/

/-- **The inverse of the limit** [Paturi, Pudlák, Saks, Zane, p. 352][PaturiPudlakSaksZane2005]:
`S k t = (t ^ (1 / (k - 1)) - t) / (1 - t)`. Solving the fixed-point equation
`t = (r + (1 - r) * t) ^ (k - 1)` with `t ∈ [0, 1)` for `r` gives `r = S k t`
(`pow_add_one_sub_mul_eq_self_iff`). The paper sets `S k 1 = (k - 2) / (k - 1)`, the limit at `1`;
here `S k 1 = 0`, which changes no statement below. -/
noncomputable def S (k : ℕ) (t : ℝ) : ℝ := (t ^ (1 / ((k : ℝ) - 1)) - t) / (1 - t)

/-- The constant `μ_k = ∑_{j ≥ 1} 1 / (j (j + 1 / (k - 1)))` of
[Paturi, Pudlák, Saks, Zane, p. 342][PaturiPudlakSaksZane2005], indexed from `j = 0` here. The
savings of PPSZ on unique k-SAT are `μ_k / (k - 1)` (`round_success_unique_limit`). The paper
defines `μ_k` only for `k ≥ 2`; for `k ≤ 1` the value `mu k` is a junk value. -/
noncomputable def mu (k : ℕ) : ℝ :=
  ∑' j : ℕ, 1 / (((j : ℝ) + 1) * ((j : ℝ) + 1 + 1 / ((k : ℝ) - 1)))

private theorem two_le_cast (hk : 2 ≤ k) : (2 : ℝ) ≤ k := by exact_mod_cast hk

private theorem one_div_cast_sub_one (hk : 2 ≤ k) : 1 / ((k : ℝ) - 1) = ((k - 1 : ℕ) : ℝ)⁻¹ := by
  rw [Nat.cast_sub (by omega), Nat.cast_one, one_div]

private theorem exponent_pos (hk : 2 ≤ k) : 0 < 1 / ((k : ℝ) - 1) :=
  one_div_pos.2 (by linarith [two_le_cast hk])

private theorem exponent_le_one (hk : 2 ≤ k) : 1 / ((k : ℝ) - 1) ≤ 1 := by
  rw [div_le_one (by linarith [two_le_cast hk])]
  linarith [two_le_cast hk]

private theorem rpow_one_div_pow (hk : 2 ≤ k) (ht : 0 ≤ t) :
    (t ^ (1 / ((k : ℝ) - 1))) ^ (k - 1) = t := by
  rw [one_div_cast_sub_one hk]
  exact Real.rpow_inv_natCast_pow ht (by omega)

/-- `S k` is nonnegative on `[0, 1)`. -/
theorem S_nonneg (hk : 2 ≤ k) (ht : t ∈ Ico (0 : ℝ) 1) : 0 ≤ S k t :=
  div_nonneg (sub_nonneg.2 (Real.self_le_rpow_of_le_one ht.1 ht.2.le (exponent_le_one hk)))
    (sub_nonneg.2 ht.2.le)

/-- **The fixed-point inequality** (original): for `t ∈ [0, 1)`, the recursion step maps `t` below
itself if and only if `r ≤ S k t`. -/
theorem pow_add_one_sub_mul_le_self_iff (hk : 2 ≤ k) (hr : r ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Ico (0 : ℝ) 1) :
    (r + (1 - r) * t) ^ (k - 1) ≤ t ↔ r ≤ S k t := by
  have hu0 : 0 ≤ t ^ (1 / ((k : ℝ) - 1)) := Real.rpow_nonneg ht.1 _
  have hb : 0 ≤ r + (1 - r) * t := (add_one_sub_mul_mem_Icc hr ⟨ht.1, ht.2.le⟩).1
  have h1t : 0 < 1 - t := sub_pos.2 ht.2
  rw [show (r + (1 - r) * t) ^ (k - 1) ≤ t ↔
      (r + (1 - r) * t) ^ (k - 1) ≤ (t ^ (1 / ((k : ℝ) - 1))) ^ (k - 1) by
      rw [rpow_one_div_pow hk ht.1],
    pow_le_pow_iff_left₀ hb hu0 (by omega), S, le_div_iff₀ h1t]
  constructor <;> intro h <;> linarith

/-- **The fixed-point equation solved for `r`** [Paturi, Pudlák, Saks, Zane, proof of Claim 1
(p. 352)][PaturiPudlakSaksZane2005]: for `t ∈ [0, 1)`, `t` is a fixed point of the recursion step
if and only if `r = S k t`. -/
theorem pow_add_one_sub_mul_eq_self_iff (hk : 2 ≤ k) (hr : r ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Ico (0 : ℝ) 1) :
    (r + (1 - r) * t) ^ (k - 1) = t ↔ r = S k t := by
  have hu0 : 0 ≤ t ^ (1 / ((k : ℝ) - 1)) := Real.rpow_nonneg ht.1 _
  have hb : 0 ≤ r + (1 - r) * t := (add_one_sub_mul_mem_Icc hr ⟨ht.1, ht.2.le⟩).1
  have h1t : 0 < 1 - t := sub_pos.2 ht.2
  rw [show (r + (1 - r) * t) ^ (k - 1) = t ↔
      (r + (1 - r) * t) ^ (k - 1) = (t ^ (1 / ((k : ℝ) - 1))) ^ (k - 1) by
      rw [rpow_one_div_pow hk ht.1],
    pow_left_inj₀ hb hu0 (by omega), S, eq_div_iff h1t.ne']
  constructor <;> intro h <;> linarith

private theorem one_le_geom_sum (hk : 2 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    1 ≤ ∑ i ∈ Finset.range (k - 1), u ^ i :=
  calc (1 : ℝ) = u ^ 0 := (pow_zero u).symm
    _ ≤ _ := Finset.single_le_sum (fun i _ => pow_nonneg hu i) (Finset.mem_range.2 (by omega))

/-- `1 - S k t = 1 / ∑_{i < k - 1} u ^ i` with `u = t ^ (1 / (k - 1))`, for `t ∈ [0, 1)`. -/
private theorem one_sub_S (hk : 2 ≤ k) (ht : t ∈ Ico (0 : ℝ) 1) :
    1 - S k t = 1 / ∑ i ∈ Finset.range (k - 1), (t ^ (1 / ((k : ℝ) - 1))) ^ i := by
  have hpow := rpow_one_div_pow hk ht.1
  have hu0 : 0 ≤ t ^ (1 / ((k : ℝ) - 1)) := Real.rpow_nonneg ht.1 _
  have hu1 : t ^ (1 / ((k : ℝ) - 1)) < 1 := Real.rpow_lt_one ht.1 ht.2 (exponent_pos hk)
  have hP := one_le_geom_sum hk hu0
  rw [S]
  generalize t ^ (1 / ((k : ℝ) - 1)) = u at hpow hu0 hu1 hP ⊢
  have hg := geom_sum_mul_neg u (k - 1)
  rw [hpow] at hg
  have ht' : t = 1 - (∑ i ∈ Finset.range (k - 1), u ^ i) * (1 - u) := by linarith
  subst ht'
  rw [show 1 - (1 - (∑ i ∈ Finset.range (k - 1), u ^ i) * (1 - u)) =
    (∑ i ∈ Finset.range (k - 1), u ^ i) * (1 - u) by ring]
  have h1u : 1 - u ≠ 0 := (sub_pos.2 hu1).ne'
  have hP0 : ∑ i ∈ Finset.range (k - 1), u ^ i ≠ 0 := (zero_lt_one.trans_le hP).ne'
  field_simp
  ring

/-- `S k` is monotone on `[0, 1)`. -/
theorem monotoneOn_S (hk : 2 ≤ k) : MonotoneOn (S k) (Ico 0 1) := by
  intro t ht t' ht' htt'
  have h := one_sub_S hk ht
  have h' := one_sub_S hk ht'
  have hu0 : 0 ≤ t ^ (1 / ((k : ℝ) - 1)) := Real.rpow_nonneg ht.1 _
  have hle : ∑ i ∈ Finset.range (k - 1), (t ^ (1 / ((k : ℝ) - 1))) ^ i ≤
      ∑ i ∈ Finset.range (k - 1), (t' ^ (1 / ((k : ℝ) - 1))) ^ i :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ hu0
      (Real.rpow_le_rpow ht.1 htt' (exponent_pos hk).le) i
  have := one_div_le_one_div_of_le (by linarith [one_le_geom_sum hk hu0]) hle
  linarith

/-- `S k t < 1` on `[0, 1)`. -/
theorem S_lt_one (hk : 2 ≤ k) (ht : t ∈ Ico (0 : ℝ) 1) : S k t < 1 := by
  have h := one_sub_S hk ht
  have hP := one_le_geom_sum hk (Real.rpow_nonneg ht.1 (1 / ((k : ℝ) - 1)))
  have : 0 < 1 / ∑ i ∈ Finset.range (k - 1), (t ^ (1 / ((k : ℝ) - 1))) ^ i :=
    one_div_pos.2 (by linarith)
  linarith

/-- `S k` is strictly monotone on `[0, 1)` for `k ≥ 3`. -/
theorem strictMonoOn_S (hk : 3 ≤ k) : StrictMonoOn (S k) (Ico 0 1) := by
  intro t ht t' ht' htt'
  have h := one_sub_S (k := k) (by omega) ht
  have h' := one_sub_S (k := k) (by omega) ht'
  have hu0 : 0 ≤ t ^ (1 / ((k : ℝ) - 1)) := Real.rpow_nonneg ht.1 _
  have hlt' : t ^ (1 / ((k : ℝ) - 1)) < t' ^ (1 / ((k : ℝ) - 1)) :=
    Real.rpow_lt_rpow ht.1 htt' (exponent_pos (by omega))
  have hlt : ∑ i ∈ Finset.range (k - 1), (t ^ (1 / ((k : ℝ) - 1))) ^ i <
      ∑ i ∈ Finset.range (k - 1), (t' ^ (1 / ((k : ℝ) - 1))) ^ i :=
    Finset.sum_lt_sum (fun i _ => pow_le_pow_left₀ hu0 hlt'.le i)
      ⟨1, Finset.mem_range.2 (by omega), by rwa [pow_one, pow_one]⟩
  have := one_div_lt_one_div_of_lt (by linarith [one_le_geom_sum (k := k) (by omega) hu0]) hlt
  linarith

/-- For `k ≥ 3`, `S k t < (k - 2) / (k - 1)` on `[0, 1)`. -/
theorem S_lt (hk : 3 ≤ k) (ht : t ∈ Ico (0 : ℝ) 1) : S k t < ((k : ℝ) - 2) / ((k : ℝ) - 1) := by
  have h := one_sub_S (k := k) (by omega) ht
  have hu0 : 0 ≤ t ^ (1 / ((k : ℝ) - 1)) := Real.rpow_nonneg ht.1 _
  have hu1 : t ^ (1 / ((k : ℝ) - 1)) < 1 := Real.rpow_lt_one ht.1 ht.2 (exponent_pos (by omega))
  have hlt : ∑ i ∈ Finset.range (k - 1), (t ^ (1 / ((k : ℝ) - 1))) ^ i < (k : ℝ) - 1 := by
    have : ∑ i ∈ Finset.range (k - 1), (1 : ℝ) = (k : ℝ) - 1 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_sub (by omega),
        Nat.cast_one]
    refine lt_of_lt_of_eq (Finset.sum_lt_sum (fun i _ => pow_le_one₀ hu0 hu1.le)
      ⟨1, Finset.mem_range.2 (by omega), by rwa [pow_one]⟩) this
  have := one_div_lt_one_div_of_lt (by linarith [one_le_geom_sum (k := k) (by omega) hu0]) hlt
  have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith [two_le_cast (k := k) (by omega)]
  rw [show ((k : ℝ) - 2) / ((k : ℝ) - 1) = 1 - 1 / ((k : ℝ) - 1) by field_simp; ring]
  linarith

/-- `S k` maps `[0, 1)` into `[0, (k - 2) / (k - 1))` for `k ≥ 3`. -/
theorem S_mem_Ico (hk : 3 ≤ k) (ht : t ∈ Ico (0 : ℝ) 1) :
    S k t ∈ Ico (0 : ℝ) (((k : ℝ) - 2) / ((k : ℝ) - 1)) :=
  ⟨S_nonneg (by omega) ht, S_lt hk ht⟩

private theorem div_lt_one_of_three_le (hk : 3 ≤ k) : ((k : ℝ) - 2) / ((k : ℝ) - 1) < 1 := by
  have : (3 : ℝ) ≤ k := by exact_mod_cast hk
  rw [div_lt_one (by linarith)]
  linarith

private theorem div_nonneg_of_three_le (hk : 3 ≤ k) : 0 ≤ ((k : ℝ) - 2) / ((k : ℝ) - 1) := by
  have : (3 : ℝ) ≤ k := by exact_mod_cast hk
  exact div_nonneg (by linarith) (by linarith)

/-- **`R k r ≤ t` if and only if `r ≤ S k t`** (original), for `r ∈ [0, 1]` and `t ∈ [0, 1)`. -/
theorem R_le_iff_le_S (hk : 2 ≤ k) (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) :
    R k r ≤ t ↔ r ≤ S k t := by
  rw [R_le_iff hr]
  constructor
  · rintro ⟨y, hy, hfy⟩
    have hyI : y ∈ Ico (0 : ℝ) 1 := ⟨hy.1, hy.2.trans_lt ht.2⟩
    exact ((pow_add_one_sub_mul_le_self_iff hk hr hyI).1 hfy).trans
      (monotoneOn_S hk hyI ht hy.2)
  · exact fun h => ⟨t, ⟨ht.1, le_rfl⟩, (pow_add_one_sub_mul_le_self_iff hk hr ht).2 h⟩

/-- `t < R k r` if and only if `S k t < r`, for `r ∈ [0, 1]` and `t ∈ [0, 1)`. -/
theorem lt_R_iff (hk : 2 ≤ k) (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) :
    t < R k r ↔ S k t < r := by
  rw [lt_iff_not_ge, lt_iff_not_ge, R_le_iff_le_S hk hr ht]

/-- **`S k` inverts `R k` where `R k < 1`** [Paturi, Pudlák, Saks, Zane, Claim 1 (p. 352)]
[PaturiPudlakSaksZane2005]: if `R k r < 1`, then
`r = (R k r ^ (1 / (k - 1)) - R k r) / (1 - R k r)`. -/
theorem S_R (hk : 2 ≤ k) (hr : r ∈ Icc (0 : ℝ) 1) (hR : R k r < 1) : S k (R k r) = r :=
  ((pow_add_one_sub_mul_eq_self_iff hk hr ⟨R_nonneg hr, hR⟩).1 (R_eq hr)).symm

/-- **`R k` inverts `S k`** [Paturi, Pudlák, Saks, Zane, Claim 1 (p. 352)]
[PaturiPudlakSaksZane2005]: `R k (S k t) = t` for `t ∈ [0, 1)` and `k ≥ 3`. -/
theorem R_S (hk : 3 ≤ k) (ht : t ∈ Ico (0 : ℝ) 1) : R k (S k t) = t := by
  have hSI : S k t ∈ Icc (0 : ℝ) 1 :=
    ⟨S_nonneg (by omega) ht, (S_lt hk ht).le.trans (div_lt_one_of_three_le hk).le⟩
  refine le_antisymm ((R_le_iff_le_S (by omega) hSI ht).2 le_rfl) (not_lt.1 fun hlt => ?_)
  have hRI : R k (S k t) ∈ Ico (0 : ℝ) 1 := ⟨R_nonneg hSI, hlt.trans ht.2⟩
  exact (strictMonoOn_S hk hRI ht hlt).ne (S_R (by omega) hSI hRI.2)

/-- **`R k = 1` on `[(k - 2) / (k - 1), 1]`** [Paturi, Pudlák, Saks, Zane, Claim 1 (p. 352)]
[PaturiPudlakSaksZane2005], for `k ≥ 3`. -/
theorem R_eq_one (hk : 3 ≤ k) (hr : ((k : ℝ) - 2) / ((k : ℝ) - 1) ≤ r) (hr1 : r ≤ 1) :
    R k r = 1 := by
  have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨(div_nonneg_of_three_le hk).trans hr, hr1⟩
  by_contra hne
  have hlt : R k r < 1 := lt_of_le_of_ne (R_le_one hrI) hne
  have := (R_le_iff_le_S (by omega) hrI ⟨R_nonneg hrI, hlt⟩).1 le_rfl
  linarith [S_lt hk ⟨R_nonneg hrI, hlt⟩]

/-- **`R k < 1` on `[0, (k - 2) / (k - 1))`** [Paturi, Pudlák, Saks, Zane, Claim 1 (p. 352)]
[PaturiPudlakSaksZane2005], for `k ≥ 3`: `S k t` tends to `(k - 2) / (k - 1)` as `t → 1`, so
some `t < 1` has `r ≤ S k t`, hence `R k r ≤ t`. -/
theorem R_lt_one (hk : 3 ≤ k) (hr0 : 0 ≤ r) (hr : r < ((k : ℝ) - 2) / ((k : ℝ) - 1)) :
    R k r < 1 := by
  have hk2 : 2 ≤ k := by omega
  have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨hr0, (hr.trans (div_lt_one_of_three_le hk)).le⟩
  set a := 1 / ((k : ℝ) - 1) with ha
  have hP : ContinuousAt (fun t : ℝ => ∑ i ∈ Finset.range (k - 1), (t ^ a) ^ i) 1 :=
    (continuous_finsetSum (Finset.range (k - 1)) fun i _ =>
      continuous_pow (M := ℝ) i).continuousAt.comp
      (Real.continuousAt_rpow_const 1 a (Or.inl one_ne_zero))
  have hP1 : ∑ i ∈ Finset.range (k - 1), ((1 : ℝ) ^ a) ^ i = (k : ℝ) - 1 := by
    rw [Real.one_rpow]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith [two_le_cast hk2]
  have hlim : Tendsto (fun t : ℝ => 1 - 1 / ∑ i ∈ Finset.range (k - 1), (t ^ a) ^ i) (𝓝 1)
      (𝓝 (((k : ℝ) - 2) / ((k : ℝ) - 1))) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).div hP.tendsto (by rw [hP1]; exact hk1)
    rw [hP1] at h
    convert h.const_sub 1 using 2
    field_simp
    ring
  obtain ⟨t, htr, ht⟩ := (((tendsto_order.1 hlim).1 r hr).filter_mono nhdsWithin_le_nhds |>.and
    (Ioo_mem_nhdsLT (zero_lt_one' ℝ))).exists
  have htI : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have hS : S k t = 1 - 1 / ∑ i ∈ Finset.range (k - 1), (t ^ a) ^ i := by
    rw [← one_sub_S hk2 htI]
    ring
  exact ((R_le_iff_le_S hk2 hrI htI).2 (hS ▸ htr.le)).trans_lt ht.2

/-- **`R k` is strictly increasing on `[0, (k - 2) / (k - 1)]`**
[Paturi, Pudlák, Saks, Zane, Claim 1 (p. 352)][PaturiPudlakSaksZane2005], for `k ≥ 3`. -/
theorem strictMonoOn_R (hk : 3 ≤ k) :
    StrictMonoOn (R k) (Icc 0 (((k : ℝ) - 2) / ((k : ℝ) - 1))) := by
  intro r hr s hs hrs
  have hc1 := div_lt_one_of_three_le hk
  have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1, hr.2.trans hc1.le⟩
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans hc1.le⟩
  have hRr := R_lt_one hk hr.1 (hrs.trans_le hs.2)
  rcases hs.2.lt_or_eq with hs' | hs'
  · refine lt_of_le_of_ne (monotoneOn_R hrI hsI hrs.le) fun heq => hrs.ne ?_
    rw [← S_R (by omega) hrI hRr, ← S_R (by omega) hsI (R_lt_one hk hs.1 hs'), heq]
  · rw [R_eq_one hk hs'.ge hsI.2]
    exact hRr

/-- **`R k` is a bijection from `[0, (k - 2) / (k - 1))` onto `[0, 1)`**
[Paturi, Pudlák, Saks, Zane, Claim 1 (p. 352)][PaturiPudlakSaksZane2005], for `k ≥ 3`; its
inverse is `S k` (`S_R`, `R_S`). -/
theorem bijOn_R (hk : 3 ≤ k) :
    BijOn (R k) (Ico 0 (((k : ℝ) - 2) / ((k : ℝ) - 1))) (Ico 0 1) := by
  have hc1 := div_lt_one_of_three_le hk
  refine ⟨fun r hr => ⟨R_nonneg ⟨hr.1, hr.2.le.trans hc1.le⟩, R_lt_one hk hr.1 hr.2⟩,
    (strictMonoOn_R hk).injOn.mono Ico_subset_Icc_self, fun t ht => ⟨S k t, S_mem_Ico hk ht,
    R_S hk ht⟩⟩

/-- **`R k` is continuous on `[0, 1]`** [Paturi, Pudlák, Saks, Zane, Claim 1 (p. 352)]
[PaturiPudlakSaksZane2005], for `k ≥ 3`: it is monotone and maps `[0, 1]` onto `[0, 1]`. -/
theorem continuousOn_R (hk : 3 ≤ k) : ContinuousOn (R k) (Icc 0 1) := by
  have hc1 := div_lt_one_of_three_le hk
  let f : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun r => ⟨R k r, R_mem_Icc r.2⟩
  have hf : Continuous f := by
    refine Monotone.continuous_of_surjective (fun r s hrs => monotoneOn_R r.2 s.2 hrs) ?_
    rintro ⟨t, ht⟩
    rcases ht.2.lt_or_eq with ht1 | rfl
    · have hS := S_mem_Ico hk ⟨ht.1, ht1⟩
      exact ⟨⟨S k t, hS.1, hS.2.le.trans hc1.le⟩, Subtype.ext (R_S hk ⟨ht.1, ht1⟩)⟩
    · exact ⟨⟨1, zero_le_one, le_rfl⟩, Subtype.ext (R_eq_one hk hc1.le le_rfl)⟩
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp hf

/-! ### The integral of the limit -/

/-- **The layer-cake step** [Paturi, Pudlák, Saks, Zane, p. 354][PaturiPudlakSaksZane2005]:
`∫₀¹ R k r dr = ∫₀¹ (1 - S k t) dt`, since `{r ∈ (0, 1] | t < R k r} = (S k t, 1]` for
`t ∈ (0, 1)` (`lt_R_iff`). -/
theorem integral_R_eq_integral_one_sub_S (hk : 2 ≤ k) :
    ∫ r in (0 : ℝ)..1, R k r = ∫ t in (0 : ℝ)..1, (1 - S k t) := by
  have hmono : MonotoneOn (R k) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact monotoneOn_R
  have hI : IntegrableOn (R k) (Ioc 0 1) := (hmono.intervalIntegrable (μ := volume)).1
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo (f := fun t => 1 - S k t),
    Integrable.integral_eq_integral_meas_lt hI
      (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => R_nonneg (Ioc_subset_Icc_self hr)),
    ← Ioi_inter_Iio, ← setIntegral_indicator measurableSet_Iio]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [measureReal_restrict_apply' measurableSet_Ioc]
  rcases lt_or_ge t 1 with ht1 | ht1
  · rw [indicator_of_mem (show t ∈ Iio 1 from ht1)]
    have htI : t ∈ Ico (0 : ℝ) 1 := ⟨le_of_lt ht, ht1⟩
    have hS0 := S_nonneg hk htI
    have hS1 : S k t ≤ 1 := (S_lt_one hk htI).le
    rw [show {a | t < R k a} ∩ Ioc 0 1 = Ioc (S k t) 1 from ?_, Real.volume_real_Ioc_of_le hS1]
    ext r
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioc]
    constructor
    · rintro ⟨h, h0, h1⟩
      exact ⟨(lt_R_iff hk ⟨h0.le, h1⟩ htI).1 h, h1⟩
    · rintro ⟨h, h1⟩
      exact ⟨(lt_R_iff hk ⟨hS0.trans h.le, h1⟩ htI).2 h, hS0.trans_lt h, h1⟩
  · rw [indicator_of_notMem (show t ∉ Iio 1 from not_lt.2 ht1),
      show {a | t < R k a} ∩ Ioc 0 1 = ∅ from ?_, measureReal_empty]
    ext r
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioc, mem_empty_iff_false, iff_false]
    rintro ⟨h, h0, h1⟩
    linarith [R_le_one (k := k) ⟨h0.le, h1⟩]

/-- On `[0, 1]`, `∑_{i < N} (t ^ i - t ^ (i + a)) = (∑_{i < N} t ^ i) * (1 - t ^ a)`. -/
private theorem sum_sub_rpow_eq {a : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (N : ℕ) :
    ∑ i ∈ Finset.range N, (t ^ i - t ^ ((i : ℝ) + a)) =
      (∑ i ∈ Finset.range N, t ^ i) * (1 - t ^ a) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.rpow_add' ht (by positivity), Real.rpow_natCast]
  ring

/-- The integral of the partial sums:
`∫₀¹ (t ^ i - t ^ (i + a)) dt = 1 / (i + 1) - 1 / (i + a + 1)`. -/
private theorem integral_sum_sub_rpow {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∫ t in (0 : ℝ)..1, ∑ i ∈ Finset.range N, (t ^ i - t ^ ((i : ℝ) + a)) =
      ∑ i ∈ Finset.range N, (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + a + 1)) := by
  have hrc : ∀ i : ℕ, Continuous fun t : ℝ => t ^ ((i : ℝ) + a) := fun i =>
    Real.continuous_rpow_const (by positivity)
  have hc : ∀ i : ℕ, Continuous fun t : ℝ => t ^ i - t ^ ((i : ℝ) + a) := fun i =>
    (continuous_pow i).sub (hrc i)
  rw [intervalIntegral.integral_finsetSum fun i _ => (hc i).intervalIntegrable 0 1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (-1 : ℝ) < (i : ℝ) + a := by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  rw [intervalIntegral.integral_sub ((continuous_pow i).intervalIntegrable 0 1)
      ((hrc i).intervalIntegrable 0 1), integral_pow, integral_rpow (Or.inl hi), Real.one_rpow,
    Real.zero_rpow (by linarith : (i : ℝ) + a + 1 ≠ 0)]
  simp

/-- **Term-by-term integration** [Paturi, Pudlák, Saks, Zane, p. 354][PaturiPudlakSaksZane2005]:
for `0 < a ≤ 1`, `∫₀¹ (1 - t ^ a) / (1 - t) dt = ∑_{i ≥ 0} (1 / (i + 1) - 1 / (i + a + 1))`, by
expanding `(1 - t ^ a) / (1 - t) = ∑_{i ≥ 0} (t ^ i - t ^ (i + a))`. The paper uses monotone
convergence; here the partial sums are bounded by `1` and dominated convergence applies. -/
private theorem hasSum_integral {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    HasSum (fun i : ℕ => 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + a + 1))
      (∫ t in (0 : ℝ)..1, (1 - t ^ a) / (1 - t)) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun i => sub_nonneg.2
    (one_div_le_one_div_of_le (by positivity) (by linarith))) _).2 ?_
  refine Tendsto.congr (fun N => integral_sum_sub_rpow ha N) ?_
  have hmem : ∀ t ∈ uIoc (0 : ℝ) 1, t ∈ Ioc (0 : ℝ) 1 := fun t ht => by
    rwa [uIoc_of_le zero_le_one] at ht
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
    (Eventually.of_forall fun N => (continuous_finsetSum _ fun i _ => (continuous_pow i).sub
      (Real.continuous_rpow_const (by positivity))).aestronglyMeasurable)
    (Eventually.of_forall fun N => ae_of_all _ fun t ht => ?_) intervalIntegrable_const
    (ae_of_all _ fun t ht => ?_)
  · obtain ⟨ht0, ht1⟩ := hmem t ht
    rw [sum_sub_rpow_eq ha ht0.le]
    have hta : t ≤ t ^ a := Real.self_le_rpow_of_le_one ht0.le ht1 ha1
    have hta1 : t ^ a ≤ 1 := Real.rpow_le_one ht0.le ht1 ha.le
    have hP0 : 0 ≤ ∑ i ∈ Finset.range N, t ^ i :=
      Finset.sum_nonneg fun i _ => pow_nonneg ht0.le i
    have hg := geom_sum_mul_neg t N
    have hle : (∑ i ∈ Finset.range N, t ^ i) * (1 - t ^ a) ≤
        (∑ i ∈ Finset.range N, t ^ i) * (1 - t) :=
      mul_le_mul_of_nonneg_left (by linarith) hP0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hP0 (sub_nonneg.2 hta1))]
    linarith [pow_nonneg ht0.le N]
  · obtain ⟨ht0, ht1⟩ := hmem t ht
    rcases ht1.lt_or_eq with ht1 | rfl
    · have h := ((hasSum_geometric_of_lt_one ht0.le ht1).mul_right (1 - t ^ a)).tendsto_sum_nat
      rw [inv_mul_eq_div] at h
      refine h.congr fun N => ?_
      rw [sum_sub_rpow_eq ha ht0.le, Finset.sum_mul]
    · simp

private theorem sub_one_div_div {a : ℝ} (ha : 0 < a) (j : ℕ) :
    (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + a + 1)) / a = 1 / (((j : ℝ) + 1) * ((j : ℝ) + 1 + a)) := by
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hja : (0 : ℝ) < (j : ℝ) + a + 1 := by positivity
  have hja' : (0 : ℝ) < (j : ℝ) + 1 + a := by positivity
  field_simp
  ring

private theorem hasSum_mu_aux (hk : 2 ≤ k) :
    HasSum (fun j : ℕ => 1 / (((j : ℝ) + 1) * ((j : ℝ) + 1 + 1 / ((k : ℝ) - 1))))
      ((∫ t in (0 : ℝ)..1, (1 - t ^ (1 / ((k : ℝ) - 1))) / (1 - t)) / (1 / ((k : ℝ) - 1))) := by
  have ha := exponent_pos hk
  exact ((hasSum_integral ha (exponent_le_one hk)).div_const _).congr_fun fun j =>
    (sub_one_div_div ha j).symm

/-- The series defining `μ_k` converges for `k ≥ 2`. -/
theorem summable_mu (hk : 2 ≤ k) :
    Summable fun j : ℕ => 1 / (((j : ℝ) + 1) * ((j : ℝ) + 1 + 1 / ((k : ℝ) - 1))) :=
  (hasSum_mu_aux hk).summable

/-- **The integral of `1 - S k`** [Paturi, Pudlák, Saks, Zane, p. 354][PaturiPudlakSaksZane2005]:
`∫₀¹ (1 - S k t) dt = μ_k / (k - 1)` for `k ≥ 2`. On `[0, 1)`,
`1 - S k t = (1 - t ^ (1 / (k - 1))) / (1 - t)`, whose integral is computed term by term. -/
theorem integral_one_sub_S (hk : 2 ≤ k) :
    ∫ t in (0 : ℝ)..1, (1 - S k t) = mu k / ((k : ℝ) - 1) := by
  have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith [two_le_cast hk]
  have hG : ∫ t in (0 : ℝ)..1, (1 - t ^ (1 / ((k : ℝ) - 1))) / (1 - t) =
      mu k / ((k : ℝ) - 1) := by
    rw [mu, (hasSum_mu_aux hk).tsum_eq, div_div, one_div_mul_cancel hk1, div_one]
  rw [← hG, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  rw [S, one_sub_div (sub_pos.2 ht.2).ne']
  ring

/-- **The integral of the limit** [Paturi, Pudlák, Saks, Zane, Lemma 8 and p. 354]
[PaturiPudlakSaksZane2005]: `∫₀¹ R k r dr = μ_k / (k - 1)` for `k ≥ 2`. The paper states it for
`k ≥ 3`. -/
theorem integral_R (hk : 2 ≤ k) : ∫ r in (0 : ℝ)..1, R k r = mu k / ((k : ℝ) - 1) := by
  rw [integral_R_eq_integral_one_sub_S hk, integral_one_sub_S hk]

/-- The equivalent form `μ_k / (k - 1) = ∑_{j ≥ 1} 1 / (j ((k - 1) j + 1))`, indexed from `j = 0`
here. -/
theorem mu_div_eq_tsum (hk : 2 ≤ k) :
    mu k / ((k : ℝ) - 1) =
      ∑' j : ℕ, 1 / (((j : ℝ) + 1) * (((k : ℝ) - 1) * ((j : ℝ) + 1) + 1)) := by
  have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith [two_le_cast hk]
  rw [mu, ← tsum_div_const]
  refine tsum_congr fun j => ?_
  rw [div_div]
  congr 1
  field_simp

/-! ### The limit of `qbar k` and unique k-SAT -/

/-- **`qbar k d` tends to `μ_k / (k - 1)`** for `k ≥ 2`, by dominated convergence from
`tendsto_Q` and `integral_R` [Paturi, Pudlák, Saks, Zane, Lemma 8 and p. 354]
[PaturiPudlakSaksZane2005]. -/
theorem tendsto_qbar (hk : 2 ≤ k) : Tendsto (qbar k) atTop (𝓝 (mu k / ((k : ℝ) - 1))) := by
  rw [← integral_R hk]
  have hmem : ∀ x ∈ uIoc (0 : ℝ) 1, x ∈ Icc (0 : ℝ) 1 := fun x hx => by
    rw [uIoc_of_le zero_le_one] at hx
    exact Ioc_subset_Icc_self hx
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
    (Eventually.of_forall fun d => (continuous_Q k d).aestronglyMeasurable)
    (Eventually.of_forall fun d => ae_of_all _ fun x hx => ?_)
    intervalIntegrable_const
    (ae_of_all _ fun x hx => tendsto_Q (hmem x hx))
  rw [Real.norm_eq_abs, abs_of_nonneg (Q_nonneg (hmem x hx))]
  exact Q_le_one (hmem x hx)

/-- `qbar k d ≤ μ_k / (k - 1)` for every depth `d`. -/
theorem qbar_le_mu_div (hk : 2 ≤ k) (d : ℕ) : qbar k d ≤ mu k / ((k : ℝ) - 1) :=
  monotone_qbar.ge_of_tendsto (tendsto_qbar hk) d

/-- For every `ε > 0`, some depth `h` has `qbar k h ≥ μ_k / (k - 1) - ε`. -/
theorem exists_le_qbar (hk : 2 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ h, mu k / ((k : ℝ) - 1) - ε ≤ qbar k h :=
  ((tendsto_order.1 (tendsto_qbar hk)).1 _ (by linarith)).exists.imp fun _ => le_of_lt

/-- **PPSZ for unique k-SAT** [Paturi, Pudlák, Saks, Zane, Theorem 1(ii)][PaturiPudlakSaksZane2005],
for PPSZ with w-implication. Let `k ≥ 2`. For every `ε > 0`
there is a bound `w` such that, for every `n`, one round of PPSZ with w-implication outputs the
unique satisfying assignment `σ` of any CNF formula `φ` on `n` variables whose clauses have at most
`k` literals with probability at least `2^{-(1 - μ_k / (k - 1) + ε) n}`, where
`μ_k = ∑_{j ≥ 1} 1 / (j (j + 1 / (k - 1)))` (`mu`).

[Paturi, Pudlák, Saks, Zane, Theorem 1(ii)][PaturiPudlakSaksZane2005] states, for `k ≥ 3` and
uniquely satisfiable k-CNF formulas, the lower bound `2^{-(1 - μ_k / (k - 1)) n - o(n)}`; the
`o(n)` term comes from its resolution bound `s(n)` growing with `n`. The form here,
`2^{-(1 - μ_k / (k - 1) + ε) n}` for every `ε > 0` with `w` depending only on `k` and `ε`, is the
`ε`-form of that bound. Letting `w` grow slowly with `n` would turn it into a lower bound
`2^{-(1 - μ_k / (k - 1)) n - o(n)}`, uniformly over all such formulas; that form is not formalized
here. The paper uses `s`-bounded resolution in place of w-implication; the per-variable analysis is
the same [Scheder, p. 3][Scheder2021]. [Scheder, Theorem 1.3][Scheder2021] states the bound with
the constant `s_k := Pr[T finite]` of its infinite-tree analysis, where `s_k = μ_k / (k - 1)`. The
case `k = 2`, where `μ_2 = 1`, is included because the proof covers it. -/
theorem round_success_unique_limit (hk : 2 ≤ k) :
    ∀ ε > 0, ∃ w : ℕ, ∀ (n : ℕ) (φ : CNF (Fin n)) (σ : Fin n → Bool), φ.eval σ = true →
      (∀ τ, φ.eval τ = true → τ = σ) → (∀ c ∈ φ, c.length ≤ k) →
      (2 : ℝ) ^ (-((1 - mu k / ((k : ℝ) - 1) + ε) * n)) ≤
        ((round φ w) fun x => some (σ x)).toReal := by
  intro ε hε
  obtain ⟨h, hh⟩ := exists_le_qbar hk hε
  refine ⟨∑ i ∈ Finset.range h, (k - 1) ^ i, fun n φ σ hσ huniq hlen => ?_⟩
  refine le_trans ?_ (round_success_of_unique hσ huniq hlen le_rfl)
  exact Real.rpow_le_rpow_of_exponent_le one_le_two
    (neg_le_neg (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)))

/-! ### The case `k = 3` -/

/-- For `k = 3` the limit is the explicit function `R3`. -/
theorem R_three (hr : r ∈ Icc (0 : ℝ) 1) : R 3 r = R3 r :=
  tendsto_nhds_unique (tendsto_Q hr) (tendsto_Q_three hr)

/-- **`μ_3 = 4 - 4 log 2`** [Paturi, Pudlák, Saks, Zane, p. 342][PaturiPudlakSaksZane2005], by
comparing `tendsto_qbar` with `tendsto_qbar_three`. -/
theorem mu_three : mu 3 = 4 - 4 * Real.log 2 := by
  have h := tendsto_nhds_unique (tendsto_qbar (k := 3) (by norm_num)) tendsto_qbar_three
  norm_num at h
  linarith

/-- `∑_{j ≥ 1} 1 / (j (2 j + 1)) = 2 - 2 log 2`, indexed from `j = 0` here. -/
theorem tsum_three :
    ∑' j : ℕ, 1 / (((j : ℝ) + 1) * (2 * ((j : ℝ) + 1) + 1)) = 2 - 2 * Real.log 2 := by
  calc ∑' j : ℕ, 1 / (((j : ℝ) + 1) * (2 * ((j : ℝ) + 1) + 1))
      = mu 3 / (((3 : ℕ) : ℝ) - 1) := by
        rw [mu_div_eq_tsum (by norm_num)]
        norm_num
    _ = 2 - 2 * Real.log 2 := by
        rw [mu_three]
        push_cast
        ring

end Cslib.Complexity.PPSZ
