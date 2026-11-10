/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.GameTheory.Congestion.Nonatomic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The Pigou bound for nonatomic selfish routing

A **Pigou-like network** ([Roughgarden2013CS364A], Lecture #11, Definition 3.2) routes `r` units
of traffic over two parallel links, one with latency `c` and one with constant latency `c(r)`.
Routing everything over the first link is a Wardrop equilibrium of cost `r c(r)`, while routing
`x` units over it costs `x c(x) + (r - x) c(r)`. The **Pigou bound** of a class `C` of latency
functions ([Roughgarden2013CS364A], Lecture #11, (2)) is the worst such ratio,

  `α(C) = sup_{c ∈ C} sup_{r ≥ 0} sup_{x ≥ 0} r c(r) / (x c(x) + (r - x) c(r))`,

taken in `ℝ≥0∞` because it may be infinite. The theorem of Roughgarden ([Roughgarden2003],
Theorem 3.8, for latencies with `x c(x)` convex; in the generality used here,
[Roughgarden2013CS364A], Lecture #11, Theorem 3.3, who credits it to [Roughgarden2003] and
[CorreaSchulzStierMoses2004]) says that `α(C)` bounds the price of anarchy of *every* nonatomic
congestion game whose latencies are nonnegative, nondecreasing and in `C`, whatever its network
topology and number of commodities. When `C` also contains the constant functions, Pigou-like
networks show that no smaller bound holds ([Roughgarden2003], Theorem 4.2): the price of anarchy is
independent of the network topology.

For polynomials of degree at most `d` with nonnegative coefficients the Pigou bound is
`(1 - d (d+1)^{-(d+1)/d})⁻¹` ([Roughgarden2003], Proposition 5.1), attained by Pigou's network
with latency `x ^ d`; `d = 1` gives the `4/3` theorem of Roughgarden and Tardos
([RoughgardenTardos2002], Theorem 4.5).

The model is `NonatomicCongestionGame`, whose Wardrop equilibria are defined by the shortest-path
characterization. The sources also assume continuous latencies, which is needed only to match that
characterization with their definition of equilibrium and for the existence of equilibria; the
bounds here hold for every Wardrop flow without it. Lean's `a / 0 = 0` is harmless for the
latencies of the theorems below, which are nonnegative and nondecreasing on `[0, ∞)`: for them a
nonpositive denominator forces `r c(r) = 0`, and such degenerate ratios do not change `α(C)` once
some `c ∈ C` is positive somewhere on `(0, ∞)` (then `α(C) ≥ 1`, `one_le_pigouBound`).

## Main definitions

* `Cslib.GameTheory.pigouRatio`, `Cslib.GameTheory.pigouBound`: the Pigou ratio and the Pigou
  bound `α(C)`.
* `Cslib.GameTheory.polynomialLatencies`: polynomials of degree at most `d` with nonnegative
  coefficients.
* `Cslib.GameTheory.NonatomicCongestionGame.pigouNetwork`: the Pigou-like network of a latency and
  a rate.

## Main results

* `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.cost_le_toReal_pigouBound_mul`
  ([Roughgarden2013CS364A], Lecture #11, Theorem 3.3): the price of anarchy is at most `α(C)`.
* `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.cost_le_mul_of_forall_mul_le`: the same
  argument for any `α` satisfying the edgewise Pigou inequalities.
* `Cslib.GameTheory.NonatomicCongestionGame.exists_lt_cost_of_lt_pigouBound` and
  `Cslib.GameTheory.NonatomicCongestionGame.pigouBound_le_ofReal_iff` ([Roughgarden2003],
  Theorem 4.2): Pigou-like networks come arbitrarily close to `α(C)`, so `α(C)` is the exact
  worst-case price of anarchy.
* `Cslib.GameTheory.pigouBound_polynomialLatencies` ([Roughgarden2003], Proposition 5.1): the Pigou
  bound of polynomials of degree at most `d`.
* `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.cost_le_of_mem_polynomialLatencies` and
  `Cslib.GameTheory.NonatomicCongestionGame.exists_cost_eq_mul_of_mem_polynomialLatencies`: the
  price of anarchy for polynomial latencies, attained by Pigou's `x ^ d` network.
* `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.cost_le` and
  `Cslib.GameTheory.NonatomicCongestionGame.exists_cost_eq_four_thirds_mul`
  ([RoughgardenTardos2002], Theorem 4.5 and Figure 3): the affine case `4/3`, attained.

## References

* [CorreaSchulzStierMoses2004]
* [Roughgarden2003]
* [Roughgarden2013CS364A]
* [RoughgardenTardos2002]
-/

public section

namespace Cslib.GameTheory

open scoped ENNReal

/-- The **Pigou ratio** `r c(r) / (x c(x) + (r - x) c(r))`: the ratio between the cost `r c(r)` of
routing all `r` units of traffic over a link of latency `c` and the cost of routing `x` units over
it and the remaining `r - x` units over a parallel link of constant latency `c(r)`. -/
@[expose] noncomputable def pigouRatio (c : ℝ → ℝ) (r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (r * c r / (x * c x + (r - x) * c r))

/-- The **Pigou bound** `α(C)` of a class `C` of latency functions: the supremum of the Pigou ratios
`pigouRatio c r x` over `c ∈ C` and `r, x ≥ 0`. -/
noncomputable def pigouBound (C : Set (ℝ → ℝ)) : ℝ≥0∞ :=
  ⨆ c ∈ C, ⨆ r ≥ (0 : ℝ), ⨆ x ≥ (0 : ℝ), pigouRatio c r x

/-- Every Pigou ratio of a function in `C` is at most `α(C)`. -/
theorem pigouRatio_le_pigouBound {C : Set (ℝ → ℝ)} {c : ℝ → ℝ} (hc : c ∈ C) {r x : ℝ}
    (hr : 0 ≤ r) (hx : 0 ≤ x) : pigouRatio c r x ≤ pigouBound C :=
  le_iSup₂_of_le c hc <| le_iSup₂_of_le r hr <| le_iSup₂_of_le x hx le_rfl

/-- `α(C) ≤ a` as soon as every Pigou ratio of a function in `C` is at most `a`. -/
theorem pigouBound_le {C : Set (ℝ → ℝ)} {a : ℝ≥0∞}
    (h : ∀ c ∈ C, ∀ r x : ℝ, 0 ≤ r → 0 ≤ x → pigouRatio c r x ≤ a) : pigouBound C ≤ a :=
  iSup₂_le fun c hc => iSup₂_le fun r hr => iSup₂_le fun x hx => h c hc r x hr hx

/-- `a < α(C)` exactly when some Pigou ratio of a function in `C` exceeds `a`. -/
theorem lt_pigouBound_iff {C : Set (ℝ → ℝ)} {a : ℝ≥0∞} :
    a < pigouBound C ↔ ∃ c ∈ C, ∃ r x : ℝ, 0 ≤ r ∧ 0 ≤ x ∧ a < pigouRatio c r x := by
  simp only [pigouBound, lt_iSup_iff, exists_prop, ge_iff_le]
  constructor
  · rintro ⟨c, hc, r, hr, x, hx, h⟩
    exact ⟨c, hc, r, x, hr, hx, h⟩
  · rintro ⟨c, hc, r, x, hr, hx, h⟩
    exact ⟨c, hc, r, hr, x, hx, h⟩

/-- The Pigou bound is at least `1` as soon as some `c ∈ C` and `r ≥ 0` have `r c(r) > 0`: the
ratio at `x = r` is `1`. -/
theorem one_le_pigouBound {C : Set (ℝ → ℝ)} {c : ℝ → ℝ} (hc : c ∈ C) {r : ℝ} (hr : 0 ≤ r)
    (hpos : 0 < r * c r) : 1 ≤ pigouBound C := by
  refine le_of_eq_of_le ?_ (pigouRatio_le_pigouBound hc hr hr)
  rw [pigouRatio, sub_self, zero_mul, add_zero, div_self hpos.ne', ENNReal.ofReal_one]

/-- For a latency `c` that is nonnegative and nondecreasing on `[0, ∞)`, a nonpositive Pigou
denominator forces both the numerator and the denominator to vanish. -/
private theorem pigou_num_eq_zero_of_denom_nonpos {c : ℝ → ℝ} (hc : ∀ x, 0 ≤ x → 0 ≤ c x)
    (hcm : MonotoneOn c (Set.Ici 0)) {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x)
    (hD : x * c x + (r - x) * c r ≤ 0) :
    r * c r = 0 ∧ x * c x + (r - x) * c r = 0 := by
  have hcr := hc r hr
  have hcx := hc x hx
  rcases le_total x r with hxr | hrx
  · have h1 : 0 ≤ x * c x := mul_nonneg hx hcx
    have h2 : 0 ≤ (r - x) * c r := mul_nonneg (sub_nonneg.2 hxr) hcr
    have h1' : x * c x = 0 := by linarith
    have h2' : (r - x) * c r = 0 := by linarith
    refine ⟨?_, by linarith⟩
    rcases mul_eq_zero.1 h2' with h | h
    · rw [show r = x by linarith]
      exact h1'
    · rw [h, mul_zero]
  · have hle : c r ≤ c x := hcm hr hx hrx
    have h1 : 0 ≤ r * c r := mul_nonneg hr hcr
    have h2 : r * c r ≤ x * c x + (r - x) * c r := by
      nlinarith [mul_nonneg hx (sub_nonneg.2 hle)]
    exact ⟨by linarith, by linarith⟩

/-- **The Pigou inequality**: if `α(C)` is finite and `c ∈ C` is nonnegative and nondecreasing on
`[0, ∞)`, then `r c(r) ≤ α(C) (x c(x) + (r - x) c(r))` for all `r, x ≥ 0`. -/
theorem mul_le_toReal_pigouBound_mul {C : Set (ℝ → ℝ)} (htop : pigouBound C ≠ ⊤) {c : ℝ → ℝ}
    (hc : c ∈ C) (hc0 : ∀ x, 0 ≤ x → 0 ≤ c x) (hcm : MonotoneOn c (Set.Ici 0)) {r x : ℝ}
    (hr : 0 ≤ r) (hx : 0 ≤ x) :
    r * c r ≤ (pigouBound C).toReal * (x * c x + (r - x) * c r) := by
  rcases le_or_gt (x * c x + (r - x) * c r) 0 with hD | hD
  · obtain ⟨h1, h2⟩ := pigou_num_eq_zero_of_denom_nonpos hc0 hcm hr hx hD
    rw [h1, h2, mul_zero]
  · have hle := pigouRatio_le_pigouBound hc hr hx
    rw [pigouRatio, ← ENNReal.ofReal_toReal htop,
      ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, div_le_iff₀ hD] at hle
    exact hle

/-- A bound `x (c(r) - c(x)) ≤ β r c(r)` with `β < 1` for every `c ∈ C` bounds the Pigou bound by
`(1 - β)⁻¹`. -/
theorem pigouBound_le_ofReal_inv_one_sub {C : Set (ℝ → ℝ)} {β : ℝ} (hβ : β < 1)
    (hC : ∀ c ∈ C, ∀ x, 0 ≤ x → 0 ≤ c x)
    (h : ∀ c ∈ C, ∀ r x : ℝ, 0 ≤ r → 0 ≤ x → x * (c r - c x) ≤ β * (r * c r)) :
    pigouBound C ≤ ENNReal.ofReal (1 - β)⁻¹ := by
  refine pigouBound_le fun c hc r x hr hx => ENNReal.ofReal_le_ofReal ?_
  have h1 : 0 < 1 - β := sub_pos.2 hβ
  have hN : 0 ≤ r * c r := mul_nonneg hr (hC c hc r hr)
  have hkey : (1 - β) * (r * c r) ≤ x * c x + (r - x) * c r := by
    linarith [h c hc r x hr hx]
  rcases le_or_gt (x * c x + (r - x) * c r) 0 with hD | hD
  · exact (div_nonpos_of_nonneg_of_nonpos hN hD).trans (inv_nonneg.2 h1.le)
  · rw [div_le_iff₀ hD, inv_mul_eq_div, le_div_iff₀ h1]
    linarith

/-! ### Polynomial latencies -/

/-- The class of **polynomial latencies of degree at most `d` with nonnegative coefficients**:
`c(x) = ∑_{i ≤ d} a_i x^i` with `a_i ≥ 0`. -/
def polynomialLatencies (d : ℕ) : Set (ℝ → ℝ) :=
  {c | ∃ a : Fin (d + 1) → ℝ, (∀ i, 0 ≤ a i) ∧ ∀ x, c x = ∑ i, a i * x ^ (i : ℕ)}

/-- Membership in `polynomialLatencies d`, unfolded. -/
theorem mem_polynomialLatencies {d : ℕ} {c : ℝ → ℝ} :
    c ∈ polynomialLatencies d ↔
      ∃ a : Fin (d + 1) → ℝ, (∀ i, 0 ≤ a i) ∧ ∀ x, c x = ∑ i, a i * x ^ (i : ℕ) :=
  Iff.rfl

/-- The monomial `x ^ d` is a polynomial latency of degree at most `d`. -/
theorem pow_mem_polynomialLatencies (d : ℕ) : (fun x : ℝ => x ^ d) ∈ polynomialLatencies d := by
  refine ⟨Pi.single (Fin.last d) 1, fun i => ?_, fun x => ?_⟩
  · by_cases h : i = Fin.last d
    · subst h; simp
    · simp [h]
  · rw [Finset.sum_eq_single (Fin.last d)]
    · simp
    · intro i _ hi
      simp [hi]
    · simp

/-- Nonnegative constant functions are polynomial latencies of every degree. -/
theorem const_mem_polynomialLatencies {d : ℕ} (a : ℝ) (ha : 0 ≤ a) :
    (fun _ : ℝ => a) ∈ polynomialLatencies d := by
  refine ⟨Pi.single 0 a, fun i => ?_, fun x => ?_⟩
  · by_cases h : i = 0
    · subst h; simpa using ha
    · simp [h]
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi
      simp [hi]
    · simp

/-- Polynomial latencies with nonnegative coefficients are nonnegative on `[0, ∞)`. -/
theorem nonneg_of_mem_polynomialLatencies {d : ℕ} {c : ℝ → ℝ} (hc : c ∈ polynomialLatencies d)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ c x := by
  obtain ⟨a, ha, hc⟩ := hc
  rw [hc]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (pow_nonneg hx _)

/-- Polynomial latencies with nonnegative coefficients are nondecreasing on `[0, ∞)`. -/
theorem monotoneOn_of_mem_polynomialLatencies {d : ℕ} {c : ℝ → ℝ}
    (hc : c ∈ polynomialLatencies d) : MonotoneOn c (Set.Ici 0) := by
  obtain ⟨a, ha, hc⟩ := hc
  intro x hx y _ hxy
  rw [hc, hc]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy _) (ha i)

/-- The tangent-line inequality for `x ↦ x ^ (n + 1)` on `[0, ∞)`. -/
private theorem pow_add_mul_sub_le_pow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    y ^ (n + 1) + (n + 1) * y ^ n * (x - y) ≤ x ^ (n + 1) := by
  rcases hy.eq_or_lt with rfl | hy
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [zero_pow hn.ne', pow_nonneg hx]
  · have hb := one_add_mul_le_pow (a := x / y - 1) (by linarith [div_nonneg hx hy.le]) (n + 1)
    have hyn : 0 < y ^ (n + 1) := pow_pos hy _
    rw [show 1 + (x / y - 1) = x / y by ring, div_pow, le_div_iff₀ hyn] at hb
    push_cast at hb
    calc y ^ (n + 1) + (n + 1) * y ^ n * (x - y)
        = (1 + (n + 1) * (x / y - 1)) * y ^ (n + 1) := by
          field_simp
          ring
      _ ≤ x ^ (n + 1) := hb

/-- The parameter `t = (d + 1)^{-1/d}` maximizes `x (1 - x ^ d)` on `[0, 1]`: `t ∈ (0, 1]`,
`t ^ d (d + 1) = 1` and `d (d + 1)^{-(d + 1)/d} = d t ^ (d + 1)`. -/
private theorem pigouParam_spec (d : ℕ) :
    0 < ((d : ℝ) + 1) ^ (-(1 / (d : ℝ))) ∧ ((d : ℝ) + 1) ^ (-(1 / (d : ℝ))) ≤ 1 ∧
      (((d : ℝ) + 1) ^ (-(1 / (d : ℝ)))) ^ d * ((d : ℝ) + 1) = 1 ∧
      (d : ℝ) * ((d : ℝ) + 1) ^ (-((d + 1 : ℝ) / d)) =
        d * (((d : ℝ) + 1) ^ (-(1 / (d : ℝ)))) ^ (d + 1) := by
  have hs : (1 : ℝ) ≤ d + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hs0 : (0 : ℝ) ≤ d + 1 := by linarith
  refine ⟨Real.rpow_pos_of_pos (by linarith) _,
    Real.rpow_le_one_of_one_le_of_nonpos hs (by
      rw [neg_nonpos]; exact div_nonneg zero_le_one (Nat.cast_nonneg d)), ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0,
        show -(1 / (d : ℝ)) * d = -1 by field_simp, Real.rpow_neg_one,
        inv_mul_cancel₀ (by linarith)]
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]
      congr 2
      push_cast
      field_simp

/-- The key one-variable inequality for monomials: `x (r^d - x^d) ≤ d (d+1)^{-(d+1)/d} r^{d+1}`
for `r, x ≥ 0`, with equality at `x = (d+1)^{-1/d} r`. -/
private theorem mul_sub_pow_le (d : ℕ) {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) :
    x * (r ^ d - x ^ d) ≤ (d : ℝ) * ((d : ℝ) + 1) ^ (-((d + 1 : ℝ) / d)) * r ^ (d + 1) := by
  obtain ⟨ht0, -, htd, hβ⟩ := pigouParam_spec d
  set t := ((d : ℝ) + 1) ^ (-(1 / (d : ℝ)))
  rw [hβ]
  have hy : 0 ≤ t * r := mul_nonneg ht0.le hr
  have htan := pow_add_mul_sub_le_pow hx hy d
  have hyd : (t * r) ^ d * ((d : ℝ) + 1) = r ^ d := by
    rw [mul_pow, mul_right_comm, htd, one_mul]
  have hy1 : (t * r) ^ d * (t * r) = t ^ (d + 1) * r ^ (d + 1) := by
    rw [← pow_succ, mul_pow]
  calc x * (r ^ d - x ^ d) = x * ((t * r) ^ d * ((d : ℝ) + 1)) - x ^ (d + 1) := by
        rw [hyd, pow_succ]; ring
    _ ≤ (d : ℝ) * ((t * r) ^ d * (t * r)) := by linear_combination htan
    _ = (d : ℝ) * t ^ (d + 1) * r ^ (d + 1) := by rw [hy1]; ring

/-- Lower-degree monomials obey the same bound as the top-degree one. -/
private theorem mul_sub_pow_le_of_le {d i : ℕ} (hid : i ≤ d) {r x : ℝ} (hr : 0 ≤ r)
    (hx : 0 ≤ x) :
    x * (r ^ i - x ^ i) ≤ (d : ℝ) * ((d : ℝ) + 1) ^ (-((d + 1 : ℝ) / d)) * r ^ (i + 1) := by
  set β := (d : ℝ) * ((d : ℝ) + 1) ^ (-((d + 1 : ℝ) / d))
  have hβ : 0 ≤ β := by positivity
  rcases le_total r x with hrx | hxr
  · have : x * (r ^ i - x ^ i) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hx (sub_nonpos.2 (pow_le_pow_left₀ hr hrx _))
    exact this.trans (by positivity)
  rcases hr.eq_or_lt with rfl | hr
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · have hx0 : x = 0 := le_antisymm hxr hx
      simp [hx0]
  · have key := mul_sub_pow_le d hr.le hx
    have hk : 0 < r ^ (d - i) := pow_pos hr _
    have hrd : r ^ d = r ^ i * r ^ (d - i) := by rw [← pow_add, Nat.add_sub_cancel' hid]
    have hxd : x ^ d = x ^ i * x ^ (d - i) := by rw [← pow_add, Nat.add_sub_cancel' hid]
    have hrd1 : r ^ (d + 1) = r ^ (i + 1) * r ^ (d - i) := by
      rw [← pow_add, show i + 1 + (d - i) = d + 1 by omega]
    have hxk : x ^ (d - i) ≤ r ^ (d - i) := pow_le_pow_left₀ hx hxr _
    rw [hrd, hxd, hrd1] at key
    refine le_of_mul_le_mul_right ?_ hk
    have hxi : 0 ≤ x * x ^ i := mul_nonneg hx (pow_nonneg hx _)
    nlinarith [mul_le_mul_of_nonneg_left hxk hxi]

/-- Polynomial latencies of degree at most `d` satisfy
`x (c(r) - c(x)) ≤ d (d+1)^{-(d+1)/d} r c(r)` for `r, x ≥ 0`. -/
private theorem mul_sub_le_of_mem_polynomialLatencies {d : ℕ} {c : ℝ → ℝ}
    (hc : c ∈ polynomialLatencies d) {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) :
    x * (c r - c x) ≤ (d : ℝ) * ((d : ℝ) + 1) ^ (-((d + 1 : ℝ) / d)) * (r * c r) := by
  obtain ⟨a, ha, hc⟩ := hc
  rw [hc, hc, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hi := mul_sub_pow_le_of_le (Nat.lt_succ_iff.1 i.isLt) hr hx
  calc x * (a i * r ^ (i : ℕ) - a i * x ^ (i : ℕ)) = a i * (x * (r ^ (i : ℕ) - x ^ (i : ℕ))) := by
        ring
    _ ≤ a i * ((d : ℝ) * ((d : ℝ) + 1) ^ (-((d + 1 : ℝ) / d)) * r ^ ((i : ℕ) + 1)) :=
        mul_le_mul_of_nonneg_left hi (ha i)
    _ = _ := by ring

/-- `1 - d (d+1)^{-(d+1)/d} > 0`, so the polynomial Pigou bound is finite. -/
private theorem one_sub_pigouConst_pos (d : ℕ) :
    0 < 1 - (d : ℝ) * ((d : ℝ) + 1) ^ (-((d + 1 : ℝ) / d)) := by
  obtain ⟨ht0, ht1, htd, hβ⟩ := pigouParam_spec d
  set t := ((d : ℝ) + 1) ^ (-(1 / (d : ℝ)))
  rw [hβ]
  have h : (d : ℝ) * t ^ (d + 1) = t - t ^ (d + 1) := by
    rw [pow_succ]; linear_combination t * htd
  rw [h]
  have : 0 < t ^ (d + 1) := pow_pos ht0 _
  linarith

/-- **The Pigou bound of polynomial latencies** ([Roughgarden2003], Proposition 5.1;
[Roughgarden2013CS364A], Lecture #11, Table 1): for polynomials of degree at most `d` with
nonnegative coefficients, `α = (1 - d (d+1)^{-(d+1)/d})⁻¹`. It is attained by Pigou's example with
latency `x ^ d`, rate `1` and `(d + 1)^{-1/d}` units of traffic on the first link. -/
theorem pigouBound_polynomialLatencies (d : ℕ) :
    pigouBound (polynomialLatencies d) =
      ENNReal.ofReal (1 - (d : ℝ) * ((d : ℝ) + 1) ^ (-((d + 1 : ℝ) / d)))⁻¹ := by
  obtain ⟨ht0, ht1, htd, hβ⟩ := pigouParam_spec d
  set t := ((d : ℝ) + 1) ^ (-(1 / (d : ℝ)))
  have hpos := one_sub_pigouConst_pos d
  refine le_antisymm (pigouBound_le_ofReal_inv_one_sub (by linarith)
    (fun c hc x hx => nonneg_of_mem_polynomialLatencies hc hx)
    (fun c hc r x hr hx => mul_sub_le_of_mem_polynomialLatencies hc hr hx)) ?_
  refine le_of_eq_of_le ?_ (pigouRatio_le_pigouBound (pow_mem_polynomialLatencies d)
    zero_le_one ht0.le)
  have hden : t * t ^ d + (1 - t) * 1 = 1 - (d : ℝ) * ((d : ℝ) + 1) ^ (-((d + 1 : ℝ) / d)) := by
    rw [hβ, pow_succ]
    linear_combination t * htd
  rw [pigouRatio]
  congr 1
  rw [← hden]
  simp

/-- The polynomial Pigou bound for `d = 1` is `4/3`. -/
private theorem pigouConst_one : (1 - ((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) + 1) ^
    (-((((1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ))))⁻¹ = 4 / 3 := by
  rw [show -((((1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num,
    Real.rpow_intCast]
  norm_num

/-- The Pigou bound of affine latencies with nonnegative coefficients is `4/3`. -/
theorem pigouBound_polynomialLatencies_one :
    pigouBound (polynomialLatencies 1) = ENNReal.ofReal (4 / 3) := by
  rw [pigouBound_polynomialLatencies, pigouConst_one]

namespace NonatomicCongestionGame

variable {K P E : Type*} [Fintype P] [DecidableEq E] {G : NonatomicCongestionGame K P E}

/-- **Edgewise inequalities bound the price of anarchy**: if `α ≥ 0` and every resource latency
satisfies `r c(r) ≤ α (x c(x) + (r - x) c(r))` for `r, x ≥ 0`, then every Wardrop equilibrium
costs at most `α` times every feasible flow. This is the argument of
[Roughgarden2013CS364A], Lecture #11, Section 5. -/
theorem IsWardrop.cost_le_mul_of_forall_mul_le [DecidableEq K] [Finite E] {α : ℝ} (hα : 0 ≤ α)
    (h : ∀ e, ∀ r x : ℝ, 0 ≤ r → 0 ≤ x →
      r * G.latency e r ≤ α * (x * G.latency e x + (r - x) * G.latency e r))
    {f g : P → ℝ} (hf : G.IsWardrop f) (hg : G.IsFeasible g) :
    G.cost f ≤ α * G.cost g := by
  have := Fintype.ofFinite E
  have hvi := hf.cost_le_sum_mul_pathLatency hg
  simp only [pathLatency] at hvi
  rw [G.sum_mul_sum_resources g, G.cost_eq_sum_edgeFlow] at hvi
  rw [G.cost_eq_sum_edgeFlow, G.cost_eq_sum_edgeFlow]
  have hfe : ∀ e, 0 ≤ G.edgeFlow f e := fun e => Finset.sum_nonneg fun p _ => hf.1.1 p
  have hge : ∀ e, 0 ≤ G.edgeFlow g e := fun e => Finset.sum_nonneg fun p _ => hg.1 p
  have hsum := Finset.sum_le_sum fun e (_ : e ∈ Finset.univ) => h e _ _ (hfe e) (hge e)
  rw [← Finset.mul_sum] at hsum
  simp only [sub_mul, add_sub_assoc', Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  nlinarith [mul_nonneg hα (sub_nonneg.2 hvi)]

/-- **The price of anarchy is at most the Pigou bound** ([Roughgarden2013CS364A], Lecture #11,
Theorem 3.3; [Roughgarden2003], Theorem 3.8; [CorreaSchulzStierMoses2004]): if every resource
latency lies in `C` and is nonnegative and nondecreasing on `[0, ∞)`, and the Pigou bound `α(C)` is
finite, then every Wardrop equilibrium `f` costs at most `α(C)` times every feasible flow `g`. -/
theorem IsWardrop.cost_le_toReal_pigouBound_mul [DecidableEq K] [Finite E] {C : Set (ℝ → ℝ)}
    (htop : pigouBound C ≠ ⊤) (hC : ∀ e, G.latency e ∈ C)
    (h0 : ∀ e x, 0 ≤ x → 0 ≤ G.latency e x) (hm : ∀ e, MonotoneOn (G.latency e) (Set.Ici 0))
    {f g : P → ℝ} (hf : G.IsWardrop f) (hg : G.IsFeasible g) :
    G.cost f ≤ (pigouBound C).toReal * G.cost g :=
  hf.cost_le_mul_of_forall_mul_le ENNReal.toReal_nonneg
    (fun e _ _ hr hx => mul_le_toReal_pigouBound_mul htop (hC e) (h0 e) (hm e) hr hx) hg

/-- **The price of anarchy of selfish routing with polynomial latencies**
([Roughgarden2003], Proposition 5.1): if every latency is a polynomial of degree at most `d` with
nonnegative coefficients, then every Wardrop equilibrium costs at most
`(1 - d (d+1)^{-(d+1)/d})⁻¹` times every feasible flow. -/
theorem IsWardrop.cost_le_of_mem_polynomialLatencies [DecidableEq K] [Finite E] {d : ℕ}
    (hG : ∀ e, G.latency e ∈ polynomialLatencies d) {f g : P → ℝ} (hf : G.IsWardrop f)
    (hg : G.IsFeasible g) :
    G.cost f ≤ (1 - (d : ℝ) * ((d : ℝ) + 1) ^ (-((d + 1 : ℝ) / d)))⁻¹ * G.cost g := by
  have h := hf.cost_le_toReal_pigouBound_mul (C := polynomialLatencies d)
    (by rw [pigouBound_polynomialLatencies]; exact ENNReal.ofReal_ne_top) hG
    (fun e _ hx => nonneg_of_mem_polynomialLatencies (hG e) hx)
    (fun e => monotoneOn_of_mem_polynomialLatencies (hG e)) hg
  rwa [pigouBound_polynomialLatencies,
    ENNReal.toReal_ofReal (inv_nonneg.2 (one_sub_pigouConst_pos d).le)] at h

/-! ### Pigou-like networks and tightness -/

/-- The **Pigou-like network** with latency `c` and rate `r` ([Roughgarden2013CS364A],
Lecture #11, Definition 3.2): `r` units of traffic on two parallel links, with latency `c` on link
`0` and constant latency `c r` on link `1`. -/
@[expose] def pigouNetwork (c : ℝ → ℝ) (r : ℝ) : NonatomicCongestionGame Unit (Fin 2) (Fin 2) where
  commodity _ := ()
  resources p := {p}
  rate _ := r
  latency e := if e = 0 then c else fun _ => c r

/-- The first link of a Pigou-like network has latency `c`. -/
theorem pigouNetwork_latency_zero (c : ℝ → ℝ) (r : ℝ) : (pigouNetwork c r).latency 0 = c := rfl

/-- The second link of a Pigou-like network has constant latency `c r`. -/
theorem pigouNetwork_latency_one (c : ℝ → ℝ) (r : ℝ) :
    (pigouNetwork c r).latency 1 = fun _ => c r := rfl

/-- The cost of a flow `f` in a Pigou-like network is `f 0 * c (f 0) + f 1 * c r`. -/
theorem pigouNetwork_cost (c : ℝ → ℝ) (r : ℝ) (f : Fin 2 → ℝ) :
    (pigouNetwork c r).cost f = f 0 * c (f 0) + f 1 * c r := by
  have hflow : ∀ e, (pigouNetwork c r).edgeFlow f e = f e := fun e => by
    simp [edgeFlow, pigouNetwork, Finset.filter_eq]
  simp only [cost, pathLatency, hflow, Fin.sum_univ_two]
  simp [pigouNetwork]

/-- Routing `x ∈ [0, r]` units over the first link of a Pigou-like network, and the rest over the
second, is feasible. -/
theorem pigouNetwork_isFeasible (c : ℝ → ℝ) {r x : ℝ} (hx : 0 ≤ x) (hxr : x ≤ r) :
    (pigouNetwork c r).IsFeasible ![x, r - x] := by
  refine ⟨fun p => ?_, fun _ => ?_⟩
  · fin_cases p
    · exact hx
    · simpa using hxr
  · simp [pigouNetwork, Fin.sum_univ_two]

/-- In a Pigou-like network, routing all traffic over the first link is a Wardrop equilibrium. -/
theorem pigouNetwork_isWardrop (c : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (pigouNetwork c r).IsWardrop ![r, 0] := by
  refine ⟨by simpa using pigouNetwork_isFeasible c hr le_rfl, fun p q _ _ => ?_⟩
  have hflow : ∀ e, (pigouNetwork c r).edgeFlow ![r, 0] e = ![r, 0] e := fun e => by
    simp [edgeFlow, pigouNetwork, Finset.filter_eq]
  have hlat : ∀ p, (pigouNetwork c r).pathLatency ![r, 0] p = c r := fun p => by
    simp only [pathLatency, hflow]
    fin_cases p <;> simp [pigouNetwork]
  rw [hlat, hlat]

/-- **Pigou-like networks attain the Pigou bound** ([Roughgarden2003], Lemma 4.1 and
Theorem 4.2; [Roughgarden2013CS364A], Lecture #11, Section 3): if `C` consists of nonnegative
functions that are nondecreasing on `[0, ∞)` and contains every nonnegative constant function, then
every `β` below the Pigou bound `α(C)` is exceeded by the ratio of a Wardrop equilibrium to a
feasible flow of positive cost in a two-link network with latencies in `C`. Together with
`IsWardrop.cost_le_toReal_pigouBound_mul`, `α(C)` is the exact worst-case price of anarchy. -/
theorem exists_lt_cost_of_lt_pigouBound {C : Set (ℝ → ℝ)} (hC : ∀ c ∈ C, ∀ x, 0 ≤ x → 0 ≤ c x)
    (hCm : ∀ c ∈ C, MonotoneOn c (Set.Ici 0)) (hconst : ∀ a : ℝ, 0 ≤ a → (fun _ => a) ∈ C)
    {β : ℝ} (hβ : ENNReal.ofReal β < pigouBound C) :
    ∃ (G : NonatomicCongestionGame Unit (Fin 2) (Fin 2)) (f g : Fin 2 → ℝ),
      (∀ e, G.latency e ∈ C) ∧ G.IsWardrop f ∧ G.IsFeasible g ∧ 0 < G.cost g ∧
        β * G.cost g < G.cost f := by
  rcases lt_or_ge β 1 with hβ1 | hβ1
  · refine ⟨pigouNetwork (fun _ => 1) 1, ![1, 0], ![1, 0], fun e => ?_,
      pigouNetwork_isWardrop _ zero_le_one, (pigouNetwork_isWardrop _ zero_le_one).1, ?_, ?_⟩
    · fin_cases e
      · exact hconst 1 zero_le_one
      · exact hconst 1 zero_le_one
    · rw [pigouNetwork_cost]; norm_num
    · rw [pigouNetwork_cost]; norm_num [hβ1]
  obtain ⟨c, hc, r, x, hr, hx, hlt⟩ := lt_pigouBound_iff.1 hβ
  rw [pigouRatio, ENNReal.ofReal_lt_ofReal_iff'] at hlt
  obtain ⟨hlt, hpos⟩ := hlt
  have hcr := hC c hc r hr
  have hcx := hC c hc x hx
  have hD : 0 < x * c x + (r - x) * c r := by
    by_contra hD
    rw [div_eq_zero_iff.2 (Or.inr (le_antisymm (not_lt.1 hD) ?_))] at hpos
    · exact lt_irrefl 0 hpos
    · obtain ⟨-, h2⟩ := pigou_num_eq_zero_of_denom_nonpos (hC c hc) (hCm c hc) hr hx (not_lt.1 hD)
      exact h2.ge
  have hxr : x < r := by
    by_contra hrx
    have hle : c r ≤ c x := hCm c hc hr hx (not_lt.1 hrx)
    have : r * c r ≤ x * c x + (r - x) * c r := by
      nlinarith [mul_nonneg hx (sub_nonneg.2 hle)]
    linarith [(div_le_one hD).2 this]
  refine ⟨pigouNetwork c r, ![r, 0], ![x, r - x], fun e => ?_, pigouNetwork_isWardrop c hr,
    pigouNetwork_isFeasible c hx hxr.le, ?_, ?_⟩
  · fin_cases e
    · exact hc
    · exact hconst _ hcr
  · rw [pigouNetwork_cost]; simpa using hD
  · rw [pigouNetwork_cost, pigouNetwork_cost]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, add_zero]
    rwa [lt_div_iff₀ hD] at hlt

/-- **The Pigou bound is the exact worst-case price of anarchy** ([Roughgarden2003], Theorem 4.2;
[Roughgarden2013CS364A], Lecture #11, Section 3): if `C` consists of nonnegative functions that
are nondecreasing on `[0, ∞)` and contains every nonnegative constant function, then
`α(C) ≤ β` exactly when, in every nonatomic congestion game with latencies in `C`, every Wardrop
equilibrium costs at most `β` times every feasible flow. Since the right side ranges over all
games, while the proof of `←` uses only Pigou-like networks, two-link networks already exhibit the
worst case. -/
theorem pigouBound_le_ofReal_iff {C : Set (ℝ → ℝ)} (hC : ∀ c ∈ C, ∀ x, 0 ≤ x → 0 ≤ c x)
    (hCm : ∀ c ∈ C, MonotoneOn c (Set.Ici 0)) (hconst : ∀ a : ℝ, 0 ≤ a → (fun _ => a) ∈ C)
    {β : ℝ} :
    pigouBound C ≤ ENNReal.ofReal β ↔
      ∀ (K P E : Type) [Fintype P] [Finite E] [DecidableEq K] [DecidableEq E]
        (G : NonatomicCongestionGame K P E) (f g : P → ℝ), (∀ e, G.latency e ∈ C) →
          G.IsWardrop f → G.IsFeasible g → G.cost f ≤ β * G.cost g := by
  constructor
  · intro h K P E _ _ _ _ G f g hG hf hg
    have hβ : 0 ≤ β := by
      have h1 := (one_le_pigouBound (hconst 1 zero_le_one) zero_le_one (by norm_num)).trans h
      by_contra hβ
      rw [ENNReal.ofReal_of_nonpos (not_le.1 hβ).le] at h1
      exact absurd h1 (by norm_num)
    have htop : pigouBound C ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
    have hcost := hf.cost_le_toReal_pigouBound_mul htop hG (fun e => hC _ (hG e))
      (fun e => hCm _ (hG e)) hg
    exact hcost.trans (mul_le_mul_of_nonneg_right (ENNReal.toReal_le_of_le_ofReal hβ h)
      (G.cost_nonneg (fun e => hC _ (hG e)) hg.1))
  · intro h
    by_contra hlt
    obtain ⟨G, f, g, hG, hf, hg, -, hlt'⟩ := exists_lt_cost_of_lt_pigouBound hC hCm hconst
      (not_le.1 hlt)
    exact absurd (h Unit (Fin 2) (Fin 2) G f g hG hf hg) (not_le.2 hlt')

/-- **Pigou's example attains the polynomial bound** ([Roughgarden2003], Section 2.4 and
Remark 5.2): with latency `x ^ d` on one link and `1` on the other, one unit of traffic has a
Wardrop equilibrium of cost exactly `(1 - d (d+1)^{-(d+1)/d})⁻¹` times the cost of the feasible flow
routing `(d + 1)^{-1/d}` units over the first link. -/
theorem exists_cost_eq_mul_of_mem_polynomialLatencies (d : ℕ) :
    ∃ (G : NonatomicCongestionGame Unit (Fin 2) (Fin 2)) (f g : Fin 2 → ℝ),
      (∀ e, G.latency e ∈ polynomialLatencies d) ∧ G.IsWardrop f ∧ G.IsFeasible g ∧
        0 < G.cost g ∧
        G.cost f = (1 - (d : ℝ) * ((d : ℝ) + 1) ^ (-((d + 1 : ℝ) / d)))⁻¹ * G.cost g := by
  obtain ⟨ht0, ht1, htd, hβ⟩ := pigouParam_spec d
  set t := ((d : ℝ) + 1) ^ (-(1 / (d : ℝ)))
  have hpos := one_sub_pigouConst_pos d
  have hcost : (pigouNetwork (fun x : ℝ => x ^ d) 1).cost ![t, 1 - t] =
      1 - (d : ℝ) * ((d : ℝ) + 1) ^ (-((d + 1 : ℝ) / d)) := by
    rw [pigouNetwork_cost, hβ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one]
    rw [pow_succ]
    linear_combination t * htd
  refine ⟨pigouNetwork (fun x => x ^ d) 1, ![1, 0], ![t, 1 - t], fun e => ?_,
    pigouNetwork_isWardrop _ zero_le_one, pigouNetwork_isFeasible _ ht0.le ht1, ?_, ?_⟩
  · fin_cases e
    · exact pow_mem_polynomialLatencies d
    · exact const_mem_polynomialLatencies _ (pow_nonneg zero_le_one d)
  · rw [hcost]; exact hpos
  · rw [hcost, inv_mul_cancel₀ hpos.ne', pigouNetwork_cost]
    simp

/-! ### Affine latencies -/

omit [Fintype P] [DecidableEq E] in
/-- Nonnegative affine latencies are polynomial latencies of degree at most `1`. -/
theorem HasAffineLatencies.latency_mem_polynomialLatencies (hG : G.HasAffineLatencies) (e : E) :
    G.latency e ∈ polynomialLatencies 1 := by
  obtain ⟨a, b, ha, hb, hl⟩ := hG
  refine ⟨![b e, a e], fun i => ?_, fun x => ?_⟩
  · fin_cases i
    · exact hb e
    · exact ha e
  · rw [hl, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero,
      Fin.val_one, pow_zero, pow_one]
    ring

/-- **The price of anarchy of selfish routing with affine latencies is at most `4/3`**
([RoughgardenTardos2002], Theorem 4.5): if the latencies are affine with nonnegative coefficients,
`f` is a Wardrop equilibrium and `g` is a feasible flow, then `cost f ≤ 4/3 * cost g`. This is the
case `d = 1` of `IsWardrop.cost_le_of_mem_polynomialLatencies`. -/
theorem IsWardrop.cost_le [DecidableEq K] [Finite E] (hG : G.HasAffineLatencies)
    {f g : P → ℝ} (hf : G.IsWardrop f) (hg : G.IsFeasible g) :
    G.cost f ≤ 4 / 3 * G.cost g := by
  have h := hf.cost_le_of_mem_polynomialLatencies hG.latency_mem_polynomialLatencies hg
  rwa [pigouConst_one] at h

/-- **The bound `4/3` is attained** by Pigou's example ([RoughgardenTardos2002], Figure 3): there
is a nonatomic congestion game with affine latencies, a Wardrop equilibrium `f` and a feasible flow
`g` with `cost f = 4/3 * cost g > 0`. So the constant in `IsWardrop.cost_le` cannot be improved. -/
theorem exists_cost_eq_four_thirds_mul :
    ∃ (G : NonatomicCongestionGame Unit (Fin 2) (Fin 2)) (f g : Fin 2 → ℝ),
      G.HasAffineLatencies ∧ G.IsWardrop f ∧ G.IsFeasible g ∧ 0 < G.cost g ∧
        G.cost f = 4 / 3 * G.cost g := by
  obtain ⟨G, f, g, hG, hf, hg, hpos, heq⟩ := exists_cost_eq_mul_of_mem_polynomialLatencies 1
  rw [pigouConst_one] at heq
  refine ⟨G, f, g, ?_, hf, hg, hpos, heq⟩
  choose a ha hl using hG
  refine ⟨fun e => a e 1, fun e => a e 0, fun e => ha e 1, fun e => ha e 0, fun e x => ?_⟩
  rw [hl, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one]
  ring

end NonatomicCongestionGame

end Cslib.GameTheory
