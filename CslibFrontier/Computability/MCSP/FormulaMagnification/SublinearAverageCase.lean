/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.FormulaMagnification.AverageCase
public import CslibFrontier.Computability.MCSP.ZeroErrorAverageCase
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt

/-!
# Hardness magnification from sublinear zero-error average-case formulas

This module states [OliveiraSanthanam2018, Section 1.2, Theorem 5, p. 8] with its concrete
threshold and a conventional ternary device:

> If `MCSP[2^{√n}]` on `N`-bit inputs cannot be solved on average with zero error by formulas of
> size `o(N)`, then NP does not have polynomial size formulas.

Here `N = 2 ^ n`. The device answers 0, 1 or "?", is never incorrect, and answers "?" on a
bounded fraction of inputs. We use the stronger average-case notion of
[OliveiraSanthanam2018, Appendix A, Definition 43, p. 34]: correctness for every large enough `n`
with "?" on at most a `1 / n` fraction of truth tables. Ruling out such devices is a weaker
hypothesis than ruling out the devices of Section 1.2, which may answer "?" on half of the
inputs, so the headline theorem implies the Section 1.2 form, recorded as a corollary.

The threshold `2 ^ √n` is rounded down to `MCSP.sqrtThreshold n = ⌊2 ^ √n⌋₊`. Circuit sizes are
natural numbers, so a size is at most `⌊2 ^ √n⌋₊` exactly when it is at most the real `2 ^ √n`
(`MCSP.le_sqrtThreshold_iff`): the rounding loses nothing. The general theorem accepts every
subexponential threshold, so other roundings such as `2 ^ ⌊√n⌋` are covered as well.

## Modelling choices

* A ternary formula device, `ZeroErrorFormula`, is a pair of De Morgan formulas: an unknown mask
  selecting "?" and an answer bit. Its size is the total leaf size. Any encoding of the outputs
  0, 1 and "?" by two output formulas converts to this one, and back, with at most a constant
  factor in size, which does not affect an `o(N)` bound.
* Size `o(N)` is a real little-o bound, `(D n).leafSize =o[atTop] 2 ^ n`, for a nonuniform family
  `D` with one device for each arity.
* Circuits are De Morgan circuits counting every gate, as in
  `CslibFrontier.Computability.MCSP.Basic`.
* No constructibility assumption on the threshold is needed: the single binary NP language
  receives thresholds and samples in its input
  (`Cslib.SuccinctMCSP.exists_language_mem_NP`).

The proof is the instantiation [OliveiraSanthanam2018, Section 3.3, p. 20] of the asymptotic
one-sided projection in `CslibFrontier.Computability.MCSP.FormulaMagnification.AverageCase`, with
the ternary device of [OliveiraSanthanam2018, Section 3.3, Theorem 27, p. 21]: it answers 0 where
the one-sided formula rejects and "?" elsewhere (`ZeroErrorFormula.ofMask`).

## Main definitions

* `Cslib.MCSP.sqrtThreshold`: the threshold `⌊2 ^ √n⌋₊`.
* `Cslib.Circuits.Boolean.ZeroErrorFormula`: a De Morgan formula device answering 0, 1 or "?".
* `Cslib.Circuits.Boolean.ZeroErrorFormula.ofMask`: the device answering 0 where a one-sided
  formula rejects and "?" elsewhere.

## Main results

* `Cslib.MCSP.le_sqrtThreshold_iff`: the rounding is exact for natural sizes.
* `Cslib.MCSP.subexponentiallyBounded_sqrtThreshold`: the threshold is subexponential.
* `Cslib.Circuits.Boolean.isZeroErrorDecider_ofMask`: translation from the one-sided
  unknown-mask formulation to a zero-error decider.
* `Cslib.Circuits.Boolean.exists_zeroErrorFormula_solvesOnAverage_of_mem_FormulaPoly`: forward
  form, with devices of at most `2 ^ (n / 2)` leaves.
* `Cslib.Circuits.Boolean.exists_NP_not_mem_FormulaPoly_of_zero_error_average_case_sublinear_hard`:
  the magnification theorem for any subexponential threshold and any unknown fraction `1 / k n`
  with `k n ≤ 2 ^ n`.
* `Cslib.Circuits.Boolean.exists_NP_not_mem_FormulaPoly_of_sqrtThreshold_average_case_hard`:
  Theorem 5 with Definition 43.
* `Cslib.Circuits.Boolean.exists_NP_not_mem_FormulaPoly_of_sqrtThreshold_half_average_case_hard`:
  Theorem 5 with the half-unknown devices of Section 1.2.

## References

* [I. C. Oliveira, R. Santhanam, *Hardness Magnification for Natural
  Problems*][OliveiraSanthanam2018]
-/

public section

open Filter Asymptotics

namespace Cslib.MCSP

/-- The circuit-size threshold `⌊2 ^ √n⌋₊` of [OliveiraSanthanam2018, Section 1.2, Theorem 5,
p. 8], for truth tables of `n`-input functions. -/
noncomputable def sqrtThreshold (n : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ Real.sqrt n⌋₊

/-- A natural number is at most `⌊2 ^ √n⌋₊` exactly when it is at most the real `2 ^ √n`. -/
theorem le_sqrtThreshold_iff {c n : ℕ} : c ≤ sqrtThreshold n ↔ (c : ℝ) ≤ 2 ^ Real.sqrt n :=
  Nat.le_floor_iff (by positivity)

/-- A truth table lies in the yes-set at threshold `⌊2 ^ √n⌋₊` exactly when its function has
circuit complexity at most the real `2 ^ √n`. -/
theorem ofFn_mem_yesSet_sqrtThreshold_iff {n : ℕ} {T : BitString (2 ^ n)} :
    List.ofFn T ∈ GapMCSP.yesSet sqrtThreshold ↔
      (Circuits.complexity Circuits.Boolean.interpretation
        (Circuits.single ((truthTable n).symm T)) : ℝ) ≤ 2 ^ Real.sqrt n := by
  rw [GapMCSP.ofFn_mem_yesSet_iff, le_sqrtThreshold_iff]

/-- At perfect squares the threshold is exact: `⌊2 ^ √(m ^ 2)⌋₊ = 2 ^ m`. -/
theorem sqrtThreshold_sq (m : ℕ) : sqrtThreshold (m ^ 2) = 2 ^ m := by
  have h : (2 : ℝ) ^ Real.sqrt ((m ^ 2 : ℕ) : ℝ) = ((2 ^ m : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg m), Real.rpow_natCast, Nat.cast_pow,
      Nat.cast_ofNat]
  rw [sqrtThreshold, h, Nat.floor_natCast]

/-- The threshold is at least `2 ^ ⌊√n⌋`. -/
theorem two_pow_sqrt_le_sqrtThreshold (n : ℕ) : 2 ^ Nat.sqrt n ≤ sqrtThreshold n := by
  rw [le_sqrtThreshold_iff, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two Real.nat_sqrt_le_real_sqrt

/-- The threshold is at most `2 ^ (⌊√n⌋ + 1)`. -/
theorem sqrtThreshold_le (n : ℕ) : sqrtThreshold n ≤ 2 ^ (Nat.sqrt n + 1) := by
  refine Nat.floor_le_of_le ?_
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two
    (by exact_mod_cast Real.real_sqrt_le_nat_sqrt_succ)

/-- The threshold `⌊2 ^ √n⌋₊` is subexponential. -/
theorem subexponentiallyBounded_sqrtThreshold : SubexponentiallyBounded sqrtThreshold := by
  refine SubexponentiallyBounded.mono_of_le ?_ sqrtThreshold_le
  intro c
  filter_upwards [eventually_ge_atTop ((c + 2) * (c + 2))] with n hn
  have hm : c + 2 ≤ Nat.sqrt n := Nat.le_sqrt.mpr hn
  have hclog : Nat.clog 2 (2 ^ (Nat.sqrt n + 1) + 1) ≤ Nat.sqrt n + 2 := by
    refine (Nat.clog_le_iff_le_pow one_lt_two).mpr ?_
    rw [pow_succ 2 (Nat.sqrt n + 1)]
    have := Nat.one_le_two_pow (n := Nat.sqrt n + 1)
    omega
  calc c * Nat.clog 2 (2 ^ (Nat.sqrt n + 1) + 1) ≤ c * (Nat.sqrt n + 2) :=
        Nat.mul_le_mul_left c hclog
    _ ≤ Nat.sqrt n * Nat.sqrt n := by nlinarith
    _ ≤ n := Nat.sqrt_le n

end Cslib.MCSP

namespace Cslib.Circuits.Boolean

/-- A De Morgan formula device on `N` input bits answering 0, 1 or "?": it answers "?" where the
formula `unknown` is true and otherwise the value of the formula `answer`. -/
structure ZeroErrorFormula (N : ℕ) where
  /-- The mask selecting the answer "?". -/
  unknown : Formula signature N
  /-- The answer outside the mask. -/
  answer : Formula signature N

namespace ZeroErrorFormula

variable {N : ℕ}

/-- The output of the device: `none` for "?" and `some b` for the answer `b`. -/
def eval (D : ZeroErrorFormula N) (T : BitString N) : Option Bool :=
  bif D.unknown.eval interpretation T then none else some (D.answer.eval interpretation T)

/-- The size of the device: the total leaf size of its two formulas. -/
def leafSize (D : ZeroErrorFormula N) : ℕ :=
  D.unknown.leafSize + D.answer.leafSize

@[simp] theorem eval_eq_none_iff {D : ZeroErrorFormula N} {T : BitString N} :
    D.eval T = none ↔ D.unknown.eval interpretation T = true := by
  cases h : D.unknown.eval interpretation T <;> simp [eval, h]

@[simp] theorem eval_eq_some_iff {D : ZeroErrorFormula N} {T : BitString N} {b : Bool} :
    D.eval T = some b ↔
      D.unknown.eval interpretation T = false ∧ D.answer.eval interpretation T = b := by
  cases h : D.unknown.eval interpretation T <;> simp [eval, h]

theorem leafSize_def (D : ZeroErrorFormula N) :
    D.leafSize = D.unknown.leafSize + D.answer.leafSize := by
  simp only [leafSize]

/-- The device answering 0 where the formula `F` is false and "?" where it is true, as in the
proof of [OliveiraSanthanam2018, Section 3.3, Theorem 27, p. 21]. -/
def ofMask (F : Formula signature N) : ZeroErrorFormula N :=
  ⟨F, Formula.const false⟩

@[simp] theorem unknown_ofMask (F : Formula signature N) : (ofMask F).unknown = F := by
  simp only [ofMask]

@[simp] theorem answer_ofMask (F : Formula signature N) :
    (ofMask F).answer = Formula.const false := by
  simp only [ofMask]

@[simp] theorem leafSize_ofMask (F : Formula signature N) : (ofMask F).leafSize = F.leafSize := by
  simp [leafSize_def]

end ZeroErrorFormula

open ZeroErrorFormula

/-- Translation from the one-sided unknown-mask formulation to a zero-error decider. If `F`
accepts every truth table in the yes-set and accepts at most `2 ^ (2 ^ n - r)` truth tables, then
`ZeroErrorFormula.ofMask F` is a zero-error decider answering "?" on at most a `1 / k` fraction
of truth tables whenever `k ≤ 2 ^ r` and `r ≤ 2 ^ n`. -/
theorem isZeroErrorDecider_ofMask {s : ℕ → ℕ} {n k r : ℕ} {F : Formula signature (2 ^ n)}
    (hyes : ∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s →
      F.eval interpretation T = true)
    (hcard : (Finset.univ.filter fun T : BitString (2 ^ n) =>
      F.eval interpretation T = true).card ≤ 2 ^ (2 ^ n - r))
    (hk : k ≤ 2 ^ r) (hr : r ≤ 2 ^ n) :
    MCSP.IsZeroErrorDecider s n k (ofMask F).eval where
  correct T b h := by
    simp only [eval_eq_some_iff, unknown_ofMask, answer_ofMask, Formula.eval_const] at h
    obtain ⟨hF, rfl⟩ := h
    simp only [Bool.false_eq_true, false_iff]
    exact fun hT => Bool.false_ne_true (hF ▸ hyes T hT)
  card_unknown_le := by
    simp only [eval_eq_none_iff, unknown_ofMask]
    calc k * (Finset.univ.filter fun T : BitString (2 ^ n) =>
          F.eval interpretation T = true).card ≤ 2 ^ r * 2 ^ (2 ^ n - r) :=
          Nat.mul_le_mul hk hcard
      _ = 2 ^ 2 ^ n := by rw [← pow_add, Nat.add_sub_cancel' hr]

/-- Forward form of [OliveiraSanthanam2018, Section 3.3, Theorem 27, p. 21] for ternary devices.
If a binary language agreeing with succinct MCSP has polynomial-size formulas, then for every
subexponential threshold `s` there are devices of at most `2 ^ (n / 2)` leaves, eventually, that
solve `MCSP[s]` on average with zero error and unknown fraction `1 / k n`, for any `k n ≤ 2 ^ n`.
-/
theorem exists_zeroErrorFormula_solvesOnAverage_of_mem_FormulaPoly {s k : ℕ → ℕ}
    (hs : SubexponentiallyBounded s) (hk : ∀ᶠ n in atTop, k n ≤ 2 ^ n) {L : Language Bool}
    (hag : ∀ x, x ∈ SuccinctMCSP ↔ SuccinctMCSP.enc x ∈ L) (hL : L ∈ FormulaPoly) :
    ∃ D : ∀ n, ZeroErrorFormula (2 ^ n), (∀ᶠ n in atTop, (D n).leafSize ≤ 2 ^ (n / 2)) ∧
      MCSP.SolvesOnAverage s k fun n => (D n).eval := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_exists_formula_zero_error_average_case_of_mem_FormulaPoly
      hs SubexponentiallyBounded.id hag hL 2 two_pos)
  let F : ∀ n, Formula signature (2 ^ n) := fun n =>
    if h : N ≤ n then Classical.choose (hN n h) else Formula.const true
  have hF : ∀ n, N ≤ n → (F n).leafSize ≤ 2 ^ (n / 2) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s →
        (F n).eval interpretation T = true) ∧
      (Finset.univ.filter fun T : BitString (2 ^ n) =>
        (F n).eval interpretation T = true).card ≤ 2 ^ (2 ^ n - n) := by
    intro n h
    simp only [F, h, ↓reduceDIte]
    exact Classical.choose_spec (hN n h)
  refine ⟨fun n => ofMask (F n), ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop N] with n hn
    simpa only [leafSize_ofMask] using (hF n hn).1
  · rw [MCSP.solvesOnAverage_iff]
    filter_upwards [eventually_ge_atTop N, hk] with n hn hkn
    obtain ⟨-, hyes, hcard⟩ := hF n hn
    exact isZeroErrorDecider_ofMask hyes hcard hkn Nat.lt_two_pow_self.le

/-- An eventual bound by `2 ^ (n / 2)` is little-o of `2 ^ n`. -/
private theorem isLittleO_two_pow_of_eventually_le_two_pow_half {f : ℕ → ℕ}
    (hf : ∀ᶠ n in atTop, f n ≤ 2 ^ (n / 2)) :
    (fun n => (f n : ℝ)) =o[atTop] fun n => (2 : ℝ) ^ n := by
  rw [isLittleO_iff_nat_mul_le]
  intro c
  filter_upwards [hf, eventually_ge_atTop (2 * c)] with n hfn hn
  have hc : c ≤ 2 ^ (n - n / 2) :=
    (show c ≤ n - n / 2 by omega).trans Nat.lt_two_pow_self.le
  have hnat : c * f n ≤ 2 ^ n :=
    calc c * f n ≤ 2 ^ (n - n / 2) * 2 ^ (n / 2) := Nat.mul_le_mul hc hfn
      _ = 2 ^ n := by rw [← pow_add, Nat.sub_add_cancel (Nat.div_le_self n 2)]
  simp only [Real.norm_natCast, norm_pow, Real.norm_ofNat]
  exact_mod_cast hnat

/-- Hardness magnification from sublinear zero-error average-case formulas, for any
subexponential threshold `s` and unknown fraction `1 / k n` with `k n ≤ 2 ^ n`: if no family of
ternary De Morgan formula devices of size `o(2 ^ n)` solves `MCSP[s]` on average with zero error,
then some binary NP language has no polynomial-size formulas. This is a library generalization of
[OliveiraSanthanam2018, Section 1.2, Theorem 5, p. 8], proved as in
[OliveiraSanthanam2018, Section 3.3, Theorem 27, p. 21]. -/
theorem exists_NP_not_mem_FormulaPoly_of_zero_error_average_case_sublinear_hard {s k : ℕ → ℕ}
    (hs : SubexponentiallyBounded s) (hk : ∀ᶠ n in atTop, k n ≤ 2 ^ n)
    (hhard : ¬ ∃ D : ∀ n, ZeroErrorFormula (2 ^ n),
      (fun n => ((D n).leafSize : ℝ)) =o[atTop] (fun n => (2 : ℝ) ^ n) ∧
        MCSP.SolvesOnAverage s k fun n => (D n).eval) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ Complexity.NP Turing.MultiTapeTM.encBits ∧
      L ∉ FormulaPoly := by
  obtain ⟨L, hLNP, hag⟩ := SuccinctMCSP.exists_language_mem_NP
  refine ⟨L, hLNP, fun hL => hhard ?_⟩
  obtain ⟨D, hsize, hsolve⟩ :=
    exists_zeroErrorFormula_solvesOnAverage_of_mem_FormulaPoly hs hk hag hL
  exact ⟨D, isLittleO_two_pow_of_eventually_le_two_pow_half hsize, hsolve⟩

/-- [OliveiraSanthanam2018, Section 1.2, Theorem 5, p. 8] with the average-case notion of
[OliveiraSanthanam2018, Appendix A, Definition 43, p. 34]: if no family of ternary De Morgan
formula devices of size `o(N)`, `N = 2 ^ n`, solves `MCSP[⌊2 ^ √n⌋₊]` with zero error and
"?" on at most a `1 / n` fraction of truth tables for every large enough `n`, then some binary NP
language has no polynomial-size formulas. -/
theorem exists_NP_not_mem_FormulaPoly_of_sqrtThreshold_average_case_hard
    (hhard : ¬ ∃ D : ∀ n, ZeroErrorFormula (2 ^ n),
      (fun n => ((D n).leafSize : ℝ)) =o[atTop] (fun n => (2 : ℝ) ^ n) ∧
        MCSP.SolvesOnAverage MCSP.sqrtThreshold (fun n => n) fun n => (D n).eval) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ Complexity.NP Turing.MultiTapeTM.encBits ∧
      L ∉ FormulaPoly :=
  exists_NP_not_mem_FormulaPoly_of_zero_error_average_case_sublinear_hard
    MCSP.subexponentiallyBounded_sqrtThreshold
    (Eventually.of_forall fun _ => Nat.lt_two_pow_self.le) hhard

/-- [OliveiraSanthanam2018, Section 1.2, Theorem 5, p. 8] with the devices of Section 1.2, which
answer "?" on at most half of the inputs. This follows from the Definition 43 form, since a device
with unknown fraction at most `1 / n` has unknown fraction at most `1 / 2` once `n ≥ 2`. -/
theorem exists_NP_not_mem_FormulaPoly_of_sqrtThreshold_half_average_case_hard
    (hhard : ¬ ∃ D : ∀ n, ZeroErrorFormula (2 ^ n),
      (fun n => ((D n).leafSize : ℝ)) =o[atTop] (fun n => (2 : ℝ) ^ n) ∧
        MCSP.SolvesOnAverage MCSP.sqrtThreshold (fun _ => 2) fun n => (D n).eval) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ Complexity.NP Turing.MultiTapeTM.encBits ∧
      L ∉ FormulaPoly :=
  exists_NP_not_mem_FormulaPoly_of_sqrtThreshold_average_case_hard fun ⟨D, hsize, hsolve⟩ =>
    hhard ⟨D, hsize, hsolve.mono (eventually_ge_atTop 2)⟩

end Cslib.Circuits.Boolean
