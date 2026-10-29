/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Braverman.Approximation
public import Complexity.Computability.Circuit.Boolean.LMN
public import Complexity.Probability.Fooling.OneSided
import Complexity.Computability.Circuit.Complexity
import Complexity.Foundations.BooleanAnalysis.FourierBitVal
import Complexity.Probability.PMF
import Cslib.Probability.PMF

/-!
# Polylogarithmic independence fools AC⁰

A `k`-wise independent distribution on the inputs fools every circuit of the unbounded fan-in
basis of constant depth, once `k` is polylogarithmic in the size of the circuit and in the inverse
of the error [Braverman, Main Theorem][Braverman2010].

The proof follows Braverman. Approximate the circuit `C` (`exists_lowDegree_approx`), for the
average of the `k`-wise independent distribution `X` and the uniform distribution, by a real
function `f` of degree at most `(ℓ s) ^ d` that agrees with `C` wherever a witness circuit `W` is
false; `W` is then true with probability at most `2 (41 / 50) ^ s · size C` under both `X` and the
uniform distribution. The witness is again a circuit of constant depth, so its `0/1` reading has a
low-degree `L²` approximation whenever its Fourier weight above some level `t` is small
(`exists_mem_lowDegree_expect_sq_bitVal_sub_eq`). Braverman's mollification, squaring trick and
one-sided chain (`IsKWiseIndependent.fools_bitVal_of_witness`) then show that `X` fools `C` once
`2 ((ℓ s) ^ d + t) ≤ k`. Braverman obtains the other direction by applying his Lemma 12 to `1 - C`
with a fresh approximation; reusing `f` and the witness through `1 - f` is our variant (it avoids
a NOT layer).

The result is first stated with the Fourier tail of the witness circuits as a hypothesis
(`fools_of_isKWiseIndependent_of_tail`), in the parametric form of
[Tal, Theorem 20][Tal2017]. The Linial–Mansour–Nisan theorem of this library
(`Unbounded.sum_fourierCoeff_sq_le_of_computes_of_depth_le`) discharges the hypothesis: if `C` has
depth at most `d`, at most `2 ^ q` gates and fan-in less than `2 ^ q`, then every
`independence d q`-wise independent distribution `2 ^ (-q)`-fools `C`
(`fools_of_independence_le`), and `independence d q ≤ (64 q) ^ ((2 d + 3) (d + 7) + 1)`
(`independence_le`, `fools_of_isKWiseIndependent`). Taking `q ≥ log₂ (fan-in + 1)` and `q` at
least `log₂` of the size and of the inverse of the error, `k = (log (m / ε)) ^ O(d²)` independence
suffices for circuits of size `m` with fan-in at most `m`, which is the form of Braverman's
theorem.

The constants are our own and are weaker than Braverman's, since the Linial–Mansour–Nisan theorem
of this library has exponent `1 / (d + 1)` and depth counts negations (`Circuit.depth`).

## Main definitions

* `Cslib.Circuits.Boolean.Braverman.level`, `Cslib.Circuits.Boolean.Braverman.independence`: the
  level of the Fourier tail and the independence used by `fools_of_independence_le`.

## Main results

* `Cslib.Circuits.Boolean.Braverman.fools_of_isKWiseIndependent_of_tail`: Braverman's theorem with
  the Fourier tail of the witness circuits as a hypothesis.
* `Cslib.Circuits.Boolean.Braverman.fools_of_independence_le`: polylogarithmic independence fools
  AC⁰, with the sharp independence `independence d q`.
* `Cslib.Circuits.Boolean.Braverman.fools_of_isKWiseIndependent`: polylogarithmic independence
  fools AC⁰, with the closed-form independence `(64 q) ^ ((2 d + 3) (d + 7) + 1)`.

## References

* [M. Braverman, *Polylogarithmic independence fools AC⁰ circuits*][Braverman2010]
* [A. Tal, *Tight bounds on the Fourier spectrum of AC⁰*][Tal2017]
* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
-/

public section

namespace Cslib.Circuits.Boolean.Braverman

open Finset BitString
open scoped BigOperators

variable {n : ℕ}

/-! ### The average with the uniform distribution -/

section Average

/-- The average of a distribution on the inputs and the uniform distribution. -/
private noncomputable def avgUniform (X : PMF (BitString n)) : PMF (BitString n) :=
  (Cslib.Probability.PMF.uniformOfFintype Bool).bind fun b =>
    cond b X (Cslib.Probability.PMF.uniformOfFintype (BitString n))

private theorem toReal_avgUniform (X : PMF (BitString n)) (x : BitString n) :
    (avgUniform X x).toReal =
      ((X x).toReal + (Cslib.Probability.PMF.uniformOfFintype (BitString n) x).toReal) / 2 := by
  rw [avgUniform, Cslib.Probability.PMF.bind_apply_toReal, Fintype.sum_bool]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_bool, Bool.cond_true,
    Bool.cond_false]
  norm_num
  ring

/-- The probability of an event is the expectation of its indicator. -/
private theorem sum_filter_toReal (p : PMF (BitString n)) (E : BitString n → Bool) :
    ∑ x with E x = true, (p x).toReal = ∑ x, (p x).toReal * bitVal ℝ (E x) := by
  rw [sum_filter]
  refine sum_congr rfl fun x _ => ?_
  cases E x <;> simp

end Average

/-! ### Braverman's theorem with a Fourier tail hypothesis -/

/-- **Braverman's theorem with a Fourier tail hypothesis** [Braverman, Main Theorem][Braverman2010],
in the parametric form of [Tal, Theorem 20][Tal2017]. Let `C` be a circuit of the unbounded fan-in
basis of depth at most `d` and fan-in at most `r < 2 ^ ℓ`, let `2 ≤ ℓ s`, and suppose every circuit
of depth at most `d + 6` and size at most `size C · ((ℓ s + 1) (r + 1) ^ 2 + 3) + 1` has Fourier
weight, read as signs, at most `τ` above level `t`. Then every `k`-wise independent distribution
with `2 ((ℓ s) ^ d + t) ≤ k` fools `C` with error
`8 (41 / 50) ^ s · size C + (2 ^ (2 (ℓ + 1) ((ℓ s) ^ d - 1)) + 1) ^ 2 τ / 2`.

The size and depth of the witness circuits and the constants are our own count. -/
theorem fools_of_isKWiseIndependent_of_tail {X : PMF (BitString n)} {ℓ s r d t k : ℕ} {τ : ℝ}
    (hℓs : 2 ≤ ℓ * s) (hr : r < 2 ^ ℓ) (C : Circuit Unbounded.signature n 1)
    (hC : C.FanInAtMost r) (hd : C.depth ≤ d)
    (htail : ∀ W : Circuit Unbounded.signature n 1,
      W.size ≤ C.size * ((ℓ * s + 1) * (r + 1) ^ 2 + 3) + 1 → W.depth ≤ d + 6 →
      ∑ U with t < #U,
        fourierCoeff (fun x => signVal (W.eval Unbounded.interpretation x 0)) U ^ 2 ≤ τ)
    (hk : 2 * ((ℓ * s) ^ d + t) ≤ k) (hX : IsKWiseIndependent k X) :
    Fools X (8 * (41 / 50) ^ s * C.size +
        (2 ^ (2 * (ℓ + 1) * ((ℓ * s) ^ d - 1)) + 1) ^ 2 * τ / 2)
      fun x => bitVal ℝ (C.eval Unbounded.interpretation x 0) := by
  obtain ⟨f, hf, hfL, W, hWs, hWd, hWν, hWf⟩ := exists_lowDegree_approx (avgUniform X) hℓs hr C hC
  set E : BitString n → Bool := fun x => W.eval Unbounded.interpretation x 0
  obtain ⟨e, he, heq⟩ := exists_mem_lowDegree_expect_sq_bitVal_sub_eq E t
  set U := Cslib.Probability.PMF.uniformOfFintype (BitString n)
  have h1 : 1 ≤ ℓ * s := by omega
  have hD : (ℓ * s) ^ C.depth ≤ (ℓ * s) ^ d := Nat.pow_le_pow_right h1 hd
  have hL (x : BitString n) : |f x| ≤ 2 ^ (2 * (ℓ + 1) * ((ℓ * s) ^ d - 1)) :=
    (hfL x).trans (pow_le_pow_right₀ one_le_two
      (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hD 1)))
  -- the witness is rare under both `X` and the uniform distribution
  have hν : ∑ x, (X x).toReal * bitVal ℝ (E x) + ∑ x, (U x).toReal * bitVal ℝ (E x) ≤
      2 * ((41 / 50) ^ s * C.size) := by
    rw [sum_filter_toReal] at hWν
    simp only [toReal_avgUniform] at hWν
    rw [← sum_add_distrib]
    calc ∑ x, ((X x).toReal * bitVal ℝ (E x) + (U x).toReal * bitVal ℝ (E x))
        = 2 * ∑ x, ((X x).toReal + (U x).toReal) / 2 * bitVal ℝ (E x) := by
          rw [mul_sum]
          exact sum_congr rfl fun x _ => by ring
      _ ≤ 2 * ((41 / 50) ^ s * C.size) := by linarith
  have hE0 (x : BitString n) : 0 ≤ bitVal ℝ (E x) := by
    cases E x <;> norm_num
  have hXE0 : 0 ≤ ∑ x, (X x).toReal * bitVal ℝ (E x) :=
    sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg (hE0 x)
  have hUE0 : 0 ≤ ∑ x, (U x).toReal * bitVal ℝ (E x) :=
    sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg (hE0 x)
  have hUE : 𝔼 x, bitVal ℝ (E x) ≤ 2 * ((41 / 50) ^ s * C.size) := by
    rw [← sum_uniformOfFintype_mul]
    linarith
  have h := hX.fools_bitVal_of_witness (lowDegree_mono hD hf) he hk hWf hL (by linarith) hUE
    heq.le
  refine h.mono ?_
  have hτ := mul_le_mul_of_nonneg_left (htail W hWs (by omega))
    (sq_nonneg ((2 : ℝ) ^ (2 * (ℓ + 1) * ((ℓ * s) ^ d - 1)) + 1))
  linarith

/-! ### Polylogarithmic independence -/

/-- The level `σ = 4 (q + 1) A ^ d + A + 4 q + 5`, with `A = q (8 q + 16)`, at which the
Linial–Mansour–Nisan theorem is applied in `fools_of_independence_le`. -/
@[expose] def level (d q : ℕ) : ℕ :=
  4 * (q + 1) * (q * (8 * q + 16)) ^ d + q * (8 * q + 16) + 4 * q + 5

/-- The independence `2 (A ^ d + 4 σ (16 σ + 1) ^ (d + 6))`, with `A = q (8 q + 16)` and
`σ = level d q`, that suffices in `fools_of_independence_le`. -/
@[expose] def independence (d q : ℕ) : ℕ :=
  2 * ((q * (8 * q + 16)) ^ d + 4 * level d q * (16 * level d q + 1) ^ (d + 6))

/-- The independence of `fools_of_independence_le` is at most
`(64 q) ^ ((2 d + 3) (d + 7) + 1)`, polynomial in `q` with exponent quadratic in `d`. -/
theorem independence_le {q : ℕ} (hq : 1 ≤ q) (d : ℕ) :
    independence d q ≤ (64 * q) ^ ((2 * d + 3) * (d + 7) + 1) := by
  set B := 64 * q with hBdef
  set A := q * (8 * q + 16) with hAdef
  set σ := level d q
  have hB : 64 ≤ B := by omega
  have hA : A ≤ B ^ 2 := by
    rw [hAdef, hBdef]
    nlinarith
  have hAd : A ^ d ≤ B ^ (2 * d) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hA d
  have hBd : 1 ≤ B ^ (2 * d) := Nat.one_le_pow _ _ (by omega)
  have hσ : σ ≤ B ^ (2 * d + 2) := by
    have e1 : 4 * (q + 1) * A ^ d ≤ 8 * q ^ 2 * B ^ (2 * d) :=
      Nat.mul_le_mul (by nlinarith) hAd
    have e2 : A + 4 * q + 5 ≤ 33 * q ^ 2 * B ^ (2 * d) :=
      (show A + 4 * q + 5 ≤ 33 * q ^ 2 by rw [hAdef]; nlinarith).trans
        (Nat.le_mul_of_pos_right _ hBd)
    have e3 : 41 * q ^ 2 * B ^ (2 * d) ≤ B ^ 2 * B ^ (2 * d) :=
      Nat.mul_le_mul_right _ (by rw [hBdef]; nlinarith)
    change 4 * (q + 1) * A ^ d + A + 4 * q + 5 ≤ _
    rw [pow_add B, mul_comm (B ^ (2 * d))]
    linarith
  have hB1 : 1 ≤ B ^ (2 * d + 2) := Nat.one_le_pow _ _ (by omega)
  have hσ5 : 5 ≤ σ := Nat.le_add_left _ _
  have hBσ : 64 * σ ≤ B ^ (2 * d + 3) := by
    rw [show 2 * d + 3 = (2 * d + 2) + 1 by ring, pow_succ B, mul_comm _ B]
    exact Nat.mul_le_mul hB hσ
  have h16 : 16 * σ + 1 ≤ B ^ (2 * d + 3) := by omega
  have h4 : 4 * σ ≤ B ^ (2 * d + 3) := by omega
  have ht : 4 * σ * (16 * σ + 1) ^ (d + 6) ≤ B ^ ((2 * d + 3) * (d + 7)) := by
    rw [show (2 * d + 3) * (d + 7) = (2 * d + 3) + (2 * d + 3) * (d + 6) by ring, pow_add B,
      pow_mul B]
    exact Nat.mul_le_mul h4 (Nat.pow_le_pow_left h16 _)
  have hAt : B ^ (2 * d) ≤ B ^ ((2 * d + 3) * (d + 7)) :=
    Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hB4 := Nat.mul_le_mul_left (B ^ ((2 * d + 3) * (d + 7))) hB
  change 2 * (A ^ d + 4 * σ * (16 * σ + 1) ^ (d + 6)) ≤ _
  rw [pow_succ B]
  linarith

/-- The arithmetic behind `fools_of_independence_le`: with `ℓ = q`, `s = 8 q + 16`, fan-in
less than `2 ^ q`, at most `2 ^ q` gates and level `σ = level d q`, the error of
`fools_of_isKWiseIndependent_of_tail` with the Linial–Mansour–Nisan tail is at most `2 ^ (-q)`. -/
private theorem error_le {q m : ℕ} (hq : 1 ≤ q) (hm : m ≤ 2 ^ q) (d : ℕ) :
    8 * (41 / 50 : ℝ) ^ (8 * q + 16) * m +
        (2 ^ (2 * (q + 1) * ((q * (8 * q + 16)) ^ d - 1)) + 1) ^ 2 *
          (2 * ((m * ((q * (8 * q + 16) + 1) * (2 ^ q - 1 + 1) ^ 2 + 3) + 1 : ℕ) : ℝ) /
            2 ^ level d q) / 2 ≤ 1 / 2 ^ q := by
  set A := q * (8 * q + 16)
  set ε := 2 * (q + 1) * (A ^ d - 1)
  set M := m * ((A + 1) * (2 ^ q - 1 + 1) ^ 2 + 3) + 1
  have hq2 : (2 : ℝ) ^ q > 0 := by positivity
  -- the first term
  have h1 : 8 * (41 / 50 : ℝ) ^ (8 * q + 16) * m ≤ 1 / 2 / 2 ^ q := by
    have hp : (41 / 50 : ℝ) ^ (8 * q + 16) ≤ (1 / 2) ^ (2 * q + 4) := by
      rw [show 8 * q + 16 = 4 * (2 * q + 4) by ring, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have hm' : (m : ℝ) ≤ 2 ^ q := by exact_mod_cast hm
    have h : (1 / 2 : ℝ) ^ (2 * q + 4) = 1 / 16 / (2 ^ q * 2 ^ q) := by
      rw [one_div_pow, pow_add, pow_mul']
      ring
    rw [h] at hp
    calc 8 * (41 / 50 : ℝ) ^ (8 * q + 16) * m ≤ 8 * (1 / 16 / (2 ^ q * 2 ^ q)) * 2 ^ q := by
          gcongr
      _ = 1 / 2 / 2 ^ q := by field_simp; ring
  -- the second term, in natural numbers
  have hN : (2 ^ ε + 1) ^ 2 * M * 2 ^ (q + 1) ≤ 2 ^ level d q := by
    have hq1 : 2 ^ q - 1 + 1 = 2 ^ q := Nat.sub_add_cancel (Nat.one_le_two_pow)
    have hA1 : A + 1 ≤ 2 ^ A := Nat.lt_two_pow_self
    have hE : (2 ^ ε + 1) ^ 2 ≤ 2 ^ (2 * ε + 2) := by
      have : 1 ≤ 2 ^ ε := Nat.one_le_two_pow
      calc (2 ^ ε + 1) ^ 2 ≤ (2 ^ ε + 2 ^ ε) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 2 ^ (2 * ε + 2) := by ring
    have hM : M ≤ 2 ^ (A + 3 * q + 2) := by
      change m * ((A + 1) * (2 ^ q - 1 + 1) ^ 2 + 3) + 1 ≤ _
      rw [hq1]
      have hX : 4 ≤ 2 ^ (A + 2 * q) := by
        calc 4 = 2 ^ 2 := rfl
          _ ≤ 2 ^ (A + 2 * q) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hS : (A + 1) * (2 ^ q) ^ 2 ≤ 2 ^ (A + 2 * q) := by
        rw [pow_add, ← pow_mul, mul_comm q 2]
        exact Nat.mul_le_mul_right _ hA1
      have h2q : 1 ≤ 2 ^ q := Nat.one_le_two_pow
      calc m * ((A + 1) * (2 ^ q) ^ 2 + 3) + 1 ≤ 2 ^ q * (2 ^ (A + 2 * q) + 3) + 1 :=
            Nat.add_le_add_right (Nat.mul_le_mul hm (Nat.add_le_add_right hS 3)) 1
        _ ≤ 2 ^ q * (4 * 2 ^ (A + 2 * q)) := by nlinarith
        _ = 2 ^ (A + 3 * q + 2) := by ring
    have hε : 2 * ε ≤ 4 * (q + 1) * A ^ d :=
      calc 2 * ε = 4 * (q + 1) * (A ^ d - 1) := by ring
        _ ≤ 4 * (q + 1) * A ^ d := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    calc (2 ^ ε + 1) ^ 2 * M * 2 ^ (q + 1)
        ≤ 2 ^ (2 * ε + 2) * 2 ^ (A + 3 * q + 2) * 2 ^ (q + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul hE hM)
      _ = 2 ^ (2 * ε + 2 + (A + 3 * q + 2) + (q + 1)) := by ring
      _ ≤ 2 ^ level d q := Nat.pow_le_pow_right (by norm_num) (by
          change _ ≤ 4 * (q + 1) * A ^ d + A + 4 * q + 5
          linarith)
  have hR : ((2 : ℝ) ^ ε + 1) ^ 2 * M * 2 ^ (q + 1) ≤ 2 ^ level d q := by exact_mod_cast hN
  have h2 : ((2 : ℝ) ^ ε + 1) ^ 2 * (2 * (M : ℝ) / 2 ^ level d q) / 2 ≤ 1 / 2 / 2 ^ q := by
    have hl : (0 : ℝ) < 2 ^ level d q := by positivity
    calc ((2 : ℝ) ^ ε + 1) ^ 2 * (2 * (M : ℝ) / 2 ^ level d q) / 2
        = ((2 : ℝ) ^ ε + 1) ^ 2 * M * 2 ^ (q + 1) / 2 ^ level d q * (1 / 2 / 2 ^ q) := by
          field_simp
          ring
      _ ≤ 1 * (1 / 2 / 2 ^ q) := by
          gcongr
          exact (div_le_one hl).2 hR
      _ = 1 / 2 / 2 ^ q := one_mul _
  have hsum : (1 : ℝ) / 2 / 2 ^ q + 1 / 2 / 2 ^ q = 1 / 2 ^ q := by ring
  linarith

/-- **Polylogarithmic independence fools AC⁰, with the sharp independence**
[Braverman, Main Theorem][Braverman2010]. Let `C` be a circuit of the unbounded fan-in basis of
depth at most `d`, with at most `2 ^ q` gates, each of fan-in less than `2 ^ q`, where `q ≥ 1`. Then
every `k`-wise independent distribution on the inputs with `independence d q ≤ k` fools `C` with
error `2 ^ (-q)`. The independence is at most `(64 q) ^ ((2 d + 3) (d + 7) + 1)`
(`independence_le`, `fools_of_isKWiseIndependent`). -/
theorem fools_of_independence_le {X : PMF (BitString n)} {d q k : ℕ} (hq : 1 ≤ q)
    (C : Circuit Unbounded.signature n 1) (hfan : C.FanInAtMost (2 ^ q - 1))
    (hsize : C.size ≤ 2 ^ q) (hd : C.depth ≤ d)
    (hk : independence d q ≤ k) (hX : IsKWiseIndependent k X) :
    Fools X (1 / 2 ^ q) fun x => bitVal ℝ (C.eval Unbounded.interpretation x 0) := by
  have hσ : 5 ≤ level d q := Nat.le_add_left _ _
  set σ := level d q
  set M := C.size * ((q * (8 * q + 16) + 1) * (2 ^ q - 1 + 1) ^ 2 + 3) + 1
  have ht : 2 * max 8 (2 * σ) * (16 * σ + 1) ^ (d + 6) ≤
      4 * σ * (16 * σ + 1) ^ (d + 6) + 1 := by
    rw [max_eq_right (by omega)]
    exact Nat.le_succ_of_le (le_of_eq (by ring))
  have htail (W : Circuit Unbounded.signature n 1) (hWs : W.size ≤ M) (hWd : W.depth ≤ d + 6) :
      ∑ U with 4 * σ * (16 * σ + 1) ^ (d + 6) < #U,
        fourierCoeff (fun x => signVal (W.eval Unbounded.interpretation x 0)) U ^ 2 ≤
        2 * (M : ℝ) / 2 ^ σ := by
    refine (Unbounded.sum_fourierCoeff_sq_le_of_computes_of_depth_le
      (f := fun x => W.eval Unbounded.interpretation x 0)
      (Circuit.computes_single_iff.2 fun x => rfl) (by omega) hWd ht).trans ?_
    gcongr
  exact (fools_of_isKWiseIndependent_of_tail (by nlinarith)
    (Nat.sub_lt Nat.one_le_two_pow one_pos) C hfan hd htail hk hX).mono
    (error_le hq hsize d)

/-- **Polylogarithmic independence fools AC⁰** [Braverman, Main Theorem][Braverman2010]. Let `C`
be a circuit of the unbounded fan-in basis of depth at most `d`, with at most `2 ^ q` gates, each of
fan-in less than `2 ^ q`, where `q ≥ 1`. Then every `k`-wise independent distribution on the
inputs with `k ≥ (64 q) ^ ((2 d + 3) (d + 7) + 1)` fools `C` with error `2 ^ (-q)`.

Taking `q ≥ log₂ (fan-in + 1)` and `q` at least `log₂` of the size and of the inverse of the error,
this is the form `k = (log (m / ε)) ^ O(d²)` of Braverman's theorem; the explicit exponent and
constants are our own, and depth counts negations (`Circuit.depth`). -/
theorem fools_of_isKWiseIndependent {X : PMF (BitString n)} {d q k : ℕ} (hq : 1 ≤ q)
    (C : Circuit Unbounded.signature n 1) (hfan : C.FanInAtMost (2 ^ q - 1))
    (hsize : C.size ≤ 2 ^ q) (hd : C.depth ≤ d)
    (hk : (64 * q) ^ ((2 * d + 3) * (d + 7) + 1) ≤ k) (hX : IsKWiseIndependent k X) :
    Fools X (1 / 2 ^ q) fun x => bitVal ℝ (C.eval Unbounded.interpretation x 0) :=
  fools_of_independence_le hq C hfan hsize hd ((independence_le hq d).trans hk) hX

end Cslib.Circuits.Boolean.Braverman
