/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.VOLE.Basic
public import CslibFrontier.Foundations.Data.ZMod.PolynomialRoots
import CslibFrontier.Probability.PMF.UniformBound
import Mathlib.Algebra.Field.ZMod

/-!
# IT-MACs over `ZMod n`: root bounds and statistical binding

Over a field, a forged IT-MAC opening passes for at most one global key (`Basic.lean`). Hazay
and Yang [HazayYang2024] run IT-MACs over the ring `ZMod (N ^ ζ)` of Damgård–Jurik plaintexts,
where `N = p * q`. There a nonzero linear or quadratic polynomial can have many roots, and binding
holds only up to the smallest prime factor of the modulus.

Degrees one and two of the root bound `ZMod.card_filter_eval_eq_zero_le` give the IT-MAC binding
lemma and the quadratic root bound of [HazayYang2024], §5.1 (Lemmas 3 and 4 of the ePrint
version), for every modulus `n`: the errors are `1 / n.minFac` and `2 * (n / n.minFac)` roots.
Both bounds are attained for every `n > 1`. For the Damgård–Jurik modulus `(p * q) ^ ζ` with primes
`p < q` they take the paper's form `1 / p` and `2 * p ^ (ζ - 1) * q ^ ζ`.

## Main definitions

* `Cslib.Crypto.Protocols.VOLE.ringMacGap`: the residue `n / n.minFac` in `ZMod n`, a nonzero
  value difference that attains both bounds.

## Main results

* `Cslib.Crypto.Protocols.VOLE.card_filter_mac_eq_le`,
  `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_voleVerifyOpening_le_minFac`: a forged opening
  `x' ≠ x` passes for at most `n / n.minFac` keys, so with probability at most `1 / n.minFac`
  under a uniform key.
* `Cslib.Crypto.Protocols.VOLE.card_filter_quadratic_eq_zero_le`: a quadratic with nonzero
  leading coefficient has at most `2 * (n / n.minFac)` roots.
* `Cslib.Crypto.Protocols.VOLE.card_filter_mac_ringMacGap`,
  `Cslib.Crypto.Protocols.VOLE.card_filter_quadratic_ringMacGap`: both bounds are attained.
* `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_voleVerifyOpening_le_inv_prime`,
  `Cslib.Crypto.Protocols.VOLE.card_filter_quadratic_eq_zero_le_mul_pow`: Lemmas 3 and 4 in the
  paper's form for `ZMod ((p * q) ^ ζ)`.

## References

* [C. Hazay, Y. Yang, *Toward Malicious Constant-Rate 2PC via Arithmetic
  Garbling*][HazayYang2024]
-/

public section

namespace Cslib.Crypto.Protocols.VOLE

open Finset Polynomial Probability
open scoped ENNReal

/-! ### IT-MAC binding over `ZMod n` -/

/-- **IT-MAC binding over `ZMod n`, counting form** ([HazayYang2024], §5.1, Lemma 3). If the
honest IT-MAC relation is `x * Δ + m` and a forger opens a different value `x' ≠ x` with any
tag `m'`, at most `n / n.minFac` global keys `Δ` accept the forgery. -/
theorem card_filter_mac_eq_le {n : ℕ} [NeZero n] {x x' : ZMod n} (m m' : ZMod n)
    (hne : x' ≠ x) :
    (Finset.univ.filter fun delta : ZMod n => x * delta + m = x' * delta + m').card ≤
      n / n.minFac := by
  classical
  let f : (ZMod n)[X] := C (x - x') * X + C (m - m')
  have hlead : x - x' ≠ 0 := sub_ne_zero.mpr hne.symm
  have h1 : f.coeff 1 = x - x' := by simp [f, coeff_C]
  have hf : f ≠ 0 := fun h => hlead (by rw [← h1, h, coeff_zero])
  have hdeg : f.natDegree ≤ 1 := natDegree_linear_le
  have hsub : (Finset.univ.filter fun delta : ZMod n => x * delta + m = x' * delta + m') ⊆
      Finset.univ.filter fun delta : ZMod n => f.eval delta = 0 := by
    intro delta hdelta
    rw [Finset.mem_filter] at hdelta ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [f, eval_add, eval_mul, eval_C, eval_X]
    linear_combination hdelta.2
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ f.natDegree * (n / n.minFac) := ZMod.card_filter_eval_eq_zero_le hf
    _ ≤ 1 * (n / n.minFac) := Nat.mul_le_mul_right _ hdeg
    _ = n / n.minFac := one_mul _

/-- **IT-MAC binding over `ZMod n`** ([HazayYang2024], §5.1, Lemma 3). For opened value vectors
`x' ≠ x`, a forged opening passes verification under a uniform global key with probability at
most `1 / n.minFac`. For the Damgård–Jurik modulus `(p * q) ^ ζ` this is `1 / p`
(`toOuterMeasure_voleVerifyOpening_le_inv_prime`). This is the ring counterpart of
`toOuterMeasure_voleVerifyOpening_le`. -/
theorem toOuterMeasure_voleVerifyOpening_le_minFac {n k : ℕ} [NeZero n]
    {x v x' v' : Fin k → ZMod n} (hne : x' ≠ x) :
    (PMF.uniformOfFintype (ZMod n)).toOuterMeasure
      {delta : ZMod n | ∀ i, x i * delta + v i = x' i * delta + v' i} ≤
      1 / (n.minFac : ℝ≥0∞) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  calc _ ≤ (PMF.uniformOfFintype (ZMod n)).toOuterMeasure
        {delta : ZMod n | x i * delta + v i = x' i * delta + v' i} := by
        apply MeasureTheory.measure_mono
        intro delta h
        exact h i
    _ ≤ ((1 : ℕ) : ℝ≥0∞) / (n.minFac : ℝ≥0∞) := by
        refine PMF.toOuterMeasure_uniformOfFintype_le_div (Nat.minFac_pos n) ?_
        rw [ZMod.card, one_mul]
        exact (Nat.mul_le_mul_left _ (card_filter_mac_eq_le (v i) (v' i) hi)).trans
          (Nat.mul_div_le n n.minFac)
    _ = 1 / (n.minFac : ℝ≥0∞) := by rw [Nat.cast_one]

/-! ### Quadratic root bound -/

/-- **Quadratic root bound over `ZMod n`** ([HazayYang2024], §5.1, Lemma 4). A quadratic
`a * χ ^ 2 + b * χ + c` with `a ≠ 0` has at most `2 * (n / n.minFac)` roots in `ZMod n`. -/
theorem card_filter_quadratic_eq_zero_le {n : ℕ} [NeZero n] {a : ZMod n} (b c : ZMod n)
    (ha : a ≠ 0) :
    (Finset.univ.filter fun χ : ZMod n => a * χ ^ 2 + b * χ + c = 0).card ≤
      2 * (n / n.minFac) := by
  classical
  let f : (ZMod n)[X] := C a * X ^ 2 + C b * X + C c
  have h2 : f.coeff 2 = a := by simp [f]
  have hf : f ≠ 0 := fun h => ha (by rw [← h2, h, coeff_zero])
  have hsub : (Finset.univ.filter fun χ : ZMod n => a * χ ^ 2 + b * χ + c = 0) ⊆
      Finset.univ.filter fun χ : ZMod n => f.eval χ = 0 := by
    intro χ hχ
    rw [Finset.mem_filter] at hχ ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [f] using hχ.2
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ f.natDegree * (n / n.minFac) := ZMod.card_filter_eval_eq_zero_le hf
    _ ≤ 2 * (n / n.minFac) := Nat.mul_le_mul_right _ natDegree_quadratic_le

/-! ### Sharpness -/

/-- The residue `n / n.minFac` in `ZMod n`. It is nonzero for `n > 1`
(`ringMacGap_ne_zero`), and a nonzero value gap of this size attains both bounds above. -/
@[expose] def ringMacGap (n : ℕ) : ZMod n :=
  ((n / n.minFac : ℕ) : ZMod n)

/-- `ringMacGap n * y = 0` exactly when `y` vanishes modulo the smallest prime factor of `n`. -/
theorem ringMacGap_mul_eq_zero_iff {n : ℕ} [NeZero n] (y : ZMod n) :
    ringMacGap n * y = 0 ↔ ZMod.castHom (Nat.minFac_dvd n) (ZMod n.minFac) y = 0 := by
  have hd : 0 < n / n.minFac :=
    Nat.div_pos (Nat.minFac_le (Nat.pos_of_ne_zero (NeZero.ne n))) (Nat.minFac_pos n)
  have key : n ∣ n / n.minFac * y.val ↔ n.minFac ∣ y.val := by
    have h := Nat.mul_dvd_mul_iff_left hd (b := n.minFac) (c := y.val)
    rwa [Nat.div_mul_cancel (Nat.minFac_dvd n)] at h
  have hy : ringMacGap n * y = ((n / n.minFac * y.val : ℕ) : ZMod n) := by
    rw [ringMacGap, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [hy, ZMod.natCast_eq_zero_iff, key, ZMod.castHom_apply, ZMod.cast_eq_val,
    ZMod.natCast_eq_zero_iff]

/-- For `n > 1`, `ringMacGap n` is nonzero. -/
theorem ringMacGap_ne_zero {n : ℕ} (hn : 1 < n) : ringMacGap n ≠ 0 := by
  have : NeZero n := ⟨by omega⟩
  intro h
  have h1 := (ringMacGap_mul_eq_zero_iff (1 : ZMod n)).1 (by rw [h, zero_mul])
  rw [map_one] at h1
  have : Fact (1 < n.minFac) := ⟨(Nat.minFac_prime (by omega)).one_lt⟩
  exact one_ne_zero h1

/-- **Lemma 3 is sharp.** Shifting the value by `ringMacGap n` leaves exactly `n / n.minFac`
accepting keys. -/
theorem card_filter_mac_ringMacGap {n : ℕ} [NeZero n] (x m : ZMod n) :
    (Finset.univ.filter fun delta : ZMod n =>
      x * delta + m = (x + ringMacGap n) * delta + m).card = n / n.minFac := by
  classical
  rw [← ZMod.card_filter_castHom_eq (Nat.minFac_dvd n) 0]
  congr 1
  ext delta
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← ringMacGap_mul_eq_zero_iff]
  constructor <;> intro h <;> linear_combination -h

/-- **Lemma 4 is sharp.** For `n > 1`, the quadratic `g * χ ^ 2 - g * χ` with
`g = ringMacGap n ≠ 0` has exactly `2 * (n / n.minFac)` roots: the residues that are `0` or `1`
modulo `n.minFac`. -/
theorem card_filter_quadratic_ringMacGap {n : ℕ} [NeZero n] (hn : 1 < n) :
    (Finset.univ.filter fun χ : ZMod n =>
      ringMacGap n * χ ^ 2 + -ringMacGap n * χ + 0 = 0).card = 2 * (n / n.minFac) := by
  classical
  have hp := Nat.minFac_prime (show n ≠ 1 by omega)
  have : Fact n.minFac.Prime := ⟨hp⟩
  set g := ZMod.castHom (Nat.minFac_dvd n) (ZMod n.minFac)
  have hsplit : (Finset.univ.filter fun χ : ZMod n =>
      ringMacGap n * χ ^ 2 + -ringMacGap n * χ + 0 = 0) =
      (Finset.univ.filter fun χ : ZMod n => g χ = 0) ∪
        Finset.univ.filter fun χ : ZMod n => g χ = 1 := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [show ringMacGap n * χ ^ 2 + -ringMacGap n * χ + 0 = ringMacGap n * (χ * (χ - 1)) by
      ring, ringMacGap_mul_eq_zero_iff, map_mul, map_sub, map_one, mul_eq_zero, sub_eq_zero]
  have hdisj : Disjoint (Finset.univ.filter fun χ : ZMod n => g χ = 0)
      (Finset.univ.filter fun χ : ZMod n => g χ = 1) := by
    rw [Finset.disjoint_filter]
    intro χ _ h0 h1
    exact zero_ne_one (h0.symm.trans h1)
  rw [hsplit, Finset.card_union_of_disjoint hdisj,
    ZMod.card_filter_castHom_eq (Nat.minFac_dvd n),
    ZMod.card_filter_castHom_eq (Nat.minFac_dvd n), two_mul]

/-! ### Damgård–Jurik moduli -/

/-- For primes `p < q` and `ζ ≠ 0`, the bound `n / n.minFac` at `n = (p * q) ^ ζ` is
`p ^ (ζ - 1) * q ^ ζ`. -/
theorem mul_pow_div_minFac {p q ζ : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hζ : ζ ≠ 0) :
    (p * q) ^ ζ / ((p * q) ^ ζ).minFac = p ^ (ζ - 1) * q ^ ζ := by
  rw [Nat.minFac_mul_pow hp hq hpq hζ, mul_pow]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hζ
  rw [pow_succ' p k, Nat.succ_sub_one, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]

/-- **IT-MAC binding for Damgård–Jurik moduli** ([HazayYang2024], §5.1, Lemma 3, in the paper's
form). Over `ZMod ((p * q) ^ ζ)` with primes `p < q`, a forged opening `x' ≠ x` passes under a
uniform key with probability at most `1 / p`. -/
theorem toOuterMeasure_voleVerifyOpening_le_inv_prime {p q ζ k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hζ : ζ ≠ 0) [NeZero ((p * q) ^ ζ)] {x v x' v' : Fin k → ZMod ((p * q) ^ ζ)}
    (hne : x' ≠ x) :
    (PMF.uniformOfFintype (ZMod ((p * q) ^ ζ))).toOuterMeasure
      {delta | ∀ i, x i * delta + v i = x' i * delta + v' i} ≤ 1 / (p : ℝ≥0∞) := by
  have h := toOuterMeasure_voleVerifyOpening_le_minFac (v := v) (v' := v') hne
  rwa [Nat.minFac_mul_pow hp hq hpq hζ] at h

/-- **Quadratic root bound for Damgård–Jurik moduli** ([HazayYang2024], §5.1, Lemma 4, in the
paper's form). Over `ZMod ((p * q) ^ ζ)` with primes `p < q`, a quadratic with nonzero leading
coefficient has at most `2 * p ^ (ζ - 1) * q ^ ζ` roots. -/
theorem card_filter_quadratic_eq_zero_le_mul_pow {p q ζ : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hζ : ζ ≠ 0) [NeZero ((p * q) ^ ζ)] {a : ZMod ((p * q) ^ ζ)}
    (b c : ZMod ((p * q) ^ ζ)) (ha : a ≠ 0) :
    #{χ : ZMod ((p * q) ^ ζ) | a * χ ^ 2 + b * χ + c = 0} ≤ 2 * p ^ (ζ - 1) * q ^ ζ := by
  have h := card_filter_quadratic_eq_zero_le b c ha
  rwa [mul_pow_div_minFac hp hq hpq hζ, ← mul_assoc] at h

end Cslib.Crypto.Protocols.VOLE
