/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.Decompose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# ML-DSA hint generation and use

ML-DSA compresses a commitment to its high-order bits. The signer supplies one hint bit per
coefficient saying whether a short correction changes those bits, and the verifier uses that bit
to move by one high-order bucket in the direction determined by the low bits. These are Algorithms
39 (`MakeHint`) and 40 (`UseHint`) of [NISTFIPS204].

## Main definitions

* `Cslib.Crypto.MLDSA.makeHint`: whether adding a correction changes the high bits.
* `Cslib.Crypto.MLDSA.useHint`: adjust the high bits by the supplied hint.
* `Cslib.Crypto.MLDSA.hintResidual`: the short residual between the hinted high part and the
  original coefficient.
* `Cslib.Crypto.MLDSA.makeHintVec`, `Cslib.Crypto.MLDSA.useHintVec`: coefficientwise forms.

## Main results

* `Cslib.Crypto.MLDSA.useHint_makeHint`: the recovery property in Lemma 1(1) of the Dilithium
  specification.
* `Cslib.Crypto.MLDSA.useHint_nonneg`, `Cslib.Crypto.MLDSA.useHint_lt`: the output range.
* `Cslib.Crypto.MLDSA.useHint_injective`: distinct hint bits give distinct adjusted high bits.
* `Cslib.Crypto.MLDSA.useHint_mul_eq_add_hintResidual`,
  `Cslib.Crypto.MLDSA.abs_hintResidual_valMinAbs_le`: the residual identity and bound in
  Lemma 1(2) of the Dilithium specification.
* `Cslib.Crypto.MLDSA.useHintVec_makeHintVec`: coefficientwise recovery.

The printed output bound of Algorithm 40 is non-strict, but NIST's potential-updates spreadsheet
(identified 2026-02-27) records the strict range `0 ≤ r₁ < (q - 1) / (2 γ₂)` used by `w1Encode`.
The range theorem below states this corrected bound.

## References

* [S. Bai et al., *CRYSTALS-Dilithium: Algorithm Specifications and Supporting
  Documentation*, Version 3.1][BaiEtAl2021Dilithium]
* [National Institute of Standards and Technology, *Module-Lattice-Based Digital Signature
  Standard*][NISTFIPS204]
-/

@[expose] public section

namespace Cslib.Crypto.MLDSA

/-- `MakeHint` from Algorithm 39 of [NISTFIPS204]. The bit is set exactly when adding `z` changes
the high bits of `r`. -/
def makeHint (q γ₂ : ℕ) (z r : ZMod q) : Bool :=
  decide (highBits q γ₂ r ≠ highBits q γ₂ (r + z))

/-- `UseHint` from Algorithm 40 of [NISTFIPS204]. A set hint moves the high part one bucket up
when the low part is positive and one bucket down otherwise, modulo the number of buckets. -/
def useHint (q γ₂ : ℕ) (h : Bool) (r : ZMod q) : ℤ :=
  let m : ℕ := (q - 1) / (2 * γ₂)
  match h with
  | true =>
    if 0 < lowBits q γ₂ r then (highBits q γ₂ r + 1) % (m : ℤ)
    else (highBits q γ₂ r - 1) % (m : ℤ)
  | false => highBits q γ₂ r

/-- The residual `u = 2 γ₂ · UseHint(h, r, 2 γ₂) - r` in `ℤ_q`. Lemma 1(2) of the
Dilithium v3.1 specification bounds its centered representative by `2 γ₂ + 1`. -/
def hintResidual (q γ₂ : ℕ) (h : Bool) (r : ZMod q) : ZMod q :=
  ((useHint q γ₂ h r * (2 * γ₂ : ℕ) : ℤ) : ZMod q) - r

/-- The hinted high part is the original coefficient plus its residual. This is the scalar
identity used in Equation (9) of Section 6.2.1 of the Dilithium v3.1 specification. -/
theorem useHint_mul_eq_add_hintResidual (q γ₂ : ℕ) (h : Bool) (r : ZMod q) :
    ((useHint q γ₂ h r * (2 * γ₂ : ℕ) : ℤ) : ZMod q) =
      r + hintResidual q γ₂ h r := by
  simp only [hintResidual]
  ring

/-- `MakeHint` is set exactly when the correction changes the high bits. -/
@[simp] theorem makeHint_eq_true_iff {q γ₂ : ℕ} {z r : ZMod q} :
    makeHint q γ₂ z r = true ↔ highBits q γ₂ r ≠ highBits q γ₂ (r + z) := by
  simp [makeHint]

/-- `MakeHint` is clear exactly when the correction leaves the high bits unchanged. -/
@[simp] theorem makeHint_eq_false_iff {q γ₂ : ℕ} {z r : ZMod q} :
    makeHint q γ₂ z r = false ↔ highBits q γ₂ r = highBits q γ₂ (r + z) := by
  simp [makeHint]

/-- A clear hint returns the existing high bits. -/
@[simp] theorem useHint_false (q γ₂ : ℕ) (r : ZMod q) :
    useHint q γ₂ false r = highBits q γ₂ r := by
  simp [useHint]

variable {q γ₂ : ℕ}

private theorem bucketCount_pos (hγ : 0 < γ₂) (hq : 4 * γ₂ < q) :
    0 < (q - 1) / (2 * γ₂) := by
  exact Nat.div_pos (by omega) (by omega)

private theorem eq_bucketCount_mul_add_one (hq : 0 < q) (hdvd : 2 * γ₂ ∣ q - 1) :
    q = (q - 1) / (2 * γ₂) * (2 * γ₂) + 1 := by
  rw [Nat.div_mul_cancel hdvd]
  omega

private theorem two_le_bucketCount (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1)
    (hq : 4 * γ₂ < q) : 2 ≤ (q - 1) / (2 * γ₂) := by
  set m : ℕ := (q - 1) / (2 * γ₂)
  have hqeq : q = m * (2 * γ₂) + 1 := by
    simpa only [m] using eq_bucketCount_mul_add_one (by omega) hdvd
  nlinarith

private theorem neg_one_emod_natCast {m : ℕ} (hm : 0 < m) :
    (-1 : ℤ) % (m : ℤ) = (m : ℤ) - 1 := by
  simpa using (Int.negSucc_emod 0 (b := (m : ℤ)) (by omega))

/-- The exceptional negative representatives next to zero are precisely the wrap-around bucket. -/
private theorem highBits_intCast_eq_zero_of_neg (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1)
    (hq : 4 * γ₂ < q) {c : ℤ} (hc₁ : -(γ₂ : ℤ) ≤ c) (hc₂ : c < 0) :
    highBits q γ₂ (c : ZMod q) = 0 := by
  have : NeZero q := ⟨by omega⟩
  set m : ℕ := (q - 1) / (2 * γ₂)
  have hm : 0 < m := by simpa only [m] using bucketCount_pos hγ hq
  have hqeq : (q : ℤ) = (m : ℤ) * (2 * γ₂ : ℕ) + 1 := by
    exact_mod_cast (show q = m * (2 * γ₂) + 1 by
      simpa only [m] using eq_bucketCount_mul_add_one (by omega) hdvd)
  have hv₀ := abs_lowBits_le (q := q) hγ (c : ZMod q)
  rw [abs_le] at hv₀
  have hv₁₀ := highBits_nonneg (q := q) hγ (c : ZMod q)
  have hv₁m := highBits_lt (q := q) hγ hdvd (by omega) (c : ZMod q)
  change highBits q γ₂ (c : ZMod q) < (m : ℤ) at hv₁m
  have hcast :
      ((highBits q γ₂ (c : ZMod q) * (2 * γ₂ : ℕ) +
        lowBits q γ₂ (c : ZMod q) : ℤ) : ZMod q) = (c : ZMod q) :=
    intCast_highBits_mul_add_lowBits (c : ZMod q)
  have hdiv : (q : ℤ) ∣
      highBits q γ₂ (c : ZMod q) * (2 * γ₂ : ℕ) +
        lowBits q γ₂ (c : ZMod q) - c :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast.symm
  obtain ⟨k, hk⟩ := hdiv
  have hlo : -(q : ℤ) <
      highBits q γ₂ (c : ZMod q) * (2 * γ₂ : ℕ) +
        lowBits q γ₂ (c : ZMod q) - c := by
    push_cast
    nlinarith
  have hhi :
      highBits q γ₂ (c : ZMod q) * (2 * γ₂ : ℕ) +
          lowBits q γ₂ (c : ZMod q) - c < q := by
    push_cast at hqeq hv₁m ⊢
    nlinarith
  rw [hk] at hlo hhi
  have hk0 : k = 0 := by nlinarith
  have heq : highBits q γ₂ (c : ZMod q) * (2 * γ₂ : ℕ) +
      lowBits q γ₂ (c : ZMod q) = c := by
    rw [hk0, mul_zero] at hk
    linarith
  by_contra hne
  have hv₁ : (1 : ℤ) ≤ highBits q γ₂ (c : ZMod q) := by omega
  push_cast at heq
  nlinarith

/-- `UseHint` always returns a nonnegative bucket index under the source parameter hypotheses. -/
theorem useHint_nonneg (hγ : 0 < γ₂) (hq : 4 * γ₂ < q) (h : Bool) (r : ZMod q) :
    0 ≤ useHint q γ₂ h r := by
  have hm := bucketCount_pos hγ hq
  have hmz : (0 : ℤ) < ((q - 1) / (2 * γ₂) : ℕ) := by exact_mod_cast hm
  cases h
  · simpa only [useHint_false] using highBits_nonneg (q := q) hγ r
  · simp only [useHint]
    split <;> exact Int.emod_nonneg _ (ne_of_gt hmz)

/-- `UseHint` returns an index below the number `(q - 1) / (2 γ₂)` of high-order buckets. -/
theorem useHint_lt (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1) (hq : 4 * γ₂ < q)
    (h : Bool) (r : ZMod q) : useHint q γ₂ h r < ((q - 1) / (2 * γ₂) : ℕ) := by
  have hm := bucketCount_pos hγ hq
  have hmz : (0 : ℤ) < ((q - 1) / (2 * γ₂) : ℕ) := by exact_mod_cast hm
  cases h
  · simpa only [useHint_false] using highBits_lt hγ hdvd (by omega) r
  · simp only [useHint]
    split <;> exact Int.emod_lt_of_pos _ hmz

/-- A set hint never produces the unadjusted high bits. This is the scalar separation underlying
Lemma 1(3) of the Dilithium v3.1 specification. -/
theorem useHint_true_ne_highBits (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1)
    (hq : 4 * γ₂ < q) (r : ZMod q) : useHint q γ₂ true r ≠ highBits q γ₂ r := by
  set m : ℕ := (q - 1) / (2 * γ₂)
  have hm : 2 ≤ m := by simpa only [m] using two_le_bucketCount hγ hdvd hq
  have hr₀ := highBits_nonneg (q := q) hγ r
  have hrm := highBits_lt (q := q) hγ hdvd (by omega) r
  change highBits q γ₂ r < (m : ℤ) at hrm
  simp only [useHint]
  split
  · by_cases hnext : highBits q γ₂ r + 1 < (m : ℤ)
    · rw [Int.emod_eq_of_lt (by omega) hnext]
      omega
    · have hnext : highBits q γ₂ r + 1 = (m : ℤ) := by omega
      rw [hnext, Int.emod_self]
      omega
  · by_cases hrpos : 0 < highBits q γ₂ r
    · rw [Int.emod_eq_of_lt (by omega) (by omega)]
      omega
    · have hrzero : highBits q γ₂ r = 0 := by omega
      have hmod := neg_one_emod_natCast (m := m) (by omega)
      rw [hrzero, zero_sub, hmod]
      omega

/-- **Hint injectivity.** For a fixed coefficient, equal `UseHint` outputs imply equal hint bits.
This is the scalar form of Lemma 1(3) in the Dilithium v3.1 specification. -/
theorem useHint_injective (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1) (hq : 4 * γ₂ < q)
    (r : ZMod q) : Function.Injective fun h : Bool => useHint q γ₂ h r := by
  intro h h' heq
  cases h <;> cases h'
  · rfl
  · exfalso
    exact useHint_true_ne_highBits hγ hdvd hq r (by simpa only [useHint_false] using heq.symm)
  · exfalso
    exact useHint_true_ne_highBits hγ hdvd hq r (by simpa only [useHint_false] using heq)
  · rfl

/-- **Arbitrary-hint residual bound.** For every hint bit and coefficient, the centered residual
between `r` and `2 γ₂ · UseHint(h, r, 2 γ₂)` has magnitude at most `2 γ₂ + 1`. This is the scalar
norm statement in Lemma 1(2) of the Dilithium v3.1 specification. The vector lemma additionally
states that only set-hint positions can exceed `γ₂`; that sparsity refinement is separate. -/
theorem abs_hintResidual_valMinAbs_le (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1)
    (hq : 4 * γ₂ < q) (h : Bool) (r : ZMod q) :
    |(hintResidual q γ₂ h r).valMinAbs| ≤ 2 * γ₂ + 1 := by
  have : NeZero q := ⟨by omega⟩
  set m : ℕ := (q - 1) / (2 * γ₂)
  have hm : 0 < m := by simpa only [m] using bucketCount_pos hγ hq
  have hqeq : (q : ℤ) = (m : ℤ) * (2 * γ₂ : ℕ) + 1 := by
    exact_mod_cast (show q = m * (2 * γ₂) + 1 by
      simpa only [m] using eq_bucketCount_mul_add_one (by omega) hdvd)
  have hr₀ := abs_lowBits_le (q := q) hγ r
  rw [abs_le] at hr₀
  have hr₁₀ := highBits_nonneg (q := q) hγ r
  have hr₁m := highBits_lt (q := q) hγ hdvd (by omega) r
  change highBits q γ₂ r < (m : ℤ) at hr₁m
  have hrec := intCast_highBits_mul_add_lowBits (γ₂ := γ₂) r
  have hqzero :
      (((m : ℤ) * (2 * γ₂ : ℕ) + 1 : ℤ) : ZMod q) = 0 := by
    rw [← hqeq]
    simp
  have hmα : (m : ZMod q) * (2 * (γ₂ : ZMod q)) = -1 := by
    have hqzero' := hqzero
    push_cast at hqzero'
    calc
      (m : ZMod q) * (2 * (γ₂ : ZMod q)) =
          (m : ZMod q) * (2 * (γ₂ : ZMod q)) + 1 - 1 := by ring
      _ = 0 - 1 := by rw [hqzero']
      _ = -1 := by ring
  cases h
  · have heq : hintResidual q γ₂ false r = ((-lowBits q γ₂ r : ℤ) : ZMod q) := by
      simp only [hintResidual, useHint_false]
      calc
        ((highBits q γ₂ r * (2 * γ₂ : ℕ) : ℤ) : ZMod q) - r =
            ((highBits q γ₂ r * (2 * γ₂ : ℕ) : ℤ) : ZMod q) -
              ((highBits q γ₂ r * (2 * γ₂ : ℕ) + lowBits q γ₂ r : ℤ) :
                ZMod q) := by rw [hrec]
        _ = ((-lowBits q γ₂ r : ℤ) : ZMod q) := by
          push_cast
          ring
    rw [heq]
    exact (ZMod.abs_valMinAbs_intCast_le _).trans (by
      rw [abs_neg, abs_le]
      constructor <;> omega)
  · change
      abs ((((if 0 < lowBits q γ₂ r then
          (highBits q γ₂ r + 1) % (m : ℤ)
        else (highBits q γ₂ r - 1) % (m : ℤ)) * (2 * γ₂ : ℕ) : ℤ) : ZMod q) -
        r).valMinAbs ≤ 2 * γ₂ + 1
    split
    · rename_i hrpos
      by_cases hnext : highBits q γ₂ r + 1 < (m : ℤ)
      · rw [Int.emod_eq_of_lt (by omega) hnext]
        have heq :
            (((highBits q γ₂ r + 1) * (2 * γ₂ : ℕ) : ℤ) : ZMod q) - r =
              (((2 * γ₂ : ℕ) - lowBits q γ₂ r : ℤ) : ZMod q) := by
          calc
            (((highBits q γ₂ r + 1) * (2 * γ₂ : ℕ) : ℤ) : ZMod q) - r =
                (((highBits q γ₂ r + 1) * (2 * γ₂ : ℕ) : ℤ) : ZMod q) -
                  ((highBits q γ₂ r * (2 * γ₂ : ℕ) + lowBits q γ₂ r : ℤ) :
                    ZMod q) := by rw [hrec]
            _ = (((2 * γ₂ : ℕ) - lowBits q γ₂ r : ℤ) : ZMod q) := by
              push_cast
              ring
        rw [heq]
        exact (ZMod.abs_valMinAbs_intCast_le _).trans (by
          rw [abs_of_nonneg (by push_cast; omega)]
          push_cast
          omega)
      · have hnext : highBits q γ₂ r + 1 = (m : ℤ) := by omega
        rw [hnext, Int.emod_self]
        have hnextZ := congrArg (fun z : ℤ => (z : ZMod q)) hnext
        push_cast at hnextZ
        have hr₁eq : (highBits q γ₂ r : ZMod q) = (m : ZMod q) - 1 := by
          calc
            (highBits q γ₂ r : ZMod q) = (highBits q γ₂ r : ZMod q) + 1 - 1 := by ring
            _ = (m : ZMod q) - 1 := by rw [hnextZ]
        have heq :
            (((0 : ℤ) * (2 * γ₂ : ℕ) : ℤ) : ZMod q) - r =
              (((2 * γ₂ : ℕ) + 1 - lowBits q γ₂ r : ℤ) : ZMod q) := by
          push_cast at hnextZ hqzero
          calc
            (((0 : ℤ) * (2 * γ₂ : ℕ) : ℤ) : ZMod q) - r =
                (((0 : ℤ) * (2 * γ₂ : ℕ) : ℤ) : ZMod q) -
                  ((highBits q γ₂ r * (2 * γ₂ : ℕ) + lowBits q γ₂ r : ℤ) :
                    ZMod q) := by rw [hrec]
            _ = (((2 * γ₂ : ℕ) + 1 - lowBits q γ₂ r : ℤ) : ZMod q) := by
              push_cast
              rw [hr₁eq]
              calc
                0 * (2 * (γ₂ : ZMod q)) -
                    (((m : ZMod q) - 1) * (2 * (γ₂ : ZMod q)) + lowBits q γ₂ r) =
                    -((m : ZMod q) * (2 * (γ₂ : ZMod q))) +
                      2 * (γ₂ : ZMod q) - lowBits q γ₂ r := by ring
                _ = 2 * (γ₂ : ZMod q) + 1 - lowBits q γ₂ r := by rw [hmα]; ring
        rw [heq]
        exact (ZMod.abs_valMinAbs_intCast_le _).trans (by
          rw [abs_of_nonneg (by push_cast; omega)]
          push_cast
          omega)
    · rename_i hrpos
      have hrnonpos : lowBits q γ₂ r ≤ 0 := le_of_not_gt hrpos
      by_cases hr₁pos : 0 < highBits q γ₂ r
      · rw [Int.emod_eq_of_lt (by omega) (by omega)]
        have heq :
            (((highBits q γ₂ r - 1) * (2 * γ₂ : ℕ) : ℤ) : ZMod q) - r =
              ((-(2 * γ₂ : ℕ) - lowBits q γ₂ r : ℤ) : ZMod q) := by
          calc
            (((highBits q γ₂ r - 1) * (2 * γ₂ : ℕ) : ℤ) : ZMod q) - r =
                (((highBits q γ₂ r - 1) * (2 * γ₂ : ℕ) : ℤ) : ZMod q) -
                  ((highBits q γ₂ r * (2 * γ₂ : ℕ) + lowBits q γ₂ r : ℤ) :
                    ZMod q) := by rw [hrec]
            _ = ((-(2 * γ₂ : ℕ) - lowBits q γ₂ r : ℤ) : ZMod q) := by
              push_cast
              ring
        rw [heq]
        exact (ZMod.abs_valMinAbs_intCast_le _).trans (by
          rw [abs_of_nonpos (by push_cast; omega)]
          push_cast
          omega)
      · have hr₁zero : highBits q γ₂ r = 0 := by omega
        have hmod := neg_one_emod_natCast (m := m) (by omega)
        rw [hr₁zero, zero_sub, hmod]
        have heq :
            ((((m : ℤ) - 1) * (2 * γ₂ : ℕ) : ℤ) : ZMod q) - r =
              ((-(2 * γ₂ : ℕ) - 1 - lowBits q γ₂ r : ℤ) : ZMod q) := by
          calc
            ((((m : ℤ) - 1) * (2 * γ₂ : ℕ) : ℤ) : ZMod q) - r =
                ((((m : ℤ) - 1) * (2 * γ₂ : ℕ) : ℤ) : ZMod q) -
                  ((highBits q γ₂ r * (2 * γ₂ : ℕ) + lowBits q γ₂ r : ℤ) :
                    ZMod q) := by rw [hrec]
            _ = ((-(2 * γ₂ : ℕ) - 1 - lowBits q γ₂ r : ℤ) : ZMod q) := by
              push_cast
              rw [hr₁zero]
              simp only [Int.cast_zero, zero_mul, zero_add]
              calc
                ((m : ZMod q) - 1) * (2 * (γ₂ : ZMod q)) - lowBits q γ₂ r =
                    (m : ZMod q) * (2 * (γ₂ : ZMod q)) -
                      2 * (γ₂ : ZMod q) - lowBits q γ₂ r := by ring
                _ = -(2 * (γ₂ : ZMod q)) - 1 - lowBits q γ₂ r := by rw [hmα]; ring
        rw [heq]
        exact (ZMod.abs_valMinAbs_intCast_le _).trans (by
          rw [abs_of_nonpos (by push_cast; omega)]
          push_cast
          omega)

/-- **Hint recovery.** If `|z| ≤ γ₂`, using the hint made from `z` and `r` recovers the high bits
of `r + z`. This is the scalar form of Lemma 1(1) in the Dilithium v3.1 specification, with its
`α` specialized to `2 γ₂`. -/
theorem useHint_makeHint (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1) (hq : 4 * γ₂ < q)
    {z r : ZMod q} (hz : |z.valMinAbs| ≤ γ₂) :
    useHint q γ₂ (makeHint q γ₂ z r) r = highBits q γ₂ (r + z) := by
  have : NeZero q := ⟨by omega⟩
  set m : ℕ := (q - 1) / (2 * γ₂)
  have hm : 0 < m := by simpa only [m] using bucketCount_pos hγ hq
  have hqeq : (q : ℤ) = (m : ℤ) * (2 * γ₂ : ℕ) + 1 := by
    exact_mod_cast (show q = m * (2 * γ₂) + 1 by
      simpa only [m] using eq_bucketCount_mul_add_one (by omega) hdvd)
  have hr₀ := abs_lowBits_le (q := q) hγ r
  rw [abs_le] at hr₀
  have hz₀ := hz
  rw [abs_le] at hz₀
  have hr₁₀ := highBits_nonneg (q := q) hγ r
  have hr₁m := highBits_lt (q := q) hγ hdvd (by omega) r
  change highBits q γ₂ r < (m : ℤ) at hr₁m
  have hsum : r + z =
      ((highBits q γ₂ r * (2 * γ₂ : ℕ) +
        (lowBits q γ₂ r + z.valMinAbs) : ℤ) : ZMod q) := by
    rw [← add_assoc, Int.cast_add, intCast_highBits_mul_add_lowBits, ZMod.coe_valMinAbs]
  by_cases heq : highBits q γ₂ r = highBits q γ₂ (r + z)
  · rw [makeHint_eq_false_iff.mpr heq, useHint_false]
    exact heq
  · rw [makeHint_eq_true_iff.mpr heq]
    simp only [useHint]
    split
    · rename_i hrpos
      have hbig : (γ₂ : ℤ) < lowBits q γ₂ r + z.valMinAbs := by
        by_contra hle
        have hv : highBits q γ₂ (r + z) = highBits q γ₂ r := by
          rw [hsum]
          exact highBits_intCast_mul_add hγ hdvd hr₁₀ hr₁m (by linarith) (by linarith)
        exact heq hv.symm
      by_cases hnext : highBits q γ₂ r + 1 < (m : ℤ)
      · have hsum' : r + z =
            (((highBits q γ₂ r + 1) * (2 * γ₂ : ℕ) +
              (lowBits q γ₂ r + z.valMinAbs - (2 * γ₂ : ℕ)) : ℤ) : ZMod q) := by
          rw [hsum]
          congr 1
          ring
        have hv : highBits q γ₂ (r + z) = highBits q γ₂ r + 1 := by
          rw [hsum']
          exact highBits_intCast_mul_add hγ hdvd (by omega) hnext (by push_cast; linarith)
            (by push_cast; linarith)
        rw [hv, Int.emod_eq_of_lt (by omega) hnext]
      · have hnext : highBits q γ₂ r + 1 = (m : ℤ) := by omega
        have hsum' : r + z =
            ((lowBits q γ₂ r + z.valMinAbs - (2 * γ₂ : ℕ) - 1 : ℤ) : ZMod q) := by
          calc
            r + z = ((highBits q γ₂ r * (2 * γ₂ : ℕ) +
                (lowBits q γ₂ r + z.valMinAbs) : ℤ) : ZMod q) := hsum
            _ = (((q : ℤ) +
                (lowBits q γ₂ r + z.valMinAbs - (2 * γ₂ : ℕ) - 1) : ℤ) :
                  ZMod q) := by
              congr 1
              push_cast at hqeq ⊢
              nlinarith
            _ = ((lowBits q γ₂ r + z.valMinAbs - (2 * γ₂ : ℕ) - 1 : ℤ) :
                  ZMod q) := by
              push_cast
              simp
        have hv : highBits q γ₂ (r + z) = 0 := by
          rw [hsum']
          exact highBits_intCast_eq_zero_of_neg hγ hdvd hq (by push_cast; linarith)
            (by push_cast; linarith)
        rw [hnext, hv, Int.emod_self]
    · rename_i hrpos
      have hrnonpos : lowBits q γ₂ r ≤ 0 := le_of_not_gt hrpos
      have hsmall : lowBits q γ₂ r + z.valMinAbs ≤ -(γ₂ : ℤ) := by
        by_contra hlt
        have hv : highBits q γ₂ (r + z) = highBits q γ₂ r := by
          rw [hsum]
          exact highBits_intCast_mul_add hγ hdvd hr₁₀ hr₁m (by linarith) (by linarith)
        exact heq hv.symm
      by_cases hrone : 0 < highBits q γ₂ r
      · have hsum' : r + z =
            (((highBits q γ₂ r - 1) * (2 * γ₂ : ℕ) +
              (lowBits q γ₂ r + z.valMinAbs + (2 * γ₂ : ℕ)) : ℤ) : ZMod q) := by
          rw [hsum]
          congr 1
          ring
        have hv : highBits q γ₂ (r + z) = highBits q γ₂ r - 1 := by
          rw [hsum']
          exact highBits_intCast_mul_add hγ hdvd (by omega) (by omega)
            (by push_cast; linarith) (by push_cast; linarith)
        rw [hv, Int.emod_eq_of_lt (by omega) (by omega)]
      · have hrzero : highBits q γ₂ r = 0 := by omega
        have hstrict : lowBits q γ₂ r + z.valMinAbs < -(γ₂ : ℤ) := by
          by_contra hlt
          have hb : lowBits q γ₂ r + z.valMinAbs = -(γ₂ : ℤ) := by omega
          have hv : highBits q γ₂ (r + z) = 0 := by
            rw [hsum, hrzero, zero_mul, zero_add, hb]
            exact highBits_intCast_eq_zero_of_neg hγ hdvd hq (by omega) (by omega)
          exact heq (by rw [hrzero, hv])
        have hsum' : r + z =
            ((((m : ℤ) - 1) * (2 * γ₂ : ℕ) +
              (lowBits q γ₂ r + z.valMinAbs + (2 * γ₂ : ℕ) + 1) : ℤ) : ZMod q) := by
          calc
            r + z = ((lowBits q γ₂ r + z.valMinAbs : ℤ) : ZMod q) := by
              rw [hsum, hrzero, zero_mul, zero_add]
            _ = (((q : ℤ) + lowBits q γ₂ r + z.valMinAbs : ℤ) : ZMod q) := by
              push_cast
              simp
            _ = ((((m : ℤ) - 1) * (2 * γ₂ : ℕ) +
                (lowBits q γ₂ r + z.valMinAbs + (2 * γ₂ : ℕ) + 1) : ℤ) :
                  ZMod q) := by
              congr 1
              push_cast at hqeq ⊢
              nlinarith
        have hv : highBits q γ₂ (r + z) = (m : ℤ) - 1 := by
          rw [hsum']
          exact highBits_intCast_mul_add hγ hdvd (by omega) (by omega)
            (by push_cast; linarith) (by push_cast; linarith)
        have hmod := neg_one_emod_natCast (m := m) (by omega)
        rw [hrzero, zero_sub, hmod, hv]

/-- Apply `MakeHint` coefficientwise. -/
def makeHintVec {ι : Type*} (q γ₂ : ℕ) (z r : ι → ZMod q) : ι → Bool :=
  fun i => makeHint q γ₂ (z i) (r i)

/-- Apply `UseHint` coefficientwise. -/
def useHintVec {ι : Type*} (q γ₂ : ℕ) (h : ι → Bool) (r : ι → ZMod q) : ι → ℤ :=
  fun i => useHint q γ₂ (h i) (r i)

/-- Coefficientwise hint recovery. -/
theorem useHintVec_makeHintVec {ι : Type*} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1)
    (hq : 4 * γ₂ < q) {z r : ι → ZMod q} (hz : ∀ i, |(z i).valMinAbs| ≤ γ₂) :
    useHintVec q γ₂ (makeHintVec q γ₂ z r) r = fun i => highBits q γ₂ (r i + z i) := by
  funext i
  exact useHint_makeHint hγ hdvd hq (hz i)

end Cslib.Crypto.MLDSA
