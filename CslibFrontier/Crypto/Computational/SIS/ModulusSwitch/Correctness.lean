/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.ModulusSwitch

/-!
# Decryption correctness after Module-LWE modulus switching

The existing decoder encodes a true bit at `⌊q/2⌋` and tests its centered magnitude against
`⌊q/4⌋`. Scaling changes that message location by
`|(p/q) * ⌊q/2⌋ - ⌊p/2⌋|`, in addition to the scaled source noise and rounding error.
Keeping this term permits both odd and even moduli without changing the decoder.

The same integer secret is cast at both moduli. An actual source phase decomposition supplies
an integer target error; the existing strict decoding margin then recovers the message.
A source decoding margin is needed only to conclude equality of the two decryptions.
These are original sufficient correctness bounds, not optimal margins or security claims.

## Main results

* `exists_moduleLWEModulusSwitch_error`: target message/error decomposition and bound.
* `moduleLWEDecrypt_modulusSwitch_eq`: recover the plaintext under the target margin.
* `moduleLWEDecrypt_modulusSwitch_eq_source`: preserve decryption under both margins.
* `moduleLWEDecrypt_modulusSwitch_encrypt_eq`: apply the bound to honest encryption using
  the existing integer error polynomial.
-/

public section

namespace Cslib.Crypto

/-- Construct a bounded target error relative to the target message encoding. The scale mismatch
between the two integer message locations is explicit; neither modulus is assumed even. -/
theorem exists_moduleLWEModulusSwitch_error {k n q p Bq Bp : ℕ}
    (hq : 0 < q) (hp : 0 < p) (ct : ModuleLWECiphertext k n q)
    (s : Fin k → Fin n → ℤ) (m : Fin n → Bool) (err : Fin n → ℤ)
    (hphase : ct.2 - innerPoly ct.1 (fun j i => (s j i : ZMod q)) =
      encodePolyMsg q m + fun i => (err i : ZMod q))
    (herr : ∀ i, |err i| ≤ Bq)
    (hbudget : (p : ℚ) / q * Bq + (1 + ∑ j, ∑ l, |(s j l : ℚ)|) / 2 +
      |(p : ℚ) / q * (q / 2 : ℕ) - (p / 2 : ℕ)| ≤ Bp) :
    ∃ err' : Fin n → ℤ,
      (moduleLWEModulusSwitch p ct).2 -
          innerPoly (moduleLWEModulusSwitch p ct).1 (fun j i => (s j i : ZMod p)) =
        encodePolyMsg p m + (fun i => (err' i : ZMod p)) ∧
      ∀ i, |err' i| ≤ Bp := by
  let a : Fin n → ℤ := fun i => if m i then ((q / 2 : ℕ) : ℤ) else 0
  let b : Fin n → ℤ := fun i => if m i then ((p / 2 : ℕ) : ℤ) else 0
  let e : Fin n → ℤ := a + err
  have he : (fun i => (e i : ZMod q)) =
      ct.2 - innerPoly ct.1 (fun j i => (s j i : ZMod q)) := by
    rw [hphase]
    funext i
    simp only [e, a, Pi.add_apply, Int.cast_add, encodePolyMsg]
    split_ifs <;> simp only [Int.cast_natCast, Int.cast_zero]
  obtain ⟨e', hphase', hnear, _⟩ :=
    exists_moduleLWEModulusSwitch_phase_of_intCast hq hp ct s e he
  let err' : Fin n → ℤ := e' - b
  refine ⟨err', ?_, ?_⟩
  · rw [hphase']
    funext i
    simp only [err', b, encodePolyMsg, Pi.add_apply, Pi.sub_apply, Int.cast_sub]
    split_ifs <;> simp only [Int.cast_natCast, Int.cast_zero] <;> ring
  · intro i
    have hc : 0 ≤ (p : ℚ) / q := by positivity
    have hei : |(err i : ℚ)| ≤ (Bq : ℚ) := by exact_mod_cast herr i
    have hshift : |(p : ℚ) / q * a i - b i| ≤
        |(p : ℚ) / q * (q / 2 : ℕ) - (p / 2 : ℕ)| := by
      dsimp only [a, b]
      split_ifs
      · exact le_rfl
      · simpa only [Int.cast_zero, mul_zero, sub_self, abs_zero] using abs_nonneg
          ((p : ℚ) / q * (q / 2 : ℕ) - (p / 2 : ℕ))
    have hid : (err' i : ℚ) = ((e' i : ℚ) - (p : ℚ) / q * e i) +
        (p : ℚ) / q * err i + ((p : ℚ) / q * a i - b i) := by
      simp only [err', e, Pi.sub_apply, Pi.add_apply, Int.cast_sub, Int.cast_add]
      ring
    have hi : |(err' i : ℚ)| ≤ (Bp : ℚ) := calc
      |(err' i : ℚ)| ≤ |(e' i : ℚ) - (p : ℚ) / q * e i| +
          (p : ℚ) / q * |(err i : ℚ)| + |(p : ℚ) / q * a i - b i| := by
        rw [hid]
        calc
          _ ≤ |(e' i : ℚ) - (p : ℚ) / q * e i + (p : ℚ) / q * err i| +
              |(p : ℚ) / q * a i - b i| := abs_add_le _ _
          _ ≤ _ := by
            apply add_le_add _ le_rfl
            simpa only [abs_mul, abs_of_nonneg hc] using
              abs_add_le ((e' i : ℚ) - (p : ℚ) / q * e i) ((p : ℚ) / q * err i)
      _ ≤ (1 + ∑ j, ∑ l, |(s j l : ℚ)|) / 2 +
          (p : ℚ) / q * Bq + |(p : ℚ) / q * (q / 2 : ℕ) - (p / 2 : ℕ)| :=
        add_le_add (add_le_add (hnear i) (mul_le_mul_of_nonneg_left hei hc)) hshift
      _ ≤ (Bp : ℚ) := by linarith [hbudget]
    exact_mod_cast hi

/-- The switched ciphertext decrypts to the supplied plaintext under the target decoding margin.
Only positivity, not a source decoding margin, is required at the source modulus. -/
theorem moduleLWEDecrypt_modulusSwitch_eq {k n q p Bq Bp : ℕ}
    (hq : 0 < q) (hp : 4 * Bp + 2 < p) (ct : ModuleLWECiphertext k n q)
    (s : Fin k → Fin n → ℤ) (m : Fin n → Bool) (err : Fin n → ℤ)
    (hphase : ct.2 - innerPoly ct.1 (fun j i => (s j i : ZMod q)) =
      encodePolyMsg q m + fun i => (err i : ZMod q))
    (herr : ∀ i, |err i| ≤ Bq)
    (hbudget : (p : ℚ) / q * Bq + (1 + ∑ j, ∑ l, |(s j l : ℚ)|) / 2 +
      |(p : ℚ) / q * (q / 2 : ℕ) - (p / 2 : ℕ)| ≤ Bp) :
    moduleLWEDecrypt (fun j i => (s j i : ZMod p)) (moduleLWEModulusSwitch p ct) = m := by
  obtain ⟨err', hphase', herr'⟩ := exists_moduleLWEModulusSwitch_error
    hq (by omega) ct s m err hphase herr hbudget
  rw [moduleLWEDecrypt, hphase']
  exact decodePolyMsg_encodePolyMsg_add_noise_of_abs_le hp m herr'

/-- With margins at both moduli, switching preserves the actual decryption result. Neither
source nor target decryption correctness is assumed: both follow from the phase/error bounds. -/
theorem moduleLWEDecrypt_modulusSwitch_eq_source {k n q p Bq Bp : ℕ}
    (hq : 4 * Bq + 2 < q) (hp : 4 * Bp + 2 < p) (ct : ModuleLWECiphertext k n q)
    (s : Fin k → Fin n → ℤ) (m : Fin n → Bool) (err : Fin n → ℤ)
    (hphase : ct.2 - innerPoly ct.1 (fun j i => (s j i : ZMod q)) =
      encodePolyMsg q m + fun i => (err i : ZMod q))
    (herr : ∀ i, |err i| ≤ Bq)
    (hbudget : (p : ℚ) / q * Bq + (1 + ∑ j, ∑ l, |(s j l : ℚ)|) / 2 +
      |(p : ℚ) / q * (q / 2 : ℕ) - (p / 2 : ℕ)| ≤ Bp) :
    moduleLWEDecrypt (fun j i => (s j i : ZMod p)) (moduleLWEModulusSwitch p ct) =
      moduleLWEDecrypt (fun j i => (s j i : ZMod q)) ct := by
  rw [moduleLWEDecrypt_modulusSwitch_eq (by omega) hp ct s m err hphase herr hbudget]
  symm
  rw [moduleLWEDecrypt, hphase]
  exact decodePolyMsg_encodePolyMsg_add_noise_of_abs_le hq m herr

/-- Honest-encryption client of the switching theorem. The integer error is the existing
`moduleLWEErrorPoly` on centered lifts. Its bound can be established by
`abs_moduleLWEErrorPoly_le` from component bounds, or by evaluating a concrete instance. -/
theorem moduleLWEDecrypt_modulusSwitch_encrypt_eq {k n q p Bq Bp : ℕ}
    (hq : 0 < q) (hp : 4 * Bp + 2 < p)
    (A : Matrix (Fin k) (Fin k) (Fin n → ZMod q))
    (s r e e₁ : Fin k → Fin n → ZMod q) (e₂ : Fin n → ZMod q) (m : Fin n → Bool)
    (herr : ∀ i, |moduleLWEErrorPoly
      (fun j => SIS.liftCentered (s j)) (fun j => SIS.liftCentered (r j))
      (fun j => SIS.liftCentered (e j)) (fun j => SIS.liftCentered (e₁ j))
      (SIS.liftCentered e₂) i| ≤ Bq)
    (hbudget : (p : ℚ) / q * Bq +
      (1 + ∑ j, ∑ l, |(SIS.liftCentered (s j) l : ℚ)|) / 2 +
      |(p : ℚ) / q * (q / 2 : ℕ) - (p / 2 : ℕ)| ≤ Bp) :
    moduleLWEDecrypt (fun j i => (SIS.liftCentered (s j) i : ZMod p))
      (moduleLWEModulusSwitch p (moduleLWEEncrypt (moduleLWEKeyGen A s e) r e₁ e₂ m)) = m := by
  apply moduleLWEDecrypt_modulusSwitch_eq hq hp _ _ m _ _ herr hbudget
  have hs : (fun j i => (SIS.liftCentered (s j) i : ZMod q)) = s := by
    funext j i
    exact ZMod.coe_valMinAbs _
  rw [hs, moduleLWEDecrypt_phase_eq, intCast_moduleLWEErrorPoly_liftCentered]

end Cslib.Crypto
