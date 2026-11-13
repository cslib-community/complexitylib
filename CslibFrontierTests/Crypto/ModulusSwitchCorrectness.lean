/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.ModulusSwitch.Correctness
import CslibFrontier.Crypto.Computational.SIS.ModulusSwitch.Native

/-! Actual encryption, all modulus parities, nonzero errors/carries, ties and decoding failures. -/

namespace CslibFrontierTests.Crypto.ModulusSwitchCorrectness

open Cslib Cslib.Crypto
open scoped Matrix

private def secret (q : ℕ) : Fin 1 → Fin 2 → ZMod q := ![![1, -1]]
private def ct (q : ℕ) : ModuleLWECiphertext 1 2 q :=
  moduleLWEEncrypt
    (moduleLWEKeyGen (!![![7, 5]]) (secret q) (![![1, 0]]))
    (![![1, 0]]) 0 (![0, -1]) (![true, false])

/-- All four parity combinations apply the honest-encryption theorem with nonzero source error,
source budget one and target budget three. -/
example : moduleLWEDecrypt (secret 16) (moduleLWEModulusSwitch 16 (ct 32)) =
    ![true, false] := by
  have h := moduleLWEDecrypt_modulusSwitch_encrypt_eq
    (q := 32) (p := 16) (Bq := 1) (Bp := 3) (by decide) (by decide)
    (!![![7, 5]]) (secret 32) (![![1, 0]]) (![![1, 0]]) 0 (![0, -1]) (![true, false])
    (by decide) (by norm_num [secret, SIS.liftCentered, Fin.sum_univ_succ,
      show (1 : ZMod 32).valMinAbs = 1 by decide,
      show (-1 : ZMod 32).valMinAbs = -1 by decide])
  have hs : (fun j i => (SIS.liftCentered (secret 32 j) i : ZMod 16)) =
      secret 16 := by decide
  rw [hs] at h
  exact h

example : moduleLWEDecrypt (secret 17) (moduleLWEModulusSwitch 17 (ct 32)) =
    ![true, false] := by
  have h := moduleLWEDecrypt_modulusSwitch_encrypt_eq
    (q := 32) (p := 17) (Bq := 1) (Bp := 3) (by decide) (by decide)
    (!![![7, 5]]) (secret 32) (![![1, 0]]) (![![1, 0]]) 0 (![0, -1]) (![true, false])
    (by decide) (by norm_num [secret, SIS.liftCentered, Fin.sum_univ_succ,
      show (1 : ZMod 32).valMinAbs = 1 by decide,
      show (-1 : ZMod 32).valMinAbs = -1 by decide])
  have hs : (fun j i => (SIS.liftCentered (secret 32 j) i : ZMod 17)) =
      secret 17 := by decide
  rw [hs] at h
  exact h

example : moduleLWEDecrypt (secret 16) (moduleLWEModulusSwitch 16 (ct 31)) =
    ![true, false] := by
  have h := moduleLWEDecrypt_modulusSwitch_encrypt_eq
    (q := 31) (p := 16) (Bq := 1) (Bp := 3) (by decide) (by decide)
    (!![![7, 5]]) (secret 31) (![![1, 0]]) (![![1, 0]]) 0 (![0, -1]) (![true, false])
    (by decide) (by norm_num [secret, SIS.liftCentered, Fin.sum_univ_succ,
      show (1 : ZMod 31).valMinAbs = 1 by decide,
      show (-1 : ZMod 31).valMinAbs = -1 by decide])
  have hs : (fun j i => (SIS.liftCentered (secret 31 j) i : ZMod 16)) =
      secret 16 := by decide
  rw [hs] at h
  exact h

example : moduleLWEDecrypt (secret 17) (moduleLWEModulusSwitch 17 (ct 31)) =
    ![true, false] := by
  have h := moduleLWEDecrypt_modulusSwitch_encrypt_eq
    (q := 31) (p := 17) (Bq := 1) (Bp := 3) (by decide) (by decide)
    (!![![7, 5]]) (secret 31) (![![1, 0]]) (![![1, 0]]) 0 (![0, -1]) (![true, false])
    (by decide) (by norm_num [secret, SIS.liftCentered, Fin.sum_univ_succ,
      show (1 : ZMod 31).valMinAbs = 1 by decide,
      show (-1 : ZMod 31).valMinAbs = -1 by decide])
  have hs : (fun j i => (SIS.liftCentered (secret 31 j) i : ZMod 17)) =
      secret 17 := by decide
  rw [hs] at h
  exact h

/-- Both decryptions follow from the actual phase relation and their respective margins. -/
example : moduleLWEDecrypt (secret 16) (moduleLWEModulusSwitch 16 (ct 32)) =
    moduleLWEDecrypt (secret 32) (ct 32) := by
  have h := moduleLWEDecrypt_modulusSwitch_eq_source
    (q := 32) (p := 16) (Bq := 1) (Bp := 3) (by decide) (by decide) (ct 32)
    (![![1, -1]]) (![true, false]) (![1, -1]) (by decide) (by decide)
    (by norm_num [Fin.sum_univ_succ])
  have hs (q : ℕ) : (fun j i => ((![![1, -1]] : Fin 1 → Fin 2 → ℤ) j i : ZMod q)) =
      secret q := by
    ext j i
    fin_cases j; fin_cases i <;> simp [secret]
  simpa only [hs] using h

/-- Canonical source lifts wrap, while the plaintext phase representative is `(17,-1)`.
The canonical ciphertext coefficients `-3` exercise negative half ties at scale one half. -/
example : (ct 32).2 = ![-3, -3] := by decide
example : (![(-3), -3] : Fin 2 → ℤ) -
    innerPoly (![![7, 5]]) (![![1, -1]]) =
    fun i => (![17, -1] : Fin 2 → ℤ) i + 32 * (![-1, 0] : Fin 2 → ℤ) i := by decide
example : round ((16 : ℚ) / 32 * (-3)) = -1 := by norm_num [round_eq]

/-- The message-scale differences in the four parity cases are not all zero. -/
example : |(16 : ℚ) / 32 * (32 / 2 : ℕ) - (16 / 2 : ℕ)| = 0 := by norm_num
example : |(17 : ℚ) / 32 * (32 / 2 : ℕ) - (17 / 2 : ℕ)| = 1 / 2 := by norm_num
example : |(16 : ℚ) / 31 * (31 / 2 : ℕ) - (16 / 2 : ℕ)| = 8 / 31 := by norm_num
example : |(17 : ℚ) / 31 * (31 / 2 : ℕ) - (17 / 2 : ℕ)| = 7 / 31 := by norm_num

private theorem switch_exec {q p : ℕ} (hq : 0 < q) (hp : 0 < p) (x : ZMod q) :
    ZMod.modulusSwitch p x = (ZMod.modulusSwitchResidue q p (x.val : ℤ) : ZMod p) := by
  let : NeZero q := ⟨hq.ne'⟩
  let : NeZero p := ⟨hp.ne'⟩
  rw [ZMod.modulusSwitchResidue_eq_val hq hp]
  simp

private theorem ct_exec {k n q p : ℕ} (hq : 0 < q) (hp : 0 < p)
    (ciphertext : ModuleLWECiphertext k n q) :
    moduleLWEModulusSwitch p ciphertext =
      (fun j i => (ZMod.modulusSwitchResidue q p (ciphertext.1 j i).val : ZMod p),
       fun i => (ZMod.modulusSwitchResidue q p (ciphertext.2 i).val : ZMod p)) := by
  simp only [moduleLWEModulusSwitch, switch_exec hq hp]

/-- Positivity alone is insufficient: a perfectly encoded true phase at eight is lost at two.
The same integer secret two is used at both moduli. -/
private def bad : ModuleLWECiphertext 1 1 8 := (![![1]], ![6])
example : moduleLWEDecrypt (![![2]]) bad = ![true] := by decide
example : moduleLWEDecrypt (![![2]]) (moduleLWEModulusSwitch 2 bad) = ![false] := by
  rw [ct_exec (by decide) (by decide)]
  decide

/-- Modulus one collapses the true message coefficient. -/
example : moduleLWEDecrypt (secret 1) (moduleLWEModulusSwitch 1 (ct 32)) = ![false, false] := by
  rw [ct_exec (by decide) (by decide)]
  decide

/-- The exact decoder threshold is strict: distance four from the true encoding at sixteen
lands at the threshold and decodes false; distance three still decodes true. -/
example : decodePolyMsg (encodePolyMsg 16 ![true] + ![-4]) = ![false] := by decide
example : decodePolyMsg (encodePolyMsg 16 ![true] + ![-3]) = ![true] := by decide

end CslibFrontierTests.Crypto.ModulusSwitchCorrectness
