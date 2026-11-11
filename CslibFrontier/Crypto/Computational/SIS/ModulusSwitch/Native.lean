/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.ModulusSwitch
public import CslibFrontier.Computability.PolyTime.ZMod.ModulusSwitch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Native modulus switching of encoded ciphertext rows

The implementation maps the native scalar conversion over runtime rows in the existing
`GeneralSIS.encodeMatrix` representation. Source and target moduli are binary inputs. Dimensions
are represented structurally by framed lists: the certificate is uniform over arbitrary row
counts and lengths, including empty and ragged lists. It counts the complete input encoding,
not a fixed-dimension family or a unary encoding of coefficient magnitudes.

## Main definitions

* `modulusSwitchRows`: apply the integer implementation to natural coefficient representatives.

## Main results

* `computableInPolyTime_modulusSwitchRows`: plain native polynomial-time certificate.
* `modulusSwitchRows_encodeMatrix_extendCiphertext`: exact agreement with the existing
  `moduleLWEModulusSwitch` ciphertext operation and its existing row-list encoding.

No new ciphertext format is introduced. This is original implementation algebra and a native
runtime certificate; it does not assert decoding preservation or cryptographic security.
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

/-- Convert the rows of an existing binary natural matrix encoding. This function preserves
all row lengths; arithmetic parameters are supplied at runtime. -/
@[expose] def modulusSwitchRows (q p : ℕ) (rows : List (List ℕ)) : List (List ℕ) :=
  rows.map fun row => row.map fun (x : ℕ) => ZMod.modulusSwitchResidue q p (x : ℤ)

/-- Uniform native polynomial time in both binary moduli and the complete framed row-list input. -/
theorem computableInPolyTime_modulusSwitchRows :
    ComputableInPolyTime
      (fun a : (ℕ × ℕ) × List (List ℕ) => modulusSwitchRows a.1.1 a.1.2 a.2)
      (encPair (encPair encNat encNat) (encList (encList encNat)))
      (encList (encList encNat)) := by
  have hinput : ComputableInPolyTime
      (fun a : (((ℕ × ℕ) × List (List ℕ)) × List ℕ) × ℕ =>
        (a.1.1.1, (a.2 : ℤ)))
      (encPair
        (encPair (encPair (encPair encNat encNat) (encList (encList encNat)))
          (encList encNat)) encNat)
      (encPair (encPair encNat encNat) encIntBin) := by fun_prop
  have hcoeff := ComputableInPolyTime.modulusSwitchResidue.comp hinput
  have hrow := ComputableInPolyTime.mapWithInput
    (f := fun (a : ((ℕ × ℕ) × List (List ℕ)) × List ℕ) (x : ℕ) =>
      ZMod.modulusSwitchResidue a.1.1.1 a.1.1.2 (x : ℤ))
    (ComputableInPolyTime.snd
      (encPair (encPair encNat encNat) (encList (encList encNat))) (encList encNat)) hcoeff
  have h := ComputableInPolyTime.mapWithInput
    (f := fun (a : (ℕ × ℕ) × List (List ℕ)) (row : List ℕ) => row.map fun (x : ℕ) =>
      ZMod.modulusSwitchResidue a.1.1 a.1.2 (x : ℤ))
    (ComputableInPolyTime.snd (encPair encNat encNat) (encList (encList encNat))) hrow
  simpa only [modulusSwitchRows, Function.comp_def] using h

/-- Applying the native row operation and existing binary encoding gives exactly the existing
switched ciphertext encoding. Neither modulus nor either matrix dimension is fixed by the
native certificate. The arithmetic interpretation assumes positive moduli. -/
theorem modulusSwitchRows_encodeMatrix_extendCiphertext {k n q p : ℕ}
    (hq : 0 < q) (hp : 0 < p) (ct : ModuleLWECiphertext k n q) :
    encList (encList encNat)
        (modulusSwitchRows q p
          (List.ofFn fun i => List.ofFn fun j => (extendCiphertext ct i j).val)) =
      GeneralSIS.encodeMatrix (extendCiphertext (moduleLWEModulusSwitch p ct)) := by
  let : NeZero q := ⟨hq.ne'⟩
  congr 1
  simp only [modulusSwitchRows, List.map_ofFn, Function.comp_def]
  congr 1 with i : 1
  congr 1 with j : 1
  rw [ZMod.modulusSwitchResidue_eq_val hq hp]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  cases i using Fin.cases <;> rfl

end Cslib.Crypto
