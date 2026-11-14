/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Binary
public import CslibFrontier.Init

/-!
# SDitH tweakable salts

SDitH v3 Algorithm 5 copies a `lambda`-bit salt, replaces its low 24 bits with the
little-endian encoding of a tweak, and reserves high bits for domain separation. The hash-based
grinding variant stores a tag in the highest bit. The cipher-based grinding variant clears the
highest bit and stores its tag in the next-highest bit.

This module formalizes only that deterministic `TweakSalt` subroutine. It does not implement
the counter-mode PRG, seed expansion, the SDitH protocol, or a signature security theorem. It is a
function-level specification, not a native machine implementation: later consumers must certify
the cost of producing the `lambda`-bit result and carry that time, output-size, and program-size
cost through their reductions. It proves neither asymptotic scheme-family security nor finite
instantiated candidate/parameter-set advantage bounds.

## Main definitions

* `Cslib.Crypto.SDitH.GrindingVariant`: the hash- and cipher-based grinding branches.
* `Cslib.Crypto.SDitH.tweakSalt`: Algorithm 5's salt transformation.

## Main results

* `Cslib.Crypto.SDitH.tweakSalt_low`: the low 24 bits are the tweak in little-endian order.
* `Cslib.Crypto.SDitH.tweakSalt_hash_high`: the hash-based high tag is exact.
* `Cslib.Crypto.SDitH.tweakSalt_cipher_high`: the cipher-based highest bit is cleared.
* `Cslib.Crypto.SDitH.tweakSalt_cipher_nextHigh`: the cipher-based tag is in the
  next-highest bit.
* `Cslib.Crypto.SDitH.tweakSalt_injective`: for a fixed salt and variant, the tweak and tag
  are recoverable from the result.

## References

* [*The Syndrome Decoding in the Head Signature Scheme*, v3.0, Algorithm 5, pp. 16--17]
  [SDitH2026]
-/

public section

namespace Cslib.Crypto.SDitH

/-- The two grinding branches distinguished by SDitH v3 Algorithm 5. -/
inductive GrindingVariant where
  | hashBased
  | cipherBased
  deriving DecidableEq

/-- SDitH v3 Algorithm 5, `TweakSalt`.

The source assignments are interpreted in their listed order: a high domain-separation tag
overrides a low tweak bit if the coordinates overlap. The standard parameter sets have
`securityBits >= 128`; the useful exactness and injectivity results below assume only
`26 <= securityBits`, which keeps the low 24 tweak coordinates disjoint from both high tags. -/
@[expose]
def tweakSalt (variant : GrindingVariant) {securityBits : Nat}
    (salt : BitString securityBits) (tweak : Fin (2 ^ 24)) (tag : Bool) : BitString securityBits :=
  fun i =>
    match variant with
    | .hashBased =>
        if i.val = securityBits - 1 then tag
        else if hlow : i.val < 24 then
          (BitString.equivFin 24).symm tweak ⟨i.val, hlow⟩
        else salt i
    | .cipherBased =>
        if i.val = securityBits - 2 then tag
        else if i.val = securityBits - 1 then false
        else if hlow : i.val < 24 then
          (BitString.equivFin 24).symm tweak ⟨i.val, hlow⟩
        else salt i

/-- The low 24 bits of a sufficiently wide tweaked salt are the source's little-endian tweak. -/
theorem tweakSalt_low (variant : GrindingVariant) {securityBits : Nat}
    (hsecurity : 26 <= securityBits) (salt : BitString securityBits)
    (tweak : Fin (2 ^ 24)) (tag : Bool) (i : Fin securityBits) (hi : i.val < 24) :
    tweakSalt variant salt tweak tag i = (tweak : Nat).testBit i.val := by
  have hnext : i.val ≠ securityBits - 2 := by omega
  have hhigh : i.val ≠ securityBits - 1 := by omega
  cases variant <;>
    simp only [tweakSalt, hnext, hhigh, ↓reduceIte, hi, dite_true,
      BitString.equivFin_symm_apply]

/-- The hash-based branch puts `tag` in the highest salt bit. -/
@[simp]
theorem tweakSalt_hash_high {securityBits : Nat} (hsecurity : 26 <= securityBits)
    (salt : BitString securityBits) (tweak : Fin (2 ^ 24)) (tag : Bool) :
    tweakSalt .hashBased salt tweak tag ⟨securityBits - 1, by omega⟩ = tag := by
  simp only [tweakSalt, ↓reduceIte]

/-- The cipher-based branch clears the highest salt bit. -/
@[simp]
theorem tweakSalt_cipher_high {securityBits : Nat} (hsecurity : 26 <= securityBits)
    (salt : BitString securityBits) (tweak : Fin (2 ^ 24)) (tag : Bool) :
    tweakSalt .cipherBased salt tweak tag ⟨securityBits - 1, by omega⟩ = false := by
  have hne : securityBits - 1 ≠ securityBits - 2 := by omega
  simp only [tweakSalt, hne, ↓reduceIte]

/-- The cipher-based branch puts `tag` in the next-highest salt bit. -/
@[simp]
theorem tweakSalt_cipher_nextHigh {securityBits : Nat} (hsecurity : 26 <= securityBits)
    (salt : BitString securityBits) (tweak : Fin (2 ^ 24)) (tag : Bool) :
    tweakSalt .cipherBased salt tweak tag ⟨securityBits - 2, by omega⟩ = tag := by
  simp only [tweakSalt, ↓reduceIte]

/-- Away from the low tweak and highest tag coordinates, the hash-based branch preserves the
salt. -/
theorem tweakSalt_hash_middle {securityBits : Nat} (salt : BitString securityBits)
    (tweak : Fin (2 ^ 24)) (tag : Bool) (i : Fin securityBits) (hlow : 24 <= i.val)
    (hhigh : i.val ≠ securityBits - 1) :
    tweakSalt .hashBased salt tweak tag i = salt i := by
  simp only [tweakSalt, hhigh, ↓reduceIte, show ¬i.val < 24 by omega, dite_false]

/-- Away from the low tweak and two highest tag coordinates, the cipher-based branch preserves
the salt. -/
theorem tweakSalt_cipher_middle {securityBits : Nat} (salt : BitString securityBits)
    (tweak : Fin (2 ^ 24)) (tag : Bool) (i : Fin securityBits) (hlow : 24 <= i.val)
    (hnext : i.val ≠ securityBits - 2) (hhigh : i.val ≠ securityBits - 1) :
    tweakSalt .cipherBased salt tweak tag i = salt i := by
  simp only [tweakSalt, hnext, hhigh, ↓reduceIte, show ¬i.val < 24 by omega, dite_false]

/-- For a fixed salt and grinding branch, the tweak and domain-separation tag are recoverable from
the transformed salt. -/
theorem tweakSalt_injective (variant : GrindingVariant) {securityBits : Nat}
    (hsecurity : 26 <= securityBits) (salt : BitString securityBits) :
    Function.Injective fun input : Fin (2 ^ 24) × Bool =>
      tweakSalt variant salt input.1 input.2 := by
  intro input input' heq
  have htweakBits :
      (BitString.equivFin 24).symm input.1 = (BitString.equivFin 24).symm input'.1 := by
    funext i
    rw [BitString.equivFin_symm_apply, BitString.equivFin_symm_apply,
      ← tweakSalt_low variant hsecurity salt input.1 input.2 ⟨i.val, by omega⟩ i.isLt,
      ← tweakSalt_low variant hsecurity salt input'.1 input'.2 ⟨i.val, by omega⟩ i.isLt]
    exact congrFun heq ⟨i.val, by omega⟩
  have htweak : input.1 = input'.1 := by
    exact (BitString.equivFin 24).symm.injective htweakBits
  have htag : input.2 = input'.2 := by
    cases variant
    · rw [← tweakSalt_hash_high hsecurity salt input.1 input.2,
        ← tweakSalt_hash_high hsecurity salt input'.1 input'.2]
      exact congrFun heq ⟨securityBits - 1, by omega⟩
    · exact (tweakSalt_cipher_nextHigh hsecurity salt input.1 input.2).symm.trans
        ((congrFun heq ⟨securityBits - 2, by omega⟩).trans
          (tweakSalt_cipher_nextHigh hsecurity salt input'.1 input'.2))
  exact Prod.ext htweak htag

end Cslib.Crypto.SDitH
