/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Encoding
public import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Probability.BitString
import CslibFrontier.Tactic.PolyTime

/-!
# Stream encryption under a random initial value

Randomized counter mode ([BonehShoup2023], Section 5.4.2) and output feedback mode
(Exercise 5.15(b)) encrypt in the same way: draw a uniform `n`-bit initial value `iv`, derive a
keystream of whole `n`-bit blocks from the key and `iv`, and output `iv` followed by the message
XORed with the keystream. They differ only in the keystream. `ivStreamEncrypt keystream` and
`ivStreamDecrypt keystream` are this construction for a keystream generator
`keystream n k iv blocks`. Decryption accepts an `n`-bit initial value followed by whole blocks.

Decryption inverts encryption on whole-block messages whenever the keystream has `blocks * n` bits
(`ivStreamDecrypt_ivStreamEncrypt`). Both algorithms are efficient whenever the keystream generator
is computable in polynomial time (`isPPTOn_ivStreamEncrypt`,
`computableInPolyTime_ivStreamDecrypt`).

## Main definitions

* `Cslib.Crypto.ivStreamEncrypt`, `Cslib.Crypto.ivStreamDecrypt`: encryption and decryption.

## Main results

* `Cslib.Crypto.ivStreamDecrypt_ivStreamEncrypt`: correctness.
* `Cslib.Crypto.isPPTOn_ivStreamEncrypt`, `Cslib.Crypto.computableInPolyTime_ivStreamDecrypt`:
  efficiency.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 5.4.2 (printed p. 189) and Exercise 5.15 (printed p. 212).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- Stream encryption under a random initial value: draw a uniform `n`-bit `iv` and output `iv`
followed by the message XORed with the keystream `keystream n k iv (msg.length / n)`. -/
@[expose]
noncomputable def ivStreamEncrypt (keystream : ℕ → List Bool → List Bool → ℕ → List Bool)
    (n : ℕ) (k msg : List Bool) : ProbComp (List Bool) := do
  let iv ← BitString.sampleList n
  return iv ++ List.zipWith xor (keystream n k iv (msg.length / n)) msg

/-- Stream decryption: accept an `n`-bit initial value followed by whole blocks, and XOR the blocks
with the keystream from that initial value. -/
def ivStreamDecrypt (keystream : ℕ → List Bool → List Bool → ℕ → List Bool) (n : ℕ)
    (k ct : List Bool) : Option (List Bool) :=
  if (decide (n ≤ ct.length) && ((ct.length - n) % n == 0)) = true then
    some (List.zipWith xor (keystream n k (ct.take n) ((ct.length - n) / n)) (ct.drop n))
  else
    none

/-- Decryption inverts encryption on whole-block messages when the keystream from every `n`-bit
initial value has `blocks * n` bits. -/
theorem ivStreamDecrypt_ivStreamEncrypt {keystream : ℕ → List Bool → List Bool → ℕ → List Bool}
    {n : ℕ} {k msg : List Bool}
    (hkeystream : ∀ iv : List Bool, iv.length = n →
      (keystream n k iv (msg.length / n)).length = msg.length / n * n)
    (hmsg : msg.length % n = 0) {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (ivStreamEncrypt keystream n k msg)).support) :
    ivStreamDecrypt keystream n k ct = some msg := by
  simp only [ivStreamEncrypt, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hct
  obtain ⟨iv, hiv, rfl⟩ := hct
  have hivLen : iv.length = n := BitString.length_of_mem_support_uniformList hiv
  have hksLen : (keystream n k iv (msg.length / n)).length = msg.length := by
    rw [hkeystream iv hivLen, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmsg)]
  set body := List.zipWith xor (keystream n k iv (msg.length / n)) msg
  have hctLen : (iv ++ body).length = n + msg.length := by
    simp [body, hivLen, hksLen]
  rw [ivStreamDecrypt, hctLen, Nat.add_sub_cancel_left, ← hivLen, List.take_left, List.drop_left,
    hivLen]
  simp [hmsg, body, BitString.zipWith_xor_self_left _ _ hksLen]

/-- Stream encryption is uniformly strict PPT in `(n, k, msg)` when the keystream generator is
computable in polynomial time on `(n, k, iv, blocks)`. -/
theorem isPPTOn_ivStreamEncrypt {keystream : ℕ → List Bool → List Bool → ℕ → List Bool}
    (hkeystream : ComputableInPolyTime
      (fun ((n, k, iv, blocks) : ℕ × List Bool × List Bool × ℕ) => keystream n k iv blocks)
      (encPair encUnary (encPair encBits (encPair encBits encUnary))) encBits) :
    IsPPTOn (encKeyedInput encBits) encBits
      (fun ((n, k, msg) : ℕ × List Bool × List Bool) => ivStreamEncrypt keystream n k msg) := by
  let EIn := encPair (encKeyedInput encBits) encBits
  have hargs : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × List Bool =>
        (p.1.1, p.1.2.1, p.2, p.1.2.2.length / p.1.1))
      EIn (encPair encUnary (encPair encBits (encPair encBits encUnary))) := by
    dsimp only [EIn]; fun_prop
  have hks : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × List Bool =>
        keystream p.1.1 p.1.2.1 p.2 (p.1.2.2.length / p.1.1)) EIn encBits :=
    hkeystream.comp hargs
  have hpost : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × List Bool =>
        p.2 ++ List.zipWith xor (keystream p.1.1 p.1.2.1 p.2 (p.1.2.2.length / p.1.1)) p.1.2.2)
      EIn encBits :=
    ComputableInPolyTime.bitsAppend (by dsimp only [EIn]; fun_prop)
      (ComputableInPolyTime.bitsZipWithInput xor hks (by dsimp only [EIn]; fun_prop))
  exact (ComputableInPolyTime.sampleList (ComputableInPolyTime.fst _ _)).bind_with hpost.isPPTOn

/-- Stream decryption is computable in polynomial time on `(n, k, ct)` when the keystream
generator is computable in polynomial time on `(n, k, iv, blocks)`. -/
theorem computableInPolyTime_ivStreamDecrypt
    {keystream : ℕ → List Bool → List Bool → ℕ → List Bool}
    (hkeystream : ComputableInPolyTime
      (fun ((n, k, iv, blocks) : ℕ × List Bool × List Bool × ℕ) => keystream n k iv blocks)
      (encPair encUnary (encPair encBits (encPair encBits encUnary))) encBits) :
    ComputableInPolyTime
      (fun ((n, k, ct) : ℕ × List Bool × List Bool) => ivStreamDecrypt keystream n k ct)
      (encKeyedInput encBits) (encOption encBits) := by
  let EIn := encKeyedInput encBits
  have hcond : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        decide (p.1 ≤ p.2.2.length) && ((p.2.2.length - p.1) % p.1 == 0))
      EIn encBool := by
    dsimp only [EIn]; fun_prop
  have hargs : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        (p.1, p.2.1, p.2.2.take p.1, (p.2.2.length - p.1) / p.1))
      EIn (encPair encUnary (encPair encBits (encPair encBits encUnary))) := by
    dsimp only [EIn]; fun_prop
  have hks : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        keystream p.1 p.2.1 (p.2.2.take p.1) ((p.2.2.length - p.1) / p.1)) EIn encBits :=
    hkeystream.comp hargs
  have hzip : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        List.zipWith xor (keystream p.1 p.2.1 (p.2.2.take p.1) ((p.2.2.length - p.1) / p.1))
          (p.2.2.drop p.1))
      EIn encBits :=
    ComputableInPolyTime.bitsZipWithInput xor hks (by dsimp only [EIn]; fun_prop)
  exact ComputableInPolyTime.ite hcond ((ComputableInPolyTime.optionSome encBits).comp hzip)
    (ComputableInPolyTime.const none)

end Cslib.Crypto
