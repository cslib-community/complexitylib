/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
public import Complexity.Crypto.Computational.CompositeResiduosity
public import Complexity.Crypto.Computational.Encryption.Basic
public import Complexity.Languages.Probabilistic.UniformNat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Probability.PMF
import Mathlib.FieldTheory.Finite.Basic

/-!
# Paillier encryption

Paillier's public-key encryption scheme ([KatzLindell2020], Construction 15.11) over a modulus
generator `gen` that outputs valid descriptions `(p, q)` of balanced moduli `N = p * q`:

* key generation draws `(p, q) ← gen n` and outputs the public key `N` and the secret key
  `⟨N, φ(N)⟩`;
* encryption of `m` draws a unit `r` modulo `N` and outputs `c = (1 + N) ^ m * r ^ N mod N ^ 2`;
* decryption outputs `((c ^ φ(N) mod N ^ 2) - 1) / N * φ(N)⁻¹ mod N`.

Decryption is correct because raising `c` to the power `φ(N)` removes the randomness and leaves
`1 + m * φ(N) * N` modulo `N ^ 2`. Multiplying two ciphertexts modulo `N ^ 2` preserves plaintext
addition under decryption modulo `N`.

The randomness `r` is drawn from `n + |N|` fair coins with `ProbComp.sampleModNat`; a draw that
is not a unit modulo `N` is replaced by `1`, so decryption is correct on every ciphertext in the
support. Decryption computes `φ(N)⁻¹ mod N` as `φ(N) ^ (φ(N) - 1) mod N`, which is the inverse by
Euler's theorem because `gcd(N, φ(N)) = 1`. Modular exponentiation is square-and-multiply.

The modulus generator is a parameter: validity of its outputs is part of their type, and its
efficiency is a hypothesis of the polynomial-time statements. Constructing such a generator is not
part of this file.

## Main definitions

* `Cslib.Crypto.Paillier.keyGen`, `Cslib.Crypto.Paillier.encrypt`, `Cslib.Crypto.Paillier.decrypt`:
  the Paillier scheme on binary words.
* `Cslib.Crypto.Paillier.addCiphertexts`: multiplication of ciphertexts modulo `N ^ 2`.

## Main results

* `Cslib.Crypto.Paillier.isPPTOn_keyGen`, `Cslib.Crypto.Paillier.isPPTOn_encrypt`,
  `Cslib.Crypto.Paillier.computableInPolyTime_decrypt`: key generation and encryption are uniform
  strict PPT, and decryption is polynomial-time.
* `Cslib.Crypto.Paillier.decrypt_encrypt`: perfect correctness.
* `Cslib.Crypto.Paillier.decrypt_addCiphertexts`: preservation of plaintext addition under
  decryption (the first condition of [KatzLindell2020], Definition 15.14).

## Scope and limitations

* `decrypt_addCiphertexts` establishes preservation of plaintext addition under decryption,
  corresponding to the first condition of [KatzLindell2020], Definition 15.14. It does not
  establish the second condition (equality of the multiplied-encryption distribution with fresh
  encryptions of the sum), which is generally false for the implemented dyadic sampler plus
  `unitOrOne`: at `N = 143`, `n = 0`, and `m₁ = m₂ = 0`, a fresh ciphertext `encNat 1` has mass
  `44 / 256 = 11 / 64`, while multiplying two independent encryptions gives mass
  `2316 / 65536 = 579 / 16384`. The full definition of an additively homomorphic scheme remains a
  separate objective; the IND-CPA reduction ([KatzLindell2020], Theorem 15.13) is in
  `Complexity.Crypto.Computational.Paillier.Security`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Chapter 15,
  Construction 15.11 and Example 15.12.
-/

@[expose] public section

namespace Cslib.Crypto.Paillier

open Probability Turing.MultiTapeTM BalancedModulus

/-! ### Arithmetic on natural numbers -/

/-- Modular exponentiation `x ^ e mod M`. For the degenerate modulus `M = 0` it returns `1`
instead of the unreduced power, so that it is computable in polynomial time on every input. -/
def powMod (M x e : ℕ) : ℕ := if M = 0 then 1 else x ^ e % M

/-- The encryption randomness that is used: `r` itself when it is a unit modulo `N`, and `1`
otherwise. -/
def unitOrOne (N r : ℕ) : ℕ := if Nat.gcd r N = 1 then r else 1

/-- The Paillier ciphertext `(1 + N) ^ m * r ^ N mod N ^ 2` ([KatzLindell2020],
Construction 15.11). -/
def ciphertext (N m r : ℕ) : ℕ := powMod (N ^ 2) (1 + N) m * powMod (N ^ 2) r N % N ^ 2

/-- Paillier decryption of `c` with modulus `N` and totient `t` ([KatzLindell2020],
Construction 15.11): `((c ^ t mod N ^ 2) - 1) / N * t⁻¹ mod N`, where `t⁻¹ mod N` is computed as
`t ^ (t - 1) mod N`. -/
def decryptNat (N t c : ℕ) : ℕ := (powMod (N ^ 2) c t - 1) / N * powMod N t (t - 1) % N

theorem coprime_unitOrOne (N r : ℕ) : (unitOrOne N r).Coprime N := by
  unfold unitOrOne
  split_ifs with h
  · exact h
  · exact Nat.coprime_one_left N

theorem powMod_of_ne_zero {M : ℕ} (hM : M ≠ 0) (x e : ℕ) : powMod M x e = x ^ e % M := by
  simp [powMod, hM]

/-- A Paillier ciphertext is `(1 + N) ^ m * r ^ N` modulo `N ^ 2`. -/
theorem natCast_ciphertext {N : ℕ} (hN : N ≠ 0) (m r : ℕ) :
    (ciphertext N m r : ZMod (N ^ 2)) = (1 + N) ^ m * (r : ZMod (N ^ 2)) ^ N := by
  have hN2 : N ^ 2 ≠ 0 := pow_ne_zero 2 hN
  simp only [ciphertext, powMod_of_ne_zero hN2, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one]

/-- **Correctness of Paillier decryption** ([KatzLindell2020], Construction 15.11): if
`c ≡ (1 + N) ^ m * r ^ N (mod N ^ 2)` for some `r` coprime to `N`, and `gcd(N, φ(N)) = 1`, then
decryption with the totient `φ(N)` returns `m mod N`. -/
theorem decryptNat_eq {N c m r : ℕ} (hN : 1 < N) (hcop : N.Coprime N.totient)
    (hr : r.Coprime N) (hc : (c : ZMod (N ^ 2)) = (1 + N) ^ m * (r : ZMod (N ^ 2)) ^ N) :
    decryptNat N N.totient c = m % N := by
  have hN0 : N ≠ 0 := by lia
  have hN2 : N ^ 2 ≠ 0 := pow_ne_zero 2 hN0
  -- Raising `c` to the power `φ(N)` leaves `1 + (m * φ(N) mod N) * N`.
  have hpow : c ^ N.totient % N ^ 2 = 1 + m * N.totient % N * N := by
    have hmod : m * N.totient % N < N := Nat.mod_lt _ (by lia)
    have hlt : 1 + m * N.totient % N * N < N ^ 2 := by nlinarith
    rw [← Nat.mod_eq_of_lt hlt, ← ZMod.natCast_eq_natCast_iff', Nat.cast_pow, hc,
      one_add_pow_mul_pow_pow_totient m hr]
    conv_lhs => rw [← Nat.mod_add_div (m * N.totient) N]
    push_cast
    linear_combination ((m * N.totient / N : ℕ) : ZMod (N ^ 2)) * natCast_mul_self N
  -- `φ(N) ^ (φ(N) - 1)` inverts `φ(N)` modulo `N`, by Euler's theorem.
  have heuler : (N.totient : ZMod N) ^ N.totient = 1 := by
    have := congrArg Units.val (ZMod.pow_totient (ZMod.unitOfCoprime N.totient hcop.symm))
    simpa only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] using this
  have hpos : 0 < N.totient := Nat.totient_pos.mpr (by lia)
  rw [decryptNat, powMod_of_ne_zero hN2, powMod_of_ne_zero hN0, hpow, Nat.add_sub_cancel_left,
    Nat.mul_div_cancel _ (by lia), ← ZMod.natCast_eq_natCast_iff']
  simp only [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_pow]
  calc (m : ZMod N) * N.totient * (N.totient : ZMod N) ^ (N.totient - 1)
      = m * (N.totient : ZMod N) ^ (N.totient - 1 + 1) := by rw [pow_succ]; ring
    _ = m := by rw [Nat.sub_add_cancel hpos, heuler, mul_one]

/-! ### The scheme on binary words -/

/-- **Paillier key generation** ([KatzLindell2020], Construction 15.11) over a modulus
generator `gen`: draw `(p, q) ← gen n` and output the public key `N = p * q` and the secret key
`⟨N, φ(N)⟩`, with `φ(N) = (p - 1) * (q - 1)`. -/
noncomputable def keyGen (gen : ℕ → ProbComp Desc) (n : ℕ) : ProbComp (List Bool × List Bool) :=
  do
  let d ← gen n
  return (encNat d.modulus, encPair encNat encNat (d.modulus, d.totient))

/-- **Paillier encryption** ([KatzLindell2020], Construction 15.11) of `m` under the public key
`pk = N`: draw `r < N` from `n + |N|` fair coins, use `1` instead if `r` is not a unit modulo
`N`, and output `(1 + N) ^ m * r ^ N mod N ^ 2`. -/
noncomputable def encrypt (n : ℕ) (pk : List Bool) (m : ℕ) : ProbComp (List Bool) := do
  let r ← ProbComp.sampleModNat (n + (encNat (ofBits pk)).length) (ofBits pk)
  return encNat (ciphertext (ofBits pk) m (unitOrOne (ofBits pk) r))

/-- **Paillier decryption** ([KatzLindell2020], Construction 15.11) of `ct` under the secret key
`sk = ⟨N, φ(N)⟩`. -/
def decrypt (sk ct : List Bool) : List Bool :=
  encNat (decryptNat (ofBits (unframe sk)) (ofBits (dropFrame sk)) (ofBits ct))

/-- Homomorphic addition: multiply two ciphertexts modulo `N ^ 2`, for the public key `pk = N`. -/
def addCiphertexts (pk ct₁ ct₂ : List Bool) : List Bool :=
  encNat (ofBits ct₁ * ofBits ct₂ % ofBits pk ^ 2)

/-! ### Efficiency -/

/-- `powMod` is computable in polynomial time. -/
theorem computableInPolyTime_powMod {α : Type} {input : α ↪ List Bool} {M x e : α → ℕ}
    (hM : ComputableInPolyTime M input encNat) (hx : ComputableInPolyTime x input encNat)
    (he : ComputableInPolyTime e input encNat) :
    ComputableInPolyTime (fun a => powMod (M a) (x a) (e a)) input encNat := by
  have hpow := ComputableInPolyTime.binary_powMod hx he
    (.of_tidy (ComputableTidilyInPolyTime.binary_add'
      (ComputableTidilyInPolyTime.binary_sub' hM.tidy (ComputableTidilyInPolyTime.const 1))
      (ComputableTidilyInPolyTime.const 1))) fun _ => Nat.succ_pos _
  have h := ComputableTidilyInPolyTime.ite_decide (condition := fun a => M a = 0)
    (ComputableTidilyInPolyTime.decide_eq' hM.tidy (ComputableTidilyInPolyTime.const 0))
    (ComputableTidilyInPolyTime.const 1) hpow.tidy
  have heq : (fun a => powMod (M a) (x a) (e a)) =
      fun a => if M a = 0 then 1 else x a ^ e a % (M a - 1 + 1) := by
    funext a
    unfold powMod
    split_ifs with h0
    · rfl
    · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h0)]
  rw [heq]
  exact .of_tidy h

/-- `unitOrOne` is computable in polynomial time. -/
theorem computableInPolyTime_unitOrOne {α : Type} {input : α ↪ List Bool} {N r : α → ℕ}
    (hN : ComputableInPolyTime N input encNat) (hr : ComputableInPolyTime r input encNat) :
    ComputableInPolyTime (fun a => unitOrOne (N a) (r a)) input encNat := by
  unfold unitOrOne
  exact .of_tidy (ComputableTidilyInPolyTime.ite_decide
    (ComputableTidilyInPolyTime.decide_eq' (ComputableInPolyTime.binary_gcd' hr hN).tidy
      (ComputableTidilyInPolyTime.const 1)) hr.tidy (ComputableTidilyInPolyTime.const 1))

/-- Squaring is computable in polynomial time. -/
private theorem computableInPolyTime_sq {α : Type} {input : α ↪ List Bool} {N : α → ℕ}
    (hN : ComputableInPolyTime N input encNat) :
    ComputableInPolyTime (fun a => N a ^ 2) input encNat := by
  simpa only [sq] using
    (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.binary_mul' hN.tidy hN.tidy))

/-- `ciphertext` is computable in polynomial time. -/
theorem computableInPolyTime_ciphertext {α : Type} {input : α ↪ List Bool} {N m r : α → ℕ}
    (hN : ComputableInPolyTime N input encNat) (hm : ComputableInPolyTime m input encNat)
    (hr : ComputableInPolyTime r input encNat) :
    ComputableInPolyTime (fun a => ciphertext (N a) (m a) (r a)) input encNat := by
  have hN2 := computableInPolyTime_sq hN
  have h₁ := computableInPolyTime_powMod hN2
    (.of_tidy (ComputableTidilyInPolyTime.binary_add' (ComputableTidilyInPolyTime.const 1)
      hN.tidy)) hm
  have h₂ := computableInPolyTime_powMod hN2 hr hN
  unfold ciphertext
  exact .of_tidy (ComputableTidilyInPolyTime.binary_mod'
    (ComputableTidilyInPolyTime.binary_mul' h₁.tidy h₂.tidy) hN2.tidy)

/-- `decryptNat` is computable in polynomial time. -/
theorem computableInPolyTime_decryptNat {α : Type} {input : α ↪ List Bool} {N t c : α → ℕ}
    (hN : ComputableInPolyTime N input encNat) (ht : ComputableInPolyTime t input encNat)
    (hc : ComputableInPolyTime c input encNat) :
    ComputableInPolyTime (fun a => decryptNat (N a) (t a) (c a)) input encNat := by
  have h₁ := computableInPolyTime_powMod (computableInPolyTime_sq hN) hc ht
  have h₂ := computableInPolyTime_powMod hN ht
    (.of_tidy (ComputableTidilyInPolyTime.binary_sub' ht.tidy (ComputableTidilyInPolyTime.const 1)))
  unfold decryptNat
  exact .of_tidy (ComputableTidilyInPolyTime.binary_mod'
    (ComputableTidilyInPolyTime.binary_mul'
      (ComputableTidilyInPolyTime.binary_div'
        (ComputableTidilyInPolyTime.binary_sub' h₁.tidy (ComputableTidilyInPolyTime.const 1))
        hN.tidy) h₂.tidy) hN.tidy)

/-- Forgetting validity does not change the encoding of a description. -/
private theorem computableInPolyTime_val :
    ComputableInPolyTime (Subtype.val : Desc → ℕ × ℕ) encDesc (encPair encNat encNat) :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- `keyGen gen` is uniformly strict PPT whenever the modulus generator `gen` is. -/
theorem isPPTOn_keyGen {gen : ℕ → ProbComp Desc} (hgen : IsPPTOn encUnary encDesc gen) :
    IsPPTOn encUnary (encPair encBits encBits) (keyGen gen) := by
  unfold keyGen
  have hd := computableInPolyTime_val.comp (ComputableInPolyTime.snd encUnary encDesc)
  have hp := hd.fst'
  have hq := hd.snd'
  have hN : ComputableInPolyTime (fun x : ℕ × Desc => x.2.modulus) (encPair encUnary encDesc)
      encNat := .of_tidy (ComputableTidilyInPolyTime.binary_mul' hp.tidy hq.tidy)
  have ht : ComputableInPolyTime (fun x : ℕ × Desc => x.2.totient) (encPair encUnary encDesc)
      encNat := .of_tidy (ComputableTidilyInPolyTime.binary_mul'
        (ComputableTidilyInPolyTime.binary_sub' hp.tidy (ComputableTidilyInPolyTime.const 1))
        (ComputableTidilyInPolyTime.binary_sub' hq.tidy (ComputableTidilyInPolyTime.const 1)))
  exact hgen.bind_with (hN.encoding_comp.prod (hN.prod ht).encoding_comp).isPPTOn

/-- `encrypt` is uniformly strict PPT. -/
theorem isPPTOn_encrypt :
    IsPPTOn (encPair encUnary (encPair encBits encNat)) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m) := by
  unfold encrypt
  let E := encPair encUnary (encPair encBits encNat)
  have hN : ComputableInPolyTime (fun x : ℕ × List Bool × ℕ => ofBits x.2.1) E encNat :=
    ComputableInPolyTime.bitsToNat.comp' (ComputableInPolyTime.snd encUnary
      (encPair encBits encNat)).fst'
  have hwidth : ComputableInPolyTime (fun x : ℕ × List Bool × ℕ =>
      x.1 + (encNat (ofBits x.2.1)).length) E encUnary :=
    (ComputableInPolyTime.fst encUnary (encPair encBits encNat)).unary_add'
      ((ComputableInPolyTime.encoding_length encNat).comp hN)
  have hN' := hN.comp' (ComputableInPolyTime.fst E encNat)
  have hm := (ComputableInPolyTime.snd encUnary (encPair encBits encNat)).snd'.comp'
    (ComputableInPolyTime.fst E encNat)
  have hr := ComputableInPolyTime.snd E encNat
  exact (isPPTOn_sampleModNat hwidth hN).bind_with
    (computableInPolyTime_ciphertext hN' hm
      (computableInPolyTime_unitOrOne hN' hr)).encoding_comp.isPPTOn

/-- `decrypt` is computable in polynomial time. -/
theorem computableInPolyTime_decrypt :
    ComputableInPolyTime (fun x : List Bool × List Bool => decrypt x.1 x.2)
      (encPair encBits encBits) encBits := by
  have hsk := ComputableInPolyTime.fst encBits encBits
  have hct := ComputableInPolyTime.snd encBits encBits
  unfold decrypt
  exact (computableInPolyTime_decryptNat
    (ComputableInPolyTime.bitsToNat.comp' (ComputableInPolyTime.unframe.comp' hsk))
    (ComputableInPolyTime.bitsToNat.comp' (ComputableInPolyTime.dropFrame.comp' hsk))
    (ComputableInPolyTime.bitsToNat.comp' hct)).encoding_comp

/-- `addCiphertexts` is computable in polynomial time. -/
theorem computableInPolyTime_addCiphertexts :
    ComputableInPolyTime
      (fun ⟨pk, ct₁, ct₂⟩ => addCiphertexts pk ct₁ ct₂)
      (encPair encBits (encPair encBits encBits)) encBits := by
  unfold addCiphertexts
  fun_prop

/-! ### Correctness and the additive homomorphism -/

private theorem ofBits_encNat (x : ℕ) : ofBits (encNat x) = x := Nat.foldr_bit_bits x

private theorem unframe_encPair_encNat (a b : ℕ) :
    unframe (encPair encNat encNat (a, b)) = encNat a := by
  simp only [encPair_apply, unframe_frame_append]

private theorem dropFrame_encPair_encNat (a b : ℕ) :
    dropFrame (encPair encNat encNat (a, b)) = encNat b := by
  simp only [encPair_apply, dropFrame_frame_append]

/-- Key pairs in the support of `keyGen gen n` come from a valid description. -/
theorem exists_of_mem_support_keyGen {gen : ℕ → ProbComp Desc} {n : ℕ}
    {keys : List Bool × List Bool} (hkeys : keys ∈ (ProbComp.eval (keyGen gen n)).support) :
    ∃ d : Desc, keys = (encNat d.modulus, encPair encNat encNat (d.modulus, d.totient)) := by
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at hkeys
  obtain ⟨d, _, rfl⟩ := hkeys
  exact ⟨d, rfl⟩

/-- Ciphertexts in the support of `encrypt n (encNat N) m` are `ciphertext N m r'` for some
`r'` coprime to `N`. -/
theorem exists_of_mem_support_encrypt {n N m : ℕ} {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (encrypt n (encNat N) m)).support) :
    ∃ r : ℕ, r.Coprime N ∧ ct = encNat (ciphertext N m r) := by
  simp only [encrypt, ofBits_encNat, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at hct
  obtain ⟨r, _, rfl⟩ := hct
  exact ⟨unitOrOne N r, coprime_unitOrOne N r, rfl⟩

/-- Decrypting with a secret key `⟨N, φ(N)⟩` of a valid description. -/
private theorem decrypt_encPair (d : Desc) (c : ℕ) :
    decrypt (encPair encNat encNat (d.modulus, d.totient)) (encNat c) =
      encNat (decryptNat d.modulus d.modulus.totient c) := by
  rw [decrypt, unframe_encPair_encNat, dropFrame_encPair_encNat, ofBits_encNat, ofBits_encNat,
    ofBits_encNat, d.totient_eq]

/-- **Perfect correctness of Paillier encryption** ([KatzLindell2020], Construction 15.11): for
every key pair in the support of `keyGen gen n`, every message `m < N`, and every ciphertext `ct`
in the support of `encrypt n pk m`, decryption returns `m`. -/
theorem decrypt_encrypt {gen : ℕ → ProbComp Desc} {n : ℕ} {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (keyGen gen n)).support) {m : ℕ} (hm : m < ofBits keys.1)
    {ct : List Bool} (hct : ct ∈ (ProbComp.eval (encrypt n keys.1 m)).support) :
    decrypt keys.2 ct = encNat m := by
  obtain ⟨d, rfl⟩ := exists_of_mem_support_keyGen hkeys
  rw [ofBits_encNat] at hm
  obtain ⟨r, hr, rfl⟩ := exists_of_mem_support_encrypt hct
  rw [decrypt_encPair, decryptNat_eq d.one_lt_modulus d.coprime_totient hr
    (natCast_ciphertext (NeZero.ne _) m r), Nat.mod_eq_of_lt hm]

/-- **Preservation of plaintext addition under decryption** ([KatzLindell2020], Definition 15.14
and the discussion of Paillier encryption that follows it): for every key pair in the support of
`keyGen gen n` and ciphertexts `ct₁`, `ct₂` in the supports of `encrypt n pk m₁` and
`encrypt n pk m₂`, the product `addCiphertexts pk ct₁ ct₂` decrypts to `(m₁ + m₂) mod N`.

Note: [KatzLindell2020], Definition 15.14 additionally requires equality of the
multiplied-ciphertext distribution with fresh encryptions of the sum. That distribution clause is
not established here (and fails for the dyadic sampler plus `unitOrOne`: at `N = 143`, `n = 0`, and
`m₁ = m₂ = 0`, fresh `encNat 1` has probability mass `44 / 256 = 11 / 64`, whereas multiplying two
independent encryptions yields mass `2316 / 65536 = 579 / 16384`). The full source definition
remains a separate objective. -/
theorem decrypt_addCiphertexts {gen : ℕ → ProbComp Desc} {n : ℕ} {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (keyGen gen n)).support) {m₁ m₂ : ℕ} {ct₁ ct₂ : List Bool}
    (hct₁ : ct₁ ∈ (ProbComp.eval (encrypt n keys.1 m₁)).support)
    (hct₂ : ct₂ ∈ (ProbComp.eval (encrypt n keys.1 m₂)).support) :
    decrypt keys.2 (addCiphertexts keys.1 ct₁ ct₂) = encNat ((m₁ + m₂) % ofBits keys.1) := by
  obtain ⟨d, rfl⟩ := exists_of_mem_support_keyGen hkeys
  obtain ⟨r₁, hr₁, rfl⟩ := exists_of_mem_support_encrypt hct₁
  obtain ⟨r₂, hr₂, rfl⟩ := exists_of_mem_support_encrypt hct₂
  have hN : d.modulus ≠ 0 := NeZero.ne _
  have hc : ((ciphertext d.modulus m₁ r₁ * ciphertext d.modulus m₂ r₂ % d.modulus ^ 2 : ℕ) :
      ZMod (d.modulus ^ 2)) = (1 + d.modulus) ^ (m₁ + m₂) *
        ((r₁ * r₂ : ℕ) : ZMod (d.modulus ^ 2)) ^ d.modulus := by
    rw [ZMod.natCast_mod, Nat.cast_mul, natCast_ciphertext hN, natCast_ciphertext hN]
    push_cast
    ring
  simp only [addCiphertexts, ofBits_encNat]
  rw [decrypt_encPair, decryptNat_eq d.one_lt_modulus d.coprime_totient
    (Nat.Coprime.mul_left hr₁ hr₂) hc]

end Cslib.Crypto.Paillier
