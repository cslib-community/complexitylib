/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
public import Complexity.Crypto.Computational.Encryption.PublicKeyReplacement
public import Complexity.Crypto.Computational.Paillier
public import Complexity.Crypto.Computational.QuadraticResiduosity
public import Complexity.Crypto.Encoding
public import Complexity.Languages.Probabilistic.UniformNat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Jacobi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.PPT.Composition
import Complexity.Computability.Probabilistic.Traverse
import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Crypto.Computational.UnitSampling
import Complexity.Crypto.Game.FourHop
import Complexity.Crypto.Game.Statistical
import Complexity.Crypto.Negligible.Basic
import Complexity.Crypto.Negligible.Dyadic
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.PMF.UniformSubset
import Complexity.Probability.StatisticalDistance
import Complexity.Probability.Uniform
import Complexity.Tactic.PPT
import Complexity.Tactic.PolyTime
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Goldwasser–Micali public-key encryption

The Goldwasser–Micali probabilistic public-key encryption scheme ([KatzLindell2020], Section 15.4.4,
Construction 15.28, Theorem 15.29, and Exercises 15.11–15.12) over distinct odd primes `p ≠ q` with
modulus `N = p * q` and public nonresidue `z ∈ QNR_N^{+1}`:

* **Keys** (`KeyDesc`, `keyGen`, `KeyDesc.ofBlum`): `pk = ⟨N, z⟩` and `sk = ⟨p, q⟩`, with
  `z = N - 1` (`-1 mod N ∈ QNR_N^{+1}`) for Blum moduli ([KatzLindell2020], Exercise 15.12).
* **1-bit scheme** (`encrypt`, `decrypt`): encrypt `m : Bool` as `z ^ m * r ^ 2 mod N` via
  `ProbComp.sampleModNat` + `unitOrOne`, and decrypt via Euler's criterion modulo `p` and `q`
  (`decrypt_encrypt`).
* **XOR homomorphism** (`mulCiphertexts`; [KatzLindell2020], Definition 15.14 and Exercise 15.11):
  ciphertext multiplication modulo `N` preserves plaintext XOR (`decrypt_mulCiphertexts`), and for
  ideal unit-sampling encryption (`idealEncrypt`) both independent multiplication
  (`idealEncrypt_mulCiphertexts_eq`) and re-randomization (`rerandomize_idealEncrypt_eq`) match the
  fresh ciphertext distribution.
* **IND-CPA security** ([KatzLindell2020], Theorem 15.29): `qrDistinguisher` reduces single-bit
  IND-CPA security to `QuadraticResiduosityHard` with factor-`2` loss plus `10 / 2 ^ n` sampling
  tail (`advantage_publicKeyGame_le_qr`, `indcpa_goldwasserMicali`), and `qrWordDistinguisher`
  extends the lossy-public-key reduction to bounded equal-length bit words (`encryptWord`) with
  factor-`2` QR loss independent of message length (`advantage_publicKeyWordGame_le_qr`,
  `indcpaOn_goldwasserMicali_bits`).
* **Necessity of `J_N(z) = +1`**: `jacobiAttackAdversary` is a certified uniform strict-PPT
  adversary achieving exact IND-CPA advantage `1` whenever `z ∈ jacobiNegSet p q`
  (`advantage_jacobiAttackAdversary_eq_one`).

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Section 15.4.4
  (Construction 15.28 and Theorem 15.29, pp. 553–556), Definition 15.14 (p. 537), and
  Exercises 15.11–15.12 (p. 568).
-/

@[expose] public section

namespace Cslib.Crypto.GoldwasserMicali

open Probability Turing.MultiTapeTM Encryption
open Paillier (powMod unitOrOne coprime_unitOrOne powMod_of_ne_zero computableInPolyTime_powMod
  computableInPolyTime_unitOrOne ofBits_encNat unframe_encPair_encNat dropFrame_encPair_encNat)
open scoped ENNReal NNReal Cslib.Probability.PMF

local instance (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] : NeZero (p * q) :=
  ⟨Nat.mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩

/-! ### Key parameters and Blum specialization -/

/-- Validity predicate for Goldwasser–Micali key parameters `((p, q), z)`: `p` and `q` are distinct
odd primes and `z` is the canonical residue `< p * q` of an element in `positiveNonresidues p q`. -/
structure KeyValid (raw : (ℕ × ℕ) × ℕ) : Prop where
  /-- First prime factor is prime. -/
  prime_p : raw.1.1.Prime
  /-- Second prime factor is prime. -/
  prime_q : raw.1.2.Prime
  /-- Prime factors are distinct. -/
  ne_pq : raw.1.1 ≠ raw.1.2
  /-- First prime factor is odd. -/
  two_lt_p : 2 < raw.1.1
  /-- Second prime factor is odd. -/
  two_lt_q : 2 < raw.1.2
  /-- `z` represents an element of `positiveNonresidues p q` (`QNR_N^{+1}`). -/
  exists_posNonresidue :
    ∃ u ∈ @positiveNonresidues raw.1.1 raw.1.2 ⟨prime_p⟩ ⟨prime_q⟩, u.val.val = raw.2

/-- Valid Goldwasser–Micali key parameters `((p, q), z)`. -/
abbrev KeyDesc : Type := { raw : (ℕ × ℕ) × ℕ // KeyValid raw }

namespace KeyDesc

/-- First odd prime factor `p`. -/
abbrev p (k : KeyDesc) : ℕ := k.val.1.1

/-- Second odd prime factor `q`. -/
abbrev q (k : KeyDesc) : ℕ := k.val.1.2

/-- Public quadratic nonresidue `z` with `J_N(z) = +1`. -/
abbrev z (k : KeyDesc) : ℕ := k.val.2

/-- Composite modulus `N = p * q`. -/
abbrev modulus (k : KeyDesc) : ℕ := k.p * k.q

/-- Underlying `ModulusDesc` `(p, q)` of a `KeyDesc`. -/
@[reducible] def toModulusDesc (k : KeyDesc) : ModulusDesc :=
  ⟨k.p, k.q, k.2.prime_p, k.2.prime_q, k.2.ne_pq, k.2.two_lt_p, k.2.two_lt_q⟩

instance (k : KeyDesc) : Fact k.p.Prime := ⟨k.2.prime_p⟩
instance (k : KeyDesc) : Fact k.q.Prime := ⟨k.2.prime_q⟩

/-- Every valid Goldwasser–Micali modulus exceeds `1`. -/
theorem one_lt_modulus (k : KeyDesc) : 1 < k.modulus := by
  have hp := k.2.two_lt_p; have hq := k.2.two_lt_q
  change 1 < k.val.1.1 * k.val.1.2; nlinarith

/-- `z` is strictly smaller than `N = p * q`. -/
theorem z_lt_modulus (k : KeyDesc) : k.z < k.modulus := by
  obtain ⟨u, _, huz⟩ := k.2.exists_posNonresidue
  rw [KeyDesc.z, ← huz]; exact u.val.val_lt

/-- `z` is coprime to `N = p * q`. -/
theorem coprime_z (k : KeyDesc) : k.z.Coprime k.modulus := by
  obtain ⟨u, _, huz⟩ := k.2.exists_posNonresidue
  rw [KeyDesc.z, ← huz]; exact ZMod.val_coe_unit_coprime u

/-- `z` viewed as a unit in `(ZMod k.modulus)ˣ`. -/
def zUnit (k : KeyDesc) : (ZMod k.modulus)ˣ := ZMod.unitOfCoprime k.z k.coprime_z

/-- The canonical natural representative of `k.zUnit` is `k.z`. -/
theorem val_zUnit (k : KeyDesc) : k.zUnit.val.val = k.z := by
  rw [zUnit, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt k.z_lt_modulus]

/-- `k.zUnit` lies in `positiveNonresidues k.p k.q` (`QNR_N^{+1}`). -/
theorem zUnit_mem_positiveNonresidues (k : KeyDesc) :
    k.zUnit ∈ positiveNonresidues k.p k.q := by
  obtain ⟨u, hu, huz⟩ := k.2.exists_posNonresidue
  have heq : k.zUnit = u := by
    ext
    change ((ZMod.unitOfCoprime k.val.2 k.coprime_z : (ZMod k.modulus)ˣ) : ZMod k.modulus) = ↑u
    rw [ZMod.coe_unitOfCoprime, ← huz, ZMod.natCast_zmod_val]
  simpa only [heq] using hu

/-- `k.zUnit` is not a square in `(ZMod k.modulus)ˣ`. -/
theorem not_isSquare_zUnit (k : KeyDesc) : ¬ IsSquare k.zUnit := by
  have hmem := k.zUnit_mem_positiveNonresidues
  simp only [positiveNonresidues, Finset.mem_filter] at hmem
  exact hmem.2.1

/-- Deterministic Blum-integer Goldwasser–Micali key description ([KatzLindell2020],
Exercise 15.12): for a Blum modulus `N = p * q` (`p ≡ q ≡ 3 (mod 4)`), `N - 1` represents `-1` in
`positiveNonresidues p q`. -/
def ofBlum (d : ModulusDesc) (h : IsBlumModulus d.p d.q) : KeyDesc :=
  ⟨((d.p, d.q), d.p * d.q - 1),
    { prime_p := d.prime_p, prime_q := d.prime_q, ne_pq := d.ne_pq,
      two_lt_p := d.two_lt_p, two_lt_q := d.two_lt_q,
      exists_posNonresidue := by
        have hN1 : 1 < d.p * d.q := by have := d.two_lt_p; have := d.two_lt_q; nlinarith
        refine ⟨-1, neg_one_mem_positiveNonresidues d.p d.q h, ?_⟩
        have hcast : ((d.p * d.q - 1 : ℕ) : ZMod (d.p * d.q)) = -1 := by
          apply eq_neg_of_add_eq_zero_left
          have h1 : (d.p * d.q - 1) + 1 = d.p * d.q := by omega
          simpa only [Nat.cast_add, Nat.cast_one] using
            (congrArg (Nat.cast : ℕ → ZMod (d.p * d.q)) h1).trans (ZMod.natCast_self _)
        calc (-1 : (ZMod (d.p * d.q))ˣ).val.val
            = (-1 : ZMod (d.p * d.q)).val := Units.val_neg (1 : (ZMod (d.p * d.q))ˣ) ▸ rfl
          _ = ((d.p * d.q - 1 : ℕ) : ZMod (d.p * d.q)).val := by rw [hcast]
          _ = d.p * d.q - 1 := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] }⟩

end KeyDesc

/-- Encoding of `KeyDesc` as the binary triple `((p, q), z)`. -/
def encKeyDesc : KeyDesc ↪ List Bool :=
  (Function.Embedding.subtype _).trans (encPair (encPair encNat encNat) encNat)

/-! ### Arithmetic encryption, Euler-criterion decryption, and homomorphic multiplication -/

/-- Goldwasser–Micali ciphertext `(if m then z else 1) * (r ^ 2 mod N) mod N`
([KatzLindell2020], Construction 15.28). -/
def ciphertext (N z : ℕ) (m : Bool) (r : ℕ) : ℕ :=
  (if m then z else 1) * powMod N r 2 % N

/-- Quadratic-residuosity test modulo `p * q` via Euler's criterion modulo `p` and `q`. -/
def isQuadResidueNat (p q c : ℕ) : Bool :=
  (powMod p c ((p - 1) / 2) == 1) && (powMod q c ((q - 1) / 2) == 1)

/-- Goldwasser–Micali decryption ([KatzLindell2020], Construction 15.28): return `false` on
quadratic residues and `true` otherwise. -/
def decryptNat (p q c : ℕ) : Bool := !isQuadResidueNat p q c

/-- Homomorphic multiplication of two ciphertexts modulo `N` ([KatzLindell2020], Exercise 15.11). -/
def mulCiphertextsNat (N c₁ c₂ : ℕ) : ℕ := c₁ * c₂ % N

/-- Cast of `ciphertext N z m r` to `ZMod N`. -/
theorem natCast_ciphertext {N : ℕ} (hN : N ≠ 0) (z : ℕ) (m : Bool) (r : ℕ) :
    (ciphertext N z m r : ZMod N) = (if m then (z : ZMod N) else 1) * (r : ZMod N) ^ 2 := by
  simp only [ciphertext, powMod_of_ne_zero hN, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow]
  cases m <;> simp

/-- Canonical residue representation of `ciphertext N z m r` for coprime `z` and `r`. -/
theorem ciphertext_eq_unit_val {N z r : ℕ} [NeZero N] (hz : z.Coprime N) (hr : r.Coprime N)
    (m : Bool) :
    ciphertext N z m r =
      ((if m then ZMod.unitOfCoprime z hz else 1) * (ZMod.unitOfCoprime r hr) ^ 2).val.val := by
  have hcast : ((ciphertext N z m r : ℕ) : ZMod N) =
      ((if m then ZMod.unitOfCoprime z hz else 1) * (ZMod.unitOfCoprime r hr) ^ 2).val := by
    rw [natCast_ciphertext (NeZero.ne N), Units.val_mul, Units.val_pow_eq_pow_val,
      ZMod.coe_unitOfCoprime]
    cases m <;> simp [ZMod.coe_unitOfCoprime]
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) with hN1 | hN1
  · subst hN1
    have hlt1 := ZMod.val_lt
      ((if m then ZMod.unitOfCoprime z hz else 1) * (ZMod.unitOfCoprime r hr) ^ 2).val
    simp only [ciphertext, Nat.mod_one]; omega
  · have hlt : ciphertext N z m r < N := Nat.mod_lt _ (by omega)
    rw [← ZMod.val_natCast_of_lt hlt, hcast]

private theorem powMod_half_eq_one_iff_isSquare (P : ℕ) [Fact P.Prime] (hP : 2 < P)
    (c : ℕ) (v : (ZMod P)ˣ) (hcv : (c : ZMod P) = v.val) :
    powMod P c ((P - 1) / 2) = 1 ↔ IsSquare v := by
  have hhalf : (P - 1) / 2 = P / 2 := by
    have := Nat.odd_iff.mp ((Fact.out : P.Prime).odd_of_ne_two (by omega)); omega
  have hmod : powMod P c ((P - 1) / 2) = 1 ↔ (c : ZMod P) ^ (P / 2) = 1 := by
    rw [powMod_of_ne_zero (by omega), ← hhalf]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simpa only [ZMod.natCast_mod, Nat.cast_pow, Nat.cast_one] using
        congrArg (Nat.cast : ℕ → ZMod P) h
    · have : Fact (1 < P) := ⟨by omega⟩
      simpa only [← Nat.cast_pow, ZMod.val_natCast, ZMod.val_one] using congrArg ZMod.val h
  rw [hmod, hcv, ← ZMod.euler_criterion P v.ne_zero]
  exact ⟨fun ⟨x, hx⟩ => ⟨Units.mk0 x (by rintro rfl; exact v.ne_zero (by rw [hx, mul_zero])),
    Units.ext hx⟩, fun ⟨x, hx⟩ => ⟨x.val, congrArg Units.val hx⟩⟩

/-- Euler's criterion on `(ZMod (d.p * d.q))ˣ`: `isQuadResidueNat d.p d.q` decides `IsSquare u`. -/
theorem isQuadResidueNat_unit_eq (d : ModulusDesc) (u : (ZMod (d.p * d.q))ˣ) :
    isQuadResidueNat d.p d.q u.val.val = decide (IsSquare u) := by
  have hcop : Nat.Coprime d.p d.q := (Nat.coprime_primes d.prime_p d.prime_q).mpr d.ne_pq
  let crt : ZMod (d.p * d.q) ≃+* ZMod d.p × ZMod d.q := ZMod.chineseRemainder hcop
  let e : (ZMod (d.p * d.q))ˣ ≃* (ZMod d.p)ˣ × (ZMod d.q)ˣ :=
    (Units.mapEquiv crt.toMulEquiv).trans MulEquiv.prodUnits
  have hcrt : IsSquare u ↔ IsSquare (e u).1 ∧ IsSquare (e u).2 :=
    ⟨fun ⟨r, hr⟩ => ⟨⟨(e r).1, by rw [hr, map_mul]; rfl⟩, ⟨(e r).2, by rw [hr, map_mul]; rfl⟩⟩,
      fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => ⟨e.symm (a, b), e.injective (by ext <;> simp [ha, hb])⟩⟩
  have hcast_p : (u.val.val : ZMod d.p) = (e u).1.val := by
    let f : ZMod (d.p * d.q) →+* ZMod d.p :=
      (RingHom.fst (ZMod d.p) (ZMod d.q)).comp crt.toRingHom
    calc (u.val.val : ZMod d.p) = f (u.val.val : ZMod (d.p * d.q)) := (map_natCast f _).symm
      _ = f u.val := by rw [ZMod.natCast_zmod_val]
      _ = (e u).1.val := rfl
  have hcast_q : (u.val.val : ZMod d.q) = (e u).2.val := by
    let g : ZMod (d.p * d.q) →+* ZMod d.q :=
      (RingHom.snd (ZMod d.p) (ZMod d.q)).comp crt.toRingHom
    calc (u.val.val : ZMod d.q) = g (u.val.val : ZMod (d.p * d.q)) := (map_natCast g _).symm
      _ = g u.val := by rw [ZMod.natCast_zmod_val]
      _ = (e u).2.val := rfl
  have hp := powMod_half_eq_one_iff_isSquare d.p d.two_lt_p u.val.val (e u).1 hcast_p
  have hq := powMod_half_eq_one_iff_isSquare d.q d.two_lt_q u.val.val (e u).2 hcast_q
  unfold isQuadResidueNat
  exact Bool.eq_iff_iff.mpr (by
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, hp, hq, hcrt])

/-- `decryptNat d.p d.q` decides non-squareness on `(ZMod (d.p * d.q))ˣ`. -/
theorem decryptNat_unit_eq (d : ModulusDesc) (u : (ZMod (d.p * d.q))ˣ) :
    decryptNat d.p d.q u.val.val = decide (¬ IsSquare u) := by
  rw [decryptNat, isQuadResidueNat_unit_eq, ← decide_not]

private theorem isSquare_cond_mul_sq_iff {G : Type*} [CommGroup G] {z : G} (hz : ¬ IsSquare z)
    (m : Bool) (r : G) :
    IsSquare ((if m then z else 1) * r ^ 2) ↔ m = false := by
  cases m
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, iff_true]; exact ⟨r, pow_two r⟩
  · simp only [↓reduceIte, Bool.true_eq_false, iff_false]
    rintro ⟨w, hw⟩; apply hz; refine ⟨w * r⁻¹, ?_⟩
    have h1 : (w * r⁻¹) * (w * r⁻¹) = (w * w) * (r * r)⁻¹ := by
      rw [mul_inv_rev, mul_assoc, mul_left_comm r⁻¹, ← mul_assoc]
    rw [h1, ← hw, pow_two, mul_assoc, mul_inv_cancel, mul_one]

/-- **Arithmetic correctness of Goldwasser–Micali decryption** ([KatzLindell2020],
Construction 15.28): for any non-square unit `z` and coprime `r`, `decryptNat` recovers `m`. -/
theorem decryptNat_ciphertext (d : ModulusDesc) {z r : ℕ}
    (hz : z.Coprime (d.p * d.q)) (hnotsq : ¬ IsSquare (ZMod.unitOfCoprime z hz))
    (hr : r.Coprime (d.p * d.q)) (m : Bool) :
    decryptNat d.p d.q (ciphertext (d.p * d.q) z m r) = m := by
  rw [ciphertext_eq_unit_val hz hr m, decryptNat_unit_eq]
  simp only [isSquare_cond_mul_sq_iff hnotsq]
  cases m <;> decide

/-- Specialization of `decryptNat_ciphertext` to a valid `KeyDesc`. -/
theorem KeyDesc.decryptNat_ciphertext (k : KeyDesc) {r : ℕ} (hr : r.Coprime k.modulus)
    (m : Bool) :
    decryptNat k.p k.q (ciphertext k.modulus k.z m r) = m :=
  GoldwasserMicali.decryptNat_ciphertext k.toModulusDesc k.coprime_z k.not_isSquare_zUnit hr m

/-- Multiplying two ciphertexts modulo `N` encrypts `b₁ ^^ b₂` with explicit combined randomness. -/
theorem mulCiphertextsNat_ciphertext {N : ℕ} (hN : N ≠ 0) (z : ℕ) (b₁ b₂ : Bool) (r₁ r₂ : ℕ) :
    mulCiphertextsNat N (ciphertext N z b₁ r₁) (ciphertext N z b₂ r₂) =
      ciphertext N z (b₁ ^^ b₂) ((if b₁ && b₂ then z else 1) * r₁ * r₂) := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hN) with rfl | hN1
  · simp only [mulCiphertextsNat, ciphertext, Nat.mod_one]
  · have hlt₁ : mulCiphertextsNat N (ciphertext N z b₁ r₁) (ciphertext N z b₂ r₂) < N :=
      Nat.mod_lt _ (by omega)
    have hlt₂ : ciphertext N z (b₁ ^^ b₂) ((if b₁ && b₂ then z else 1) * r₁ * r₂) < N :=
      Nat.mod_lt _ (by omega)
    rw [← ZMod.val_natCast_of_lt hlt₁, ← ZMod.val_natCast_of_lt hlt₂]
    congr 1
    simp only [mulCiphertextsNat, ZMod.natCast_mod, Nat.cast_mul, natCast_ciphertext hN]
    cases b₁ <;> cases b₂ <;> simp <;> ring

/-! ### Word-level 1-bit scheme and efficiency certificates -/

/-- **Goldwasser–Micali key generation** ([KatzLindell2020], Construction 15.28): draw `k ← gen n`
and output `pk = ⟨N, z⟩` and `sk = ⟨p, q⟩`. -/
noncomputable def keyGen (gen : ℕ → ProbComp KeyDesc) (n : ℕ) :
    ProbComp (List Bool × List Bool) := do
  let k ← gen n
  return (encPair encNat encNat (k.modulus, k.z), encPair encNat encNat (k.p, k.q))

/-- **Goldwasser–Micali 1-bit encryption** ([KatzLindell2020], Construction 15.28) under
`pk = ⟨N, z⟩`. -/
noncomputable def encrypt (n : ℕ) (pk : List Bool) (m : Bool) : ProbComp (List Bool) := do
  let N := ofBits (unframe pk)
  let z := ofBits (dropFrame pk)
  let r ← ProbComp.sampleModNat (n + (encNat N).length) N
  return encNat (ciphertext N z m (unitOrOne N r))

/-- **Goldwasser–Micali decryption** ([KatzLindell2020], Construction 15.28) under `sk = ⟨p, q⟩`. -/
def decrypt (sk ct : List Bool) : Bool :=
  decryptNat (ofBits (unframe sk)) (ofBits (dropFrame sk)) (ofBits ct)

/-- **Homomorphic XOR combiner** ([KatzLindell2020], Exercise 15.11): multiply ciphertexts modulo
`N`. -/
def mulCiphertexts (pk ct₁ ct₂ : List Bool) : List Bool :=
  encNat (mulCiphertextsNat (ofBits (unframe pk)) (ofBits ct₁) (ofBits ct₂))

/-- `ciphertext` is computable in polynomial time. -/
theorem computableInPolyTime_ciphertext {α : Type} {input : α ↪ List Bool}
    {N z : α → ℕ} {m : α → Bool} {r : α → ℕ}
    (hN : ComputableInPolyTime N input encNat) (hz : ComputableInPolyTime z input encNat)
    (hm : ComputableInPolyTime m input encBool) (hr : ComputableInPolyTime r input encNat) :
    ComputableInPolyTime (fun a => ciphertext (N a) (z a) (m a) (r a)) input encNat := by
  have hfactor := ComputableTidilyInPolyTime.cond hm.tidy hz.tidy (.const 1)
  have hpow := computableInPolyTime_powMod hN hr (.const 2)
  unfold ciphertext
  exact .of_tidy (.binary_mod' (.binary_mul' hfactor hpow.tidy) hN.tidy)

/-- `isQuadResidueNat` is computable in polynomial time. -/
theorem computableInPolyTime_isQuadResidueNat {α : Type} {input : α ↪ List Bool}
    {p q c : α → ℕ} (hp : ComputableInPolyTime p input encNat)
    (hq : ComputableInPolyTime q input encNat) (hc : ComputableInPolyTime c input encNat) :
    ComputableInPolyTime (fun a => isQuadResidueNat (p a) (q a) (c a)) input encBool := by
  have hexpP : ComputableInPolyTime (fun a => (p a - 1) / 2) input encNat :=
    .of_tidy (.binary_div' (.binary_sub' hp.tidy (.const 1)) (.const 2))
  have hexpQ : ComputableInPolyTime (fun a => (q a - 1) / 2) input encNat :=
    .of_tidy (.binary_div' (.binary_sub' hq.tidy (.const 1)) (.const 2))
  unfold isQuadResidueNat
  exact .of_tidy (.bool_and'
    (.beq (computableInPolyTime_powMod hp hc hexpP).tidy (.const 1))
    (.beq (computableInPolyTime_powMod hq hc hexpQ).tidy (.const 1)))

/-- `decryptNat` is computable in polynomial time. -/
theorem computableInPolyTime_decryptNat {α : Type} {input : α ↪ List Bool}
    {p q c : α → ℕ} (hp : ComputableInPolyTime p input encNat)
    (hq : ComputableInPolyTime q input encNat) (hc : ComputableInPolyTime c input encNat) :
    ComputableInPolyTime (fun a => decryptNat (p a) (q a) (c a)) input encBool :=
  .of_tidy (ComputableTidilyInPolyTime.bool_not.comp
    (computableInPolyTime_isQuadResidueNat hp hq hc).tidy)

/-- `keyGen gen` is uniformly strict PPT whenever `gen` is. -/
theorem isPPTOn_keyGen {gen : ℕ → ProbComp KeyDesc} (hgen : IsPPTOn encUnary encKeyDesc gen) :
    IsPPTOn encUnary (encPair encBits encBits) (keyGen gen) := by
  unfold keyGen
  have hk := (ComputableInPolyTime.of_eq (f := Subtype.val) (encIn := encKeyDesc)
    (encOut := encPair (encPair encNat encNat) encNat) fun _ => rfl).comp
    (ComputableInPolyTime.snd encUnary encKeyDesc)
  have hp := hk.fst'.fst'; have hq := hk.fst'.snd'; have hz := hk.snd'
  have hN : ComputableInPolyTime (fun x : ℕ × KeyDesc => x.2.modulus)
      (encPair encUnary encKeyDesc) encNat := .of_tidy (.binary_mul' hp.tidy hq.tidy)
  exact hgen.bind_with ((hN.prod hz).encoding_comp.prod (hp.prod hq).encoding_comp).isPPTOn

/-- `encrypt` is uniformly strict PPT. -/
@[program_certificate]
theorem isPPTOn_encrypt :
    IsPPTOn (encKeyedInput encBool) encBits (fun ⟨n, pk, m⟩ => encrypt n pk m) := by
  unfold encrypt
  let E := encKeyedInput encBool
  have hpk := (ComputableInPolyTime.snd encUnary (encPair encBits encBool)).fst'
  have hN : ComputableInPolyTime (fun x : ℕ × List Bool × Bool => ofBits (unframe x.2.1))
      E encNat := ComputableInPolyTime.bitsToNat.comp' (ComputableInPolyTime.unframe.comp' hpk)
  have hz : ComputableInPolyTime (fun x : ℕ × List Bool × Bool => ofBits (dropFrame x.2.1))
      E encNat := ComputableInPolyTime.bitsToNat.comp' (ComputableInPolyTime.dropFrame.comp' hpk)
  have hwidth := (ComputableInPolyTime.fst encUnary (encPair encBits encBool)).unary_add'
    ((ComputableInPolyTime.encoding_length encNat).comp hN)
  have hp1 := ComputableInPolyTime.fst E encNat
  have hN' := hN.comp' hp1
  exact (isPPTOn_sampleModNat hwidth hN).bind_with
    (computableInPolyTime_ciphertext hN' (hz.comp' hp1)
      ((ComputableInPolyTime.snd encUnary (encPair encBits encBool)).snd'.comp' hp1)
      (computableInPolyTime_unitOrOne hN'
        (ComputableInPolyTime.snd E encNat))).encoding_comp.isPPTOn

/-- `decrypt` is computable in polynomial time. -/
theorem computableInPolyTime_decrypt :
    ComputableInPolyTime (fun x : List Bool × List Bool => decrypt x.1 x.2)
      (encPair encBits encBits) encBool := by
  have hsk := ComputableInPolyTime.fst encBits encBits
  unfold decrypt
  exact computableInPolyTime_decryptNat
    (ComputableInPolyTime.bitsToNat.comp' (ComputableInPolyTime.unframe.comp' hsk))
    (ComputableInPolyTime.bitsToNat.comp' (ComputableInPolyTime.dropFrame.comp' hsk))
    (ComputableInPolyTime.bitsToNat.comp' (ComputableInPolyTime.snd encBits encBits))

/-- `mulCiphertexts` is computable in polynomial time. -/
theorem computableInPolyTime_mulCiphertexts :
    ComputableInPolyTime (fun ⟨pk, ct₁, ct₂⟩ => mulCiphertexts pk ct₁ ct₂)
      (encPair encBits (encPair encBits encBits)) encBits := by
  unfold mulCiphertexts mulCiphertextsNat; fun_prop

/-! ### Support-level correctness and XOR homomorphism -/

private theorem decrypt_encPair (p q c : ℕ) :
    decrypt (encPair encNat encNat (p, q)) (encNat c) = decryptNat p q c := by
  rw [decrypt, unframe_encPair_encNat, dropFrame_encPair_encNat, ofBits_encNat, ofBits_encNat,
    ofBits_encNat]

/-- Key pairs in the support of `keyGen gen n` arise from a valid `KeyDesc`. -/
theorem exists_of_mem_support_keyGen {gen : ℕ → ProbComp KeyDesc} {n : ℕ}
    {keys : List Bool × List Bool} (hkeys : keys ∈ (ProbComp.eval (keyGen gen n)).support) :
    ∃ k : KeyDesc,
      keys = (encPair encNat encNat (k.modulus, k.z), encPair encNat encNat (k.p, k.q)) := by
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at hkeys
  obtain ⟨k, _, rfl⟩ := hkeys; exact ⟨k, rfl⟩

/-- Supported ciphertexts under `pk = ⟨N, z⟩` have the form `encNat (ciphertext N z m r)` with
`r.Coprime N`. -/
theorem exists_of_mem_support_encrypt {n N z : ℕ} {pk : List Bool}
    (hpk : pk = encPair encNat encNat (N, z)) {m : Bool} {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (encrypt n pk m)).support) :
    ∃ r : ℕ, r.Coprime N ∧ ct = encNat (ciphertext N z m r) := by
  simp only [encrypt, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at hct
  obtain ⟨r, _, hct_eq⟩ := hct
  have hN : ofBits (unframe pk) = N := by rw [hpk, unframe_encPair_encNat, ofBits_encNat]
  have hz : ofBits (dropFrame pk) = z := by rw [hpk, dropFrame_encPair_encNat, ofBits_encNat]
  rw [hN, hz] at hct_eq
  exact ⟨unitOrOne N r, coprime_unitOrOne N r, hct_eq⟩

/-- **Perfect correctness of Goldwasser–Micali encryption** ([KatzLindell2020],
Construction 15.28). -/
theorem decrypt_encrypt {gen : ℕ → ProbComp KeyDesc} {n : ℕ} {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (keyGen gen n)).support) (m : Bool) {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (encrypt n keys.1 m)).support) :
    decrypt keys.2 ct = m := by
  obtain ⟨k, hkeq⟩ := exists_of_mem_support_keyGen hkeys
  have hpk : keys.1 = encPair encNat encNat (k.modulus, k.z) := congrArg Prod.fst hkeq
  have hsk : keys.2 = encPair encNat encNat (k.p, k.q) := congrArg Prod.snd hkeq
  obtain ⟨r, hr, rfl⟩ := exists_of_mem_support_encrypt hpk hct
  rw [hsk, decrypt_encPair]
  exact k.decryptNat_ciphertext hr m

/-- **Preservation of plaintext XOR under ciphertext multiplication** ([KatzLindell2020],
Definition 15.14 and Exercise 15.11, first clause). -/
theorem decrypt_mulCiphertexts {gen : ℕ → ProbComp KeyDesc} {n : ℕ} {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (keyGen gen n)).support) {b₁ b₂ : Bool} {ct₁ ct₂ : List Bool}
    (hct₁ : ct₁ ∈ (ProbComp.eval (encrypt n keys.1 b₁)).support)
    (hct₂ : ct₂ ∈ (ProbComp.eval (encrypt n keys.1 b₂)).support) :
    decrypt keys.2 (mulCiphertexts keys.1 ct₁ ct₂) = (b₁ ^^ b₂) := by
  obtain ⟨k, hkeq⟩ := exists_of_mem_support_keyGen hkeys
  have hpk : keys.1 = encPair encNat encNat (k.modulus, k.z) := congrArg Prod.fst hkeq
  have hsk : keys.2 = encPair encNat encNat (k.p, k.q) := congrArg Prod.snd hkeq
  obtain ⟨r₁, hr₁, rfl⟩ := exists_of_mem_support_encrypt hpk hct₁
  obtain ⟨r₂, hr₂, rfl⟩ := exists_of_mem_support_encrypt hpk hct₂
  have hr' : ((if b₁ && b₂ then k.z else 1) * r₁ * r₂).Coprime k.modulus := by
    refine Nat.Coprime.mul_left (Nat.Coprime.mul_left ?_ hr₁) hr₂
    cases b₁ && b₂
    · exact Nat.coprime_one_left _
    · exact k.coprime_z
  rw [hpk, hsk, mulCiphertexts, unframe_encPair_encNat, ofBits_encNat, ofBits_encNat, ofBits_encNat,
    mulCiphertextsNat_ciphertext (NeZero.ne k.modulus), decrypt_encPair]
  exact k.decryptNat_ciphertext hr' (b₁ ^^ b₂)

/-! ### Ideal unit-sampling encryption, re-randomization, and distributional XOR homomorphism -/

/-- Ideal Goldwasser–Micali unit-level encryption law: sample `r` uniformly from `(ZMod N)ˣ` and
output `(if m then z else 1) * r ^ 2`. -/
noncomputable def idealEncryptUnit (N : ℕ) [NeZero N] (z : (ZMod N)ˣ) (m : Bool) :
    PMF (ZMod N)ˣ :=
  (PMF.uniformOfFintype (ZMod N)ˣ).map fun r => (if m then z else 1) * r ^ 2

/-- Ideal Goldwasser–Micali word-level encryption law: encode the canonical residue of
`idealEncryptUnit N z m` via `encNat`. -/
noncomputable def idealEncrypt (N : ℕ) [NeZero N] (z : (ZMod N)ˣ) (m : Bool) :
    PMF (List Bool) :=
  (idealEncryptUnit N z m).map fun u => encNat u.val.val

/-- **Ciphertext re-randomization** ([KatzLindell2020], Exercise 15.11): multiplying any fixed
ciphertext `(if m then z else 1) * r₀ ^ 2` by `r ^ 2` for a uniform unit `r` yields
`idealEncryptUnit N z m`. -/
theorem rerandomize_idealEncryptUnit_eq (N : ℕ) [NeZero N] (z r₀ : (ZMod N)ˣ) (m : Bool) :
    ((PMF.uniformOfFintype (ZMod N)ˣ).map fun r => ((if m then z else 1) * r₀ ^ 2) * r ^ 2) =
      idealEncryptUnit N z m := by
  unfold idealEncryptUnit
  conv_rhs => rw [← Probability.PMF.uniformOfFintype_map_equiv (Equiv.mulLeft r₀)]
  rw [PMF.map_comp]
  refine congrArg _ (funext fun r => ?_)
  change PMF.pure (((if m then z else 1) * r₀ ^ 2) * r ^ 2) =
    PMF.pure ((if m then z else 1) * (r₀ * r) ^ 2)
  rw [mul_pow, mul_assoc]

/-- Word-level ciphertext re-randomization via `mulCiphertexts` with a fresh draw from
`idealEncrypt N z false`. -/
theorem rerandomize_idealEncrypt_eq (N : ℕ) [NeZero N] (z r₀ : (ZMod N)ˣ) (m : Bool) :
    (do
      let ct ← idealEncrypt N z false
      pure (mulCiphertexts (encPair encNat encNat (N, z.val.val))
        (encNat ((if m then z else 1) * r₀ ^ 2).val.val) ct)) =
      idealEncrypt N z m := by
  have hval (u v : (ZMod N)ˣ) : mulCiphertextsNat N u.val.val v.val.val = (u * v).val.val := by
    simp only [mulCiphertextsNat, Units.val_mul, ZMod.val_mul]
  have hbind_eq_map :
      (do
        let ct ← idealEncrypt N z false
        pure (mulCiphertexts (encPair encNat encNat (N, z.val.val))
          (encNat ((if m then z else 1) * r₀ ^ 2).val.val) ct)) =
      (idealEncrypt N z false).map (fun ct =>
        mulCiphertexts (encPair encNat encNat (N, z.val.val))
          (encNat ((if m then z else 1) * r₀ ^ 2).val.val) ct) := by
    rw [← PMF.monad_map_eq_map, ← bind_pure_comp]
  rw [hbind_eq_map, idealEncrypt, idealEncryptUnit, PMF.map_comp, PMF.map_comp,
    idealEncrypt, ← rerandomize_idealEncryptUnit_eq N z r₀ m, PMF.map_comp]
  refine congrArg (PMF.map · (PMF.uniformOfFintype (ZMod N)ˣ)) (funext fun r => ?_)
  simp only [Function.comp_apply, Bool.false_eq_true, ↓reduceIte, one_mul, mulCiphertexts,
    unframe_encPair_encNat, ofBits_encNat, hval]

/-- **Distributional XOR homomorphism on `(ZMod N)ˣ`** ([KatzLindell2020], Exercise 15.11). -/
theorem idealEncryptUnit_mul_eq (N : ℕ) [NeZero N] (z : (ZMod N)ˣ) (b₁ b₂ : Bool) :
    (do
      let c₁ ← idealEncryptUnit N z b₁
      let c₂ ← idealEncryptUnit N z b₂
      pure (c₁ * c₂)) =
      idealEncryptUnit N z (b₁ ^^ b₂) := by
  have halg (r₁ r₂ : (ZMod N)ˣ) :
      ((if b₁ then z else 1) * r₁ ^ 2) * ((if b₂ then z else 1) * r₂ ^ 2) =
        (if (b₁ ^^ b₂) then z else 1) * (((if b₁ && b₂ then z else 1) * r₁) * r₂) ^ 2 := by
    cases b₁ <;> cases b₂ <;> simp [pow_two, mul_comm, mul_left_comm]
  have hinner (r₁ : (ZMod N)ˣ) :
      ((idealEncryptUnit N z b₂).map fun c₂ => ((if b₁ then z else 1) * r₁ ^ 2) * c₂) =
        idealEncryptUnit N z (b₁ ^^ b₂) := by
    unfold idealEncryptUnit; rw [PMF.map_comp]
    conv_rhs =>
      rw [← Probability.PMF.uniformOfFintype_map_equiv
        (Equiv.mulLeft ((if b₁ && b₂ then z else 1) * r₁))]
    rw [PMF.map_comp]
    exact congrArg (PMF.map · (PMF.uniformOfFintype (ZMod N)ˣ)) (funext (halg r₁))
  have hm (c₁ : (ZMod N)ˣ) :
      (do let c₂ ← idealEncryptUnit N z b₂; pure (c₁ * c₂)) =
        (idealEncryptUnit N z b₂).map (fun c₂ => c₁ * c₂) := by
    rw [← PMF.monad_map_eq_map, ← bind_pure_comp]
  change ((PMF.uniformOfFintype (ZMod N)ˣ).map fun r₁ => (if b₁ then z else 1) * r₁ ^ 2).bind
      (fun c₁ => do let c₂ ← idealEncryptUnit N z b₂; pure (c₁ * c₂)) =
    idealEncryptUnit N z (b₁ ^^ b₂)
  rw [PMF.bind_map]
  have hstep : (fun r₁ : (ZMod N)ˣ =>
      (do let c₂ ← idealEncryptUnit N z b₂; pure (((if b₁ then z else 1) * r₁ ^ 2) * c₂))) =
      fun _ => idealEncryptUnit N z (b₁ ^^ b₂) :=
    funext fun r₁ => (hm _).trans (hinner r₁)
  change (PMF.uniformOfFintype (ZMod N)ˣ).bind (fun r₁ =>
      do let c₂ ← idealEncryptUnit N z b₂; pure (((if b₁ then z else 1) * r₁ ^ 2) * c₂)) =
    idealEncryptUnit N z (b₁ ^^ b₂)
  rw [hstep, PMF.bind_const]

/-- **Exercise 15.11** ([KatzLindell2020], p. 568, and Definition 15.14, second clause):
multiplying two independent ideal ciphertexts of `b₁` and `b₂` with `mulCiphertexts` produces the
exact fresh ciphertext distribution `idealEncrypt N z (b₁ ^^ b₂)`. -/
theorem idealEncrypt_mulCiphertexts_eq (N : ℕ) [NeZero N] (z : (ZMod N)ˣ) (b₁ b₂ : Bool) :
    (do
      let ct₁ ← idealEncrypt N z b₁
      let ct₂ ← idealEncrypt N z b₂
      pure (mulCiphertexts (encPair encNat encNat (N, z.val.val)) ct₁ ct₂)) =
      idealEncrypt N z (b₁ ^^ b₂) := by
  have hval (u v : (ZMod N)ˣ) : mulCiphertextsNat N u.val.val v.val.val = (u * v).val.val := by
    simp only [mulCiphertextsNat, Units.val_mul, ZMod.val_mul]
  conv_rhs => rw [idealEncrypt, ← idealEncryptUnit_mul_eq N z b₁ b₂]
  simp only [idealEncrypt, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map,
    PMF.map_bind, PMF.pure_map, Function.comp_def, mulCiphertexts, unframe_encPair_encNat,
    ofBits_encNat, hval]

/-- When `IsSquare y`, `idealEncryptUnit N y m` is independent of `m`. -/
theorem idealEncryptUnit_of_isSquare (N : ℕ) [NeZero N] {y : (ZMod N)ˣ} (hy : IsSquare y)
    (m : Bool) :
    idealEncryptUnit N y m = idealEncryptUnit N y false := by
  cases m
  · rfl
  · obtain ⟨s, rfl⟩ := hy
    have h1 : idealEncryptUnit N (s * s) true =
        ((PMF.uniformOfFintype (ZMod N)ˣ).map fun r =>
          ((if false then s * s else 1) * s ^ 2) * r ^ 2) := by
      simp only [idealEncryptUnit, ↓reduceIte, Bool.false_eq_true, one_mul, pow_two]
    exact h1.trans (rerandomize_idealEncryptUnit_eq N (s * s) s false)

/-- Word-level lossiness on quadratic-residue keys: when `IsSquare y`, `idealEncrypt N y m` is
independent of `m`. -/
theorem idealEncrypt_of_isSquare (N : ℕ) [NeZero N] {y : (ZMod N)ˣ} (hy : IsSquare y) (m : Bool) :
    idealEncrypt N y m = idealEncrypt N y false := by
  simp only [idealEncrypt, idealEncryptUnit_of_isSquare N hy m]

/-! ### Sampling statistical distance between `encrypt` and `idealEncrypt` -/

/-- For `d : ModulusDesc` with `n`-bit primes (`n ≤ d.p.size ∧ n ≤ d.q.size`), sampling
`r ← ProbComp.sampleModNat (n + |N|) N` and applying `unitOrOne N` is within `5 / 2 ^ n`
statistical distance of a uniform unit `u ← PMF.uniformOfFintype (ZMod N)ˣ`. -/
theorem advantage_sampleModNat_unitOrOne_le (d : ModulusDesc) (n : ℕ)
    (hsize : n ≤ d.p.size ∧ n ≤ d.q.size) (k : ℕ → Game) :
    Game.advantage
      ((ProbComp.eval (ProbComp.sampleModNat (n + (encNat (d.p * d.q)).length) (d.p * d.q))).bind
        fun r => k (unitOrOne (d.p * d.q) r))
      ((PMF.uniformOfFintype (ZMod (d.p * d.q))ˣ).bind fun u => k u.val.val) ≤
      5 / 2 ^ n := by
  have hk (u : (ZMod (d.p * d.q))ˣ) : k (unitOrOne (d.p * d.q) u.val.val) = k u.val.val := by
    rw [unitOrOne, ite_eq_left (ZMod.val_coe_unit_coprime u)]
  simpa only [hk] using Game.advantage_sampleModNat_units_le d.prime_p d.prime_q d.ne_pq
    hsize.1 hsize.2 fun r => k (unitOrOne (d.p * d.q) r)

/-- Replacing `encrypt` by `idealEncrypt` inside any continuation `k` changes game advantage by at
most `5 / 2 ^ n` when `n ≤ d.p.size ∧ n ≤ d.q.size`. -/
theorem advantage_encrypt_idealEncrypt_le (d : ModulusDesc) (n : ℕ)
    (hsize : n ≤ d.p.size ∧ n ≤ d.q.size) (y : (ZMod (d.p * d.q))ˣ) (m : Bool)
    (k : List Bool → Game) :
    Game.advantage
      ((ProbComp.eval
        (encrypt n (encPair encNat encNat (d.p * d.q, y.val.val)) m)).bind k)
      ((idealEncrypt (d.p * d.q) y m).bind k) ≤
      5 / 2 ^ n := by
  have hy_cop : y.val.val.Coprime (d.p * d.q) := ZMod.val_coe_unit_coprime y
  have hy_unit : ZMod.unitOfCoprime y.val.val hy_cop = y := by ext; simp [ZMod.coe_unitOfCoprime]
  have hct (u : (ZMod (d.p * d.q))ˣ) :
      ciphertext (d.p * d.q) y.val.val m u.val.val =
        ((if m then y else 1) * u ^ 2).val.val := by
    have hu_cop : u.val.val.Coprime (d.p * d.q) := ZMod.val_coe_unit_coprime u
    have hu_unit : ZMod.unitOfCoprime u.val.val hu_cop = u := by ext; simp [ZMod.coe_unitOfCoprime]
    rw [ciphertext_eq_unit_val hy_cop hu_cop m, hy_unit, hu_unit]
  rw [encrypt, unframe_encPair_encNat, dropFrame_encPair_encNat, ofBits_encNat, ofBits_encNat]
  simp only [idealEncrypt, idealEncryptUnit, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.bind_bind, PMF.pure_bind, PMF.bind_map, Function.comp_def]
  have hrhs : ((PMF.uniformOfFintype (ZMod (d.p * d.q))ˣ).bind fun u =>
        k (encNat ((if m then y else 1) * u ^ 2).val.val)) =
      (PMF.uniformOfFintype (ZMod (d.p * d.q))ˣ).bind fun u =>
        k (encNat (ciphertext (d.p * d.q) y.val.val m u.val.val)) :=
    congrArg _ (funext fun u => by rw [hct u])
  rw [hrhs]
  exact advantage_sampleModNat_unitOrOne_le d n hsize
    (fun r => k (encNat (ciphertext (d.p * d.q) y.val.val m r)))

/-! ### Theorem 15.29: single-bit IND-CPA security under Quadratic Residuosity -/

/-- Ideal Goldwasser–Micali public-key distribution ([KatzLindell2020], Construction 15.28): sample
`d ← setup n` and `z` uniformly from `positiveNonresidues d.p d.q`. -/
noncomputable def publicKeyLaw (setup : ℕ → PMF ModulusDesc) (n : ℕ) : PMF (List Bool) := do
  let d ← setup n
  let z ← PMF.uniformOfFintype (positiveNonresidues d.p d.q)
  pure (encPair encNat encNat (d.p * d.q, z.1.val.val))

/-- Lossy quadratic-residue public-key distribution ([KatzLindell2020], proof of Theorem 15.29):
sample `d ← setup n` and `y` uniformly from `quadResidueSet d.p d.q`. -/
noncomputable def qrPublicKeyLaw (setup : ℕ → PMF ModulusDesc) (n : ℕ) : PMF (List Bool) := do
  let d ← setup n
  let y ← PMF.uniformOfFintype (quadResidueSet d.p d.q)
  pure (encPair encNat encNat (d.p * d.q, y.1.val.val))

/-- **Single-bit QR reduction distinguisher** ([KatzLindell2020], proof of Theorem 15.29). -/
noncomputable def qrDistinguisher (adversary : Encryption.Adversary) (n : ℕ)
    (input : ℕ × ℕ) : ProbComp Bool :=
  Encryption.keyDistinguisher encrypt adversary n (encPair encNat encNat input)

/-- `qrDistinguisher adversary` is uniformly strict PPT whenever `adversary` is. -/
theorem isPPTOn_qrDistinguisher {adversary : Encryption.Adversary} (hA : adversary.IsPPT) :
    IsPPTOn (encPair encUnary (encPair encNat encNat)) encBool
      (fun input => qrDistinguisher adversary input.1 input.2) :=
  (Encryption.isPPT_keyDistinguisher isPPTOn_encrypt hA).on.preprocess
    ((ComputableInPolyTime.fst encUnary (encPair encNat encNat)).prod
      (ComputableInPolyTime.snd encUnary (encPair encNat encNat)).encoding_comp)

/-- Under `qrPublicKeyLaw`, the chosen-message advantage is at most `10 / 2 ^ n`. -/
theorem advantage_publicKeyGame_qrPublicKeyLaw_le {setup : ℕ → PMF ModulusDesc} {n : ℕ}
    (hsize : ∀ d ∈ (setup n).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (adversary : Encryption.Adversary) :
    Game.advantage
      (Encryption.publicKeyGame (qrPublicKeyLaw setup n) encrypt adversary false n)
      (Encryption.publicKeyGame (qrPublicKeyLaw setup n) encrypt adversary true n) ≤
      10 / 2 ^ n := by
  let idealGame (bit : Bool) : Game := do
    let d ← setup n
    let y ← PMF.uniformOfFintype (quadResidueSet d.p d.q)
    let choice ← ProbComp.eval (adversary.choose n (encPair encNat encNat (d.p * d.q, y.1.val.val)))
    let ct ← idealEncrypt (d.p * d.q) y.1
      (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice)
    ProbComp.eval (adversary.guess n (ChoiceOut.state choice) ct)
  have hideal_eq : idealGame false = idealGame true := by
    dsimp only [idealGame]; simp only [PMF.monad_bind_eq_bind]
    refine congrArg (PMF.bind _) (funext fun d => congrArg (PMF.bind _) (funext fun y => ?_))
    have hy_sq : IsSquare y.1 := (Finset.mem_filter.mp y.2).2
    refine congrArg (PMF.bind _) (funext fun choice => ?_)
    have htrue := idealEncrypt_of_isSquare (d.p * d.q) hy_sq true
    cases ChoiceOut.msg₀ choice <;> cases ChoiceOut.msg₁ choice <;>
      simp only [↓reduceIte, Bool.false_eq_true, htrue]
  have hhop (bit : Bool) :
      Game.advantage (Encryption.publicKeyGame (qrPublicKeyLaw setup n) encrypt adversary bit n)
        (idealGame bit) ≤ 5 / 2 ^ n := by
    simp only [Encryption.publicKeyGame, qrPublicKeyLaw, idealGame, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
    refine Game.advantage_bind_le_of_support _ _ _ fun d hd =>
      Game.advantage_bind_le_nnreal _ _ _ fun y =>
        Game.advantage_bind_le_nnreal _ _ _ fun _ =>
          advantage_encrypt_idealEncrypt_le d n (hsize d hd) y.1 _ _
  have h4 := Game.advantage_four_hop_le (hhop false) (hhop true)
  rw [hideal_eq, Game.advantage_self, add_zero] at h4
  calc _ ≤ (5 : ℝ≥0) / 2 ^ n + 5 / 2 ^ n := h4
    _ = 10 / 2 ^ n := by ring

/-- **Quantitative Theorem 15.29 bound** ([KatzLindell2020], pp. 554–556): single-bit IND-CPA
advantage under `publicKeyLaw setup n` is at most twice `qrDistinguisher adversary`'s QR advantage
plus `10 / 2 ^ n`. -/
theorem advantage_publicKeyGame_le_qr {setup : ℕ → PMF ModulusDesc} {n : ℕ}
    (hsize : ∀ d ∈ (setup n).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (adversary : Encryption.Adversary) :
    Game.advantage
      (Encryption.publicKeyGame (publicKeyLaw setup n) encrypt adversary false n)
      (Encryption.publicKeyGame (publicKeyLaw setup n) encrypt adversary true n) ≤
      2 * Game.advantage (qrRealGame setup (qrDistinguisher adversary) n)
        (qrIdealGame setup (qrDistinguisher adversary) n) +
      10 / 2 ^ n := by
  have hrep := Encryption.advantage_publicKeyGame_le
    (publicKeyLaw setup n) (qrPublicKeyLaw setup n) encrypt adversary n
  have hqrI : distinguishingGame (publicKeyLaw setup n)
      (Encryption.keyDistinguisher encrypt adversary n) =
      qrIdealGame setup (qrDistinguisher adversary) n := by
    simp only [distinguishingGame, publicKeyLaw, qrIdealGame, qrDistinguisher,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  have hqrR : distinguishingGame (qrPublicKeyLaw setup n)
      (Encryption.keyDistinguisher encrypt adversary n) =
      qrRealGame setup (qrDistinguisher adversary) n := by
    simp only [distinguishingGame, qrPublicKeyLaw, qrRealGame, qrDistinguisher,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rw [hqrI, hqrR, Game.advantage_comm (qrIdealGame setup (qrDistinguisher adversary) n)] at hrep
  exact hrep.trans (add_le_add le_rfl (advantage_publicKeyGame_qrPublicKeyLaw_le hsize adversary))

/-- **Asymptotic IND-CPA security for `publicKeyLaw`** ([KatzLindell2020], Theorem 15.29). -/
theorem indistinguishable_publicKeyGame {setup : ℕ → PMF ModulusDesc}
    (hsize : ∀ n, ∀ d ∈ (setup n).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hQR : QuadraticResiduosityHard setup) :
    Game.Indistinguishable
      (fun adversary n =>
        Encryption.publicKeyGame (publicKeyLaw setup n) encrypt adversary false n)
      (fun adversary n =>
        Encryption.publicKeyGame (publicKeyLaw setup n) encrypt adversary true n)
      Encryption.Adversary.IsPPT := by
  intro adversary hA
  have hD := hQR (qrDistinguisher adversary) (isPPTOn_qrDistinguisher hA)
  refine negligible_of_le ((hD.add hD).add (negligible_const_div_two_pow 10)) fun n => ?_
  dsimp only [Pi.add_apply]; rw [← two_mul]
  exact advantage_publicKeyGame_le_qr (hsize n) adversary

/-- **Theorem 15.29 (`Encryption.INDCPA`)** ([KatzLindell2020], pp. 554–556): under
`QuadraticResiduosityHard setup`, `n`-bit prime growth, and a key generator whose public-key
marginal is computationally indistinguishable from `publicKeyLaw setup`, `(keyGen gen, encrypt)`
satisfies `Encryption.INDCPA`. -/
theorem indcpa_goldwasserMicali {setup : ℕ → PMF ModulusDesc} {gen : ℕ → ProbComp KeyDesc}
    (hsize : ∀ n, ∀ d ∈ (setup n).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hkeys : ComputationallyIndistinguishable
      (fun n => (ProbComp.eval (keyGen gen n)).map Prod.fst) (publicKeyLaw setup))
    (hQR : QuadraticResiduosityHard setup) :
    Encryption.INDCPA (keyGen gen) encrypt := by
  intro adversary hA
  have hk := hkeys (Encryption.keyDistinguisher encrypt adversary)
    (Encryption.isPPT_keyDistinguisher isPPTOn_encrypt hA)
  have hmid := indistinguishable_publicKeyGame hsize hQR adversary hA
  refine negligible_of_le ((hk.add hk).add hmid) fun n => ?_
  dsimp only [Pi.add_apply]
  rw [← two_mul, Encryption.eval_game_eq_publicKeyGame, Encryption.eval_game_eq_publicKeyGame]
  exact Encryption.advantage_publicKeyGame_le
    ((ProbComp.eval (keyGen gen n)).map Prod.fst) (publicKeyLaw setup n) encrypt adversary n

/-! ### Multi-bit bitwise Goldwasser–Micali encryption and lossy-key IND-CPA -/

/-- Encrypt each bit of `bits` independently with `encrypt n pk`. -/
noncomputable def encryptBits (n : ℕ) (pk : List Bool) (bits : List Bool) :
    ProbComp (List (List Bool)) :=
  bits.mapM (encrypt n pk)

/-- Word-valued bitwise encryption for `Encryption.gameOn`: frame `encryptBits` via
`encList encBits`. -/
noncomputable def encryptWord (n : ℕ) (pk : List Bool) (bits : List Bool) :
    ProbComp (List Bool) :=
  encList encBits <$> encryptBits n pk bits

/-- Decrypt a list of Goldwasser–Micali ciphertexts bit-by-bit. -/
def decryptBits (sk : List Bool) (cts : List (List Bool)) : List Bool :=
  cts.map (decrypt sk)

/-- Componentwise homomorphic XOR of two ciphertext lists. -/
def xorCiphertexts (pk : List Bool) (cts₁ cts₂ : List (List Bool)) : List (List Bool) :=
  List.zipWith (mulCiphertexts pk) cts₁ cts₂

/-- `encryptBits` is uniformly strict PPT. -/
theorem isPPTOn_encryptBits :
    IsPPTOn (encKeyedInput encBits) (encList encBits)
      (fun ⟨n, pk, bits⟩ => encryptBits n pk bits) := by
  let prog (x : ℕ × List Bool × List Bool) (b : Bool) : ProbComp (List Bool) :=
    encrypt x.1 x.2.1 b
  have hstep : IsPPTOn (encPair (encKeyedInput encBits) encBool) encBits
      (fun p => prog p.1 p.2) := by
    have hp1 := ComputableInPolyTime.fst (encKeyedInput encBits) encBool
    have hn := (ComputableInPolyTime.fst encUnary (encPair encBits encBits)).comp hp1
    have hpk := ((ComputableInPolyTime.snd encUnary (encPair encBits encBits)).fst').comp hp1
    have hb := ComputableInPolyTime.snd (encKeyedInput encBits) encBool
    exact (isPPTOn_encrypt.preprocess
      (prepare := fun p : (ℕ × List Bool × List Bool) × Bool => (p.1.1, p.1.2.1, p.2))
      (hn.prod (hpk.prod hb))).congr fun _ => rfl
  have hlist : ComputableInPolyTime (fun x : ℕ × List Bool × List Bool => x.2.2)
      (encKeyedInput encBits) (encList encBool) :=
    ComputableInPolyTime.bitsToList.comp
      (ComputableInPolyTime.snd encUnary (encPair encBits encBits)).snd'
  exact (IsPPTOn.mapMWith (program := prog) hstep hlist).congr fun ⟨_, _, _⟩ => rfl

/-- `encryptWord` is uniformly strict PPT. -/
@[program_certificate]
theorem isPPTOn_encryptWord :
    IsPPTOn (encKeyedInput encBits) encBits
      (fun ⟨n, pk, bits⟩ => encryptWord n pk bits) :=
  (isPPTOn_iff_encoded.mp isPPTOn_encryptBits).congr fun ⟨_, _, _⟩ => rfl

/-- Perfect correctness of bitwise Goldwasser–Micali encryption. -/
theorem decryptBits_encryptBits {gen : ℕ → ProbComp KeyDesc} {n : ℕ}
    {keys : List Bool × List Bool} (hkeys : keys ∈ (ProbComp.eval (keyGen gen n)).support)
    (bits : List Bool) {cts : List (List Bool)}
    (hcts : cts ∈ (ProbComp.eval (encryptBits n keys.1 bits)).support) :
    decryptBits keys.2 cts = bits := by
  induction bits generalizing cts with
  | nil =>
    simp only [encryptBits, List.mapM_nil, ProbComp.eval_pure, PMF.support_pure,
      Set.mem_singleton_iff] at hcts
    subst hcts; rfl
  | cons b bs ih =>
    simp only [encryptBits, List.mapM_cons, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at hcts
    obtain ⟨ct, hct, rest, hrest, rfl⟩ := hcts
    simp only [decryptBits, List.map_cons, decrypt_encrypt hkeys b hct]
    exact congrArg (b :: ·) (ih hrest)

/-- Ideal bitwise encryption law on a bit list `bits`. -/
noncomputable def idealEncryptBits (N : ℕ) [NeZero N] (z : (ZMod N)ˣ) (bits : List Bool) :
    PMF (List (List Bool)) :=
  bits.mapM (idealEncrypt N z)

/-- When `IsSquare y`, `idealEncryptBits N y` agrees on any two equal-length bit lists. -/
theorem idealEncryptBits_eq_of_isSquare_of_length_eq (N : ℕ) [NeZero N] {y : (ZMod N)ˣ}
    (hy : IsSquare y) {m₀ m₁ : List Bool} (hlen : m₀.length = m₁.length) :
    idealEncryptBits N y m₀ = idealEncryptBits N y m₁ := by
  induction m₀ generalizing m₁ with
  | nil => cases m₁ with | nil => rfl | cons _ _ => simp at hlen
  | cons b₀ bs₀ ih =>
    cases m₁ with
    | nil => simp at hlen
    | cons b₁ bs₁ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hih := ih hlen
      dsimp only [idealEncryptBits] at hih ⊢
      simp only [List.mapM_cons, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      rw [idealEncrypt_of_isSquare N hy b₀, idealEncrypt_of_isSquare N hy b₁]
      exact congrArg (PMF.bind _) (funext fun _ => by rw [hih])

/-- Statistical distance between `encryptBits` and `idealEncryptBits` is at most
`bits.length * (5 / 2 ^ n)` for a modulus with `n`-bit primes. -/
theorem advantage_encryptBits_idealEncryptBits_le (d : ModulusDesc) (n : ℕ)
    (hsize : n ≤ d.p.size ∧ n ≤ d.q.size) (y : (ZMod (d.p * d.q))ˣ) (bits : List Bool)
    (k : List (List Bool) → Game) :
    Game.advantage
      ((ProbComp.eval (encryptBits n
        (encPair encNat encNat (d.p * d.q, y.val.val)) bits)).bind k)
      ((idealEncryptBits (d.p * d.q) y bits).bind k) ≤
      (bits.length : ℝ≥0) * (5 / 2 ^ n) := by
  induction bits generalizing k with
  | nil =>
    simp only [encryptBits, idealEncryptBits, List.mapM_nil, ProbComp.eval_pure,
      PMF.monad_pure_eq_pure, PMF.pure_bind, List.length_nil, Nat.cast_zero, zero_mul,
      Game.advantage_self, le_refl]
  | cons b bs ih =>
    simp only [encryptBits, idealEncryptBits, List.mapM_cons, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
      PMF.pure_bind]
    let pk := encPair encNat encNat (d.p * d.q, y.val.val)
    let mid : Game := (idealEncrypt (d.p * d.q) y b).bind fun ct =>
      (ProbComp.eval (encryptBits n pk bs)).bind fun cts => k (ct :: cts)
    refine (Game.advantage_triangle _ mid _).trans ?_
    have hhead := advantage_encrypt_idealEncrypt_le d n hsize y b
      (fun ct => (ProbComp.eval (encryptBits n pk bs)).bind fun cts => k (ct :: cts))
    have htail :
        Game.advantage mid ((idealEncrypt (d.p * d.q) y b).bind fun ct =>
          (idealEncryptBits (d.p * d.q) y bs).bind fun cts => k (ct :: cts)) ≤
          (bs.length : ℝ≥0) * (5 / 2 ^ n) :=
      Game.advantage_bind_le_nnreal _ _ _ fun ct => ih (fun cts => k (ct :: cts))
    calc _ ≤ 5 / 2 ^ n + (bs.length : ℝ≥0) * (5 / 2 ^ n) := add_le_add hhead htail
      _ = ((b :: bs).length : ℝ≥0) * (5 / 2 ^ n) := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

/-- Admissibility predicate for bounded equal-length bit-word challenges. -/
def validBoundedWords (maxLen : ℕ → ℕ) (n : ℕ) (_pk : List Bool) (m₀ m₁ : List Bool) : Bool :=
  (m₀.length == m₁.length) && decide (m₀.length ≤ maxLen n)

/-- Chosen-message experiment for `encryptWord` under a given public-key `PMF` law and
`validBoundedWords maxLen`. -/
noncomputable def publicKeyWordGame (maxLen : ℕ → ℕ) (keys : PMF (List Bool))
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) : Game := do
  let pk ← keys
  let choice ← ProbComp.eval (adversary.choose n pk)
  if validBoundedWords maxLen n pk (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) then
    let ct ← ProbComp.eval
      (encryptWord n pk (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice))
    ProbComp.eval (adversary.guess n (ChoiceOut.state choice) ct)
  else
    pure false

/-- Public-key distinguisher for bounded-word `encryptWord` with a hidden fair challenge bit. -/
noncomputable def wordKeyDistinguisher (maxLen : ℕ → ℕ)
    (adversary : Encryption.WordAdversary) : Distinguisher := fun n pk => do
  let choice ← adversary.choose n pk
  let bit ← ProbComp.uniform Bool
  if validBoundedWords maxLen n pk (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) then
    let ct ← encryptWord n pk (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice)
    let guess ← adversary.guess n (ChoiceOut.state choice) ct
    return guess ^^ bit
  else
    return false ^^ bit

/-- **Multi-bit QR reduction distinguisher** via Goldwasser–Micali lossy public keys. -/
noncomputable def qrWordDistinguisher (maxLen : ℕ → ℕ) (adversary : Encryption.WordAdversary)
    (n : ℕ) (input : ℕ × ℕ) : ProbComp Bool :=
  wordKeyDistinguisher maxLen adversary n (encPair encNat encNat input)

/-- `wordKeyDistinguisher maxLen adversary` is uniformly strict PPT whenever `maxLen` is unary
polynomial-time computable and `adversary` is strict PPT. -/
theorem isPPT_wordKeyDistinguisher {maxLen : ℕ → ℕ}
    (hmax : ComputableInPolyTime maxLen encUnary encUnary)
    {adversary : Encryption.WordAdversary} (hA : adversary.IsPPT) :
    IsPPT encBool (wordKeyDistinguisher maxLen adversary) := by
  have hmaxT := hmax.tidy; have hchoose := hA.choose; have hguess := hA.guess
  have hvalid : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × ((List Bool × List Bool) × List Bool)) × Bool =>
        validBoundedWords maxLen p.1.1.1 p.1.1.2 (ChoiceOut.msg₀ p.1.2) (ChoiceOut.msg₁ p.1.2))
      (encPair (encPair (encPair encUnary encBits) (encChoiceOut encBits)) encBool) encBool := by
    unfold validBoundedWords ChoiceOut.msg₀ ChoiceOut.msg₁ ChoiceOut.msgs; polytime
  unfold Probability.IsPPT wordKeyDistinguisher; ppt

/-- `qrWordDistinguisher maxLen adversary` is uniformly strict PPT whenever `maxLen` is unary
polynomial-time computable and `adversary` is strict PPT. -/
theorem isPPTOn_qrWordDistinguisher {maxLen : ℕ → ℕ}
    (hmax : ComputableInPolyTime maxLen encUnary encUnary)
    {adversary : Encryption.WordAdversary} (hA : adversary.IsPPT) :
    IsPPTOn (encPair encUnary (encPair encNat encNat)) encBool
      (fun input => qrWordDistinguisher maxLen adversary input.1 input.2) :=
  (isPPT_wordKeyDistinguisher hmax hA).on.preprocess
    ((ComputableInPolyTime.fst encUnary (encPair encNat encNat)).prod
      (ComputableInPolyTime.snd encUnary (encPair encNat encNat)).encoding_comp)

private theorem distinguishingGame_wordKeyDistinguisher (maxLen : ℕ → ℕ) (keys : PMF (List Bool))
    (adversary : Encryption.WordAdversary) (n : ℕ) :
    distinguishingGame keys (wordKeyDistinguisher maxLen adversary n) =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (publicKeyWordGame maxLen keys adversary bit n).map (fun guess => guess ^^ bit) := by
  simp only [distinguishingGame, wordKeyDistinguisher, publicKeyWordGame, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.map_bind,
    apply_ite ProbComp.eval]
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun pk => ?_)
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun bit => congrArg (PMF.bind _) (funext fun choice => ?_))
  cases validBoundedWords maxLen n pk (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, PMF.monad_pure_eq_pure, PMF.pure_map]
  | true =>
    simp only [↓reduceIte, PMF.map_bind]; rfl

private theorem advantage_publicKeyWordGame_le (maxLen : ℕ → ℕ) (real ideal : PMF (List Bool))
    (adversary : Encryption.WordAdversary) (n : ℕ) :
    Game.advantage (publicKeyWordGame maxLen real adversary false n)
      (publicKeyWordGame maxLen real adversary true n) ≤
      2 * Game.advantage
        (distinguishingGame real (wordKeyDistinguisher maxLen adversary n))
        (distinguishingGame ideal (wordKeyDistinguisher maxLen adversary n)) +
      Game.advantage (publicKeyWordGame maxLen ideal adversary false n)
        (publicKeyWordGame maxLen ideal adversary true n) := by
  have hprob (keys : PMF (List Bool)) :
      (Game.succProbability
        (distinguishingGame keys (wordKeyDistinguisher maxLen adversary n)) : ℝ) =
        (1 + (Game.succProbability (publicKeyWordGame maxLen keys adversary false n) : ℝ) -
          Game.succProbability (publicKeyWordGame maxLen keys adversary true n)) / 2 := by
    rw [distinguishingGame_wordKeyDistinguisher]
    simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal,
      PMF.bind_apply_toReal, Fintype.sum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool]
    norm_num [PMF.toReal_false_eq_one_sub]; ring
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, Game.coe_advantage, hprob]
  have h := abs_sub_le
    ((Game.succProbability (publicKeyWordGame maxLen real adversary false n) : ℝ) -
      Game.succProbability (publicKeyWordGame maxLen real adversary true n))
    ((Game.succProbability (publicKeyWordGame maxLen ideal adversary false n) : ℝ) -
      Game.succProbability (publicKeyWordGame maxLen ideal adversary true n)) 0
  have hscale (a b c d : ℝ) :
      2 * |(1 + a - b) / 2 - (1 + c - d) / 2| = |(a - b) - (c - d)| := by
    calc 2 * |(1 + a - b) / 2 - (1 + c - d) / 2|
        = |2 * ((1 + a - b) / 2 - (1 + c - d) / 2)| := by rw [abs_mul]; norm_num
      _ = |(a - b) - (c - d)| := by congr 1; ring
  simpa only [hscale, sub_zero] using h

/-- **Quantitative multi-bit Goldwasser–Micali IND-CPA bound**: via lossy quadratic-residue public
keys, bitwise encryption of equal-length words of length at most `maxLen n` reduces to
`QuadraticResiduosityHard` with **factor-`2` loss** (independent of `maxLen n`) plus
`(10 * maxLen n) / 2 ^ n`. -/
theorem advantage_publicKeyWordGame_le_qr (maxLen : ℕ → ℕ) {setup : ℕ → PMF ModulusDesc} {n : ℕ}
    (hsize : ∀ d ∈ (setup n).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (adversary : Encryption.WordAdversary) :
    Game.advantage
      (publicKeyWordGame maxLen (publicKeyLaw setup n) adversary false n)
      (publicKeyWordGame maxLen (publicKeyLaw setup n) adversary true n) ≤
      2 * Game.advantage (qrRealGame setup (qrWordDistinguisher maxLen adversary) n)
        (qrIdealGame setup (qrWordDistinguisher maxLen adversary) n) +
      (10 * maxLen n : ℝ≥0) / 2 ^ n := by
  have hrep := advantage_publicKeyWordGame_le maxLen (publicKeyLaw setup n) (qrPublicKeyLaw setup n)
    adversary n
  have hqrI : distinguishingGame (publicKeyLaw setup n)
      (wordKeyDistinguisher maxLen adversary n) =
      qrIdealGame setup (qrWordDistinguisher maxLen adversary) n := by
    simp only [distinguishingGame, publicKeyLaw, qrIdealGame, qrWordDistinguisher,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  have hqrR : distinguishingGame (qrPublicKeyLaw setup n)
      (wordKeyDistinguisher maxLen adversary n) =
      qrRealGame setup (qrWordDistinguisher maxLen adversary) n := by
    simp only [distinguishingGame, qrPublicKeyLaw, qrRealGame, qrWordDistinguisher,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rw [hqrI, hqrR,
    Game.advantage_comm (qrIdealGame setup (qrWordDistinguisher maxLen adversary) n)] at hrep
  let idealWordGame (bit : Bool) : Game := do
    let d ← setup n
    let y ← PMF.uniformOfFintype (quadResidueSet d.p d.q)
    let pk := encPair encNat encNat (d.p * d.q, y.1.val.val)
    let choice ← ProbComp.eval (adversary.choose n pk)
    if validBoundedWords maxLen n pk (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) then
      let cts ← idealEncryptBits (d.p * d.q) y.1
        (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice)
      ProbComp.eval (adversary.guess n (ChoiceOut.state choice) (encList encBits cts))
    else
      pure false
  have hideal_eq : idealWordGame false = idealWordGame true := by
    dsimp only [idealWordGame]; simp only [PMF.monad_bind_eq_bind]
    refine congrArg (PMF.bind _) (funext fun d => congrArg (PMF.bind _) (funext fun y => ?_))
    have hy_sq : IsSquare y.1 := (Finset.mem_filter.mp y.2).2
    refine congrArg (PMF.bind _) (funext fun choice => ?_)
    by_cases hv : validBoundedWords maxLen n
        (encPair encNat encNat (d.p * d.q, y.1.val.val))
        (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) = true
    · have hlen : (ChoiceOut.msg₀ choice).length = (ChoiceOut.msg₁ choice).length := by
        simp only [validBoundedWords, Bool.and_eq_true, beq_iff_eq] at hv; exact hv.1
      simp only [hv, ↓reduceIte, Bool.false_eq_true]
      rw [idealEncryptBits_eq_of_isSquare_of_length_eq (d.p * d.q) hy_sq hlen]
    · simp only [hv, Bool.false_eq_true, ↓reduceIte]
  have hhop (bit : Bool) :
      Game.advantage
        (publicKeyWordGame maxLen (qrPublicKeyLaw setup n) adversary bit n)
        (idealWordGame bit) ≤ (maxLen n : ℝ≥0) * (5 / 2 ^ n) := by
    simp only [publicKeyWordGame, qrPublicKeyLaw, idealWordGame, encryptWord,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ProbComp.eval_map, PMF.bind_bind,
      PMF.pure_bind, PMF.bind_map, Function.comp_def]
    refine Game.advantage_bind_le_of_support _ _ _ fun d hd =>
      Game.advantage_bind_le_nnreal _ _ _ fun y =>
        Game.advantage_bind_le_nnreal _ _ _ fun choice => ?_
    by_cases hv : validBoundedWords maxLen n
        (encPair encNat encNat (d.p * d.q, y.1.val.val))
        (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) = true
    · have hle : (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice).length ≤
          maxLen n := by
        simp only [validBoundedWords, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
        cases bit <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
      simp only [hv, ↓reduceIte]
      exact (advantage_encryptBits_idealEncryptBits_le d n (hsize d hd) y.1 _ _).trans
        (by gcongr)
    · simp only [hv, Bool.false_eq_true, ↓reduceIte, Game.advantage_self, zero_le]
  have h4 := Game.advantage_four_hop_le (hhop false) (hhop true)
  rw [hideal_eq, Game.advantage_self, add_zero] at h4
  refine hrep.trans (add_le_add le_rfl (h4.trans (le_of_eq ?_)))
  ring

/-- **Multi-bit Goldwasser–Micali IND-CPA security** (`Encryption.INDCPAOn`) under
`QuadraticResiduosityHard` for any unary polynomial-time length schedule `maxLen`, with the same
key hypotheses as `indcpa_goldwasserMicali`: `n`-bit prime growth and a sampled generator
`keyGen gen` whose public-key marginal is computationally indistinguishable from
`publicKeyLaw setup`. The lossy quadratic-residue keys `qrPublicKeyLaw` occur only inside the
proof. -/
theorem indcpaOn_goldwasserMicali_bits {maxLen : ℕ → ℕ}
    (hmax : ComputableInPolyTime maxLen encUnary encUnary)
    {setup : ℕ → PMF ModulusDesc} {gen : ℕ → ProbComp KeyDesc}
    (hsize : ∀ n, ∀ d ∈ (setup n).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hkeys : ComputationallyIndistinguishable
      (fun n => (ProbComp.eval (keyGen gen n)).map Prod.fst) (publicKeyLaw setup))
    (hQR : QuadraticResiduosityHard setup) :
    Encryption.INDCPAOn (validBoundedWords maxLen) encBits (keyGen gen) encryptWord := by
  intro adversary hA
  have hk := hkeys (wordKeyDistinguisher maxLen adversary) (isPPT_wordKeyDistinguisher hmax hA)
  have hD := hQR (qrWordDistinguisher maxLen adversary) (isPPTOn_qrWordDistinguisher hmax hA)
  obtain ⟨c, d, hlen⟩ := hmax.isPPTOn.length_le
  have hpoly : PolynomiallyBounded maxLen := PolynomiallyBounded.of_forall_le c d fun n => by
    simpa only [encUnary_apply, List.length_replicate] using
      hlen n (maxLen n) (by simp [ProbComp.eval_pure])
  have htail := (negligible_const_div_two_pow 10).polynomiallyBounded_mul hpoly
  have hmid : Negligible fun n => Game.advantage
      (publicKeyWordGame maxLen (publicKeyLaw setup n) adversary false n)
      (publicKeyWordGame maxLen (publicKeyLaw setup n) adversary true n) := by
    refine negligible_of_le ((hD.add hD).add htail) fun n => ?_
    dsimp only [Pi.add_apply]; rw [← two_mul]
    refine (advantage_publicKeyWordGame_le_qr maxLen (hsize n) adversary).trans (le_of_eq ?_)
    congr 1; ring
  refine negligible_of_le ((hk.add hk).add hmid) fun n => ?_
  dsimp only [Pi.add_apply]
  rw [← two_mul, Encryption.eval_gameOn, Encryption.eval_gameOn]
  exact advantage_publicKeyWordGame_le maxLen
    ((ProbComp.eval (keyGen gen n)).map Prod.fst) (publicKeyLaw setup n) adversary n

/-! ### Necessity of `J_N(z) = +1`: polynomial-time Jacobi-symbol attack on `jacobiNegSet` -/

/-- Chosen-message adversary exploiting a public parameter `z` with Jacobi symbol `-1`:
challenge on `(false, true)`, save `unframe pk`, and test `jacobiSym (ofBits ct) N = -1`. -/
def jacobiAttackAdversary : Encryption.Adversary where
  choose _ pk := pure ((false, true), unframe pk)
  guess _ state ct := pure (decide (jacobiSym (ofBits ct : ℤ) (ofBits state) = -1))

/-- `jacobiAttackAdversary` is a certified uniform strict-PPT `Encryption.Adversary`. -/
theorem jacobiAttackAdversary_isPPT : jacobiAttackAdversary.IsPPT where
  choose := by
    change IsPPT (encChoiceOut encBool) (fun _ pk => pure ((false, true), unframe pk))
    exact ((ComputableInPolyTime.const (encIn := encPair encUnary encBits) (false, true)).prod
      (ComputableInPolyTime.unframe.comp'
        (ComputableInPolyTime.snd encUnary encBits))).isPPTOn
  guess := by
    change IsPPTOn encGuessInput encBool
      (fun ⟨_, state, ct⟩ => pure (decide (jacobiSym (ofBits ct : ℤ) (ofBits state) = -1)))
    have hN := ComputableInPolyTime.bitsToNat.comp'
      (ComputableInPolyTime.snd encUnary (encPair encBits encBits)).fst'
    have hc := ComputableInPolyTime.bitsToNat.comp'
      (ComputableInPolyTime.snd encUnary (encPair encBits encBits)).snd'
    exact (ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.decide_eq'
        (ComputableInPolyTime.binary_jacobiSym' hc hN).tidy
        (ComputableTidilyInPolyTime.const (-1 : ℤ)))).isPPTOn

/-- **Necessity of `z ∈ QNR_N^{+1}`** ([KatzLindell2020], Section 15.4.4): if `z ∈ jacobiNegSet p q`
(`J_N(z) = -1`), `jacobiAttackAdversary` distinguishes `encrypt` of `false` from `true` with exact
IND-CPA advantage `1` at every `n` without factoring `N`. -/
theorem advantage_jacobiAttackAdversary_eq_one (d : ModulusDesc)
    (z : (ZMod (d.p * d.q))ˣ) (hz : z ∈ jacobiNegSet d.p d.q) (n : ℕ) :
    let pk := encPair encNat encNat (d.p * d.q, z.val.val)
    Game.advantage
      (Encryption.publicKeyGame (PMF.pure pk) encrypt jacobiAttackAdversary false n)
      (Encryption.publicKeyGame (PMF.pure pk) encrypt jacobiAttackAdversary true n) = 1 := by
  intro pk
  simp only [jacobiNegSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  have hz_cop : z.val.val.Coprime (d.p * d.q) := ZMod.val_coe_unit_coprime z
  have hz_unit : ZMod.unitOfCoprime z.val.val hz_cop = z := by ext; simp [ZMod.coe_unitOfCoprime]
  have hjac_ct (bit : Bool) (r : ℕ) :
      jacobiSym (ciphertext (d.p * d.q) z.val.val bit (unitOrOne (d.p * d.q) r) : ℤ)
        (d.p * d.q) = if bit then -1 else 1 := by
    let u := ZMod.unitOfCoprime (unitOrOne (d.p * d.q) r) (coprime_unitOrOne (d.p * d.q) r)
    rw [ciphertext_eq_unit_val hz_cop (coprime_unitOrOne (d.p * d.q) r) bit, hz_unit,
      ← jacobiSymbol_eq_jacobiSym d.p d.q ((if bit then z else 1) * u ^ 2)]
    cases bit
    · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      exact jacobiSymbol_eq_one_of_isSquare d.p d.q ⟨u, pow_two u⟩
    · simp only [↓reduceIte]
      rw [jacobiSymbol_eq_jacobiSym, Units.val_mul, ZMod.val_mul]; push_cast
      rw [← Nat.cast_mul d.p d.q, ← jacobiSym.mod_left, jacobiSym.mul_left,
        ← jacobiSymbol_eq_jacobiSym d.p d.q z, hz]
      have hsq1 : jacobiSym ((u ^ 2).val.val : ℤ) (d.p * d.q) = 1 := by
        rw [← jacobiSymbol_eq_jacobiSym d.p d.q (u ^ 2)]
        exact jacobiSymbol_eq_one_of_isSquare d.p d.q ⟨u, pow_two u⟩
      rw [← Units.val_pow_eq_pow_val, hsq1, mul_one]
  have hgame (bit : Bool) :
      Encryption.publicKeyGame (PMF.pure pk) encrypt jacobiAttackAdversary bit n =
        PMF.pure bit := by
    simp only [Encryption.publicKeyGame, jacobiAttackAdversary, pk, ProbComp.eval_pure,
      PMF.monad_bind_eq_bind, PMF.pure_bind, ChoiceOut.msg₀_mk, ChoiceOut.msg₁_mk,
      ChoiceOut.state_mk]
    rw [encrypt, unframe_encPair_encNat, dropFrame_encPair_encNat, ofBits_encNat, ofBits_encNat]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, ofBits_encNat]
    have hstep (r : ℕ) :
        decide (jacobiSym (ciphertext (d.p * d.q) z.val.val
          (if bit then true else false) (unitOrOne (d.p * d.q) r) : ℤ) (d.p * d.q) = -1) =
          bit := by
      cases bit <;> simp only [↓reduceIte, Bool.false_eq_true] <;> rw [hjac_ct] <;> decide
    simp only [hstep, PMF.bind_const]
  rw [hgame false, hgame true]
  apply NNReal.coe_injective
  simp [Game.succProbability]

end Cslib.Crypto.GoldwasserMicali
