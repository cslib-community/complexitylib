/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.PseudorandomFunction.MultiKey
public import Complexity.Crypto.Computational.PseudorandomPermutation
public import Complexity.Crypto.Protocols.Cipher.EvenMansour
public import Complexity.Languages.Probabilistic.Oracle.CoinFixing
public import Complexity.Crypto.Encoding
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import Complexity.Crypto.Negligible.Basic
import Complexity.Foundations.Data.BitString.List.Operations
import Complexity.Probability.PMF.Bind
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Computational Even–Mansour block cipher and ideal-permutation PRP security

The Even–Mansour block cipher ([EvenMansour1997]; [BonehShoup2023], Section 4.7;
[KatzLindell2020]) constructs a block cipher on `n`-bit blocks from a public permutation `P` by
XORing pre-whitening and post-whitening keys before and after `P`:
$$E_{k_1, k_2}(x) = P(x \oplus k_1) \oplus k_2, \qquad
  D_{k_1, k_2}(y) = P^{-1}(y \oplus k_2) \oplus k_1,$$
together with the single-key variant $E_k(x) = P(x \oplus k) \oplus k$
([DunkelmanKellerShamir2012]).

This module provides the computational word-level counterpart to
`Complexity.Crypto.Protocols.Cipher.EvenMansour`, mirroring how
`Complexity.Crypto.Computational.LubyRackoff` pairs with
`Complexity.Crypto.Protocols.Cipher.LubyRackoff`:

1. **Word-level Even–Mansour operations and `ComputableInPolyTime` certificates**:
   `evenMansourPreKeyWord`, `evenMansourPostKeyWord`, `splitTwoKeys`, `evenMansourEncryptWord`,
   `evenMansourDecryptWord`, `singleKeyEvenMansourEncryptWord`, and
   `singleKeyEvenMansourDecryptWord` act on `List Bool` words, satisfy exact length, involution,
   inversion, and `BitString n` representation laws, and carry `ComputableInPolyTime` certificates.
   Given polynomial-time word-level forward and inverse permutations `P, P_inv : ℕ → List Bool →
   List Bool`, `evenMansourCipher` and `singleKeyEvenMansourCipher` bundle the two-key (`2 * n`-bit
   key, `n`-bit block) and single-key (`n`-bit key, `n`-bit block) constructions as uniform
   `BlockCipher` instances whose induced permutations `BlockCipher.permEquiv` agree with
   `EvenMansour.evenMansourEquiv` and `EvenMansour.singleKeyEvenMansourEquiv`.
2. **Randomized (`ProbOracleComp`) ideal-permutation security via coin fixing**:
   fixing private coins (`ProbOracleComp.coinLaw` from
   `Complexity.Languages.Probabilistic.Oracle.CoinFixing`) lifts the information-theoretic
   bad-key coupling bounds `EvenMansour.advantage_evenMansourRealGame_evenMansourIdealGame_le` and
   `EvenMansour.advantage_singleKeyEvenMansourRealGame_evenMansourIdealGame_le` from deterministic
   `OracleComp` distinguishers to randomized `ProbOracleComp (EvenMansourSpec G) Bool`
   distinguishers (`advantage_evenMansourProbRealGame_evenMansourProbIdealGame_le`,
   `advantage_singleKeyEvenMansourProbRealGame_evenMansourProbIdealGame_le`), and yields asymptotic
   `Negligible` distinguishing advantage whenever the cipher and primitive query budgets
   `Q_C, Q_P : ℕ → ℕ` are polynomially bounded (`negligible_advantage_evenMansourProbRealGame`,
   `negligible_advantage_singleKeyEvenMansourProbRealGame`).
3. **Word-oracle (`WordOracleComp`) ideal-permutation games and `IsOraclePPT` security**:
   `evenMansourWordRealGame`, `singleKeyEvenMansourWordRealGame`, and `evenMansourWordIdealGame`
   expose the bidirectional cipher and primitive permutation channels as word oracles (rejecting
   malformed queries with `[]`), satisfy the `2 * Q_C * Q_P / 2 ^ n` security bound, and are
   computationally indistinguishable against all `IsOraclePPT encBool` distinguishers
   (`indistinguishable_evenMansourWordRealGame_evenMansourWordIdealGame`,
   `indistinguishable_singleKeyEvenMansourWordRealGame_evenMansourWordIdealGame`).

## Main definitions

* `Cslib.Crypto.evenMansourPreKeyWord`, `Cslib.Crypto.evenMansourPostKeyWord`,
  `Cslib.Crypto.splitTwoKeys`: word-level XOR key masking and `2 * n`-bit key splitting.
* `Cslib.Crypto.evenMansourEncryptWord`, `Cslib.Crypto.evenMansourDecryptWord`,
  `Cslib.Crypto.singleKeyEvenMansourEncryptWord`,
  `Cslib.Crypto.singleKeyEvenMansourDecryptWord`: word-level Even–Mansour encryption and decryption.
* `Cslib.Crypto.evenMansourCipher`, `Cslib.Crypto.singleKeyEvenMansourCipher`: uniform
  `BlockCipher` bundles for two-key and single-key Even–Mansour.
* `Cslib.Crypto.IsProbCallBounded`, `Cslib.Crypto.evenMansourProbRealGame`,
  `Cslib.Crypto.singleKeyEvenMansourProbRealGame`, `Cslib.Crypto.evenMansourProbIdealGame`:
  randomized ideal-permutation games and separate cipher/primitive query budgets.
* `Cslib.Crypto.EvenMansourDistinguisher`, `Cslib.Crypto.evenMansourWordRealGame`,
  `Cslib.Crypto.singleKeyEvenMansourWordRealGame`, `Cslib.Crypto.evenMansourWordIdealGame`:
  word-oracle ideal-permutation games.

## Main results

* `Cslib.Crypto.computableInPolyTime_evenMansourPreKeyWord`,
  `Cslib.Crypto.computableInPolyTime_evenMansourPostKeyWord`,
  `Cslib.Crypto.computableInPolyTime_splitTwoKeys`,
  `Cslib.Crypto.computableInPolyTime_evenMansourEncryptWord`,
  `Cslib.Crypto.computableInPolyTime_evenMansourDecryptWord`: polynomial-time certificates for
  word-level Even–Mansour operations.
* `Cslib.Crypto.evenMansourDecryptWord_evenMansourEncryptWord`,
  `Cslib.Crypto.evenMansourEncryptWord_evenMansourDecryptWord`: word-level inversion laws.
* `Cslib.Crypto.advantage_evenMansourProbRealGame_evenMansourProbIdealGame_le`,
  `Cslib.Crypto.advantage_singleKeyEvenMansourProbRealGame_evenMansourProbIdealGame_le`:
  `2 * Q_C * Q_P / |G|` security bounds for randomized `ProbOracleComp` distinguishers.
* `Cslib.Crypto.negligible_advantage_evenMansourProbRealGame`,
  `Cslib.Crypto.negligible_advantage_singleKeyEvenMansourProbRealGame`: asymptotic `Negligible`
  security when `Q_C` and `Q_P` are polynomially bounded.
* `Cslib.Crypto.advantage_evenMansourWordRealGame_evenMansourWordIdealGame_le`,
  `Cslib.Crypto.advantage_singleKeyEvenMansourWordRealGame_evenMansourWordIdealGame_le`,
  `Cslib.Crypto.indistinguishable_evenMansourWordRealGame_evenMansourWordIdealGame`,
  `Cslib.Crypto.indistinguishable_singleKeyEvenMansourWordRealGame_evenMansourWordIdealGame`:
  quantitative and asymptotic `IsOraclePPT` security for word-oracle distinguishers.

## References

* [S. Even, Y. Mansour, *A Construction of a Cipher from a Single Pseudorandom
  Permutation*][EvenMansour1997].
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 4.7 (Theorem 4.14, p. 159).
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020].
* [O. Dunkelman, N. Keller, A. Shamir, *Minimalism in Cryptography: The Even–Mansour Scheme
  Revisited*][DunkelmanKellerShamir2012].
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Word-level Even–Mansour operations and `ComputableInPolyTime` certificates -/

/-- Pre-whitening XOR mask on bit words: `x ⊕ k₁` (`List.zipWith Bool.xor x k₁`). -/
@[expose] def evenMansourPreKeyWord (k₁ x : List Bool) : List Bool :=
  List.zipWith Bool.xor x k₁

/-- Post-whitening XOR mask on bit words: `y ⊕ k₂` (`List.zipWith Bool.xor y k₂`). -/
@[expose] def evenMansourPostKeyWord (k₂ y : List Bool) : List Bool :=
  List.zipWith Bool.xor y k₂

/-- Split a `2 * n`-bit key word `k₁ ++ k₂` into its two `n`-bit subkeys
`(keyBlock n 0 key, keyBlock n 1 key)`. -/
@[expose] def splitTwoKeys (n : ℕ) (key : List Bool) : List Bool × List Bool :=
  (keyBlock n 0 key, keyBlock n 1 key)

/-- Word-level two-key Even–Mansour encryption `E_{k₁, k₂}(x) = P(x ⊕ k₁) ⊕ k₂`
([EvenMansour1997]; [BonehShoup2023], Section 4.7). -/
@[expose] def evenMansourEncryptWord (P : List Bool → List Bool) (k₁ k₂ x : List Bool) :
    List Bool :=
  evenMansourPostKeyWord k₂ (P (evenMansourPreKeyWord k₁ x))

/-- Word-level two-key Even–Mansour decryption `D_{k₁, k₂}(y) = P⁻¹(y ⊕ k₂) ⊕ k₁`
([EvenMansour1997]; [BonehShoup2023], Section 4.7). -/
@[expose] def evenMansourDecryptWord (P_inv : List Bool → List Bool) (k₁ k₂ y : List Bool) :
    List Bool :=
  evenMansourPreKeyWord k₁ (P_inv (evenMansourPostKeyWord k₂ y))

/-- Word-level single-key Even–Mansour encryption `E_k(x) = P(x ⊕ k) ⊕ k`
([DunkelmanKellerShamir2012]). -/
@[expose] def singleKeyEvenMansourEncryptWord (P : List Bool → List Bool) (k x : List Bool) :
    List Bool :=
  evenMansourEncryptWord P k k x

/-- Word-level single-key Even–Mansour decryption `D_k(y) = P⁻¹(y ⊕ k) ⊕ k`
([DunkelmanKellerShamir2012]). -/
@[expose] def singleKeyEvenMansourDecryptWord (P_inv : List Bool → List Bool) (k y : List Bool) :
    List Bool :=
  evenMansourDecryptWord P_inv k k y

/-- Parameterized two-key Even–Mansour encryption on a `2 * n`-bit key `k₁ ++ k₂` and `n`-bit
block. -/
@[expose] def evenMansourEncrypt (P : ℕ → List Bool → List Bool) (n : ℕ)
    (key block : List Bool) : List Bool :=
  let keys := splitTwoKeys n key
  evenMansourEncryptWord (P n) keys.1 keys.2 block

/-- Parameterized two-key Even–Mansour decryption on a `2 * n`-bit key `k₁ ++ k₂` and `n`-bit
ciphertext. -/
@[expose] def evenMansourDecrypt (P_inv : ℕ → List Bool → List Bool) (n : ℕ)
    (key block : List Bool) : List Bool :=
  let keys := splitTwoKeys n key
  evenMansourDecryptWord (P_inv n) keys.1 keys.2 block

/-- Parameterized single-key Even–Mansour encryption on an `n`-bit key and `n`-bit block. -/
@[expose] def singleKeyEvenMansourEncrypt (P : ℕ → List Bool → List Bool) (n : ℕ)
    (key block : List Bool) : List Bool :=
  singleKeyEvenMansourEncryptWord (P n) key block

/-- Parameterized single-key Even–Mansour decryption on an `n`-bit key and `n`-bit ciphertext. -/
@[expose] def singleKeyEvenMansourDecrypt (P_inv : ℕ → List Bool → List Bool) (n : ℕ)
    (key block : List Bool) : List Bool :=
  singleKeyEvenMansourDecryptWord (P_inv n) key block

/-! #### Length, involution, and representation lemmas -/

@[simp] theorem length_evenMansourPreKeyWord (k₁ x : List Bool) :
    (evenMansourPreKeyWord k₁ x).length = min x.length k₁.length := by
  simp [evenMansourPreKeyWord]

@[simp] theorem length_evenMansourPostKeyWord (k₂ y : List Bool) :
    (evenMansourPostKeyWord k₂ y).length = min y.length k₂.length := by
  simp [evenMansourPostKeyWord]

theorem length_evenMansourPreKeyWord_of_eq {n : ℕ} {k₁ x : List Bool}
    (hk₁ : k₁.length = n) (hx : x.length = n) :
    (evenMansourPreKeyWord k₁ x).length = n := by
  simp [hk₁, hx]

theorem length_evenMansourPostKeyWord_of_eq {n : ℕ} {k₂ y : List Bool}
    (hk₂ : k₂.length = n) (hy : y.length = n) :
    (evenMansourPostKeyWord k₂ y).length = n := by
  simp [hk₂, hy]

private theorem zipWith_xor_self_right :
    ∀ msg pad : List Bool, msg.length = pad.length →
      List.zipWith Bool.xor (List.zipWith Bool.xor msg pad) pad = msg
  | [], [], _ => rfl
  | m :: msg, b :: pad, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zipWith_cons_cons, zipWith_xor_self_right msg pad h]
    cases m <;> cases b <;> rfl

/-- Applying `evenMansourPreKeyWord k₁` twice cancels on equal-length words. -/
@[simp] theorem evenMansourPreKeyWord_self (k₁ x : List Bool) (h : x.length = k₁.length) :
    evenMansourPreKeyWord k₁ (evenMansourPreKeyWord k₁ x) = x :=
  zipWith_xor_self_right x k₁ h

/-- Applying `evenMansourPostKeyWord k₂` twice cancels on equal-length words. -/
@[simp] theorem evenMansourPostKeyWord_self (k₂ y : List Bool) (h : y.length = k₂.length) :
    evenMansourPostKeyWord k₂ (evenMansourPostKeyWord k₂ y) = y :=
  zipWith_xor_self_right y k₂ h

/-- On `BitString n`, `evenMansourPreKeyWord` computes `x + k₁`. -/
theorem evenMansourPreKeyWord_ofFn {n : ℕ} (k₁ x : BitString n) :
    evenMansourPreKeyWord (List.ofFn k₁) (List.ofFn x) = List.ofFn (x + k₁) :=
  (BitString.ofFn_add x k₁).symm

/-- On `BitString n`, `evenMansourPostKeyWord` computes `y + k₂`. -/
theorem evenMansourPostKeyWord_ofFn {n : ℕ} (k₂ y : BitString n) :
    evenMansourPostKeyWord (List.ofFn k₂) (List.ofFn y) = List.ofFn (y + k₂) :=
  (BitString.ofFn_add y k₂).symm

theorem splitTwoKeys_fst_eq_take (n : ℕ) (key : List Bool) :
    (splitTwoKeys n key).1 = key.take n := by
  simp [splitTwoKeys, keyBlock]

theorem length_splitTwoKeys_fst {n : ℕ} {key : List Bool} (hkey : key.length = 2 * n) :
    (splitTwoKeys n key).1.length = n :=
  length_keyBlock hkey (by decide)

theorem length_splitTwoKeys_snd {n : ℕ} {key : List Bool} (hkey : key.length = 2 * n) :
    (splitTwoKeys n key).2.length = n :=
  length_keyBlock hkey (by decide)

/-- Word-level Even–Mansour encryption preserves `n`-bit block length when `P` preserves `n`-bit
words and the subkeys have length `n`. -/
theorem length_evenMansourEncryptWord {n : ℕ} {P : List Bool → List Bool}
    (hP : ∀ u : List Bool, u.length = n → (P u).length = n)
    {k₁ k₂ x : List Bool} (hk₁ : k₁.length = n) (hk₂ : k₂.length = n) (hx : x.length = n) :
    (evenMansourEncryptWord P k₁ k₂ x).length = n := by
  have hpre : (evenMansourPreKeyWord k₁ x).length = n :=
    length_evenMansourPreKeyWord_of_eq hk₁ hx
  exact length_evenMansourPostKeyWord_of_eq hk₂ (hP _ hpre)

/-- Word-level Even–Mansour decryption preserves `n`-bit block length when `P_inv` preserves
`n`-bit words and the subkeys have length `n`. -/
theorem length_evenMansourDecryptWord {n : ℕ} {P_inv : List Bool → List Bool}
    (hP_inv : ∀ v : List Bool, v.length = n → (P_inv v).length = n)
    {k₁ k₂ y : List Bool} (hk₁ : k₁.length = n) (hk₂ : k₂.length = n) (hy : y.length = n) :
    (evenMansourDecryptWord P_inv k₁ k₂ y).length = n := by
  have hpost : (evenMansourPostKeyWord k₂ y).length = n :=
    length_evenMansourPostKeyWord_of_eq hk₂ hy
  exact length_evenMansourPreKeyWord_of_eq hk₁ (hP_inv _ hpost)

/-- Word-level Even–Mansour decryption inverts encryption on `n`-bit words whenever `P_inv`
left-inverts `P` on `n`-bit words and `P` preserves `n`-bit length. -/
theorem evenMansourDecryptWord_evenMansourEncryptWord {n : ℕ}
    {P P_inv : List Bool → List Bool}
    (hP : ∀ u : List Bool, u.length = n → (P u).length = n)
    (hleft : ∀ u : List Bool, u.length = n → P_inv (P u) = u)
    {k₁ k₂ x : List Bool} (hk₁ : k₁.length = n) (hk₂ : k₂.length = n) (hx : x.length = n) :
    evenMansourDecryptWord P_inv k₁ k₂ (evenMansourEncryptWord P k₁ k₂ x) = x := by
  have hpre : (evenMansourPreKeyWord k₁ x).length = n :=
    length_evenMansourPreKeyWord_of_eq hk₁ hx
  have hPpre : (P (evenMansourPreKeyWord k₁ x)).length = n := hP _ hpre
  simp only [evenMansourEncryptWord, evenMansourDecryptWord]
  rw [evenMansourPostKeyWord_self k₂ _ (hPpre.trans hk₂.symm), hleft _ hpre,
    evenMansourPreKeyWord_self k₁ x (hx.trans hk₁.symm)]

/-- Word-level Even–Mansour encryption inverts decryption on `n`-bit words whenever `P_inv`
right-inverts `P` on `n`-bit words and `P_inv` preserves `n`-bit length. -/
theorem evenMansourEncryptWord_evenMansourDecryptWord {n : ℕ}
    {P P_inv : List Bool → List Bool}
    (hP_inv : ∀ v : List Bool, v.length = n → (P_inv v).length = n)
    (hright : ∀ v : List Bool, v.length = n → P (P_inv v) = v)
    {k₁ k₂ y : List Bool} (hk₁ : k₁.length = n) (hk₂ : k₂.length = n) (hy : y.length = n) :
    evenMansourEncryptWord P k₁ k₂ (evenMansourDecryptWord P_inv k₁ k₂ y) = y := by
  have hpost : (evenMansourPostKeyWord k₂ y).length = n :=
    length_evenMansourPostKeyWord_of_eq hk₂ hy
  have hPpost : (P_inv (evenMansourPostKeyWord k₂ y)).length = n := hP_inv _ hpost
  simp only [evenMansourEncryptWord, evenMansourDecryptWord]
  rw [evenMansourPreKeyWord_self k₁ _ (hPpost.trans hk₁.symm), hright _ hpost,
    evenMansourPostKeyWord_self k₂ y (hy.trans hk₂.symm)]

/-- Single-key word-level decryption inverts encryption on `n`-bit words. -/
theorem singleKeyEvenMansourDecryptWord_singleKeyEvenMansourEncryptWord {n : ℕ}
    {P P_inv : List Bool → List Bool}
    (hP : ∀ u : List Bool, u.length = n → (P u).length = n)
    (hleft : ∀ u : List Bool, u.length = n → P_inv (P u) = u)
    {k x : List Bool} (hk : k.length = n) (hx : x.length = n) :
    singleKeyEvenMansourDecryptWord P_inv k (singleKeyEvenMansourEncryptWord P k x) = x :=
  evenMansourDecryptWord_evenMansourEncryptWord hP hleft hk hk hx

/-- Single-key word-level encryption inverts decryption on `n`-bit words. -/
theorem singleKeyEvenMansourEncryptWord_singleKeyEvenMansourDecryptWord {n : ℕ}
    {P P_inv : List Bool → List Bool}
    (hP_inv : ∀ v : List Bool, v.length = n → (P_inv v).length = n)
    (hright : ∀ v : List Bool, v.length = n → P (P_inv v) = v)
    {k y : List Bool} (hk : k.length = n) (hy : y.length = n) :
    singleKeyEvenMansourEncryptWord P k (singleKeyEvenMansourDecryptWord P_inv k y) = y :=
  evenMansourEncryptWord_evenMansourDecryptWord hP_inv hright hk hk hy

/-- When `P` represents `π : Equiv.Perm (BitString n)` on `n`-bit words, `evenMansourEncryptWord`
computes `EvenMansour.evenMansourEquiv π k₁ k₂`. -/
theorem evenMansourEncryptWord_ofFn {n : ℕ} {P : List Bool → List Bool}
    {π : Equiv.Perm (BitString n)} (hP : ∀ u : BitString n, P (List.ofFn u) = List.ofFn (π u))
    (k₁ k₂ x : BitString n) :
    evenMansourEncryptWord P (List.ofFn k₁) (List.ofFn k₂) (List.ofFn x) =
      List.ofFn (EvenMansour.evenMansourEquiv π k₁ k₂ x) := by
  simp only [evenMansourEncryptWord, evenMansourPreKeyWord_ofFn, hP, evenMansourPostKeyWord_ofFn,
    EvenMansour.evenMansourEquiv_apply]

/-- When `P_inv` represents `π.symm` on `n`-bit words, `evenMansourDecryptWord` computes
`(EvenMansour.evenMansourEquiv π k₁ k₂).symm`. -/
theorem evenMansourDecryptWord_ofFn {n : ℕ} {P_inv : List Bool → List Bool}
    {π : Equiv.Perm (BitString n)}
    (hP_inv : ∀ v : BitString n, P_inv (List.ofFn v) = List.ofFn (π.symm v))
    (k₁ k₂ y : BitString n) :
    evenMansourDecryptWord P_inv (List.ofFn k₁) (List.ofFn k₂) (List.ofFn y) =
      List.ofFn ((EvenMansour.evenMansourEquiv π k₁ k₂).symm y) := by
  rw [EvenMansour.evenMansourEquiv_symm_bitString]
  exact evenMansourEncryptWord_ofFn hP_inv k₂ k₁ y

/-! #### `ComputableInPolyTime` certificates -/

/-- Pre-whitening XOR masking is computable in polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_evenMansourPreKeyWord :
    ComputableInPolyTime (fun p : List Bool × List Bool => evenMansourPreKeyWord p.1 p.2)
      (encPair encBits encBits) encBits := by
  unfold evenMansourPreKeyWord
  polytime

/-- Post-whitening XOR masking is computable in polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_evenMansourPostKeyWord :
    ComputableInPolyTime (fun p : List Bool × List Bool => evenMansourPostKeyWord p.1 p.2)
      (encPair encBits encBits) encBits := by
  unfold evenMansourPostKeyWord
  polytime

/-- Splitting a `2 * n`-bit key into two `n`-bit keys is computable in polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_splitTwoKeys :
    ComputableInPolyTime (fun p : ℕ × List Bool => splitTwoKeys p.1 p.2)
      (encPair encUnary encBits) (encPair encBits encBits) := by
  unfold splitTwoKeys keyBlock
  polytime

/-- Word-level Even–Mansour encryption is computable in polynomial time whenever `P` is. -/
@[program_certificate]
theorem computableInPolyTime_evenMansourEncryptWord {P : List Bool → List Bool}
    (hP : ComputableInPolyTime P encBits encBits) :
    ComputableInPolyTime
      (fun t : List Bool × List Bool × List Bool => evenMansourEncryptWord P t.1 t.2.1 t.2.2)
      (encPair encBits (encPair encBits encBits)) encBits := by
  have hpre : ComputableInPolyTime
      (fun t : List Bool × List Bool × List Bool => evenMansourPreKeyWord t.1 t.2.2)
      (encPair encBits (encPair encBits encBits)) encBits := by
    unfold evenMansourPreKeyWord
    polytime
  have hmid : ComputableInPolyTime
      (fun t : List Bool × List Bool × List Bool => P (evenMansourPreKeyWord t.1 t.2.2))
      (encPair encBits (encPair encBits encBits)) encBits := hP.comp hpre
  exact computableInPolyTime_evenMansourPostKeyWord.comp ((by polytime :
    ComputableInPolyTime (fun t : List Bool × List Bool × List Bool => t.2.1)
      (encPair encBits (encPair encBits encBits)) encBits).prod hmid)

/-- Word-level Even–Mansour decryption is computable in polynomial time whenever `P_inv` is. -/
@[program_certificate]
theorem computableInPolyTime_evenMansourDecryptWord {P_inv : List Bool → List Bool}
    (hP_inv : ComputableInPolyTime P_inv encBits encBits) :
    ComputableInPolyTime
      (fun t : List Bool × List Bool × List Bool => evenMansourDecryptWord P_inv t.1 t.2.1 t.2.2)
      (encPair encBits (encPair encBits encBits)) encBits := by
  have hpost : ComputableInPolyTime
      (fun t : List Bool × List Bool × List Bool => evenMansourPostKeyWord t.2.1 t.2.2)
      (encPair encBits (encPair encBits encBits)) encBits := by
    unfold evenMansourPostKeyWord
    polytime
  have hmid : ComputableInPolyTime
      (fun t : List Bool × List Bool × List Bool => P_inv (evenMansourPostKeyWord t.2.1 t.2.2))
      (encPair encBits (encPair encBits encBits)) encBits := hP_inv.comp hpost
  exact computableInPolyTime_evenMansourPreKeyWord.comp ((by polytime :
    ComputableInPolyTime (fun t : List Bool × List Bool × List Bool => t.1)
      (encPair encBits (encPair encBits encBits)) encBits).prod hmid)

/-- Parameterized two-key Even–Mansour encryption is computable in polynomial time whenever `P`
is. -/
@[program_certificate]
theorem computableInPolyTime_evenMansourEncrypt {P : ℕ → List Bool → List Bool}
    (hP : ComputableInPolyTime (fun p : ℕ × List Bool => P p.1 p.2)
      (encPair encUnary encBits) encBits) :
    ComputableInPolyTime (fun t : ℕ × List Bool × List Bool => evenMansourEncrypt P t.1 t.2.1 t.2.2)
      (encKeyedInput encBits) encBits := by
  have hpre : ComputableInPolyTime
      (fun t : ℕ × List Bool × List Bool =>
        (t.1, evenMansourPreKeyWord (splitTwoKeys t.1 t.2.1).1 t.2.2))
      (encPair encUnary (encPair encBits encBits)) (encPair encUnary encBits) := by
    unfold evenMansourPreKeyWord splitTwoKeys keyBlock
    polytime
  have hmid : ComputableInPolyTime
      (fun t : ℕ × List Bool × List Bool =>
        P t.1 (evenMansourPreKeyWord (splitTwoKeys t.1 t.2.1).1 t.2.2))
      (encPair encUnary (encPair encBits encBits)) encBits := hP.comp hpre
  have hk₂ : ComputableInPolyTime
      (fun t : ℕ × List Bool × List Bool => (splitTwoKeys t.1 t.2.1).2)
      (encPair encUnary (encPair encBits encBits)) encBits := by
    unfold splitTwoKeys keyBlock
    polytime
  exact computableInPolyTime_evenMansourPostKeyWord.comp (hk₂.prod hmid)

/-- Parameterized two-key Even–Mansour decryption is computable in polynomial time whenever `P_inv`
is. -/
@[program_certificate]
theorem computableInPolyTime_evenMansourDecrypt {P_inv : ℕ → List Bool → List Bool}
    (hP_inv : ComputableInPolyTime (fun p : ℕ × List Bool => P_inv p.1 p.2)
      (encPair encUnary encBits) encBits) :
    ComputableInPolyTime
      (fun t : ℕ × List Bool × List Bool => evenMansourDecrypt P_inv t.1 t.2.1 t.2.2)
      (encKeyedInput encBits) encBits := by
  have hpost : ComputableInPolyTime
      (fun t : ℕ × List Bool × List Bool =>
        (t.1, evenMansourPostKeyWord (splitTwoKeys t.1 t.2.1).2 t.2.2))
      (encPair encUnary (encPair encBits encBits)) (encPair encUnary encBits) := by
    unfold evenMansourPostKeyWord splitTwoKeys keyBlock
    polytime
  have hmid : ComputableInPolyTime
      (fun t : ℕ × List Bool × List Bool =>
        P_inv t.1 (evenMansourPostKeyWord (splitTwoKeys t.1 t.2.1).2 t.2.2))
      (encPair encUnary (encPair encBits encBits)) encBits := hP_inv.comp hpost
  have hk₁ : ComputableInPolyTime
      (fun t : ℕ × List Bool × List Bool => (splitTwoKeys t.1 t.2.1).1)
      (encPair encUnary (encPair encBits encBits)) encBits := by
    unfold splitTwoKeys keyBlock
    polytime
  exact computableInPolyTime_evenMansourPreKeyWord.comp (hk₁.prod hmid)

/-- Parameterized single-key Even–Mansour encryption is computable in polynomial time whenever `P`
is. -/
@[program_certificate]
theorem computableInPolyTime_singleKeyEvenMansourEncrypt {P : ℕ → List Bool → List Bool}
    (hP : ComputableInPolyTime (fun p : ℕ × List Bool => P p.1 p.2)
      (encPair encUnary encBits) encBits) :
    ComputableInPolyTime
      (fun t : ℕ × List Bool × List Bool => singleKeyEvenMansourEncrypt P t.1 t.2.1 t.2.2)
      (encKeyedInput encBits) encBits := by
  have hpre : ComputableInPolyTime
      (fun t : ℕ × List Bool × List Bool => (t.1, evenMansourPreKeyWord t.2.1 t.2.2))
      (encPair encUnary (encPair encBits encBits)) (encPair encUnary encBits) := by
    unfold evenMansourPreKeyWord
    polytime
  have hmid : ComputableInPolyTime
      (fun t : ℕ × List Bool × List Bool => P t.1 (evenMansourPreKeyWord t.2.1 t.2.2))
      (encPair encUnary (encPair encBits encBits)) encBits := hP.comp hpre
  have hk : ComputableInPolyTime
      (fun t : ℕ × List Bool × List Bool => t.2.1)
      (encPair encUnary (encPair encBits encBits)) encBits := by polytime
  exact computableInPolyTime_evenMansourPostKeyWord.comp (hk.prod hmid)

/-- Parameterized single-key Even–Mansour decryption is computable in polynomial time whenever
`P_inv` is. -/
@[program_certificate]
theorem computableInPolyTime_singleKeyEvenMansourDecrypt {P_inv : ℕ → List Bool → List Bool}
    (hP_inv : ComputableInPolyTime (fun p : ℕ × List Bool => P_inv p.1 p.2)
      (encPair encUnary encBits) encBits) :
    ComputableInPolyTime
      (fun t : ℕ × List Bool × List Bool => singleKeyEvenMansourDecrypt P_inv t.1 t.2.1 t.2.2)
      (encKeyedInput encBits) encBits := by
  have hpost : ComputableInPolyTime
      (fun t : ℕ × List Bool × List Bool => (t.1, evenMansourPostKeyWord t.2.1 t.2.2))
      (encPair encUnary (encPair encBits encBits)) (encPair encUnary encBits) := by
    unfold evenMansourPostKeyWord
    polytime
  have hmid : ComputableInPolyTime
      (fun t : ℕ × List Bool × List Bool => P_inv t.1 (evenMansourPostKeyWord t.2.1 t.2.2))
      (encPair encUnary (encPair encBits encBits)) encBits := hP_inv.comp hpost
  have hk : ComputableInPolyTime
      (fun t : ℕ × List Bool × List Bool => t.2.1)
      (encPair encUnary (encPair encBits encBits)) encBits := by polytime
  exact computableInPolyTime_evenMansourPreKeyWord.comp (hk.prod hmid)

/-! #### Uniform `BlockCipher` bundles -/

/-- The permutation on `BitString n` induced by a pair of length-preserving inverse word functions
`(P n, P_inv n)`. -/
@[expose] def permOfWordFamily (P P_inv : ℕ → List Bool → List Bool)
    (hP_len : ∀ n block, block.length = n → (P n block).length = n)
    (hP_inv_len : ∀ n block, block.length = n → (P_inv n block).length = n)
    (hleft : ∀ n block, block.length = n → P_inv n (P n block) = block)
    (hright : ∀ n block, block.length = n → P n (P_inv n block) = block)
    (n : ℕ) : Equiv.Perm (BitString n) where
  toFun x := BitString.ofList n (P n (List.ofFn x))
  invFun y := BitString.ofList n (P_inv n (List.ofFn y))
  left_inv x := by
    dsimp only
    have hx : (List.ofFn x).length = n := List.length_ofFn
    rw [BitString.ofFn_ofList (hP_len n _ hx), hleft n _ hx, BitString.ofList_ofFn]
  right_inv y := by
    dsimp only
    have hy : (List.ofFn y).length = n := List.length_ofFn
    rw [BitString.ofFn_ofList (hP_inv_len n _ hy), hright n _ hy, BitString.ofList_ofFn]

/-- The uniform two-key Even–Mansour `BlockCipher` with `2 * n`-bit keys and `n`-bit blocks, built
from polynomial-time inverse word permutations `P` and `P_inv`
([EvenMansour1997]; [BonehShoup2023], Section 4.7). -/
@[expose] def evenMansourCipher (P P_inv : ℕ → List Bool → List Bool)
    (hP_poly : ComputableInPolyTime (fun p : ℕ × List Bool => P p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hP_inv_poly : ComputableInPolyTime (fun p : ℕ × List Bool => P_inv p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hP_len : ∀ n block, block.length = n → (P n block).length = n)
    (hP_inv_len : ∀ n block, block.length = n → (P_inv n block).length = n)
    (hleft : ∀ n block, block.length = n → P_inv n (P n block) = block)
    (hright : ∀ n block, block.length = n → P n (P_inv n block) = block) :
    BlockCipher where
  keyLen n := 2 * n
  blockLen n := n
  keyLen_polyTime := by polytime
  blockLen_polyTime := ComputableInPolyTime.id'
  encrypt := evenMansourEncrypt P
  decrypt := evenMansourDecrypt P_inv
  encrypt_polyTime := computableInPolyTime_evenMansourEncrypt hP_poly
  decrypt_polyTime := computableInPolyTime_evenMansourDecrypt hP_inv_poly
  length_encrypt n key block hkey hblock :=
    length_evenMansourEncryptWord (hP_len n)
      (length_splitTwoKeys_fst hkey) (length_splitTwoKeys_snd hkey) hblock
  length_decrypt n key block hkey hblock :=
    length_evenMansourDecryptWord (hP_inv_len n)
      (length_splitTwoKeys_fst hkey) (length_splitTwoKeys_snd hkey) hblock
  decrypt_encrypt n key block hkey hblock :=
    evenMansourDecryptWord_evenMansourEncryptWord (hP_len n) (hleft n)
      (length_splitTwoKeys_fst hkey) (length_splitTwoKeys_snd hkey) hblock
  encrypt_decrypt n key block hkey hblock :=
    evenMansourEncryptWord_evenMansourDecryptWord (hP_inv_len n) (hright n)
      (length_splitTwoKeys_fst hkey) (length_splitTwoKeys_snd hkey) hblock

/-- The uniform single-key Even–Mansour `BlockCipher` with `n`-bit keys and `n`-bit blocks, built
from polynomial-time inverse word permutations `P` and `P_inv` ([DunkelmanKellerShamir2012]). -/
@[expose] def singleKeyEvenMansourCipher (P P_inv : ℕ → List Bool → List Bool)
    (hP_poly : ComputableInPolyTime (fun p : ℕ × List Bool => P p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hP_inv_poly : ComputableInPolyTime (fun p : ℕ × List Bool => P_inv p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hP_len : ∀ n (block : List Bool), block.length = n → (P n block).length = n)
    (hP_inv_len : ∀ n (block : List Bool), block.length = n → (P_inv n block).length = n)
    (hleft : ∀ n (block : List Bool), block.length = n → P_inv n (P n block) = block)
    (hright : ∀ n (block : List Bool), block.length = n → P n (P_inv n block) = block) :
    BlockCipher where
  keyLen n := n
  blockLen n := n
  keyLen_polyTime := ComputableInPolyTime.id'
  blockLen_polyTime := ComputableInPolyTime.id'
  encrypt := singleKeyEvenMansourEncrypt P
  decrypt := singleKeyEvenMansourDecrypt P_inv
  encrypt_polyTime := computableInPolyTime_singleKeyEvenMansourEncrypt hP_poly
  decrypt_polyTime := computableInPolyTime_singleKeyEvenMansourDecrypt hP_inv_poly
  length_encrypt n _ _ hkey hblock :=
    length_evenMansourEncryptWord (hP_len n) hkey hkey hblock
  length_decrypt n _ _ hkey hblock :=
    length_evenMansourDecryptWord (hP_inv_len n) hkey hkey hblock
  decrypt_encrypt n _ _ hkey hblock :=
    singleKeyEvenMansourDecryptWord_singleKeyEvenMansourEncryptWord (hP_len n) (hleft n) hkey hblock
  encrypt_decrypt n _ _ hkey hblock :=
    singleKeyEvenMansourEncryptWord_singleKeyEvenMansourDecryptWord (hP_inv_len n) (hright n)
      hkey hblock

/-- The permutation induced by `evenMansourCipher` on a `2 * n`-bit key `key` equals
`EvenMansour.evenMansourEquiv` with the split `n`-bit subkeys. -/
theorem permEquiv_evenMansourCipher (P P_inv : ℕ → List Bool → List Bool)
    (hP_poly : ComputableInPolyTime (fun p : ℕ × List Bool => P p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hP_inv_poly : ComputableInPolyTime (fun p : ℕ × List Bool => P_inv p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hP_len : ∀ n block, block.length = n → (P n block).length = n)
    (hP_inv_len : ∀ n block, block.length = n → (P_inv n block).length = n)
    (hleft : ∀ n block, block.length = n → P_inv n (P n block) = block)
    (hright : ∀ n block, block.length = n → P n (P_inv n block) = block)
    (n : ℕ) (key : List Bool) (hkey : key.length = 2 * n) :
    (evenMansourCipher P P_inv hP_poly hP_inv_poly hP_len hP_inv_len hleft hright).permEquiv
      n key hkey =
    EvenMansour.evenMansourEquiv
      (permOfWordFamily P P_inv hP_len hP_inv_len hleft hright n)
      (BitString.ofList n (splitTwoKeys n key).1)
      (BitString.ofList n (splitTwoKeys n key).2) := by
  ext (x : BitString n) : 1
  have hk₁ : (splitTwoKeys n key).1.length = n := length_splitTwoKeys_fst hkey
  have hk₂ : (splitTwoKeys n key).2.length = n := length_splitTwoKeys_snd hkey
  have hrep : ∀ u : BitString n, P n (List.ofFn u) =
      List.ofFn (permOfWordFamily P P_inv hP_len hP_inv_len hleft hright n u) := by
    intro u
    dsimp only [permOfWordFamily, Equiv.coe_fn_mk]
    rw [BitString.ofFn_ofList (hP_len n _ List.length_ofFn)]
  change BitString.ofList n
      (evenMansourEncryptWord (P n) (splitTwoKeys n key).1 (splitTwoKeys n key).2 (List.ofFn x)) =
    EvenMansour.evenMansourEquiv
      (permOfWordFamily P P_inv hP_len hP_inv_len hleft hright n)
      (BitString.ofList n (splitTwoKeys n key).1)
      (BitString.ofList n (splitTwoKeys n key).2) x
  conv_lhs =>
    rw [← BitString.ofFn_ofList hk₁, ← BitString.ofFn_ofList hk₂,
      evenMansourEncryptWord_ofFn hrep]
  exact BitString.ofList_ofFn _

/-- The permutation induced by `singleKeyEvenMansourCipher` on an `n`-bit key `key` equals
`EvenMansour.singleKeyEvenMansourEquiv`. -/
theorem permEquiv_singleKeyEvenMansourCipher (P P_inv : ℕ → List Bool → List Bool)
    (hP_poly : ComputableInPolyTime (fun p : ℕ × List Bool => P p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hP_inv_poly : ComputableInPolyTime (fun p : ℕ × List Bool => P_inv p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hP_len : ∀ n block, block.length = n → (P n block).length = n)
    (hP_inv_len : ∀ n block, block.length = n → (P_inv n block).length = n)
    (hleft : ∀ n block, block.length = n → P_inv n (P n block) = block)
    (hright : ∀ n block, block.length = n → P n (P_inv n block) = block)
    (n : ℕ) (key : List Bool) (hkey : key.length = n) :
    (singleKeyEvenMansourCipher P P_inv hP_poly hP_inv_poly hP_len hP_inv_len hleft
      hright).permEquiv n key hkey =
    EvenMansour.singleKeyEvenMansourEquiv
      (permOfWordFamily P P_inv hP_len hP_inv_len hleft hright n)
      (BitString.ofList n key) := by
  ext (x : BitString n) : 1
  have hrep : ∀ u : BitString n, P n (List.ofFn u) =
      List.ofFn (permOfWordFamily P P_inv hP_len hP_inv_len hleft hright n u) := by
    intro u
    dsimp only [permOfWordFamily, Equiv.coe_fn_mk]
    rw [BitString.ofFn_ofList (hP_len n _ List.length_ofFn)]
  change BitString.ofList n (evenMansourEncryptWord (P n) key key (List.ofFn x)) =
    EvenMansour.singleKeyEvenMansourEquiv
      (permOfWordFamily P P_inv hP_len hP_inv_len hleft hright n)
      (BitString.ofList n key) x
  conv_lhs =>
    rw [← BitString.ofFn_ofList hkey, evenMansourEncryptWord_ofFn hrep]
  exact BitString.ofList_ofFn _

/-! ### Randomized (`ProbOracleComp`) ideal-permutation security via coin fixing -/

section ProbOracleSecurity

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]

omit [AddGroup G] [DecidableEq G] [Nonempty G] in
instance instFintypeEvenMansourSpec
    (q : RandomPermutation.PermQuery G ⊕ RandomPermutation.PermQuery G) :
    Fintype (EvenMansour.EvenMansourSpec G q) := by
  cases q <;> exact inferInstanceAs (Fintype G)

/-- Answer a single `EvenMansourSpec G` query against cipher permutation `E` and primitive
permutation `π`. -/
@[expose] def evalTwoPermsQuery (E π : Equiv.Perm G)
    (q : RandomPermutation.PermQuery G ⊕ RandomPermutation.PermQuery G) :
    EvenMansour.EvenMansourSpec G q :=
  match q with
  | .inl qe => RandomPermutation.evalPerm E qe
  | .inr qπ => RandomPermutation.evalPerm π qπ

/-- Evaluate a randomized oracle program `ProbOracleComp (EvenMansourSpec G) α` against cipher
permutation `E` and primitive permutation `π`. -/
@[expose] noncomputable def evalProbTwoPerms {α : Type} (E π : Equiv.Perm G)
    (program : ProbOracleComp (EvenMansour.EvenMansourSpec G) α) : PMF α :=
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifOracle (fun q => PMF.pure (evalTwoPermsQuery E π q)))
    program

/-- A randomized adversary `program : ProbOracleComp (EvenMansourSpec G) α` makes at most `Q_e`
cipher queries and at most `Q_π` primitive permutation queries on every execution path, regardless
of its private coin choices. -/
@[expose] def IsProbCallBounded {α : Type}
    (program : ProbOracleComp (EvenMansour.EvenMansourSpec G) α) (Q_e Q_π : ℕ) : Prop :=
  OracleComp.IsCostBounded (Sum.elim (fun _ => 0) EvenMansour.cipherCost) program Q_e ∧
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) EvenMansour.permCost) program Q_π

omit [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] in
/-- Fixing the private coins `ω` of a randomized `(Q_e, Q_π)`-call-bounded distinguisher yields a
deterministic distinguisher satisfying `EvenMansour.IsCallBounded _ Q_e Q_π`. -/
theorem IsProbCallBounded.fixCoins {α : Type}
    {program : ProbOracleComp (EvenMansour.EvenMansourSpec G) α} {Q_e Q_π : ℕ}
    (h : IsProbCallBounded program Q_e Q_π) (ω : ProbOracleComp.Coins program) :
    EvenMansour.IsCallBounded (ProbOracleComp.fixCoins program ω) Q_e Q_π :=
  ⟨ProbOracleComp.isCostBounded_fixCoins h.1 ω, ProbOracleComp.isCostBounded_fixCoins h.2 ω⟩

omit [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] in
/-- A closed probabilistic sample makes `0` cipher queries and `0` primitive queries. -/
theorem isProbCallBounded_sample {α : Type} (p : ProbComp α) :
    IsProbCallBounded (ProbOracleComp.sample (spec := EvenMansour.EvenMansourSpec G) p) 0 0 :=
  ⟨ProbOracleComp.isCostBounded_sample EvenMansour.cipherCost p,
   ProbOracleComp.isCostBounded_sample EvenMansour.permCost p⟩

omit [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] in
/-- Lifting a deterministic `EvenMansour.IsCallBounded` program to `ProbOracleComp` preserves its
`(Q_e, Q_π)` query budgets. -/
theorem IsProbCallBounded.of_isCallBounded {α : Type}
    {program : OracleComp (EvenMansour.EvenMansourSpec G) α} {Q_e Q_π : ℕ}
    (h : EvenMansour.IsCallBounded program Q_e Q_π) :
    IsProbCallBounded
      (OracleComp.interpret (fun q => ProbOracleComp.query q) program) Q_e Q_π :=
  ⟨ProbOracleComp.isCostBounded_interpret_query h.1,
   ProbOracleComp.isCostBounded_interpret_query h.2⟩

omit [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] in
/-- Any randomized program making at most `Q` total external queries satisfies
`IsProbCallBounded program Q Q`. -/
theorem IsProbCallBounded.of_isQueryBounded {α : Type}
    {program : ProbOracleComp (EvenMansour.EvenMansourSpec G) α} {Q : ℕ}
    (hQ : program.IsQueryBounded Q) : IsProbCallBounded program Q Q :=
  ⟨hQ.of_le fun q => by
      cases q with
      | inl _ => rfl
      | inr q => cases q <;> simp [EvenMansour.cipherCost],
   hQ.of_le fun q => by
      cases q with
      | inl _ => rfl
      | inr q => cases q <;> simp [EvenMansour.permCost]⟩

/-- The real two-key Even–Mansour game for a randomized distinguisher
`program : ProbOracleComp (EvenMansourSpec G) Bool`. -/
@[expose] noncomputable def evenMansourProbRealGame
    (program : ProbOracleComp (EvenMansour.EvenMansourSpec G) Bool) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k ← PMF.uniformOfFintype (G × G)
  evalProbTwoPerms (EvenMansour.evenMansourEquiv π k.1 k.2) π program

/-- The real single-key Even–Mansour game for a randomized distinguisher
`program : ProbOracleComp (EvenMansourSpec G) Bool`. -/
@[expose] noncomputable def singleKeyEvenMansourProbRealGame
    (program : ProbOracleComp (EvenMansour.EvenMansourSpec G) Bool) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k ← PMF.uniformOfFintype G
  evalProbTwoPerms (EvenMansour.singleKeyEvenMansourEquiv π k) π program

/-- The ideal Even–Mansour game for a randomized distinguisher
`program : ProbOracleComp (EvenMansourSpec G) Bool`: two independent uniform permutations
`E, π ← Equiv.Perm G`. -/
@[expose] noncomputable def evenMansourProbIdealGame
    (program : ProbOracleComp (EvenMansour.EvenMansourSpec G) Bool) : Game := do
  let E ← PMF.uniformOfFintype (Equiv.Perm G)
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  evalProbTwoPerms E π program

omit [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] in
private theorem interpret_evalTwoPermsQuery_eq_pure_evalTwoPerms {α : Type} (E π : Equiv.Perm G)
    (program : OracleComp (EvenMansour.EvenMansourSpec G) α) :
    OracleComp.interpret (fun q => PMF.pure (evalTwoPermsQuery E π q)) program =
      PMF.pure (EvenMansour.evalTwoPerms E π program) := by
  induction program with
  | pure a => rfl
  | liftBind q cont ih =>
    change OracleComp.interpret (fun q => PMF.pure (evalTwoPermsQuery E π q))
        (OracleComp.query q >>= cont) =
      PMF.pure (EvenMansour.evalTwoPerms E π (OracleComp.query q >>= cont))
    cases q <;>
      · simp only [EvenMansour.evalTwoPerms, evalTwoPermsQuery, OracleComp.sumHandler,
          OracleComp.interpret_bind, OracleComp.interpret_query, Id.run_bind,
          Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
        exact ih _

/-- Coin-fixing decomposition of `evenMansourProbRealGame`: sampling `(π, k)` independently of
`program`'s private coins equals averaging the deterministic `EvenMansour.evenMansourRealGame` over
`ProbOracleComp.coinLaw program`. -/
theorem evenMansourProbRealGame_eq_coinLaw_bind
    (program : ProbOracleComp (EvenMansour.EvenMansourSpec G) Bool) :
    evenMansourProbRealGame program =
      (ProbOracleComp.coinLaw program).bind fun ω =>
        EvenMansour.evenMansourRealGame (ProbOracleComp.fixCoins program ω) := by
  let μ : PMF (Equiv.Perm G × (G × G)) :=
    (PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
      (PMF.uniformOfFintype (G × G)).map fun k => (π, k)
  have hcoins := ProbOracleComp.table_bind_interpret_eq_coinLaw_bind μ
    (fun p => evalTwoPermsQuery (EvenMansour.evenMansourEquiv p.1 p.2.1 p.2.2) p.1) program
  simp only [μ, evenMansourProbRealGame, EvenMansour.evenMansourRealGame,
    EvenMansour.evalEvenMansour, evalProbTwoPerms, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.bind_map, Function.comp_def,
    interpret_evalTwoPermsQuery_eq_pure_evalTwoPerms] at hcoins ⊢
  exact hcoins

/-- Coin-fixing decomposition of `singleKeyEvenMansourProbRealGame`: sampling `(π, k)`
independently of `program`'s private coins equals averaging the deterministic
`EvenMansour.singleKeyEvenMansourRealGame` over `ProbOracleComp.coinLaw program`. -/
theorem singleKeyEvenMansourProbRealGame_eq_coinLaw_bind
    (program : ProbOracleComp (EvenMansour.EvenMansourSpec G) Bool) :
    singleKeyEvenMansourProbRealGame program =
      (ProbOracleComp.coinLaw program).bind fun ω =>
        EvenMansour.singleKeyEvenMansourRealGame (ProbOracleComp.fixCoins program ω) := by
  let μ : PMF (Equiv.Perm G × G) :=
    (PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
      (PMF.uniformOfFintype G).map fun k => (π, k)
  have hcoins := ProbOracleComp.table_bind_interpret_eq_coinLaw_bind μ
    (fun p => evalTwoPermsQuery (EvenMansour.singleKeyEvenMansourEquiv p.1 p.2) p.1) program
  simp only [μ, singleKeyEvenMansourProbRealGame, EvenMansour.singleKeyEvenMansourRealGame,
    EvenMansour.evalEvenMansour, evalProbTwoPerms, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.bind_map, Function.comp_def,
    interpret_evalTwoPermsQuery_eq_pure_evalTwoPerms] at hcoins ⊢
  exact hcoins

omit [AddGroup G] [Nonempty G] in
/-- Coin-fixing decomposition of `evenMansourProbIdealGame`: sampling `(E, π)` independently of
`program`'s private coins equals averaging the deterministic `EvenMansour.evenMansourIdealGame`
over `ProbOracleComp.coinLaw program`. -/
theorem evenMansourProbIdealGame_eq_coinLaw_bind
    (program : ProbOracleComp (EvenMansour.EvenMansourSpec G) Bool) :
    evenMansourProbIdealGame program =
      (ProbOracleComp.coinLaw program).bind fun ω =>
        EvenMansour.evenMansourIdealGame (ProbOracleComp.fixCoins program ω) := by
  let μ : PMF (Equiv.Perm G × Equiv.Perm G) :=
    (PMF.uniformOfFintype (Equiv.Perm G)).bind fun E =>
      (PMF.uniformOfFintype (Equiv.Perm G)).map fun π => (E, π)
  have hcoins := ProbOracleComp.table_bind_interpret_eq_coinLaw_bind μ
    (fun p => evalTwoPermsQuery p.1 p.2) program
  simp only [μ, evenMansourProbIdealGame, EvenMansour.evenMansourIdealGame, evalProbTwoPerms,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.bind_map, Function.comp_def, interpret_evalTwoPermsQuery_eq_pure_evalTwoPerms] at hcoins ⊢
  exact hcoins

/-- **Randomized two-key Even–Mansour PRP security in the ideal-permutation model**
([EvenMansour1997]; [BonehShoup2023], Theorem 4.14; [KatzLindell2020]): for any randomized
distinguisher `program : ProbOracleComp (EvenMansourSpec G) Bool` making at most `Q_e` cipher
queries and at most `Q_π` primitive permutation queries (`IsProbCallBounded program Q_e Q_π`), the
distinguishing advantage between `evenMansourProbRealGame program` and
`evenMansourProbIdealGame program` is at most `2 * Q_e * Q_π / |G|`. -/
theorem advantage_evenMansourProbRealGame_evenMansourProbIdealGame_le
    {program : ProbOracleComp (EvenMansour.EvenMansourSpec G) Bool} {Q_e Q_π : ℕ}
    (hcall : IsProbCallBounded program Q_e Q_π) :
    (Game.advantage (evenMansourProbRealGame program) (evenMansourProbIdealGame program) : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) := by
  rw [evenMansourProbRealGame_eq_coinLaw_bind, evenMansourProbIdealGame_eq_coinLaw_bind]
  refine Game.advantage_bind_le _ _ _ fun ω => ?_
  exact EvenMansour.advantage_evenMansourRealGame_evenMansourIdealGame_le (hcall.fixCoins ω)

/-- **Randomized single-key Even–Mansour PRP security in the ideal-permutation model**
([DunkelmanKellerShamir2012]; [BonehShoup2023], Section 4.7): for any randomized distinguisher
`program : ProbOracleComp (EvenMansourSpec G) Bool` making at most `Q_e` cipher queries and at
most `Q_π` primitive permutation queries (`IsProbCallBounded program Q_e Q_π`), the distinguishing
advantage between `singleKeyEvenMansourProbRealGame program` and
`evenMansourProbIdealGame program` is at most `2 * Q_e * Q_π / |G|`. -/
theorem advantage_singleKeyEvenMansourProbRealGame_evenMansourProbIdealGame_le
    {program : ProbOracleComp (EvenMansour.EvenMansourSpec G) Bool} {Q_e Q_π : ℕ}
    (hcall : IsProbCallBounded program Q_e Q_π) :
    (Game.advantage (singleKeyEvenMansourProbRealGame program)
      (evenMansourProbIdealGame program) : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) := by
  rw [singleKeyEvenMansourProbRealGame_eq_coinLaw_bind, evenMansourProbIdealGame_eq_coinLaw_bind]
  refine Game.advantage_bind_le _ _ _ fun ω => ?_
  exact EvenMansour.advantage_singleKeyEvenMansourRealGame_evenMansourIdealGame_le
    (hcall.fixCoins ω)

end ProbOracleSecurity

/-- Specialization of `advantage_evenMansourProbRealGame_evenMansourProbIdealGame_le` to `n`-bit
strings `BitString n`: the distinguishing advantage is at most `2 * Q_e * Q_π / 2 ^ n`. -/
theorem advantage_evenMansourProbRealGame_bitString_le {n Q_e Q_π : ℕ}
    {program : ProbOracleComp (EvenMansour.EvenMansourSpec (BitString n)) Bool}
    (hcall : IsProbCallBounded program Q_e Q_π) :
    (Game.advantage (evenMansourProbRealGame program) (evenMansourProbIdealGame program) : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (2 : ℝ) ^ n := by
  have h := advantage_evenMansourProbRealGame_evenMansourProbIdealGame_le hcall
  simpa only [Fintype.card_pi, Fintype.card_fin, Fintype.card_bool, Finset.prod_const,
    Finset.card_univ, Nat.cast_pow, Nat.cast_ofNat] using h

/-- Specialization of `advantage_singleKeyEvenMansourProbRealGame_evenMansourProbIdealGame_le` to
`n`-bit strings `BitString n`: the distinguishing advantage is at most `2 * Q_e * Q_π / 2 ^ n`. -/
theorem advantage_singleKeyEvenMansourProbRealGame_bitString_le {n Q_e Q_π : ℕ}
    {program : ProbOracleComp (EvenMansour.EvenMansourSpec (BitString n)) Bool}
    (hcall : IsProbCallBounded program Q_e Q_π) :
    (Game.advantage (singleKeyEvenMansourProbRealGame program)
      (evenMansourProbIdealGame program) : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (2 : ℝ) ^ n := by
  have h := advantage_singleKeyEvenMansourProbRealGame_evenMansourProbIdealGame_le hcall
  simpa only [Fintype.card_pi, Fintype.card_fin, Fintype.card_bool, Finset.prod_const,
    Finset.card_univ, Nat.cast_pow, Nat.cast_ofNat] using h

/-- **Asymptotic two-key Even–Mansour security for polynomially query-bounded randomized
distinguishers** ([EvenMansour1997]; [BonehShoup2023], Theorem 4.14): for any family of randomized
distinguishers `program : (n : ℕ) → ProbOracleComp (EvenMansourSpec (BitString n)) Bool` whose
cipher and primitive query budgets `Q_e, Q_π : ℕ → ℕ` are polynomially bounded, the distinguishing
advantage is `Negligible`. -/
theorem negligible_advantage_evenMansourProbRealGame
    {program : (n : ℕ) → ProbOracleComp (EvenMansour.EvenMansourSpec (BitString n)) Bool}
    {Q_e Q_π : ℕ → ℕ} (hQ_e : PolynomiallyBounded Q_e) (hQ_π : PolynomiallyBounded Q_π)
    (hcall : ∀ n, IsProbCallBounded (program n) (Q_e n) (Q_π n)) :
    Negligible fun n =>
      Game.advantage (evenMansourProbRealGame (program n))
        (evenMansourProbIdealGame (program n)) := by
  have hpoly : PolynomiallyBounded fun n => 2 * Q_e n * Q_π n :=
    ((PolynomiallyBounded.const 2).mul hQ_e).mul hQ_π
  have hgeom : Negligible fun n => ((2 : ℝ≥0) ^ n)⁻¹ := by
    simpa only [inv_pow] using negligible_geometric (ratio := (2 : ℝ≥0)⁻¹) (by norm_num)
  refine negligible_of_le (hgeom.polynomiallyBounded_mul hpoly) fun n => ?_
  rw [← NNReal.coe_le_coe]
  have h := advantage_evenMansourProbRealGame_bitString_le (hcall n)
  simpa only [div_eq_mul_inv, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_inv, NNReal.coe_pow,
    NNReal.coe_ofNat, Nat.cast_mul, Nat.cast_ofNat, mul_comm, mul_left_comm, mul_assoc] using h

/-- **Asymptotic single-key Even–Mansour security for polynomially query-bounded randomized
distinguishers** ([DunkelmanKellerShamir2012]; [BonehShoup2023], Section 4.7): for any family of
randomized distinguishers `program : (n : ℕ) → ProbOracleComp (EvenMansourSpec (BitString n)) Bool`
whose cipher and primitive query budgets `Q_e, Q_π : ℕ → ℕ` are polynomially bounded, the
distinguishing advantage is `Negligible`. -/
theorem negligible_advantage_singleKeyEvenMansourProbRealGame
    {program : (n : ℕ) → ProbOracleComp (EvenMansour.EvenMansourSpec (BitString n)) Bool}
    {Q_e Q_π : ℕ → ℕ} (hQ_e : PolynomiallyBounded Q_e) (hQ_π : PolynomiallyBounded Q_π)
    (hcall : ∀ n, IsProbCallBounded (program n) (Q_e n) (Q_π n)) :
    Negligible fun n =>
      Game.advantage (singleKeyEvenMansourProbRealGame (program n))
        (evenMansourProbIdealGame (program n)) := by
  have hpoly : PolynomiallyBounded fun n => 2 * Q_e n * Q_π n :=
    ((PolynomiallyBounded.const 2).mul hQ_e).mul hQ_π
  have hgeom : Negligible fun n => ((2 : ℝ≥0) ^ n)⁻¹ := by
    simpa only [inv_pow] using negligible_geometric (ratio := (2 : ℝ≥0)⁻¹) (by norm_num)
  refine negligible_of_le (hgeom.polynomiallyBounded_mul hpoly) fun n => ?_
  rw [← NNReal.coe_le_coe]
  have h := advantage_singleKeyEvenMansourProbRealGame_bitString_le (hcall n)
  simpa only [div_eq_mul_inv, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_inv, NNReal.coe_pow,
    NNReal.coe_ofNat, Nat.cast_mul, Nat.cast_ofNat, mul_comm, mul_left_comm, mul_assoc] using h

/-! ### Word-oracle (`WordOracleComp`) ideal-permutation games and `IsOraclePPT` security -/

/-- A parameterized adaptive word-oracle distinguisher in the Even–Mansour ideal-permutation model:
operation `(false, false)` queries cipher encryption, `(false, true)` queries cipher decryption,
`(true, false)` queries the forward public permutation, and `(true, true)` queries the inverse
public permutation. -/
abbrev EvenMansourDistinguisher := ℕ → List Bool → WordOracleComp (Bool × Bool) Bool

/-- Cost function counting word-oracle cipher queries (`1` when `op.1 = false`, `0` when
`op.1 = true`). -/
@[expose] def wordCipherCost : (Bool × Bool) × List Bool → ℕ
  | ((false, _), _) => 1
  | ((true, _), _) => 0

/-- Cost function counting word-oracle primitive permutation queries (`0` when `op.1 = false`, `1`
when `op.1 = true`). -/
@[expose] def wordPermCost : (Bool × Bool) × List Bool → ℕ
  | ((false, _), _) => 0
  | ((true, _), _) => 1

/-- Separate cipher and primitive query budgets for a `WordOracleComp (Bool × Bool)` distinguisher.
-/
@[expose] def IsWordCallBounded {α : Type} (program : WordOracleComp (Bool × Bool) α)
    (Q_e Q_π : ℕ) : Prop :=
  OracleComp.IsCostBounded (Sum.elim (fun _ => 0) wordCipherCost) program Q_e ∧
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) wordPermCost) program Q_π

/-- Any word-oracle distinguisher making at most `Q` total queries satisfies
`IsWordCallBounded program Q Q`. -/
theorem IsWordCallBounded.of_isQueryBounded {α : Type}
    {program : WordOracleComp (Bool × Bool) α} {Q : ℕ}
    (hQ : program.IsQueryBounded Q) : IsWordCallBounded program Q Q :=
  ⟨hQ.of_le fun q => by
      rcases q with _ | ⟨⟨b, _⟩, _⟩
      · rfl
      · cases b <;> simp [wordCipherCost],
   hQ.of_le fun q => by
      rcases q with _ | ⟨⟨b, _⟩, _⟩
      · rfl
      · cases b <;> simp [wordPermCost]⟩

/-- Two-permutation word oracle on `n`-bit blocks: `op.1 = false` dispatches to the cipher
permutation `E` (in direction `op.2`) and `op.1 = true` dispatches to the primitive permutation
`π` (in direction `op.2`), rejecting malformed words of length `≠ n` with `[]`. -/
@[expose] def evenMansourTwoPermWordOracle (n : ℕ) (E π : Equiv.Perm (BitString n))
    (request : (Bool × Bool) × List Bool) : List Bool :=
  match request with
  | ((isPerm, inverse), query) =>
    strongRandomPermOracle n (if isPerm then π else E) (inverse, query)

/-- Keyed word-level two-key Even–Mansour oracle on a `2 * n`-bit key `key` and primitive
permutation `π`: cipher queries (`isPerm = false`) apply word-level `evenMansourEncrypt` /
`evenMansourDecrypt` around `strongRandomPermOracle n π`, and primitive queries (`isPerm = true`)
query `strongRandomPermOracle n π` directly. -/
@[expose] def evenMansourKeyedWordOracle (n : ℕ) (π : Equiv.Perm (BitString n)) (key : List Bool)
    (request : (Bool × Bool) × List Bool) : List Bool :=
  match request with
  | ((false, false), query) =>
    if query.length = n then
      evenMansourEncrypt (fun _ block => strongRandomPermOracle n π (false, block)) n key query
    else []
  | ((false, true), query) =>
    if query.length = n then
      evenMansourDecrypt (fun _ block => strongRandomPermOracle n π (true, block)) n key query
    else []
  | ((true, inverse), query) =>
    strongRandomPermOracle n π (inverse, query)

/-- Keyed word-level single-key Even–Mansour oracle on an `n`-bit key `key` and primitive
permutation `π`. -/
@[expose] def singleKeyEvenMansourKeyedWordOracle (n : ℕ) (π : Equiv.Perm (BitString n))
    (key : List Bool) (request : (Bool × Bool) × List Bool) : List Bool :=
  match request with
  | ((false, false), query) =>
    if query.length = n then
      singleKeyEvenMansourEncrypt
        (fun _ block => strongRandomPermOracle n π (false, block)) n key query
    else []
  | ((false, true), query) =>
    if query.length = n then
      singleKeyEvenMansourDecrypt
        (fun _ block => strongRandomPermOracle n π (true, block)) n key query
    else []
  | ((true, inverse), query) =>
    strongRandomPermOracle n π (inverse, query)

/-- For any `2 * n`-bit key `key`, `evenMansourKeyedWordOracle` agrees on all requests with
`evenMansourTwoPermWordOracle` for `EvenMansour.evenMansourEquiv π k₁ k₂`. -/
theorem evenMansourKeyedWordOracle_eq_twoPermWordOracle {n : ℕ} (π : Equiv.Perm (BitString n))
    {key : List Bool} (hkey : key.length = 2 * n) (request : (Bool × Bool) × List Bool) :
    evenMansourKeyedWordOracle n π key request =
      evenMansourTwoPermWordOracle n
        (EvenMansour.evenMansourEquiv π
          (BitString.ofList n (splitTwoKeys n key).1)
          (BitString.ofList n (splitTwoKeys n key).2))
        π request := by
  rcases request with ⟨⟨isPerm, inverse⟩, query⟩
  have hk₁ : (splitTwoKeys n key).1.length = n := length_splitTwoKeys_fst hkey
  have hk₂ : (splitTwoKeys n key).2.length = n := length_splitTwoKeys_snd hkey
  have hrep_fwd : ∀ u : BitString n,
      strongRandomPermOracle n π (false, List.ofFn u) = List.ofFn (π u) := by
    intro u
    simp [strongRandomPermOracle]
  have hrep_inv : ∀ v : BitString n,
      strongRandomPermOracle n π (true, List.ofFn v) = List.ofFn (π.symm v) := by
    intro v
    simp [strongRandomPermOracle]
  cases isPerm
  · cases inverse
    · simp only [evenMansourKeyedWordOracle, evenMansourTwoPermWordOracle, strongRandomPermOracle,
        Bool.false_eq_true, ↓reduceIte]
      split_ifs with hq
      · dsimp only [evenMansourEncrypt]
        conv_lhs =>
          rw [← BitString.ofFn_ofList hk₁, ← BitString.ofFn_ofList hk₂,
            ← BitString.ofFn_ofList hq]
        exact evenMansourEncryptWord_ofFn hrep_fwd _ _ _
      · rfl
    · simp only [evenMansourKeyedWordOracle, evenMansourTwoPermWordOracle, strongRandomPermOracle,
        Bool.false_eq_true, ↓reduceIte]
      split_ifs with hq
      · dsimp only [evenMansourDecrypt]
        conv_lhs =>
          rw [← BitString.ofFn_ofList hk₁, ← BitString.ofFn_ofList hk₂,
            ← BitString.ofFn_ofList hq]
        exact evenMansourDecryptWord_ofFn hrep_inv _ _ _
      · rfl
  · rfl

/-- For any `n`-bit key `key`, `singleKeyEvenMansourKeyedWordOracle` agrees on all requests with
`evenMansourTwoPermWordOracle` for `EvenMansour.singleKeyEvenMansourEquiv π k`. -/
theorem singleKeyEvenMansourKeyedWordOracle_eq_twoPermWordOracle {n : ℕ}
    (π : Equiv.Perm (BitString n)) {key : List Bool} (hkey : key.length = n)
    (request : (Bool × Bool) × List Bool) :
    singleKeyEvenMansourKeyedWordOracle n π key request =
      evenMansourTwoPermWordOracle n
        (EvenMansour.singleKeyEvenMansourEquiv π (BitString.ofList n key))
        π request := by
  rcases request with ⟨⟨isPerm, inverse⟩, query⟩
  have hrep_fwd : ∀ u : BitString n,
      strongRandomPermOracle n π (false, List.ofFn u) = List.ofFn (π u) := by
    intro u
    simp [strongRandomPermOracle]
  have hrep_inv : ∀ v : BitString n,
      strongRandomPermOracle n π (true, List.ofFn v) = List.ofFn (π.symm v) := by
    intro v
    simp [strongRandomPermOracle]
  cases isPerm
  · cases inverse
    · simp only [singleKeyEvenMansourKeyedWordOracle, evenMansourTwoPermWordOracle,
        strongRandomPermOracle, Bool.false_eq_true, ↓reduceIte]
      split_ifs with hq
      · dsimp only [singleKeyEvenMansourEncrypt, singleKeyEvenMansourEncryptWord]
        conv_lhs =>
          rw [← BitString.ofFn_ofList hkey, ← BitString.ofFn_ofList hq]
        exact evenMansourEncryptWord_ofFn hrep_fwd _ _ _
      · rfl
    · simp only [singleKeyEvenMansourKeyedWordOracle, evenMansourTwoPermWordOracle,
        strongRandomPermOracle, Bool.false_eq_true, ↓reduceIte]
      split_ifs with hq
      · dsimp only [singleKeyEvenMansourDecrypt, singleKeyEvenMansourDecryptWord]
        conv_lhs =>
          rw [← BitString.ofFn_ofList hkey, ← BitString.ofFn_ofList hq]
        exact evenMansourDecryptWord_ofFn hrep_inv _ _ _
      · rfl
  · rfl

/-- The real word-oracle two-key Even–Mansour experiment: sample a uniform permutation `π` of
`BitString n` and a uniform `2 * n`-bit key `key`, and run `adversary n []` against
`evenMansourKeyedWordOracle n π key`. -/
@[expose] noncomputable def evenMansourWordRealGame (adversary : EvenMansourDistinguisher)
    (n : ℕ) : ProbComp Bool := do
  let π ← ProbComp.uniform (Equiv.Perm (BitString n))
  let key ← BitString.sampleList (2 * n)
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifFin
      (fun request => pure (evenMansourKeyedWordOracle n π key request)))
    (adversary n [])

/-- The real word-oracle single-key Even–Mansour experiment: sample a uniform permutation `π` of
`BitString n` and a uniform `n`-bit key `key`, and run `adversary n []` against
`singleKeyEvenMansourKeyedWordOracle n π key`. -/
@[expose] noncomputable def singleKeyEvenMansourWordRealGame
    (adversary : EvenMansourDistinguisher) (n : ℕ) : ProbComp Bool := do
  let π ← ProbComp.uniform (Equiv.Perm (BitString n))
  let key ← BitString.sampleList n
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifFin
      (fun request => pure (singleKeyEvenMansourKeyedWordOracle n π key request)))
    (adversary n [])

/-- The ideal word-oracle Even–Mansour experiment: sample two independent uniform permutations
`E, π` of `BitString n` and run `adversary n []` against `evenMansourTwoPermWordOracle n E π`. -/
@[expose] noncomputable def evenMansourWordIdealGame (adversary : EvenMansourDistinguisher)
    (n : ℕ) : ProbComp Bool := do
  let E ← ProbComp.uniform (Equiv.Perm (BitString n))
  let π ← ProbComp.uniform (Equiv.Perm (BitString n))
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifFin
      (fun request => pure (evenMansourTwoPermWordOracle n E π request)))
    (adversary n [])

/-- Translate a single word-oracle request into a typed `EvenMansourSpec (BitString n)` query,
returning `[]` on malformed words of length `≠ n` without querying. -/
@[expose] def evenMansourWordQuery (n : ℕ) (request : (Bool × Bool) × List Bool) :
    ProbOracleComp (EvenMansour.EvenMansourSpec (BitString n)) (List Bool) :=
  match request with
  | ((isPerm, inverse), query) =>
    if query.length = n then
      let x := BitString.ofList n query
      let pq : RandomPermutation.PermQuery (BitString n) :=
        if inverse then .inverse x else .forward x
      if isPerm then
        List.ofFn <$> ProbOracleComp.query
          (spec := EvenMansour.EvenMansourSpec (BitString n)) (Sum.inr pq)
      else
        List.ofFn <$> ProbOracleComp.query
          (spec := EvenMansour.EvenMansourSpec (BitString n)) (Sum.inl pq)
    else pure []

/-- Adapt a `WordOracleComp (Bool × Bool)` program into a typed
`ProbOracleComp (EvenMansourSpec (BitString n))` program. -/
@[expose] def evenMansourWordAdapter {α : Type} (n : ℕ)
    (program : WordOracleComp (Bool × Bool) α) :
    ProbOracleComp (EvenMansour.EvenMansourSpec (BitString n)) α :=
  OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (evenMansourWordQuery n))
    program

/-- `evenMansourWordAdapter` preserves separate cipher and primitive query budgets `(Q_e, Q_π)`. -/
theorem IsWordCallBounded.evenMansourWordAdapter {α : Type} (n : ℕ)
    {program : WordOracleComp (Bool × Bool) α} {Q_e Q_π : ℕ}
    (h : IsWordCallBounded program Q_e Q_π) :
    IsProbCallBounded (evenMansourWordAdapter n program) Q_e Q_π := by
  constructor
  · refine h.1.interpret fun q => ?_
    rcases q with k | ⟨⟨isPerm, inverse⟩, query⟩
    · exact ProbOracleComp.isCostBounded_sample EvenMansour.cipherCost (ProbComp.unifFin k)
    · dsimp only [OracleComp.sumHandler, evenMansourWordQuery]
      by_cases hq : query.length = n
      · simp only [hq, ↓reduceIte]
        cases isPerm <;>
          simpa only [map_eq_bind_pure_comp, Function.comp_def, Nat.add_zero, Sum.elim_inr,
            wordCipherCost, EvenMansour.cipherCost, ↓reduceIte, Bool.false_eq_true] using
            (ProbOracleComp.isCostBounded_query EvenMansour.cipherCost _).bind fun _ =>
              OracleComp.IsCostBounded.pure _ 0
      · simp only [hq, ↓reduceIte]
        exact OracleComp.IsCostBounded.pure [] _
  · refine h.2.interpret fun q => ?_
    rcases q with k | ⟨⟨isPerm, inverse⟩, query⟩
    · exact ProbOracleComp.isCostBounded_sample EvenMansour.permCost (ProbComp.unifFin k)
    · dsimp only [OracleComp.sumHandler, evenMansourWordQuery]
      by_cases hq : query.length = n
      · simp only [hq, ↓reduceIte]
        cases isPerm <;>
          simpa only [map_eq_bind_pure_comp, Function.comp_def, Nat.add_zero, Sum.elim_inr,
            wordPermCost, EvenMansour.permCost, ↓reduceIte, Bool.false_eq_true] using
            (ProbOracleComp.isCostBounded_query EvenMansour.permCost _).bind fun _ =>
              OracleComp.IsCostBounded.pure _ 0
      · simp only [hq, ↓reduceIte]
        exact OracleComp.IsCostBounded.pure [] _

private theorem evalProbTwoPerms_evenMansourWordAdapter {α : Type} (n : ℕ)
    (E π : Equiv.Perm (BitString n)) (program : WordOracleComp (Bool × Bool) α) :
    evalProbTwoPerms E π (evenMansourWordAdapter n program) =
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle
          (fun request => PMF.pure (evenMansourTwoPermWordOracle n E π request)))
        program := by
  simp only [evalProbTwoPerms, evenMansourWordAdapter, OracleComp.interpret_interpret,
    OracleComp.interpret_sumHandler, ProbOracleComp.interpret_sample, ProbComp.unifFin,
    OracleComp.interpret_query]
  congr 1
  refine congrArg (OracleComp.sumHandler ProbComp.unifOracle) ?_
  funext ⟨⟨isPerm, inverse⟩, query⟩
  by_cases hq : query.length = n
  · simp only [evenMansourWordQuery, evenMansourTwoPermWordOracle, strongRandomPermOracle,
      hq, ↓reduceIte]
    cases isPerm <;> cases inverse <;>
      simp [ProbOracleComp.interpret_query, evalTwoPermsQuery, RandomPermutation.evalPerm,
        PMF.monad_map_eq_map]
  · simp [evenMansourWordQuery, evenMansourTwoPermWordOracle, strongRandomPermOracle, hq,
      Probability.PMF.monad_pure_eq_pure]

private def twoKeyEquiv (n : ℕ) : BitString (2 * n) ≃ BitString n × BitString n where
  toFun z :=
    (BitString.ofList n (splitTwoKeys n (List.ofFn z)).1,
     BitString.ofList n (splitTwoKeys n (List.ofFn z)).2)
  invFun p := BitString.ofList (2 * n) (List.ofFn p.1 ++ List.ofFn p.2)
  left_inv z := by
    have hz : (List.ofFn z).length = 2 * n := List.length_ofFn
    have h1 : (splitTwoKeys n (List.ofFn z)).1 = (List.ofFn z).take n :=
      splitTwoKeys_fst_eq_take n (List.ofFn z)
    have h2 : (splitTwoKeys n (List.ofFn z)).2 = (List.ofFn z).drop n := by
      simp only [splitTwoKeys, keyBlock, one_mul]
      exact List.take_of_length_le (by simp only [List.length_drop, hz]; omega)
    dsimp only
    rw [BitString.ofFn_ofList (length_splitTwoKeys_fst hz),
      BitString.ofFn_ofList (length_splitTwoKeys_snd hz), h1, h2, List.take_append_drop,
      BitString.ofList_ofFn]
  right_inv p := by
    obtain ⟨k₁, k₂⟩ := p
    have hlen : (List.ofFn k₁ ++ List.ofFn k₂).length = 2 * n := by
      simp only [List.length_append, List.length_ofFn]
      omega
    dsimp only
    rw [BitString.ofFn_ofList hlen]
    have h1 : (splitTwoKeys n (List.ofFn k₁ ++ List.ofFn k₂)).1 = List.ofFn k₁ := by
      simp [splitTwoKeys, keyBlock, List.take_left' List.length_ofFn]
    have h2 : (splitTwoKeys n (List.ofFn k₁ ++ List.ofFn k₂)).2 = List.ofFn k₂ := by
      simp [splitTwoKeys, keyBlock, List.drop_left' List.length_ofFn]
    rw [h1, h2, BitString.ofList_ofFn, BitString.ofList_ofFn]

/-- Evaluating `evenMansourWordRealGame` produces the exact same distribution as running
`evenMansourProbRealGame` on `evenMansourWordAdapter`. -/
theorem eval_evenMansourWordRealGame (adversary : EvenMansourDistinguisher) (n : ℕ) :
    ProbComp.eval (evenMansourWordRealGame adversary n) =
      evenMansourProbRealGame (evenMansourWordAdapter n (adversary n [])) := by
  simp only [evenMansourWordRealGame, evenMansourProbRealGame, ProbComp.eval_bind,
    ProbComp.eval_uniform, BitString.eval_sampleList, ProbOracleComp.eval_interpret,
    ProbComp.eval_pure, Probability.PMF.monad_bind_eq_bind]
  congr 1 with π : 1
  rw [← PMF.uniformOfFintype_map_equiv (twoKeyEquiv n), PMF.bind_map, BitString.uniformList,
    PMF.bind_map]
  congr 1 with z : 1
  simp only [Function.comp_apply, twoKeyEquiv, Equiv.coe_fn_mk,
    evalProbTwoPerms_evenMansourWordAdapter]
  congr 2 with request : 1
  rw [evenMansourKeyedWordOracle_eq_twoPermWordOracle π List.length_ofFn request]

/-- Evaluating `singleKeyEvenMansourWordRealGame` produces the exact same distribution as running
`singleKeyEvenMansourProbRealGame` on `evenMansourWordAdapter`. -/
theorem eval_singleKeyEvenMansourWordRealGame (adversary : EvenMansourDistinguisher) (n : ℕ) :
    ProbComp.eval (singleKeyEvenMansourWordRealGame adversary n) =
      singleKeyEvenMansourProbRealGame (evenMansourWordAdapter n (adversary n [])) := by
  simp only [singleKeyEvenMansourWordRealGame, singleKeyEvenMansourProbRealGame, ProbComp.eval_bind,
    ProbComp.eval_uniform, BitString.eval_sampleList, ProbOracleComp.eval_interpret,
    ProbComp.eval_pure, Probability.PMF.monad_bind_eq_bind]
  congr 1 with π : 1
  rw [BitString.uniformList, PMF.bind_map]
  congr 1 with k : 1
  simp only [Function.comp_apply, evalProbTwoPerms_evenMansourWordAdapter]
  congr 2 with request : 1
  rw [singleKeyEvenMansourKeyedWordOracle_eq_twoPermWordOracle π List.length_ofFn request,
    BitString.ofList_ofFn]

/-- Evaluating `evenMansourWordIdealGame` produces the exact same distribution as running
`evenMansourProbIdealGame` on `evenMansourWordAdapter`. -/
theorem eval_evenMansourWordIdealGame (adversary : EvenMansourDistinguisher) (n : ℕ) :
    ProbComp.eval (evenMansourWordIdealGame adversary n) =
      evenMansourProbIdealGame (evenMansourWordAdapter n (adversary n [])) := by
  simp only [evenMansourWordIdealGame, evenMansourProbIdealGame, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbOracleComp.eval_interpret, ProbComp.eval_pure,
    Probability.PMF.monad_bind_eq_bind, evalProbTwoPerms_evenMansourWordAdapter]

/-- **Word-oracle two-key Even–Mansour security bound** ([EvenMansour1997];
[BonehShoup2023], Theorem 4.14): any word-oracle distinguisher making at most `Q_e` cipher queries
and at most `Q_π` primitive permutation queries at security parameter `n` has distinguishing
advantage at most `2 * Q_e * Q_π / 2 ^ n`. -/
theorem advantage_evenMansourWordRealGame_evenMansourWordIdealGame_le
    (adversary : EvenMansourDistinguisher) (n Q_e Q_π : ℕ)
    (hcall : IsWordCallBounded (adversary n []) Q_e Q_π) :
    (Game.advantage (ProbComp.eval (evenMansourWordRealGame adversary n))
      (ProbComp.eval (evenMansourWordIdealGame adversary n)) : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (2 : ℝ) ^ n := by
  rw [eval_evenMansourWordRealGame, eval_evenMansourWordIdealGame]
  exact advantage_evenMansourProbRealGame_bitString_le (hcall.evenMansourWordAdapter n)

/-- **Word-oracle single-key Even–Mansour security bound** ([DunkelmanKellerShamir2012];
[BonehShoup2023], Section 4.7): any word-oracle distinguisher making at most `Q_e` cipher queries
and at most `Q_π` primitive permutation queries at security parameter `n` has distinguishing
advantage at most `2 * Q_e * Q_π / 2 ^ n`. -/
theorem advantage_singleKeyEvenMansourWordRealGame_evenMansourWordIdealGame_le
    (adversary : EvenMansourDistinguisher) (n Q_e Q_π : ℕ)
    (hcall : IsWordCallBounded (adversary n []) Q_e Q_π) :
    (Game.advantage (ProbComp.eval (singleKeyEvenMansourWordRealGame adversary n))
      (ProbComp.eval (evenMansourWordIdealGame adversary n)) : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (2 : ℝ) ^ n := by
  rw [eval_singleKeyEvenMansourWordRealGame, eval_evenMansourWordIdealGame]
  exact advantage_singleKeyEvenMansourProbRealGame_bitString_le (hcall.evenMansourWordAdapter n)

/-- **Asymptotic word-oracle two-key Even–Mansour security** for any distinguisher with
polynomially bounded cipher and primitive query schedules `Q_e, Q_π : ℕ → ℕ`. -/
theorem negligible_advantage_evenMansourWordRealGame (adversary : EvenMansourDistinguisher)
    {Q_e Q_π : ℕ → ℕ} (hQ_e : PolynomiallyBounded Q_e) (hQ_π : PolynomiallyBounded Q_π)
    (hcall : ∀ n, IsWordCallBounded (adversary n []) (Q_e n) (Q_π n)) :
    Negligible fun n =>
      Game.advantage (ProbComp.eval (evenMansourWordRealGame adversary n))
        (ProbComp.eval (evenMansourWordIdealGame adversary n)) := by
  simpa only [eval_evenMansourWordRealGame, eval_evenMansourWordIdealGame] using
    negligible_advantage_evenMansourProbRealGame hQ_e hQ_π
      (fun n => (hcall n).evenMansourWordAdapter n)

/-- **Asymptotic word-oracle single-key Even–Mansour security** for any distinguisher with
polynomially bounded cipher and primitive query schedules `Q_e, Q_π : ℕ → ℕ`. -/
theorem negligible_advantage_singleKeyEvenMansourWordRealGame
    (adversary : EvenMansourDistinguisher)
    {Q_e Q_π : ℕ → ℕ} (hQ_e : PolynomiallyBounded Q_e) (hQ_π : PolynomiallyBounded Q_π)
    (hcall : ∀ n, IsWordCallBounded (adversary n []) (Q_e n) (Q_π n)) :
    Negligible fun n =>
      Game.advantage (ProbComp.eval (singleKeyEvenMansourWordRealGame adversary n))
        (ProbComp.eval (evenMansourWordIdealGame adversary n)) := by
  simpa only [eval_singleKeyEvenMansourWordRealGame, eval_evenMansourWordIdealGame] using
    negligible_advantage_singleKeyEvenMansourProbRealGame hQ_e hQ_π
      (fun n => (hcall n).evenMansourWordAdapter n)

/-- **Computational two-key Even–Mansour ideal-permutation security against `IsOraclePPT`
distinguishers** ([EvenMansour1997]; [BonehShoup2023], Theorem 4.14; [KatzLindell2020]): no
uniform `IsOraclePPT encBool` distinguisher can distinguish `evenMansourWordRealGame` from
`evenMansourWordIdealGame` with non-negligible advantage. -/
theorem indistinguishable_evenMansourWordRealGame_evenMansourWordIdealGame :
    Game.Indistinguishable
      (fun adversary n => ProbComp.eval (evenMansourWordRealGame adversary n))
      (fun adversary n => ProbComp.eval (evenMansourWordIdealGame adversary n))
      (IsOraclePPT encBool) := by
  intro adversary hadversary
  obtain ⟨c, d, hbounds⟩ := hadversary.query_bounds
  let Q : ℕ → ℕ := fun n => c * (n + 2) ^ d
  have hQ : PolynomiallyBounded Q := by dsimp only [Q]; fun_prop
  exact negligible_advantage_evenMansourWordRealGame adversary hQ hQ fun n =>
    IsWordCallBounded.of_isQueryBounded
      (by simpa only [List.length_nil, Nat.add_zero, Q] using (hbounds n []).1)

/-- **Computational single-key Even–Mansour ideal-permutation security against `IsOraclePPT`
distinguishers** ([DunkelmanKellerShamir2012]; [BonehShoup2023], Section 4.7): no uniform
`IsOraclePPT encBool` distinguisher can distinguish `singleKeyEvenMansourWordRealGame` from
`evenMansourWordIdealGame` with non-negligible advantage. -/
theorem indistinguishable_singleKeyEvenMansourWordRealGame_evenMansourWordIdealGame :
    Game.Indistinguishable
      (fun adversary n => ProbComp.eval (singleKeyEvenMansourWordRealGame adversary n))
      (fun adversary n => ProbComp.eval (evenMansourWordIdealGame adversary n))
      (IsOraclePPT encBool) := by
  intro adversary hadversary
  obtain ⟨c, d, hbounds⟩ := hadversary.query_bounds
  let Q : ℕ → ℕ := fun n => c * (n + 2) ^ d
  have hQ : PolynomiallyBounded Q := by dsimp only [Q]; fun_prop
  exact negligible_advantage_singleKeyEvenMansourWordRealGame adversary hQ hQ fun n =>
    IsWordCallBounded.of_isQueryBounded
      (by simpa only [List.length_nil, Nat.add_zero, Q] using (hbounds n []).1)

end Cslib.Crypto
