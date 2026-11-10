/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.RealIdealAE
public import CslibFrontier.Crypto.Computational.PseudorandomPermutation
public import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Probabilistic.Oracle.Tidy
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.BitString
import CslibFrontier.Tactic.PolyTime

/-!
# Half-Block Encryption from a Block Cipher

This module formalizes the scheme of [Katz and Lindell, Exercise 5.8][KatzLindell2020], which
encrypts `m` under a block cipher `F` as `F_k(r ‖ m)` for a fresh nonce `r`, and proves
[Katz and Lindell, Exercise 5.9][KatzLindell2020]: the scheme is not authenticated encryption.
Every block of the right length decrypts, so an adversary that makes no queries and outputs a fixed
block wins the ciphertext-integrity game with probability `1`.

## Main definitions

* `Cslib.Crypto.BlockCipher.halfBlockCipher`: the half-block scheme built from a block cipher
  whose blocks have length `2 n`.
* `Cslib.Crypto.BlockCipher.allOnesForger`: the forger that outputs the all-ones block.

## Main results

* `Cslib.Crypto.BlockCipher.eval_ciGame_halfBlockCipher_allOnesForger`: the forger always wins.
* `Cslib.Crypto.BlockCipher.not_ciphertextIntegrity_halfBlockCipher`,
  `Cslib.Crypto.BlockCipher.not_authenticatedEncryption_halfBlockCipher`,
  `Cslib.Crypto.BlockCipher.not_realIdealAE_halfBlockCipher`: the scheme has none of these
  properties, whatever the block cipher.

## Implementation notes

* Katz and Lindell use `n`-bit blocks with an `n/2`-bit nonce and `n/2`-bit messages. A
  `SymmetricCipher` encrypts `n`-bit messages, so here the nonce and the message have `n` bits each
  and the blocks have `2 n` bits.
* The forger makes no queries, so it also breaks Katz and Lindell's unforgeability.
* The negative results hold for every block cipher. The CCA security of the scheme for a strong
  pseudorandom permutation, also asked in Exercise 5.8, is not formalized here.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, Exercises 5.8 and 5.9
  (p. 165)][KatzLindell2020]
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace BlockCipher

/-! ### The scheme -/

/-- The half-block encryption scheme of [Katz and Lindell, Exercise 5.8][KatzLindell2020], built
from a block cipher `F` whose blocks have length `2 n` at security parameter `n`.
* Key generation samples a uniform key of length `F.keyLen n`.
* Encryption of an `n`-bit message `msg` samples a uniform `n`-bit nonce `r` and returns the block
  `F.encrypt n k (r ++ msg)`.
* Decryption of a word `ct` of length `F.blockLen n` applies `F.decrypt n k` and drops the first
  `n` bits; words of any other length are rejected. -/
@[expose]
noncomputable def halfBlockCipher (F : BlockCipher) (hblock : ∀ n, F.blockLen n = 2 * n) :
    SymmetricCipher where
  keyGen n := BitString.sampleList (F.keyLen n)
  encrypt n k msg := do
    let r ← BitString.sampleList n
    return F.encrypt n k (r ++ msg)
  decrypt n k ct :=
    if ct.length == F.blockLen n then some ((F.decrypt n k ct).drop n) else none
  keyGen_ppt := by exact ComputableInPolyTime.sampleList F.keyLen_polyTime
  encrypt_ppt := by
    let I := encPair encUnary (encPair encBits encBits)
    have hn := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
    have hrest := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
    have hfirst := ComputableInPolyTime.fst I encBits
    have hk := ((ComputableInPolyTime.fst encBits encBits).comp hrest).comp hfirst
    have hmsg := ((ComputableInPolyTime.snd encBits encBits).comp hrest).comp hfirst
    have hplain := ComputableInPolyTime.bitsAppend (ComputableInPolyTime.snd I encBits) hmsg
    have hf := F.encrypt_polyTime.comp ((hn.comp hfirst).prod (hk.prod hplain))
    simpa only [bind_pure_comp, Function.comp_def] using IsPPTOn.of_seeded hn hf
  decrypt_polyTime := by
    have hn := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
    have hrest := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
    have hk := (ComputableInPolyTime.fst encBits encBits).comp hrest
    have hct := (ComputableInPolyTime.snd encBits encBits).comp hrest
    have hcond := ComputableInPolyTime.beq (encB := encUnary)
      (ComputableInPolyTime.length_bits.comp hct) (F.blockLen_polyTime.comp hn)
    have hplain := ComputableInPolyTime.bitsDropWithInput
      (F.decrypt_polyTime.comp (hn.prod (hk.prod hct))) hn
    exact ComputableInPolyTime.ite hcond ((ComputableInPolyTime.optionSome encBits).comp hplain)
      (ComputableInPolyTime.const none)
  decrypt_encrypt := by
    intro n k hk msg hmsg ct hct
    simp only [BitString.eval_sampleList, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hk hct
    obtain ⟨r, hr, rfl⟩ := hct
    have hkLen := BitString.length_of_mem_support_uniformList hk
    have hrLen := BitString.length_of_mem_support_uniformList hr
    have hlen : (r ++ msg).length = F.blockLen n := by
      rw [List.length_append, hrLen, hmsg, hblock, Nat.two_mul]
    simp [F.length_encrypt n k _ hkLen hlen, F.decrypt_encrypt n k _ hkLen hlen,
      List.drop_left' hrLen]

/-! ### The scheme is not authenticated encryption -/

/-- The forger that makes no queries and outputs the all-ones word of length `F.blockLen n`. -/
@[expose]
def allOnesForger (F : BlockCipher) : CIAdversary :=
  fun n _ => pure (List.replicate (F.blockLen n) true)

/-- The all-ones forger is a polynomial-time CI adversary. -/
theorem isOraclePPT_allOnesForger (F : BlockCipher) : IsOraclePPT encBits F.allOnesForger := by
  have hlen := ComputableInPolyTime.encoding_comp
    (F.blockLen_polyTime.comp (ComputableInPolyTime.fst encUnary encBits))
  have htidy := IsTidyOraclePPTOn.of_computableInPolyTime (Operation := Unit) hlen
  exact htidy.isOraclePPTOn.isOraclePPT

/-- Every word of length `F.blockLen n` decrypts and the forger makes no queries, so it wins
`ciGame` against the half-block scheme with probability `1`. -/
theorem eval_ciGame_halfBlockCipher_allOnesForger (F : BlockCipher)
    (hblock : ∀ n, F.blockLen n = 2 * n) (n : ℕ) :
    ProbComp.eval ((F.halfBlockCipher hblock).ciGame F.allOnesForger n) = PMF.pure true := by
  have hmap (p : PMF (List Bool)) : p.map (fun _ => true) = PMF.pure true := PMF.map_const p true
  simp [SymmetricCipher.ciGame, allOnesForger, halfBlockCipher, hmap]

/-- The half-block scheme does not have ciphertext integrity, whatever the block cipher. -/
theorem not_ciphertextIntegrity_halfBlockCipher (F : BlockCipher)
    (hblock : ∀ n, F.blockLen n = 2 * n) : ¬ (F.halfBlockCipher hblock).CiphertextIntegrity := by
  intro hci
  have hneg := hci.negligible F.allOnesForger F.isOraclePPT_allOnesForger
  simp only [eval_ciGame_halfBlockCipher_allOnesForger, Game.succProbability,
    PMF.pure_apply_self, ENNReal.toNNReal_one] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- **Katz and Lindell, Exercise 5.9.** The half-block scheme is not an authenticated encryption
scheme, whatever the block cipher. -/
theorem not_authenticatedEncryption_halfBlockCipher (F : BlockCipher)
    (hblock : ∀ n, F.blockLen n = 2 * n) :
    ¬ (F.halfBlockCipher hblock).AuthenticatedEncryption :=
  fun h => F.not_ciphertextIntegrity_halfBlockCipher hblock h.2

/-- The half-block scheme is not authenticated encryption in the real/ideal sense of
[Katz and Lindell, Definition 5.4][KatzLindell2020] either. -/
theorem not_realIdealAE_halfBlockCipher (F : BlockCipher)
    (hblock : ∀ n, F.blockLen n = 2 * n) : ¬ (F.halfBlockCipher hblock).RealIdealAE :=
  fun h => F.not_ciphertextIntegrity_halfBlockCipher hblock h.ciphertextIntegrity

end BlockCipher

end Cslib.Crypto
