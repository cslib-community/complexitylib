/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.PublicKeyReplacement
public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.LWE
public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Serialized.PolyTime
public import CslibFrontier.Crypto.Computational.LWE.Regev
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Tactic.PPT

/-!
# Generated-key Regev security from decision LWE

The serialized Regev encryption program reads a public word with the fixed-width row-major
encoding of `Matrix.toBinary`, samples `m` fair coins and writes the `n + 1` ciphertext residues
with `w` bits each. Missing bits and coins are zero and excess data is ignored, so the program is
total. Key generation is the existing serialized LWE key generator
`Homomorphic.GSW.keyGenSerialized`, whose public word is exactly a decision-LWE sample.

Both honest programs are strict PPT, and the reduction to decision LWE is one uniform strict PPT
distinguisher with loss two. The remaining statistical term is the single-challenge
leftover-hash bound `sqrt(2 ^ ((n + 1) * w) / 2 ^ m)` of `Regev.challengeGame_uniform_advantage_le`.
This is the single-challenge IND-CPA theorem of [Regev2009, Section 5] and
[Peikert2016, Section 5.2.1] against uniform classical strict PPT adversaries; the adaptive
`Q`-query bound of `Regev.lorGame_advantage_le` is stated for typed adversaries only.

## Main definitions

* `Regev.serializeCiphertext`: canonical ciphertext words.
* `Regev.encryptWithCoinsSerialized`, `Regev.encryptSerialized`: the actual word encryption.
* `Regev.lweDistinguisher`: the uniform hidden-bit reduction.
* `Regev.hidingError`: the explicit statistical term.

## Main results

* `Regev.encryptWithCoinsSerialized_eq`, `Regev.eval_encryptSerialized_toBinary`: exact bridges
  to the typed encryption.
* `Regev.isPPTOn_encryptSerialized`, `Regev.isPPT_lweDistinguisher`: native certificates.
* `Regev.advantage_game_le`: twice the decision-LWE advantage plus the statistical term.
* `Regev.indCPA_of_decisionLWE`: IND-CPA under decision LWE with an eventual entropy margin.

## References

* [O. Regev, *On Lattices, Learning with Errors, Random Linear Codes, and Cryptography*,
  Section 5][Regev2009]
* [C. Peikert, *A Decade of Lattice Cryptography*, Section 5.2.1][Peikert2016]
-/

@[expose] public section

namespace Cslib.Crypto.Regev

open Probability BitString Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open scoped BigOperators NNReal

/-- Canonical ciphertext words: `n + 1` residues, `w` low-order-first bits each. -/
def serializeCiphertext {n w : ℕ} (c : Ciphertext n w) : List Bool :=
  Cslib.Matrix.toBinary (Matrix.of fun _ : Fin 1 => c)

/-- Column `j` of `xᵀ A + (μ * 2 ^ (w - 1), 0, …, 0)`, read from an arbitrary public word and
arbitrary coins, as a canonical residue. -/
def encryptEntry (n m w : ℕ) (publicWord : List Bool) (message : Bool) (coins : List Bool)
    (j : ℕ) : ℕ :=
  (((List.range m).map fun r =>
      if coins.getD r false then Cslib.Matrix.binaryEntry (n + 1) w publicWord r j else 0).sum +
    if j = 0 then message.toNat * 2 ^ (w - 1) else 0) % 2 ^ w

/-- Compute every ciphertext bit from the public word, the message and the coins. -/
def encryptWithCoinsSerialized (n m w : ℕ) (publicWord : List Bool) (message : Bool)
    (coins : List Bool) : List Bool :=
  (List.range (n + 1)).flatMap fun j => lowBits w (encryptEntry n m w publicWord message coins j)

/-- Sample `m` fair coins and run the word encryption. -/
noncomputable def encryptSerialized (n m w : ℕ) (publicWord : List Bool) (message : Bool) :
    ProbComp (List Bool) := do
  let coins ← OracleComp.replicate m (ProbComp.uniform Bool)
  return encryptWithCoinsSerialized n m w publicWord message coins

/-- A computed entry is the canonical residue of the typed ciphertext entry. -/
theorem encryptEntry_eq (n m w : ℕ) (publicWord : List Bool) (message : Bool)
    (coins : List Bool) (j : Fin (n + 1)) :
    encryptEntry n m w publicWord message coins j.val =
      (encryptWithCoins (Cslib.Matrix.ofBinary m (n + 1) w publicWord) message
        (fun r => coins.getD r.val false) j).val := by
  unfold encryptEntry
  rw [List.map_range_eq_ofFn, List.sum_ofFn, ← ZMod.val_natCast]
  congr 1
  rw [Nat.cast_add, Nat.cast_sum, encryptWithCoins, Pi.add_apply]
  congr 1
  · simp only [Matrix.vecMul, dotProduct, coinVector]
    apply Finset.sum_congr rfl
    intro r _
    rw [Cslib.Matrix.ofBinary_apply]
    cases coins.getD r.val false <;> simp
  · by_cases hj : j = 0
    · subst hj
      simp [encodeBit]
    · have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp [hj, hv]

/-- The word encryption is the typed encryption of the decoded public matrix and coins. -/
theorem encryptWithCoinsSerialized_eq (n m w : ℕ) (publicWord : List Bool) (message : Bool)
    (coins : List Bool) :
    encryptWithCoinsSerialized n m w publicWord message coins = serializeCiphertext
      (encryptWithCoins (Cslib.Matrix.ofBinary m (n + 1) w publicWord) message
        (fun r => coins.getD r.val false)) := by
  unfold encryptWithCoinsSerialized serializeCiphertext
  rw [Cslib.Matrix.toBinary_eq]
  simp only [List.flatMap_def, List.map_range_eq_ofFn, lowBits_eq_ofFn, encryptEntry_eq,
    Matrix.of_apply, List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil]

/-- On canonical public words, the word encryption has the typed encryption law. -/
theorem eval_encryptSerialized_toBinary {n m w : ℕ} (A : PublicKey n m w) (message : Bool) :
    ProbComp.eval (encryptSerialized n m w (Cslib.Matrix.toBinary A) message) =
      (ProbComp.eval (encrypt A message)).map serializeCiphertext := by
  rw [eval_encrypt, PMF.map_comp, ← PMF.pi_uniformOfFintype]
  simp only [encryptSerialized, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_replicate,
    ProbComp.eval_uniform, PMF.bind_map, Function.comp_def, encryptWithCoinsSerialized_eq,
    Cslib.Matrix.ofBinary_toBinary]
  congr 1 with x : 1
  simp [List.getD_eq_getElem?_getD]

variable {α : Type} {input : α ↪ List Bool} {n m w j : α → ℕ}

/-- One ciphertext entry is polynomial-time in the dimensions, the public word and the coins. -/
@[fun_prop]
theorem computableInPolyTime_encryptEntry
    {publicWord : α → List Bool} {message : α → Bool} {coins : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hpublicWord : ComputableInPolyTime publicWord input encBits)
    (hmessage : ComputableInPolyTime message input encBool)
    (hcoins : ComputableInPolyTime coins input encBits)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime
      (fun a => encryptEntry (n a) (m a) (w a) (publicWord a) (message a) (coins a) (j a))
      input encNat := by
  unfold encryptEntry
  have hterm : ComputableInPolyTime
      (fun p : α × ℕ => if (coins p.1).getD p.2 false
        then Cslib.Matrix.binaryEntry (n p.1 + 1) (w p.1) (publicWord p.1) p.2 (j p.1) else 0)
      (encPair input encUnary) encNat := by
    apply ((bitsGetD false).comp
      ((hcoins.comp (fst input encUnary)).prod (snd input encUnary))).ite'
    · exact matrixBinaryEntry (by fun_prop) (by fun_prop) (by fun_prop)
        (snd input encUnary) (by fun_prop)
    · exact const 0
  have hsum := (show ComputableInPolyTime List.sum (encList encNat) encNat by fun_prop).comp
    (mapWithInput
      (f := fun a r => if (coins a).getD r false
        then Cslib.Matrix.binaryEntry (n a + 1) (w a) (publicWord a) r (j a) else 0)
      (range.comp hm) hterm)
  have hboolUnary : ComputableInPolyTime Bool.toNat encBool encUnary := of_finite Bool.toNat
  have hhalf : ComputableInPolyTime (fun a => w a - 1) input encUnary := by fun_prop
  have hmessageTerm : ComputableInPolyTime
      (fun a => if j a = 0 then (message a).toNat * 2 ^ (w a - 1) else 0) input encNat := by
    simpa only [Function.comp_apply, beq_iff_eq] using (beq hj (const 0)).ite'
      (binary_mul' (unary_to_binary.comp (hboolUnary.comp hmessage))
        (binary_pow' (const 2) hhalf)) (const 0)
  exact binary_mod.comp
    ((binary_add.comp (hsum.prod hmessageTerm)).prod (binary_pow' (const 2) hw))

/-- The word encryption is polynomial-time on arbitrary public words and coins, charging the
complete ciphertext output. -/
@[fun_prop]
theorem computableInPolyTime_encryptWithCoinsSerialized
    {publicWord : α → List Bool} {message : α → Bool} {coins : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hpublicWord : ComputableInPolyTime publicWord input encBits)
    (hmessage : ComputableInPolyTime message input encBool)
    (hcoins : ComputableInPolyTime coins input encBits) :
    ComputableInPolyTime
      (fun a => encryptWithCoinsSerialized (n a) (m a) (w a) (publicWord a) (message a)
        (coins a)) input encBits := by
  unfold encryptWithCoinsSerialized
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  fun_prop

/-- The complete encryption program is strict PPT on arbitrary public words and messages. -/
@[fun_prop]
theorem isPPTOn_encryptSerialized {publicWord : α → List Bool} {message : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hpublicWord : ComputableInPolyTime publicWord input encBits)
    (hmessage : ComputableInPolyTime message input encBool) :
    IsPPTOn input encBits
      (fun a => encryptSerialized (n a) (m a) (w a) (publicWord a) (message a)) := by
  have hsample := (isPPTOn_uniform_bool input).replicate_bool hm
  unfold encryptSerialized
  ppt

/-- The single-challenge leftover-hash term `sqrt(2 ^ ((n + 1) * w) / 2 ^ m)`. -/
noncomputable def hidingError (n m w : ℕ) : ℝ≥0 :=
  NNReal.sqrt ((2 : ℝ≥0) ^ ((n + 1) * w) / 2 ^ m)

/-- The uniform hidden-bit reduction running the actual word encryption. -/
noncomputable def lweDistinguisher (n m w : ℕ → ℕ) (adversary : Encryption.Adversary) :
    Distinguisher :=
  Encryption.keyDistinguisher
    (fun security => encryptSerialized (n security) (m security) (w security)) adversary

/-- Efficient dimensions make the reduction one uniform strict PPT distinguisher. -/
theorem isPPT_lweDistinguisher {n m w : ℕ → ℕ} {adversary : Encryption.Adversary}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (hadversary : adversary.IsPPT) : IsPPT encBool (lweDistinguisher n m w adversary) := by
  apply Encryption.isPPT_keyDistinguisher ?_ hadversary
  exact isPPTOn_encryptSerialized (hn.comp (by fun_prop)) (hm.comp (by fun_prop))
    (hw.comp (by fun_prop)) (by fun_prop) (by fun_prop)

/-- Under the uniform decision-LWE ensemble, the word experiment is the typed single-challenge
experiment with the adversary's stages composed with the canonical encodings. -/
theorem publicKeyGame_uniformEnsemble (n m w : ℕ → ℕ) (adversary : Encryption.Adversary)
    (bit : Bool) (security : ℕ) :
    Encryption.publicKeyGame (LWE.uniformEnsemble n m w security)
      (fun k => encryptSerialized (n k) (m k) (w k)) adversary bit security =
        challengeGame (PMF.uniformOfFintype (PublicKey (n security) (m security) (w security)))
          (fun A => ProbComp.eval (adversary.choose security (Cslib.Matrix.toBinary A)))
          (fun state c => ProbComp.eval (adversary.guess security state (serializeCiphertext c)))
          bit := by
  simp only [Encryption.publicKeyGame, LWE.uniformEnsemble, challengeGame,
    PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, eval_encryptSerialized_toBinary]

/-- Under the uniform ensemble, the advantage is at most the leftover-hash term. -/
theorem advantage_uniformEnsemble_le (n m w : ℕ → ℕ) (adversary : Encryption.Adversary)
    (security : ℕ) :
    Game.advantage
      (Encryption.publicKeyGame (LWE.uniformEnsemble n m w security)
        (fun k => encryptSerialized (n k) (m k) (w k)) adversary false security)
      (Encryption.publicKeyGame (LWE.uniformEnsemble n m w security)
        (fun k => encryptSerialized (n k) (m k) (w k)) adversary true security) ≤
          hidingError (n security) (m security) (w security) := by
  apply NNReal.coe_le_coe.mp
  rw [publicKeyGame_uniformEnsemble, publicKeyGame_uniformEnsemble]
  simpa only [hidingError, Real.coe_sqrt, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat] using
    challengeGame_uniform_advantage_le _ _

/-- One uniform reduction bounds the actual IND-CPA advantage by twice its decision-LWE
advantage plus the leftover-hash term. No efficiency is needed for this inequality. -/
theorem advantage_game_le (n m w η : ℕ → ℕ) (adversary : Encryption.Adversary) (security : ℕ) :
    Encryption.advantage
      (Encryption.game (fun k => Homomorphic.GSW.keyGenSerialized (n k) (m k) (w k) (η k))
        (fun k => encryptSerialized (n k) (m k) (w k)) adversary) security ≤
      2 * Game.advantage
        (distinguishingGame
          (LWE.realEnsemble n m w (fun k => Homomorphic.GSW.noiseLaw (w k) (η k)) security)
          (lweDistinguisher n m w adversary security))
        (distinguishingGame (LWE.uniformEnsemble n m w security)
          (lweDistinguisher n m w adversary security)) +
        hidingError (n security) (m security) (w security) := by
  simp only [Encryption.advantage, Encryption.eval_game_eq_publicKeyGame,
    Homomorphic.GSW.eval_keyGenSerialized_publicWord]
  exact (Encryption.advantage_publicKeyGame_le _ (LWE.uniformEnsemble n m w security)
    _ adversary security).trans
      (add_le_add le_rfl (advantage_uniformEnsemble_le n m w adversary security))

open Filter in
/-- Regev encryption is IND-CPA secure under decision LWE for its exact centered-binomial error
law, for efficient dimensions with an eventual entropy surplus of twice the security parameter. -/
theorem indCPA_of_decisionLWE {n m w η : ℕ → ℕ}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (hmargin : ∀ᶠ security in atTop, (n security + 1) * w security + 2 * security ≤ m security)
    (hLWE : DecisionLWE n m w (fun k => Homomorphic.GSW.noiseLaw (w k) (η k))) :
    Encryption.INDCPA (fun k => Homomorphic.GSW.keyGenSerialized (n k) (m k) (w k) (η k))
      (fun k => encryptSerialized (n k) (m k) (w k)) := by
  intro adversary hadversary
  have hsource := hLWE (lweDistinguisher n m w adversary)
    (isPPT_lweDistinguisher hn hm hw hadversary)
  have herror := negligible_mul_sqrt_pow_two_div_pow_two
    (count := fun _ => 1) (outputBits := fun k => (n k + 1) * w k) (by fun_prop) hmargin
  apply negligible_of_le
    ((hsource.polynomiallyBounded_mul (p := fun _ => 2) (by fun_prop)).add herror)
  intro security
  refine (advantage_game_le n m w η adversary security).trans (le_of_eq ?_)
  simp [hidingError]

end Cslib.Crypto.Regev
