/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.KPKE
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.PMFSwap

/-!
# A two-stage IND-CPA bound for K-PKE from Module-LWE

The K-PKE public key `(A, A s + e)` is a Module-LWE sample with secret and error drawn from
`CBD_{η₁}`. Once the public key is uniform, the uncompressed ciphertext `(Aᵀ r + e₁, bᵀ r + e₂)`
together with `(A, b)` is a `(k + 1) × k` Module-LWE sample with secret `r ← CBD_{η₁}^k` and errors
`(e₂, e₁) ← CBD_{η₂}^{k + 1}`; replacing it by a uniform sample makes the adversary's view
independent of the challenge bit.

The adversary is a two-stage IND-CPA adversary `A` against `toExplicitCoinPKE P`, in the experiment
of `ExplicitCoinPKE.cpaAdvantage`: its first stage receives the public key and chooses the two
challenge messages and a state, and its second stage receives the state and the challenge. Both hops
are explicit reductions that are uniform in `A`: each runs `A`'s first stage on the public key it
reads from its sample, so the messages are `A`'s own, and encrypts the message that a fixed bit `b`
selects.

* `mlweKeyReduction A b` reads a `k × k` sample `(M, t)` as the public key and encrypts with fresh
  K-PKE coins.
* `mlweReduction A b` reads a `(k + 1) × k` sample `(M, w)` as the public key
  `unextendPublicKeyMatrix M` and the ciphertext
  `compressCiphertext (unextendCiphertext w + (0, messagePoly P m))` for the selected message `m`.

The three game identities are exact (`eval_cpaExperiment_eq_realGame`,
`randomGame_mlweKeyReduction`, `randomGame_mlweReduction`). `cpaAdvantage_le` bounds the
two-stage IND-CPA advantage of `toExplicitCoinPKE P` by four `ModuleLWE.advantage` terms: the two
hops for each value of the challenge bit.

This is the two-hop argument behind Kyber v3.02 ([AvanziEtAl2021], §4.3.1, Theorem 1, p. 20), in
the form of §4.4, eq. (6), p. 22, which uses a `k × k` Module-LWE term with `η₁` for the key and a
`(k + 1) × k` term with secret width `η₁` and error width `η₂` for the ciphertext. It is a concrete
bound for one parameter set in this library's model, which differs from the source as follows.

* The matrix `A` is uniform rather than expanded from a seed by `XOF`, and the coins are sampled
  rather than derived by `PRF`, so no random oracle is involved and there is no `PRF` term.
* The ciphertext hop is decision Module-LWE on the uncompressed sample, with secret width `η₁` and
  error width `η₂`: the Module-LWER problem of eq. (6) without compression (footnote 3,
  pp. 21–22). The reduction adds the message and compresses the ciphertext itself.
* The advantage is the two-world difference `|Pr[A → 1 | b = 0] - Pr[A → 1 | b = 1]|`. The proof
  goes through the bit-independent game `uniformCiphertextGame`, so each hop appears once for each
  bit, with its own reductions.
* No running time is charged. The bound holds for every adversary, efficient or not; it is not an
  asymptotic security theorem.

## Main definitions

* `Cslib.Crypto.MLKEM.mlweKeyReduction`, `Cslib.Crypto.MLKEM.mlweReduction`: the two reductions.
* `Cslib.Crypto.MLKEM.uniformCiphertextGame`: the bit-independent final game.

## Main results

* `Cslib.Crypto.MLKEM.cpaAdvantage_le`: the two-stage IND-CPA advantage of K-PKE is at most the sum
  of four Module-LWE advantages of the explicit reductions.

## References

* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, Section 5][NISTFIPS203]
* [R. Avanzi et al., *CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation
  (version 3.02)*][AvanziEtAl2021], 4 August 2021, §4.3.1 (Theorem 1, p. 20) and §4.4 (eq. (6),
  p. 22)
* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki--Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017], §2.1, Definition 2.2 (two-stage IND-CPA)
-/

@[expose] public section

namespace Cslib.Crypto.MLKEM

open Probability Cslib.Crypto.Protocols
open scoped NNReal

/-! ### The reductions -/

/-- A two-stage IND-CPA adversary against K-PKE: its first stage receives a public key and chooses
two messages and a state of type `σ`, and its second stage receives the state and a ciphertext. -/
abbrev CpaAdversary (P : Params) (σ : Type) : Type :=
  TwoStage (PublicKey P) (MessagePair (Fin P.n → Bool)) (Ciphertext P) Bool σ

variable (P : Params) {σ : Type}

/-- **Public-key hop**: read a `k × k` Module-LWE sample `(M, t)` as the public key, run the first
stage of `A` on it, and encrypt the message that `b` selects with fresh K-PKE coins. -/
noncomputable def mlweKeyReduction (A : CpaAdversary P σ) (b : Bool)
    (M : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (t : Fin P.k → Fin P.n → ZMod P.q) : ProbComp Bool := do
  let (pair, state) ← A.choose (M, t)
  let coins ← sampleCoins P
  A.guess state (encrypt P (M, t) (pair.select b) coins)

/-- **Ciphertext hop**: read a `(k + 1) × k` Module-LWE sample `(M, w)` as the public key
`unextendPublicKeyMatrix M` (row `0` of `M` is `b`, the other rows are `Aᵀ`), run the first stage of
`A` on it, and give the second stage the ciphertext obtained by adding the polynomial of the
message that `b` selects to `v = w 0` and compressing. -/
def mlweReduction (A : CpaAdversary P σ) (b : Bool)
    (M : Matrix (Fin (P.k + 1)) (Fin P.k) (Fin P.n → ZMod P.q))
    (w : Fin (P.k + 1) → Fin P.n → ZMod P.q) : ProbComp Bool := do
  let (pair, state) ← A.choose (unextendPublicKeyMatrix M)
  A.guess state
    (compressCiphertext P (unextendCiphertext w + (0, messagePoly P (pair.select b))))

/-- The final game: the first stage of `A` receives a uniform public key, and the second stage
receives the compression of a uniform ciphertext, independent of the chosen messages. -/
noncomputable def uniformCiphertextGame [NeZero P.q] (A : CpaAdversary P σ) : ProbComp Bool := do
  let pk ← ProbComp.uniform (PublicKey P)
  let (_, state) ← A.choose pk
  let ct ← ProbComp.uniform (ModuleLWECiphertext P.k P.n P.q)
  A.guess state (compressCiphertext P ct)

/-- The `(k + 1) × k` sample built from a public key `pk`, secret `r` and errors `(e₂, e₁)`, read
back by `mlweReduction`, is the uncompressed K-PKE ciphertext. -/
theorem unextendCiphertext_sample_add_messagePoly (pk : PublicKey P)
    (r e₁ : Fin P.k → Fin P.n → ZMod P.q) (e₂ : Fin P.n → ZMod P.q) (m : Fin P.n → Bool) :
    unextendCiphertext (ModuleLWE.sample (extendPublicKeyMatrix pk) r (Fin.cons e₂ e₁)) +
        (0, messagePoly P m) = encryptRaw P pk r e₁ e₂ m := by
  have h := extendCiphertext_moduleLWEEncrypt pk r e₁ e₂ (fun _ => false)
  have hz : (Fin.cons 0 0 : Fin (P.k + 1) → Fin P.n → ZMod P.q) = 0 := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [encodePolyMsg_false, hz, add_zero] at h
  rw [← h, unextendCiphertext_extendCiphertext, encryptRaw_eq_moduleLWEEncrypt_add]

/-! ### Game identities -/

/-- **Real game**: the IND-CPA experiment with challenge bit `b` is the real `k × k` Module-LWE game
for `mlweKeyReduction A b` with `CBD_{η₁}` secret and error. -/
theorem eval_cpaExperiment_eq_realGame [NeZero P.q] (A : CpaAdversary P σ) (b : Bool) :
    ProbComp.eval ((toExplicitCoinPKE P).toPKE.cpaExperiment (fun _ _ _ => true) A b) =
      ModuleLWE.realGame (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
        (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁)) (mlweKeyReduction P A b) := by
  rw [ModuleLWE.realGame_eq_uniform_bind]
  simp only [PKE.cpaExperiment, lrExperiment, ExplicitCoinPKE.toPKE, ExplicitCoinPKE.encrypt,
    toExplicitCoinPKE, keyGen, mlweKeyReduction, moduleLWEKeyGen_eq_sample, ↓reduceIte, bind_assoc,
    pure_bind, ProbComp.eval_bind, ProbComp.eval_uniform]

/-- **Hybrid game**: with a uniform public key, the experiment is the real `(k + 1) × k` Module-LWE
game for `mlweReduction A b` with `CBD_{η₁}` secret and `CBD_{η₂}` errors. -/
theorem randomGame_mlweKeyReduction [NeZero P.q] (A : CpaAdversary P σ) (b : Bool) :
    ModuleLWE.randomGame (mlweKeyReduction P A b) =
      ModuleLWE.realGame (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
        (ProbComp.eval (sampleVecCBD (P.k + 1) P.n P.q P.η₂)) (mlweReduction P A b) := by
  rw [ModuleLWE.randomGame_eq, ModuleLWE.realGame_eq_uniform_bind,
    ← PMF.uniformOfFintype_map_equiv (extendPublicKeyEquiv P.k P.n P.q), PMF.bind_map]
  refine congrArg _ (funext fun pk => ?_)
  simp only [Function.comp_apply, extendPublicKeyEquiv, Equiv.coe_fn_mk, mlweKeyReduction,
    mlweReduction, unextendPublicKeyMatrix_extendPublicKeyMatrix, Prod.mk.eta, sampleCoins,
    sampleVecCBD, OracleComp.replicateFin_succ, pmf_norm]
  pmf_hoist (ProbComp.eval (A.choose pk))
  simp only [unextendCiphertext_sample_add_messagePoly, encrypt]
  pmf_swap

/-- **Final game**: on a uniform `(k + 1) × k` sample, `mlweReduction A b` is the bit-independent
`uniformCiphertextGame A`. -/
theorem randomGame_mlweReduction [NeZero P.q] (A : CpaAdversary P σ) (b : Bool) :
    ModuleLWE.randomGame (mlweReduction P A b) =
      ProbComp.eval (uniformCiphertextGame P A) := by
  rw [ModuleLWE.randomGame, ModuleLWE.eval_randomExperiment,
    ← PMF.uniformOfFintype_map_equiv (extendPublicKeyEquiv P.k P.n P.q), PMF.bind_map]
  simp only [uniformCiphertextGame, mlweReduction, pmf_norm, ProbComp.eval_uniform,
    extendPublicKeyEquiv, Equiv.coe_fn_mk, unextendPublicKeyMatrix_extendPublicKeyMatrix]
  refine congrArg _ (funext fun pk => ?_)
  pmf_hoist (ProbComp.eval (A.choose pk))
  refine congrArg _ (funext fun ps => ?_)
  rw [← PMF.uniformOfFintype_map_equiv ((extendCiphertextEquiv P.k P.n P.q).symm.trans
    (Equiv.addRight ((0, messagePoly P (ps.1.select b)) : ModuleLWECiphertext P.k P.n P.q))),
    PMF.bind_map]
  rfl

/-! ### The IND-CPA bound -/

/-- Distance of the IND-CPA experiment with challenge bit `b` from the final game: the public-key
hop and the ciphertext hop for `b`. -/
theorem advantage_cpaExperiment_uniformCiphertextGame_le [NeZero P.q] (A : CpaAdversary P σ)
    (b : Bool) :
    Game.advantage
        (ProbComp.eval ((toExplicitCoinPKE P).toPKE.cpaExperiment (fun _ _ _ => true) A b))
        (ProbComp.eval (uniformCiphertextGame P A)) ≤
      ModuleLWE.advantage (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
          (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁)) (mlweKeyReduction P A b) +
        ModuleLWE.advantage (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
          (ProbComp.eval (sampleVecCBD (P.k + 1) P.n P.q P.η₂)) (mlweReduction P A b) := by
  rw [eval_cpaExperiment_eq_realGame, ← randomGame_mlweReduction P A b]
  refine le_trans (Game.advantage_triangle _
    (ModuleLWE.randomGame (mlweKeyReduction P A b)) _) ?_
  rw [ModuleLWE.advantage, ModuleLWE.advantage, ← randomGame_mlweKeyReduction]

/-- **Concrete two-stage IND-CPA bound for K-PKE**: for every two-stage adversary `A`, the IND-CPA
advantage of `toExplicitCoinPKE P` (`ExplicitCoinPKE.cpaAdvantage`, messages chosen by `A` after
seeing the public key) is at most the sum, over both values `b` of the challenge bit, of the
Module-LWE advantages of `mlweKeyReduction A b` (`k × k`, `CBD_{η₁}` secret and error) and
`mlweReduction A b` (`(k + 1) × k`, `CBD_{η₁}` secret, `CBD_{η₂}` errors). This is the two-hop
argument behind Kyber v3.02 ([AvanziEtAl2021], §4.3.1, Theorem 1, p. 20), with the hops of §4.4,
eq. (6), p. 22, in the model and with the deviations listed in the module documentation: a uniform
matrix and sampled coins instead of `XOF` and `PRF`, an uncompressed ciphertext hop, and no running
time. It is a concrete lemma for one parameter set, not an asymptotic security theorem. -/
theorem cpaAdvantage_le [NeZero P.q] (A : CpaAdversary P σ) :
    (toExplicitCoinPKE P).cpaAdvantage A ≤
      (ModuleLWE.advantage (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
          (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁)) (mlweKeyReduction P A false) +
        ModuleLWE.advantage (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
          (ProbComp.eval (sampleVecCBD (P.k + 1) P.n P.q P.η₂)) (mlweReduction P A false)) +
      (ModuleLWE.advantage (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
          (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁)) (mlweKeyReduction P A true) +
        ModuleLWE.advantage (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
          (ProbComp.eval (sampleVecCBD (P.k + 1) P.n P.q P.η₂)) (mlweReduction P A true)) := by
  refine le_trans (Game.advantage_triangle _
    (ProbComp.eval (uniformCiphertextGame P A)) _) ?_
  rw [Game.advantage_comm (ProbComp.eval (uniformCiphertextGame P A))]
  exact add_le_add (advantage_cpaExperiment_uniformCiphertextGame_le P A false)
    (advantage_cpaExperiment_uniformCiphertextGame_le P A true)

end Cslib.Crypto.MLKEM
