/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.KPKE
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.Abel

/-!
# IND-CPA security of K-PKE from Module-LWE

The K-PKE public key `(A, A s + e)` is a Module-LWE sample with secret and error drawn from
`CBD_{η₁}`. Once the public key is uniform, the uncompressed ciphertext `(Aᵀ r + e₁, bᵀ r + e₂)`
together with `(A, b)` is a `(k + 1) × k` Module-LWE sample with secret `r ← CBD_{η₁}^k` and errors
`(e₂, e₁) ← CBD_{η₂}^{k + 1}`; replacing it by a uniform sample makes the view independent of the
message. Both hops are explicit reductions:

* `mlweKeyReduction`: embeds a `k × k` sample as the public key and encrypts honestly;
* `mlweReduction`: splits a `(k + 1) × k` sample `(M, w)` into the public key
  `unextendPublicKeyMatrix M` and the ciphertext
  `compressCiphertext (unextendCiphertext w + (0, messagePoly m))`.

The three game identities are exact (`eval_indCpaGame_eq`, `eval_mlweIdealGame_mlweKeyReduction`,
`eval_mlweIdealGame_mlweReduction`), and `indCpaAdvantage_le` bounds the fixed-message IND-CPA
advantage of `toExplicitCoinPKE` by four Module-LWE advantages of the explicit reductions, two for
each message. This is the usual two-hop argument for Kyber-style encryption, stated here as an
original concrete bound in this model: the matrix `A` is uniform rather than expanded from a seed,
so no random oracle is involved.

`ModuleLWE.sampleLaw` and `DecisionModuleLWE` fix a uniform secret, while K-PKE needs Module-LWE
with centered-binomial secrets. `mlweAdvantage` is therefore the concrete Module-LWE advantage for
arbitrary secret and error samplers. (Informally, a uniform secret program recovers the setting of
`ModuleLWE.sampleLaw`; no bridge lemma is proved here.)

## Main definitions

* `Cslib.Crypto.MLKEM.mlweRealGame`, `Cslib.Crypto.MLKEM.mlweIdealGame`,
  `Cslib.Crypto.MLKEM.mlweAdvantage`: Module-LWE experiments with explicit samplers.
* `Cslib.Crypto.MLKEM.mlweKeyReduction`, `Cslib.Crypto.MLKEM.mlweReduction`: the two reductions.
* `Cslib.Crypto.MLKEM.uniformCiphertextGame`: the message-independent final game.

## Main results

* `Cslib.Crypto.MLKEM.indCpaAdvantage_le`: IND-CPA advantage of K-PKE is at most the sum of the
  four Module-LWE advantages.

## References

* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, Section 5][NISTFIPS203]
-/

@[expose] public section

namespace Cslib.Crypto.MLKEM

open Probability Cslib.Crypto.Protocols
open scoped NNReal

/-! ### Module-LWE with explicit secret and error samplers -/

/-- The real Module-LWE experiment: a uniform `A ∈ R_q^{m×d}`, a secret `s ← secret` and an error
`e ← error`; the distinguisher sees `(A, A s + e)`. -/
noncomputable def mlweRealGame (m d n q : ℕ) [NeZero q]
    (secret : ProbComp (Fin d → Fin n → ZMod q)) (error : ProbComp (Fin m → Fin n → ZMod q))
    (distinguisher :
      Matrix (Fin m) (Fin d) (Fin n → ZMod q) × (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    ProbComp Bool := do
  let A ← ProbComp.uniform (Matrix (Fin m) (Fin d) (Fin n → ZMod q))
  let s ← secret
  let e ← error
  distinguisher (A, ModuleLWE.sample A s e)

/-- The ideal Module-LWE experiment: the distinguisher sees a uniform pair `(A, b)`. -/
noncomputable def mlweIdealGame (m d n q : ℕ) [NeZero q]
    (distinguisher :
      Matrix (Fin m) (Fin d) (Fin n → ZMod q) × (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    ProbComp Bool := do
  let sample ← ProbComp.uniform
    (Matrix (Fin m) (Fin d) (Fin n → ZMod q) × (Fin m → Fin n → ZMod q))
  distinguisher sample

/-- Concrete Module-LWE distinguishing advantage for the given secret and error samplers. -/
noncomputable def mlweAdvantage (m d n q : ℕ) [NeZero q]
    (secret : ProbComp (Fin d → Fin n → ZMod q)) (error : ProbComp (Fin m → Fin n → ZMod q))
    (distinguisher :
      Matrix (Fin m) (Fin d) (Fin n → ZMod q) × (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    ℝ≥0 :=
  Game.advantage (ProbComp.eval (mlweRealGame m d n q secret error distinguisher))
    (ProbComp.eval (mlweIdealGame m d n q distinguisher))

/-! ### The reductions -/

variable (P : Params)

/-- **Public-key hop**: use a `k × k` Module-LWE sample as the public key and encrypt `m` with
fresh K-PKE coins. -/
noncomputable def mlweKeyReduction (adversary : PublicKey P → Ciphertext P → ProbComp Bool)
    (m : Fin P.n → Bool) (pk : PublicKey P) : ProbComp Bool := do
  let coins ← sampleCoins P
  adversary pk (encrypt P pk m coins)

/-- **Ciphertext hop**: read a `(k + 1) × k` Module-LWE sample `(M, w)` as the public key
`unextendPublicKeyMatrix M` (row `0` of `M` is `b`, the other rows are `Aᵀ`) and the ciphertext
obtained by adding the message polynomial to `v = w 0` and compressing. -/
def mlweReduction (adversary : PublicKey P → Ciphertext P → ProbComp Bool) (m : Fin P.n → Bool)
    (sample : Matrix (Fin (P.k + 1)) (Fin P.k) (Fin P.n → ZMod P.q) ×
      (Fin (P.k + 1) → Fin P.n → ZMod P.q)) : ProbComp Bool :=
  adversary (unextendPublicKeyMatrix sample.1)
    (compressCiphertext P (unextendCiphertext sample.2 + (0, messagePoly P m)))

/-- The final game: a uniform public key and the compression of a uniform ciphertext, independent
of the message. -/
noncomputable def uniformCiphertextGame [NeZero P.q]
    (adversary : PublicKey P → Ciphertext P → ProbComp Bool) : ProbComp Bool := do
  let view ← ProbComp.uniform (PublicKey P × ModuleLWECiphertext P.k P.n P.q)
  adversary view.1 (compressCiphertext P view.2)

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

/-- **Real game**: the IND-CPA experiment encrypting `m_b` is the real `k × k` Module-LWE game for
`mlweKeyReduction` with `CBD_{η₁}` secret and error. -/
theorem eval_indCpaGame_eq [NeZero P.q] (m₀ m₁ : Fin P.n → Bool) (b : Bool)
    (adversary : PublicKey P → Ciphertext P → ProbComp Bool) :
    ProbComp.eval ((toExplicitCoinPKE P).indCpaGame m₀ m₁ b adversary) =
      ProbComp.eval (mlweRealGame P.k P.k P.n P.q (sampleVecCBD P.k P.n P.q P.η₁)
        (sampleVecCBD P.k P.n P.q P.η₁) (mlweKeyReduction P adversary (if b then m₁ else m₀))) := by
  simp only [ExplicitCoinPKE.indCpaGame, ExplicitCoinPKE.encrypt, toExplicitCoinPKE, keyGen,
    mlweRealGame, mlweKeyReduction, moduleLWEKeyGen_eq_sample, bind_assoc, pure_bind]

/-- **Hybrid game**: with a uniform public key, the experiment is the real `(k + 1) × k`
Module-LWE game for `mlweReduction` with `CBD_{η₁}` secret and `CBD_{η₂}` errors. -/
theorem eval_mlweIdealGame_mlweKeyReduction [NeZero P.q]
    (adversary : PublicKey P → Ciphertext P → ProbComp Bool) (m : Fin P.n → Bool) :
    ProbComp.eval (mlweIdealGame P.k P.k P.n P.q (mlweKeyReduction P adversary m)) =
      ProbComp.eval (mlweRealGame (P.k + 1) P.k P.n P.q (sampleVecCBD P.k P.n P.q P.η₁)
        (sampleVecCBD (P.k + 1) P.n P.q P.η₂) (mlweReduction P adversary m)) := by
  simp only [mlweIdealGame, mlweRealGame, mlweKeyReduction, mlweReduction, sampleCoins,
    sampleVecCBD, OracleComp.replicateFin_succ, bind_assoc, pure_bind, bind_map_left,
    ProbComp.eval_bind, ProbComp.eval_uniform]
  rw [← PMF.uniformOfFintype_map_equiv (extendPublicKeyEquiv P.k P.n P.q), PMF.bind_map]
  congr 1
  funext pk
  simp only [Function.comp_apply, extendPublicKeyEquiv, Equiv.coe_fn_mk,
    unextendPublicKeyMatrix_extendPublicKeyMatrix, unextendCiphertext_sample_add_messagePoly]
  congr 1
  funext r
  rw [PMF.bind_comm]
  rfl

/-- **Final game**: on a uniform `(k + 1) × k` sample, `mlweReduction` produces the
message-independent `uniformCiphertextGame`. -/
theorem eval_mlweIdealGame_mlweReduction [NeZero P.q]
    (adversary : PublicKey P → Ciphertext P → ProbComp Bool) (m : Fin P.n → Bool) :
    ProbComp.eval (mlweIdealGame (P.k + 1) P.k P.n P.q (mlweReduction P adversary m)) =
      ProbComp.eval (uniformCiphertextGame P adversary) := by
  let e := (extendPublicKeyEquiv P.k P.n P.q).symm.prodCongr
    ((extendCiphertextEquiv P.k P.n P.q).symm.trans
      (Equiv.addRight ((0, messagePoly P m) : ModuleLWECiphertext P.k P.n P.q)))
  simp only [mlweIdealGame, uniformCiphertextGame, ProbComp.eval_bind, ProbComp.eval_uniform]
  rw [← PMF.uniformOfFintype_map_equiv e, PMF.bind_map]
  rfl

/-! ### The IND-CPA bound -/

/-- Distance of the real experiment for one message from the final game. -/
theorem advantage_indCpa_uniform_le [NeZero P.q]
    (adversary : PublicKey P → Ciphertext P → ProbComp Bool) (m₀ m₁ : Fin P.n → Bool)
    (b : Bool) :
    Game.advantage (ProbComp.eval ((toExplicitCoinPKE P).indCpaGame m₀ m₁ b adversary))
        (ProbComp.eval (uniformCiphertextGame P adversary)) ≤
      mlweAdvantage P.k P.k P.n P.q (sampleVecCBD P.k P.n P.q P.η₁)
          (sampleVecCBD P.k P.n P.q P.η₁) (mlweKeyReduction P adversary (if b then m₁ else m₀)) +
        mlweAdvantage (P.k + 1) P.k P.n P.q (sampleVecCBD P.k P.n P.q P.η₁)
          (sampleVecCBD (P.k + 1) P.n P.q P.η₂)
          (mlweReduction P adversary (if b then m₁ else m₀)) := by
  rw [eval_indCpaGame_eq, ← eval_mlweIdealGame_mlweReduction P adversary (if b then m₁ else m₀)]
  refine le_trans (Game.advantage_triangle _
    (ProbComp.eval (mlweIdealGame P.k P.k P.n P.q
      (mlweKeyReduction P adversary (if b then m₁ else m₀)))) _) ?_
  rw [mlweAdvantage, mlweAdvantage, ← eval_mlweIdealGame_mlweKeyReduction]

/-- **IND-CPA security of K-PKE**: for all fixed messages `m₀, m₁` and every adversary, the
fixed-message IND-CPA advantage of `toExplicitCoinPKE P` is at most the sum, over both messages,
of the Module-LWE advantages of `mlweKeyReduction` (`k × k`, `CBD_{η₁}` secret and error) and
`mlweReduction` (`(k + 1) × k`, `CBD_{η₁}` secret, `CBD_{η₂}` errors). -/
theorem indCpaAdvantage_le [NeZero P.q] (m₀ m₁ : Fin P.n → Bool)
    (adversary : PublicKey P → Ciphertext P → ProbComp Bool) :
    (toExplicitCoinPKE P).indCpaAdvantage m₀ m₁ adversary ≤
      (mlweAdvantage P.k P.k P.n P.q (sampleVecCBD P.k P.n P.q P.η₁)
          (sampleVecCBD P.k P.n P.q P.η₁) (mlweKeyReduction P adversary m₀) +
        mlweAdvantage (P.k + 1) P.k P.n P.q (sampleVecCBD P.k P.n P.q P.η₁)
          (sampleVecCBD (P.k + 1) P.n P.q P.η₂) (mlweReduction P adversary m₀)) +
      (mlweAdvantage P.k P.k P.n P.q (sampleVecCBD P.k P.n P.q P.η₁)
          (sampleVecCBD P.k P.n P.q P.η₁) (mlweKeyReduction P adversary m₁) +
        mlweAdvantage (P.k + 1) P.k P.n P.q (sampleVecCBD P.k P.n P.q P.η₁)
          (sampleVecCBD (P.k + 1) P.n P.q P.η₂) (mlweReduction P adversary m₁)) := by
  have h₀ := advantage_indCpa_uniform_le P adversary m₀ m₁ false
  have h₁ := advantage_indCpa_uniform_le P adversary m₀ m₁ true
  simp only [Bool.false_eq_true, ↓reduceIte] at h₀ h₁
  refine le_trans (Game.advantage_triangle _
    (ProbComp.eval (uniformCiphertextGame P adversary)) _) ?_
  rw [Game.advantage_comm (ProbComp.eval (uniformCiphertextGame P adversary))]
  exact add_le_add h₀ h₁

end Cslib.Crypto.MLKEM
