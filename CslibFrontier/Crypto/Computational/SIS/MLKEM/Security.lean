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

* `mlweKeyReduction`: reads a `k × k` sample `(A, b)` as the public key and encrypts honestly;
* `mlweReduction`: reads a `(k + 1) × k` sample `(M, w)` as the public key
  `unextendPublicKeyMatrix M` and the ciphertext
  `compressCiphertext (unextendCiphertext w + (0, messagePoly m))`.

The three game identities are exact (`eval_indCpaGame_eq`, `randomGame_mlweKeyReduction`,
`randomGame_mlweReduction`), and `indCpaAdvantage_le` bounds the fixed-message IND-CPA advantage
of `toExplicitCoinPKE` by four `ModuleLWE.advantage` terms of the explicit reductions, two for
each message. This is the usual two-hop argument for Kyber-style encryption, stated here as an
original concrete bound in this model: the matrix `A` is uniform rather than expanded from a seed,
so no random oracle is involved.

The Module-LWE terms use the shared games `ModuleLWE.realGame` and `ModuleLWE.randomGame` with
centered-binomial secret and error laws. `DecisionModuleLWE` fixes a uniform secret, so it does
not bound these terms; no bridge between the two secret laws is proved here.

## Main definitions

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

/-! ### The reductions -/

variable (P : Params)

/-- **Public-key hop**: use a `k × k` Module-LWE sample `(A, b)` as the public key and encrypt
`m` with fresh K-PKE coins. -/
noncomputable def mlweKeyReduction (adversary : PublicKey P → Ciphertext P → ProbComp Bool)
    (m : Fin P.n → Bool) (A : Matrix (Fin P.k) (Fin P.k) (Fin P.n → ZMod P.q))
    (b : Fin P.k → Fin P.n → ZMod P.q) : ProbComp Bool := do
  let coins ← sampleCoins P
  adversary (A, b) (encrypt P (A, b) m coins)

/-- **Ciphertext hop**: read a `(k + 1) × k` Module-LWE sample `(M, w)` as the public key
`unextendPublicKeyMatrix M` (row `0` of `M` is `b`, the other rows are `Aᵀ`) and the ciphertext
obtained by adding the message polynomial to `v = w 0` and compressing. -/
def mlweReduction (adversary : PublicKey P → Ciphertext P → ProbComp Bool) (m : Fin P.n → Bool)
    (M : Matrix (Fin (P.k + 1)) (Fin P.k) (Fin P.n → ZMod P.q))
    (w : Fin (P.k + 1) → Fin P.n → ZMod P.q) : ProbComp Bool :=
  adversary (unextendPublicKeyMatrix M)
    (compressCiphertext P (unextendCiphertext w + (0, messagePoly P m)))

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
      ModuleLWE.realGame (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
        (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
        (mlweKeyReduction P adversary (if b then m₁ else m₀)) := by
  rw [ModuleLWE.realGame_eq_uniform_bind]
  simp only [ExplicitCoinPKE.indCpaGame, ExplicitCoinPKE.encrypt, toExplicitCoinPKE, keyGen,
    mlweKeyReduction, moduleLWEKeyGen_eq_sample, bind_assoc, pure_bind, ProbComp.eval_bind,
    ProbComp.eval_uniform]

/-- **Hybrid game**: with a uniform public key, the experiment is the real `(k + 1) × k`
Module-LWE game for `mlweReduction` with `CBD_{η₁}` secret and `CBD_{η₂}` errors. -/
theorem randomGame_mlweKeyReduction [NeZero P.q]
    (adversary : PublicKey P → Ciphertext P → ProbComp Bool) (m : Fin P.n → Bool) :
    ModuleLWE.randomGame (mlweKeyReduction P adversary m) =
      ModuleLWE.realGame (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
        (ProbComp.eval (sampleVecCBD (P.k + 1) P.n P.q P.η₂)) (mlweReduction P adversary m) := by
  rw [ModuleLWE.randomGame_eq, ModuleLWE.realGame_eq_uniform_bind]
  simp only [mlweKeyReduction, mlweReduction, sampleCoins, sampleVecCBD,
    OracleComp.replicateFin_succ, bind_assoc, pure_bind, ProbComp.eval_bind, ProbComp.eval_map,
    PMF.bind_map, PMF.bind_bind, Function.comp_def]
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
theorem randomGame_mlweReduction [NeZero P.q]
    (adversary : PublicKey P → Ciphertext P → ProbComp Bool) (m : Fin P.n → Bool) :
    ModuleLWE.randomGame (mlweReduction P adversary m) =
      ProbComp.eval (uniformCiphertextGame P adversary) := by
  let e := (extendPublicKeyEquiv P.k P.n P.q).symm.prodCongr
    ((extendCiphertextEquiv P.k P.n P.q).symm.trans
      (Equiv.addRight ((0, messagePoly P m) : ModuleLWECiphertext P.k P.n P.q)))
  simp only [ModuleLWE.randomGame_eq, uniformCiphertextGame, ProbComp.eval_bind,
    ProbComp.eval_uniform]
  rw [← PMF.uniformOfFintype_map_equiv e, PMF.bind_map]
  rfl

/-! ### The IND-CPA bound -/

/-- Distance of the real experiment for one message from the final game. -/
theorem advantage_indCpa_uniform_le [NeZero P.q]
    (adversary : PublicKey P → Ciphertext P → ProbComp Bool) (m₀ m₁ : Fin P.n → Bool)
    (b : Bool) :
    Game.advantage (ProbComp.eval ((toExplicitCoinPKE P).indCpaGame m₀ m₁ b adversary))
        (ProbComp.eval (uniformCiphertextGame P adversary)) ≤
      ModuleLWE.advantage (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
          (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
          (mlweKeyReduction P adversary (if b then m₁ else m₀)) +
        ModuleLWE.advantage (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
          (ProbComp.eval (sampleVecCBD (P.k + 1) P.n P.q P.η₂))
          (mlweReduction P adversary (if b then m₁ else m₀)) := by
  rw [eval_indCpaGame_eq, ← randomGame_mlweReduction P adversary (if b then m₁ else m₀)]
  refine le_trans (Game.advantage_triangle _
    (ModuleLWE.randomGame (mlweKeyReduction P adversary (if b then m₁ else m₀))) _) ?_
  rw [ModuleLWE.advantage, ModuleLWE.advantage, ← randomGame_mlweKeyReduction]

/-- **IND-CPA security of K-PKE**: for all fixed messages `m₀, m₁` and every adversary, the
fixed-message IND-CPA advantage of `toExplicitCoinPKE P` is at most the sum, over both messages,
of the Module-LWE advantages of `mlweKeyReduction` (`k × k`, `CBD_{η₁}` secret and error) and
`mlweReduction` (`(k + 1) × k`, `CBD_{η₁}` secret, `CBD_{η₂}` errors). -/
theorem indCpaAdvantage_le [NeZero P.q] (m₀ m₁ : Fin P.n → Bool)
    (adversary : PublicKey P → Ciphertext P → ProbComp Bool) :
    (toExplicitCoinPKE P).indCpaAdvantage m₀ m₁ adversary ≤
      (ModuleLWE.advantage (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
          (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁)) (mlweKeyReduction P adversary m₀) +
        ModuleLWE.advantage (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
          (ProbComp.eval (sampleVecCBD (P.k + 1) P.n P.q P.η₂))
          (mlweReduction P adversary m₀)) +
      (ModuleLWE.advantage (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
          (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁)) (mlweKeyReduction P adversary m₁) +
        ModuleLWE.advantage (ProbComp.eval (sampleVecCBD P.k P.n P.q P.η₁))
          (ProbComp.eval (sampleVecCBD (P.k + 1) P.n P.q P.η₂))
          (mlweReduction P adversary m₁)) := by
  have h₀ := advantage_indCpa_uniform_le P adversary m₀ m₁ false
  have h₁ := advantage_indCpa_uniform_le P adversary m₀ m₁ true
  simp only [Bool.false_eq_true, ↓reduceIte] at h₀ h₁
  refine le_trans (Game.advantage_triangle _
    (ProbComp.eval (uniformCiphertextGame P adversary)) _) ?_
  rw [Game.advantage_comm (ProbComp.eval (uniformCiphertextGame P adversary))]
  exact add_le_add h₀ h₁

end Cslib.Crypto.MLKEM
