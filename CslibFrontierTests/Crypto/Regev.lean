/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Parameters
import CslibFrontier.Crypto.Computational.LWE.DualRegev
import CslibFrontier.Crypto.Computational.LWE.Regev.Security

/-!
Regression clients for Regev and dual-Regev encryption: concrete encryptions and decryptions with
nonzero errors, a gadget preimage sampler satisfying the trapdoor interface, and the growing
GSW parameter family, which satisfies every correctness and security premise apart from its
decision-LWE assumption.
-/

namespace CslibFrontierTests.Regev

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Regev Turing.MultiTapeTM
open scoped Matrix

/-! ### Regev -/

private def toyB : Matrix (Fin 2) (Fin 1) (ZMod (2 ^ 4)) := !![3; 7]
private def toySecret : Fin 1 → ZMod (2 ^ 4) := ![5]
private def toyError : Fin 2 → ℤ := ![1, -1]

-- Both bits round-trip with nonzero errors of both signs, and the coins select the noise.
example : decrypt toySecret
      (encryptWithCoins (Homomorphic.GSW.publicMatrix toyB toySecret toyError) false ![true, false])
      = false ∧
    decrypt toySecret
      (encryptWithCoins (Homomorphic.GSW.publicMatrix toyB toySecret toyError) true ![true, true])
      = true ∧
    noise ![true, false] toyError = 1 := by
  decide +kernel

-- The generic correctness theorem covers this instance: `4 * (2 * 1) < 2 ^ 4`.
example (μ : Bool) (x : Fin 2 → Bool) :
    decrypt toySecret (encryptWithCoins (Homomorphic.GSW.publicMatrix toyB toySecret toyError) μ x)
      = μ :=
  decrypt_encryptWithCoins toyB toySecret toyError μ x (by norm_num) (bound := 1)
    (by decide) (by norm_num)

-- Without a noise margin, decryption can fail: errors of `±4` cross the quarter boundary.
example : decrypt toySecret
    (encryptWithCoins (Homomorphic.GSW.publicMatrix toyB toySecret ![4, 0]) false ![true, false])
      = true := by
  decide +kernel

-- The parameter family's fresh-noise margin gives zero-error correctness for every generated key.
example (security : ℕ) (μ : Bool)
    {keys : PublicKey (Homomorphic.GSW.Parameters.dimension security)
        (Homomorphic.GSW.Parameters.samples security) (Homomorphic.GSW.Parameters.width security) ×
      (Fin (Homomorphic.GSW.Parameters.dimension security) →
        ZMod (2 ^ Homomorphic.GSW.Parameters.width security))}
    (hkeys : keys ∈ (ProbComp.eval (Homomorphic.GSW.keyGen
      (Homomorphic.GSW.Parameters.dimension security) (Homomorphic.GSW.Parameters.samples security)
      (Homomorphic.GSW.Parameters.width security)
      (Homomorphic.GSW.Parameters.noise security))).support)
    {c : Ciphertext (Homomorphic.GSW.Parameters.dimension security)
      (Homomorphic.GSW.Parameters.width security)}
    (hc : c ∈ (ProbComp.eval (encrypt keys.1 μ)).support) : decrypt keys.2 c = μ := by
  have hmargin := Homomorphic.GSW.Parameters.fresh_margin security
  rw [Nat.mul_assoc] at hmargin
  exact keyGen_encrypt_correct (Homomorphic.GSW.Parameters.width_pos security) hmargin hkeys μ hc

-- An adaptive two-query adversary: the second query depends on the first ciphertext.
private noncomputable def adaptiveAdversary :
    LoRAdversary 1 2 4 (List (Ciphertext 1 4)) where
  start _ := PMF.pure []
  query transcript := PMF.pure ((false, (transcript.headD 0) 0 == 0), transcript)
  receive transcript c := c :: transcript
  guess transcript := PMF.pure ((transcript.headD 0) 0 == 0)

-- The two-query bound applies to this adaptive adversary (numerically trivial at these sizes).
example : (Game.advantage
      (lorGame (PMF.uniformOfFintype (PublicKey 1 2 4)) 2 adaptiveAdversary false)
      (lorGame (PMF.uniformOfFintype (PublicKey 1 2 4)) 2 adaptiveAdversary true) : ℝ) ≤
    2 * Real.sqrt ((2 : ℝ) ^ ((1 + 1) * 4) / (2 : ℝ) ^ 2) := by
  exact_mod_cast lorGame_uniform_advantage_le 2 adaptiveAdversary

-- The reduction covers this adversary under the generated-key law with the actual noise law.
example : (Game.advantage
      (lorGame (LWE.publicMatrixLaw 1 2 4 (Homomorphic.GSW.noiseLaw 4 1)) 2 adaptiveAdversary false)
      (lorGame (LWE.publicMatrixLaw 1 2 4 (Homomorphic.GSW.noiseLaw 4 1)) 2 adaptiveAdversary
        true) : ℝ) ≤
    Game.advantage
        ((LWE.publicMatrixLaw 1 2 4 (Homomorphic.GSW.noiseLaw 4 1)).bind
          (lorDistinguisher 2 adaptiveAdversary false))
        ((PMF.uniformOfFintype (PublicKey 1 2 4)).bind (lorDistinguisher 2 adaptiveAdversary false))
      + Game.advantage
        ((LWE.publicMatrixLaw 1 2 4 (Homomorphic.GSW.noiseLaw 4 1)).bind
          (lorDistinguisher 2 adaptiveAdversary true))
        ((PMF.uniformOfFintype (PublicKey 1 2 4)).bind (lorDistinguisher 2 adaptiveAdversary true))
      + 2 * Real.sqrt ((2 : ℝ) ^ ((1 + 1) * 4) / (2 : ℝ) ^ 2) := by
  exact_mod_cast lorGame_advantage_le (Homomorphic.GSW.noiseLaw 4 1) 2 adaptiveAdversary

-- A uniform PPT adversary choosing its messages from the public key and keeping it as state.
private def keyAdversary : Encryption.Adversary where
  choose _ pk := pure ((pk.headD false, !pk.headD false), pk)
  guess _ state ciphertext := pure (state.headD false ^^ ciphertext.headD false)

private theorem keyAdversary_isPPT : keyAdversary.IsPPT := by
  constructor <;> simp only [keyAdversary] <;> ppt

-- The honest encryption program is strict PPT for the growing parameter family.
example : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => encryptSerialized (Homomorphic.GSW.Parameters.dimension p.1)
      (Homomorphic.GSW.Parameters.samples p.1) (Homomorphic.GSW.Parameters.width p.1)
      p.2.1 p.2.2) :=
  isPPTOn_encryptSerialized (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

-- The asymptotic theorem applies to an actual family; only decision LWE remains assumed.
example (hLWE : DecisionLWE Homomorphic.GSW.Parameters.dimension
      Homomorphic.GSW.Parameters.samples Homomorphic.GSW.Parameters.width
      (fun k => Homomorphic.GSW.noiseLaw (Homomorphic.GSW.Parameters.width k)
        (Homomorphic.GSW.Parameters.noise k))) :
    Negligible (fun k => Encryption.advantage
      (Encryption.game
        (fun k => Homomorphic.GSW.keyGenSerialized (Homomorphic.GSW.Parameters.dimension k)
          (Homomorphic.GSW.Parameters.samples k) (Homomorphic.GSW.Parameters.width k)
          (Homomorphic.GSW.Parameters.noise k))
        (fun k => encryptSerialized (Homomorphic.GSW.Parameters.dimension k)
          (Homomorphic.GSW.Parameters.samples k) (Homomorphic.GSW.Parameters.width k))
        keyAdversary) k) :=
  indCPA_of_decisionLWE Homomorphic.GSW.Parameters.computableInPolyTime_dimension
    Homomorphic.GSW.Parameters.computableInPolyTime_samples
    Homomorphic.GSW.Parameters.computableInPolyTime_width
    (Filter.Eventually.of_forall Homomorphic.GSW.Parameters.entropy_margin) hLWE
    keyAdversary keyAdversary_isPPT

/-! ### Dual Regev -/

open Cslib.Crypto.DualRegev in
private def dualA : Matrix (Fin 2) (Fin 1) (ZMod (2 ^ 4)) := !![3; 6]

open Cslib.Crypto.DualRegev in
-- Both bits round-trip with a short secret and nonzero errors.
example : DualRegev.decrypt ![1, -1]
      (DualRegev.encryptWithCoins (publicKeyOf dualA ![1, -1]) false ![5] ![1, -1] 1) = false ∧
    DualRegev.decrypt ![1, -1]
      (DualRegev.encryptWithCoins (publicKeyOf dualA ![1, -1]) true ![5] ![1, 0] (-1)) = true := by
  decide +kernel

/-- The gadget matrix `(1, 2, 4)ᵀ` with binary decomposition as its preimage sampler. -/
private def gadgetTrapdoor : DualRegev.GPVTrapdoor 1 3 3 Unit where
  trapGen := pure (!![1; 2; 4], ())
  samplePre _ u := pure fun k => ((u 0).val.testBit k.val).toNat

private theorem gadget_preimage (u : Fin 1 → ZMod (2 ^ 3)) :
    DualRegev.castVector 3 (fun k : Fin 3 => (((u 0).val.testBit k.val).toNat : ℤ)) ᵥ*
      !![1; 2; 4] = u := by
  revert u
  decide +kernel

-- The trapdoor interface is satisfiable with entry bound one (a non-uniform gadget matrix).
example : gadgetTrapdoor.SamplesShortPreimages 1 := by
  intro keys hkeys u e he
  simp only [gadgetTrapdoor, ProbComp.eval_pure,
    PMF.mem_support_pure_iff] at hkeys he
  subst hkeys he
  exact ⟨gadget_preimage u, fun k => by simpa using Bool.toNat_le _⟩

end CslibFrontierTests.Regev
