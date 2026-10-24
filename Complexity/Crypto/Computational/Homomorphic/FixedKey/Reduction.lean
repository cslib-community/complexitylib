/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.FixedKey.Encoding
public import Complexity.Crypto.Computational.Homomorphic.Efficiency
import Complexity.Probability.PMF.Bind
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Tactic.PPT

/-!
# The fixed-key security reduction

The public-artifact game allows adaptive message selection after the entire encrypted-secret
vector is visible. In the zero-vector experiment, a concrete base adversary samples an
independent key only to learn the common supported secret length. It encrypts that many zero
bits under the challenge public key and preserves both stages of the target adversary.

The unknown challenge secret is never available to the reduction. The supported-width premise
is used only in the exact game identity, not by the algorithm or its native runtime certificate.

## Main definitions

* `Cslib.Crypto.Homomorphic.FixedKey.publicKeyGame`: adaptive challenge on a public artifact.
* `Cslib.Crypto.Homomorphic.FixedKey.zeroAdversary`: the actual base-game reduction.

## Main results

* `Cslib.Crypto.Homomorphic.FixedKey.isPPTOn_publicKeyGame`: native artifact postprocessing.
* `Cslib.Crypto.Homomorphic.FixedKey.isPPT_zeroAdversary`: native reduction admissibility.
* `Cslib.Crypto.Homomorphic.FixedKey.eval_zeroAdversary`: exact zero-vector simulation.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*][Gentry2009], Section 2.
* [D. Boneh, S. Halevi, M. Hamburg, R. Ostrovsky,
  *Circular-Secure Encryption from Decision Diffie-Hellman*][BonehHaleviHamburgOstrovsky2008],
  Section 2.1.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.FixedKey

open Probability Turing.MultiTapeTM

/-- Choose messages after seeing the complete artifact, then encrypt under its base public
key and retain the adversary's exact saved state. -/
def publicKeyGame (E : Scheme) (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ)
    (artifact : List Bool × List (List Bool)) : ProbComp Bool := do
  let choice ← adversary.choose n (encPublicKey artifact)
  let ciphertext ← E.encrypt n artifact.1 (if bit then choice.1.2 else choice.1.1)
  adversary.guess n choice.2 ciphertext

/-- Build the zero-vector public artifact from the challenge public key. An independently
generated secret supplies only its length; the challenge secret is neither read nor saved. -/
def zeroAdversary (E : Scheme) (adversary : Encryption.Adversary) : Encryption.Adversary where
  choose n challengePk := do
    let auxiliary ← E.keyGen n
    let encrypted ← E.encryptBits n challengePk (List.replicate auxiliary.2.length false)
    adversary.choose n (encPublicKey (challengePk, encrypted))
  guess := adversary.guess

variable {E : Scheme}
  (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => E.encrypt p.1 p.2.1 p.2.2))
  {adversary : Encryption.Adversary} (hadversary : adversary.IsPPT)

include hencrypt hadversary

/-- Both adversary stages and the complete public encoding have native certificates. -/
theorem isPPTOn_publicKeyGame (bit : Bool) :
    IsPPTOn (encPair encUnary encPublicKey) encBool
      (fun p => publicKeyGame E adversary bit p.1 p.2) := by
  have hchoose := hadversary.choose
  have hguess := hadversary.guess
  have hpublic := (ComputableTidilyInPolyTime.snd encUnary encPublicKey).encoded
  unfold publicKeyGame
  dsimp only [encPublicKey, Encryption.encCircularPublicKey] at hpublic ⊢
  ppt

/-- The reduction is uniform strict PPT without any width-computability premise. -/
theorem isPPT_zeroAdversary
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen) :
    (zeroAdversary E adversary).IsPPT := by
  have hchoose := hadversary.choose
  constructor
  · change IsPPTOn (encPair encUnary encBits) (encPair (encPair encBool encBool) encBits)
      (fun p => (zeroAdversary E adversary).choose p.1 p.2)
    dsimp only [zeroAdversary]
    apply (hkeyGen.preprocess (ComputableInPolyTime.fst encUnary encBits)).bind_with
    have hbits : IsPPTOn
        (encPair (encPair encUnary encBits) (encPair encBits encBits)) (encList encBits)
        (fun p => E.encryptBits p.1.1 p.1.2 (List.replicate p.2.2.length false)) := by
      apply Scheme.isPPTOn_encryptBits hencrypt <;> fun_prop
    apply hbits.bind_with
    have hpublic : ComputableTidilyInPolyTime
        (fun p : ((ℕ × List Bool) × (List Bool × List Bool)) × List (List Bool) =>
          (p.1.1.2, p.2))
        (encPair (encPair (encPair encUnary encBits) (encPair encBits encBits))
          (encList encBits)) encPublicKey := by
      dsimp only [encPublicKey, Encryption.encCircularPublicKey]
      fun_prop
    exact hchoose.preprocess (by fun_prop) hpublic.encoded
  · exact hadversary.guess

omit hencrypt hadversary in
/-- A supported auxiliary key supplies exactly the challenge secret's length. Removing that
unused auxiliary sample then gives the complete zero-vector chosen-message experiment. -/
theorem eval_zeroAdversary (E : Scheme) (adversary : Encryption.Adversary)
    (bit : Bool) (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width) :
    ProbComp.eval (Encryption.game E.keyGen E.encrypt (zeroAdversary E adversary) bit n) =
      ProbComp.eval (Encryption.circularPublicKey E.keyGen E.encrypt false n >>=
        publicKeyGame E adversary bit n) := by
  simp only [Encryption.game, zeroAdversary, Encryption.circularPublicKey, publicKeyGame,
    Scheme.encryptBits, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.bind_bind, PMF.pure_bind]
  apply Probability.PMF.bind_congr_on_support
  intro keys hkeys
  conv_rhs => rw [hwidth keys hkeys]
  refine (Probability.PMF.bind_congr_on_support _ _ _ ?_).trans (PMF.bind_const _ _)
  intro auxiliary hauxiliary
  rw [hwidth auxiliary hauxiliary]

end Cslib.Crypto.Homomorphic.FixedKey
