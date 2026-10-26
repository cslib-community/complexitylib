/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.KeyChain.Reduction
public import Complexity.Crypto.Computational.Homomorphic.KeyChain.Hybrid.Game
import Complexity.Probability.PMF.Bind

/-!
# Exact games of the encrypted-link reduction

The concrete two-stage reduction simulates the full public key-chain distribution. Its saved
state contains only keys that it generated and the public challenge key. Fixed supported secret
length justifies replacing the unknown challenge secret by an equally long zero word after its
outgoing link has been erased.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.eval_guessLink_active`: exact simulation after inserting a
  challenge ciphertext.
* `Cslib.Crypto.Homomorphic.Scheme.eval_linkAdversaryAt`: the complete base encryption game at a
  supplied link and bit coordinate, including rejection of padding coordinates.
* `Cslib.Crypto.Homomorphic.Scheme.eval_linkAdversary`: exact uniform averaging of the concrete
  two-stage adversary.
* `Cslib.Crypto.Homomorphic.Scheme.publicKeyChainHybrid_advantage_linkAdversary`: the exact
  unsigned reduction loss for the complete public artifact.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

open ProbComp Probability
open scoped NNReal

variable (E : Scheme)

/-- An active reduction reconstructs the corresponding complete bit hybrid. The target secret
is used only in this specification; the algorithm knows its length from the predecessor. -/
theorem eval_guessLink_active
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool)
    (n : ℕ) (before : List (List Bool × List Bool))
    (predecessor next : List Bool × List Bool) (after : List (List Bool × List Bool))
    (cut : ℕ) (bit : Bool) (hcut : cut < predecessor.2.length)
    (hlength : next.2.length = predecessor.2.length) :
    ProbComp.eval (do
      let challenge ← E.encrypt n next.1 (if bit then false else predecessor.2.getD cut false)
      E.guessLink test n (activeLinkState before predecessor next.1 after cut) challenge) =
      ProbComp.eval (do
        let links ← E.encryptKeyLinkHybrid n before predecessor next after
          (cut + if bit then 1 else 0)
        test n ((before ++ predecessor :: next :: after).map Prod.fst, links)) := by
  have hsecret : E.encryptKeyLinkHybrid n before predecessor
      (next.1, List.replicate predecessor.2.length false) after
      (cut + if bit then 1 else 0) =
        E.encryptKeyLinkHybrid n before predecessor next after
          (cut + if bit then 1 else 0) :=
    (E.encryptKeyLinkHybrid_secret_congr n before predecessor next.1 next.2
      (List.replicate predecessor.2.length false) after _ (by simpa using hlength)).symm
  simp only [guessLink_active, ProbComp.eval_bind]
  rw [← PMF.bind_bind, ← ProbComp.eval_bind]
  cases bit <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hsecret ⊢
  · rw [E.eval_spliceEncryptedKeyLink_original n before predecessor
      (next.1, List.replicate predecessor.2.length false) after cut hcut, hsecret]
    simp
  · rw [E.eval_spliceEncryptedKeyLink_zero n before predecessor
      (next.1, List.replicate predecessor.2.length false) after cut hcut, hsecret]
    simp

/-- The real single-challenge encryption game equals the chosen bit hybrid. The fixed-width
hypothesis ranges only over honestly generated keys; no decryption correctness is assumed. -/
theorem eval_linkAdversaryAt (beforeCount afterCount bitIndex : ℕ → ℕ)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool)
    (n width : ℕ) (bit : Bool)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width) :
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (E.linkAdversaryAt beforeCount afterCount bitIndex test) bit n) =
      if bitIndex n < width then
        ProbComp.eval (E.publicKeyLinkHybrid n (beforeCount n) (afterCount n)
          (bitIndex n + if bit then 1 else 0) >>= test n)
      else PMF.pure false := by
  simp only [Encryption.game, Encryption.gameOn, ↓reduceIte,
    linkAdversaryAt, chooseLinkAt, bind_assoc, ProbComp.eval_bind]
  by_cases hi : bitIndex n < width
  · rw [ite_eq_left hi]
    simp only [publicKeyLinkHybrid, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_bind, PMF.pure_bind]
    apply Probability.PMF.bind_congr_on_support
    intro next hnext
    congr 1
    funext before
    apply Probability.PMF.bind_congr_on_support
    intro predecessor hpredecessor
    congr 1
    funext after
    simp only [hwidth predecessor hpredecessor, hi, ↓reduceIte,
      ProbComp.eval_pure, PMF.pure_bind]
    simpa only [ProbComp.eval_bind] using
      E.eval_guessLink_active test n before predecessor next after (bitIndex n) bit
        (by rwa [hwidth predecessor hpredecessor])
        ((hwidth next hnext).trans (hwidth predecessor hpredecessor).symm)
  · rw [ite_eq_right hi]
    rw [← PMF.bind_const (ProbComp.eval (E.keyGen n)) (PMF.pure false)]
    congr 1
    funext next
    rw [← PMF.bind_const
      (ProbComp.eval (OracleComp.replicate (beforeCount n) (E.keyGen n))) (PMF.pure false)]
    congr 1
    funext before
    rw [← PMF.bind_const (ProbComp.eval (E.keyGen n)) (PMF.pure false)]
    apply Probability.PMF.bind_congr_on_support
    intro predecessor hpredecessor
    simp [hwidth predecessor hpredecessor, hi, rejectLinkChoice]

/-- The actual uniformly sampled two-stage reduction realizes the exact two-coordinate game.
Every random choice and every saved-state computation is part of the concrete adversary. -/
theorem eval_linkAdversary (depth capacity : ℕ → ℕ)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool)
    (n width : ℕ) (bit : Bool)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width) :
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (E.linkAdversary depth capacity test) bit n) =
        E.keyChainHybridGame n (depth n) width (capacity n) (test n) bit := by
  simp only [Encryption.game, Encryption.gameOn, ↓reduceIte, linkAdversary, bind_assoc,
    ProbComp.eval_bind, eval_sampleDyadicIndex, PMF.bind_map, Function.comp_def,
    keyChainHybridGame]
  rw [PMF.bind_comm]
  congr 1
  funext i
  rw [PMF.bind_comm]
  by_cases hi : i.val < depth n
  · simp only [hi, ↓reduceIte]
    congr 1
    funext j
    simpa only [Encryption.game, Encryption.gameOn, ↓reduceIte,
      linkAdversaryAt, ProbComp.eval_bind, PMF.monad_pure_eq_pure] using
      E.eval_linkAdversaryAt (fun _ => depth n - i.val - 1) (fun _ => i.val)
        (fun _ => j.val) test n width bit hwidth
  · simp [hi, rejectLinkChoice]

/-- The public key-chain gap is exactly the concrete base adversary's signed gap, with the
explicit dyadic sampling loss. No maximizing coordinate or nonuniform advice is selected. -/
theorem publicKeyChainHybrid_gap_linkAdversary (depth capacity : ℕ → ℕ)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool)
    (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    (Game.succProbability (ProbComp.eval
      (E.publicKeyChainHybrid n (depth n) (depth n) >>= test n)) : ℝ) -
      Game.succProbability (ProbComp.eval
        (E.publicKeyChainHybrid n (depth n) 0 >>= test n)) =
      (dyadicSize (depth n) : ℝ) * dyadicSize (capacity n) *
        (Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
          (E.linkAdversary depth capacity test) false n)) -
          Game.succProbability (ProbComp.eval (Encryption.game E.keyGen E.encrypt
            (E.linkAdversary depth capacity test) true n))) := by
  rw [E.eval_linkAdversary depth capacity test n width false hwidth,
    E.eval_linkAdversary depth capacity test n width true hwidth]
  exact E.publicKeyChainHybrid_gap n (depth n) width (capacity n) hwidth hcapacity (test n)

/-- The exact unsigned reduction loss for the full public artifact. Padding contributes no
gap, including when there are no links or no secret bits. -/
theorem publicKeyChainHybrid_advantage_linkAdversary (depth capacity : ℕ → ℕ)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool)
    (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity n) :
    Game.advantage
      (ProbComp.eval (E.publicKeyChainHybrid n (depth n) (depth n) >>= test n))
      (ProbComp.eval (E.publicKeyChainHybrid n (depth n) 0 >>= test n)) =
      (dyadicSize (depth n) : ℝ≥0) * dyadicSize (capacity n) *
        Game.advantage
          (ProbComp.eval (Encryption.game E.keyGen E.encrypt
            (E.linkAdversary depth capacity test) false n))
          (ProbComp.eval (Encryption.game E.keyGen E.encrypt
            (E.linkAdversary depth capacity test) true n)) := by
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_natCast,
    Game.coe_advantage, Game.coe_advantage,
    E.publicKeyChainHybrid_gap_linkAdversary depth capacity test n width hwidth hcapacity,
    abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]

end Cslib.Crypto.Homomorphic.Scheme
