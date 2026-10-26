/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Leveled.Reduction
import Complexity.Probability.PMF.Bind

/-!
# Exact chosen-message games of leveled encryption

The actual serialized scheme experiment is the real public-chain hybrid followed by adaptive
message selection. At the zero-link endpoint, one base IND-CPA challenge simulates the entire
experiment, including the adversary's retained state and the fresh-ciphertext tag.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.eval_keyGen_public`: the exact serialized public marginal.
* `Cslib.Crypto.Homomorphic.Leveled.eval_game_keyGen`: the actual scheme game is the real-chain
  public-artifact experiment.
* `Cslib.Crypto.Homomorphic.Leveled.eval_zeroLinkAdversary`: an exact simulation of the zero-chain
  chosen-message experiment, including depth zero.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Probability

/-- The actual key generator's public marginal is the serialized real-chain hybrid. -/
theorem eval_keyGen_public (E : Scheme) (n budget : ℕ) :
    (ProbComp.eval (keyGen E n budget)).map Prod.fst =
      (ProbComp.eval (E.publicKeyChainHybrid n (2 * budget) (2 * budget))).map encPublicKey := by
  rw [E.eval_publicKeyChainHybrid_depth]
  simp only [keyGen, keyPair, ProbComp.eval_map, PMF.map_comp, Function.comp_def]

/-- The public artifact and tagged challenge in the actual scheme game agree with the real
chain experiment; intermediate and endpoint secrets remain hidden. -/
theorem eval_game_keyGen (E : Scheme) (budget : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.game (fun n => keyGen E n (budget n)) (encrypt E)
      adversary bit n) =
      ProbComp.eval (E.publicKeyChainHybrid n (2 * budget n) (2 * budget n) >>=
        publicKeyGame E adversary bit n) := by
  rw [ProbComp.eval_bind, E.eval_publicKeyChainHybrid_depth]
  simp only [Encryption.game, Encryption.gameOn, ↓reduceIte, keyGen, keyPair, encrypt,
    publicKeyGame, ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map, Function.comp_def,
    publicKeyDecoder_decode_enc]

/-- The zero-link base adversary simulates the entire adaptive chosen-message experiment.
When the chain is nonempty, a generated secret supplies the unknown first secret's length;
when it is empty, no secret length is used. -/
theorem eval_zeroLinkAdversary (E : Scheme) (depth : ℕ → ℕ)
    (adversary : Encryption.Adversary) (bit : Bool) (n width : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width) :
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (zeroLinkAdversary E depth adversary) bit n) =
      ProbComp.eval (E.publicKeyChainHybrid n (depth n) 0 >>=
        publicKeyGame E adversary bit n) := by
  simp only [Encryption.game, Encryption.gameOn, ↓reduceIte,
    zeroLinkAdversary, Scheme.publicKeyChainHybrid_zero,
    Scheme.generateKeys, OracleComp.replicate_succ, publicKeyGame,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.bind_bind, PMF.bind_map, PMF.pure_bind, Function.comp_def,
    List.map_cons, List.getD_cons_zero]
  apply Probability.PMF.bind_congr_on_support
  intro first hfirst
  apply Probability.PMF.bind_congr_on_support
  intro rest hrest
  have hlinks : E.encryptZeroKeyLinks n ((first.1, (rest.headD ([], [])).2) :: rest) =
      E.encryptZeroKeyLinks n (first :: rest) := by
    cases rest with
    | nil => rfl
    | cons second tail =>
      have hsecond : second ∈ (ProbComp.eval (E.keyGen n)).support :=
        ((ProbComp.mem_support_replicate_iff (depth n) (E.keyGen n) (second :: tail)).mp
          hrest).2 second (by simp)
      exact E.encryptZeroKeyLinks_cons_congr n (first.1, second.2) first (second :: tail)
        ((hwidth second hsecond).trans (hwidth first hfirst).symm)
  rw [hlinks]

end Cslib.Crypto.Homomorphic.Leveled
