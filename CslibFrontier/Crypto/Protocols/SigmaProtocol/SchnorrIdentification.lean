/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Identification
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Linear

/-!
# Schnorr identification

Schnorr's identification scheme ([BonehShoup2023], Section 19.1) is Schnorr's Sigma protocol
with the key generator that draws `α` uniformly from `ZMod q` and publishes `u = α • g`. The
one-way game for this key generator is the discrete-logarithm experiment for `g`: the adversary
wins when it outputs some `α'` with `α' • g = u`. When `g` generates a group of prime order `q`,
this `α'` is the sampled `α`.

The two theorems here are the exact forms of Boneh and Shoup's Theorems 19.1 and 19.5 at a fixed
group. They make no efficiency or hardness claim; the discrete-logarithm assumption and the
asymptotic security statement need a group family with efficient operations.
As for the identification experiments they instantiate, the group and challenge types are in
`Type`.

## Main definitions

* `SigmaProtocol.schnorrKeyGen`: a uniform secret `α` and the public key `α • g`.

## Main results

* `SigmaProtocol.schnorr_succProbability_directAttack_le`: `ε ≤ 1 / N + √ε'`, with `ε'` the
  rewinding extractor's discrete-logarithm success probability (Theorem 19.1).
* `SigmaProtocol.schnorr_eavesdropAttack_eq_directAttack`: an eavesdropper is no stronger than
  the direct impersonator that simulates its views (Theorem 19.5).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 19.1.
* [C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*][Schnorr1991]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability

variable {q : ℕ} [NeZero q] {G C : Type} [AddCommGroup G] [Module (ZMod q) G]

/-- Schnorr key generation ([BonehShoup2023], Section 19.1): a uniform secret `α` and the
verification key `α • g`. -/
noncomputable def schnorrKeyGen (g : G) : PMF (ZMod q × G) :=
  (PMF.uniformOfFintype (ZMod q)).map fun α => (α, α • g)

/-- Every Schnorr key pair is in Schnorr's relation. -/
theorem mem_support_schnorrKeyGen {g : G} {key : ZMod q × G}
    (h : key ∈ (schnorrKeyGen g).support) : key.1 • g = key.2 := by
  obtain ⟨α, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  rfl

variable [DecidableEq G] [Fintype C] [Nonempty C] {ι : C ↪ ZMod q} {g : G}

/-- **Schnorr identification against direct attacks** ([BonehShoup2023], Theorem 19.1, exact
form): an impersonator's success probability is at most `1 / N + √ε'`, where `ε'` is the
probability that rewinding it computes a discrete logarithm of the key and `N` is the number of
challenges. -/
theorem schnorr_succProbability_directAttack_le [Fact q.Prime] (A : Impersonator G G C (ZMod q)) :
    (Game.succProbability ((schnorr ι g).directAttack (schnorrKeyGen g) A) : ℝ) ≤
      1 / Fintype.card C + √(Game.succProbability
        (oneWayGame (schnorrKeyGen g) (fun α u => α • g = u) (A.rewind (linearExtract ι)))) :=
  succProbability_directAttack_le (schnorr_specialSoundness.specialSoundOn _) A

/-- **Schnorr identification against eavesdropping** ([BonehShoup2023], Theorem 19.5, exact
form): an eavesdropper succeeds with exactly the probability of the direct impersonator that
simulates its `Q` conversations. -/
theorem schnorr_eavesdropAttack_eq_directAttack {Q : ℕ}
    (A : Impersonator (G × (Fin Q → G × C × ZMod q)) G C (ZMod q)) :
    (schnorr ι g).eavesdropAttack (schnorrKeyGen g) Q A =
      (schnorr ι g).directAttack (schnorrKeyGen g)
        (A.withSimulatedViews
          (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod q) G g) id ι)) :=
  eavesdropAttack_eq_directAttack schnorr_specialHVZK (fun _ => mem_support_schnorrKeyGen) A

end Cslib.Crypto.Protocols.SigmaProtocol
