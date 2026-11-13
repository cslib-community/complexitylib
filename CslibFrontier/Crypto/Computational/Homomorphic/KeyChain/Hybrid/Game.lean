/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.KeyChain.Hybrid
public import CslibFrontier.Crypto.Game.Hybrid
public import CslibFrontier.Probability.UniformNat

/-!
# Averaging acyclic key-chain hybrids

The signed gap of a key-chain experiment telescopes over links, then over secret-key bits.
Both coordinates are averaged over fixed dyadic ranges. Unused coordinates reject in both
worlds, including zero links and empty secret words. No parameter-dependent best coordinate
is selected.

These are exact game identities. Connecting the averaged game to an actual native IND-CPA
adversary is a separate reduction obligation.

## Main definitions

* `Cslib.Crypto.Homomorphic.Scheme.keyChainHybridGame`: the two-coordinate hybrid average.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.publicKeyLinkHybrid_gap`: signed bitwise telescoping.
* `Cslib.Crypto.Homomorphic.Scheme.publicKeyChainHybrid_gap`: the full signed two-coordinate
  identity with its explicit dyadic loss.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Probability

variable (E : Scheme)

/-- Telescope the bit hybrids of one link. The cap can be any upper bound on the common
supported secret length; it need not equal that length. -/
theorem publicKeyLinkHybrid_gap (n beforeCount afterCount width capacity : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity)
    (test : (List (List Bool) × List (List (List Bool))) → ProbComp Bool) :
    (Game.succProbability (ProbComp.eval
      (E.publicKeyChainHybrid n (beforeCount + afterCount + 1) (beforeCount + 1) >>= test)) : ℝ) -
      Game.succProbability (ProbComp.eval
        (E.publicKeyChainHybrid n (beforeCount + afterCount + 1) beforeCount >>= test)) =
      (dyadicSize capacity : ℝ) *
        (Game.succProbability ((PMF.uniformOfFintype (Fin (dyadicSize capacity))).bind
          (fun j => if j.val < width then ProbComp.eval
            (E.publicKeyLinkHybrid n beforeCount afterCount j.val >>= test) else PMF.pure false)) -
        Game.succProbability ((PMF.uniformOfFintype (Fin (dyadicSize capacity))).bind
          (fun j => if j.val < width then ProbComp.eval
            (E.publicKeyLinkHybrid n beforeCount afterCount (j.val + 1) >>= test)
            else PMF.pure false))) := by
  have h := Game.succProbability_hybrid_average
    (fun j => ProbComp.eval (E.publicKeyLinkHybrid n beforeCount afterCount j >>= test))
    width (dyadicSize capacity) (hcapacity.trans (lt_dyadicSize capacity).le)
  simpa only [ProbComp.eval_bind, E.eval_publicKeyLinkHybrid_zero,
    E.eval_publicKeyLinkHybrid_length n beforeCount afterCount width hwidth] using h

/-- Average reverse link indices and forward bit indices. Inactive coordinates return the same
constant in both worlds. This is a distributional definition, not an unchecked sampler. -/
noncomputable def keyChainHybridGame (n depth width capacity : ℕ)
    (test : (List (List Bool) × List (List (List Bool))) → ProbComp Bool) (bit : Bool) : Game := do
  let i ← PMF.uniformOfFintype (Fin (dyadicSize depth))
  if i.val < depth then
    let j ← PMF.uniformOfFintype (Fin (dyadicSize capacity))
    if j.val < width then
      ProbComp.eval (E.publicKeyLinkHybrid n (depth - i.val - 1) i.val
        (j.val + if bit then 1 else 0) >>= test)
    else pure false
  else pure false

/-- The real-to-zero public-key gap is the signed gap of one uniformly selected link/bit
hybrid, multiplied by the two dyadic range sizes. -/
theorem publicKeyChainHybrid_gap (n depth width capacity : ℕ)
    (hwidth : ∀ keys ∈ (ProbComp.eval (E.keyGen n)).support, keys.2.length = width)
    (hcapacity : width ≤ capacity)
    (test : (List (List Bool) × List (List (List Bool))) → ProbComp Bool) :
    (Game.succProbability (ProbComp.eval (E.publicKeyChainHybrid n depth depth >>= test)) : ℝ) -
      Game.succProbability (ProbComp.eval (E.publicKeyChainHybrid n depth 0 >>= test)) =
      (dyadicSize depth : ℝ) * dyadicSize capacity *
        (Game.succProbability (E.keyChainHybridGame n depth width capacity test false) -
          Game.succProbability (E.keyChainHybridGame n depth width capacity test true)) := by
  let games := fun i => ProbComp.eval (E.publicKeyChainHybrid n depth (depth - i) >>= test)
  let original := fun i => (PMF.uniformOfFintype (Fin (dyadicSize capacity))).bind
    (fun j => if j.val < width then ProbComp.eval
      (E.publicKeyLinkHybrid n (depth - i - 1) i j.val >>= test) else PMF.pure false)
  let replacement := fun i => (PMF.uniformOfFintype (Fin (dyadicSize capacity))).bind
    (fun j => if j.val < width then ProbComp.eval
      (E.publicKeyLinkHybrid n (depth - i - 1) i (j.val + 1) >>= test) else PMF.pure false)
  have hstep (i : ℕ) (hi : i < depth) :
      (Game.succProbability (games i) : ℝ) - Game.succProbability (games (i + 1)) =
        (dyadicSize capacity : ℝ) *
          (Game.succProbability (original i) - Game.succProbability (replacement i)) := by
    have hdepth : depth - i - 1 + i + 1 = depth := by omega
    have hbefore : depth - i - 1 + 1 = depth - i := by omega
    have h := E.publicKeyLinkHybrid_gap n (depth - i - 1) i width capacity
      hwidth hcapacity test
    rw [hdepth, hbefore] at h
    simpa only [games, original, replacement, Nat.sub_sub] using h
  have h := Game.succProbability_hybrid_reduction games original replacement
    depth (dyadicSize depth) (lt_dyadicSize depth).le (dyadicSize capacity) hstep
  simpa only [games, original, replacement, keyChainHybridGame, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure,
    Nat.sub_zero, Nat.sub_self, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using h

end Cslib.Crypto.Homomorphic.Scheme
