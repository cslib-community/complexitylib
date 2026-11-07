/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Crypto.Multiparty.Tetrahedral
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# An obstruction to the advertised multi-tetrahedral rates

[Beaver2027], Section 10, Figure 31 (PDF p. 12), defines the output count as
the number of ranks having occupancy (2,1) or (1,2). There are m ranks in a
deck of n=4m distinct cards. `goodRanks` implements that definition for actual
permutations and arbitrary hand-position sets, including the unequal and equal
hand sizes in Theorems 10.1 and 10.2. Each successful rank contributes one OT.

The pointwise bound m, hence also the uniform-expectation bound m, contradicts
the advertised asymptotic rates (9/32)n and (81/256)n (PDF p. 13): both exceed
n/4. This obstruction applies at every positive deck size and does not depend
on the privacy analysis. It does not refute the weaker Theta(n) assertion, nor
prove a corrected asymptotic constant or an upper bound for other protocols.

## Main results

* `yield_le`, `expectedYield_le`: the actual protocol outputs at most one OT per rank.
* `advertised_rates_exceed_bound`: both advertised constants violate that bound.
* `reverse_message_leakage`: the public message violates the reverse protocol's
  complete-view privacy claim in Theorem 5.1 (PDF p. 5).
-/

public section

open scoped BigOperators

namespace Cslib.Crypto.Tetrahedral

/-- Cards of rank r in the hand occupying positions H of the shuffled deck.
The source's rank map is the card value modulo m. -/
@[expose] def rankHand (m : ℕ) (ρ : Equiv.Perm (Fin (4 * m)))
    (H : Finset (Fin (4 * m))) (r : Fin m) : Finset (Fin (4 * m)) :=
  H.filter fun p => (ρ p).val % m = r.val

/-- Figure 31's successful ranks, with both OT orientations counted. -/
@[expose] def goodRanks (m : ℕ) (ρ : Equiv.Perm (Fin (4 * m)))
    (A B : Finset (Fin (4 * m))) : Finset (Fin m) :=
  Finset.univ.filter fun r =>
    ((rankHand m ρ A r).card = 2 ∧ (rankHand m ρ B r).card = 1) ∨
    ((rankHand m ρ A r).card = 1 ∧ (rankHand m ρ B r).card = 2)

/-- One output per successful rank, exactly g(rho) in Section 10. -/
@[expose] def yield (m : ℕ) (ρ : Equiv.Perm (Fin (4 * m)))
    (A B : Finset (Fin (4 * m))) : ℕ := (goodRanks m ρ A B).card

/-- No permutation, or choice of hand positions, can yield more than m outputs.
Disjointness and hand sizes are unnecessary for this upper bound. -/
theorem yield_le (m : ℕ) (ρ : Equiv.Perm (Fin (4 * m)))
    (A B : Finset (Fin (4 * m))) : yield m ρ A B ≤ m := by
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin m)

/-- Expected number of outputs under the actual uniform full-deck shuffle. -/
@[expose] def expectedYield (m : ℕ) (A B : Finset (Fin (4 * m))) : ℚ :=
  𝔼 ρ : Equiv.Perm (Fin (4 * m)), (yield m ρ A B : ℚ)

/-- Averaging over all (4m)! full shuffles preserves the pointwise rank bound. -/
theorem expectedYield_le (m : ℕ) (A B : Finset (Fin (4 * m))) :
    expectedYield m A B ≤ m := by
  apply Finset.expect_le Finset.univ_nonempty
  intro ρ _
  exact_mod_cast yield_le m ρ A B

/-- A uniform normalized bound: the expected outputs per card never exceed 1/4.
In particular, the gap to either advertised asymptotic rate cannot vanish. -/
theorem normalizedYield_le (m : ℕ) (hm : 0 < m) (A B : Finset (Fin (4 * m))) :
    expectedYield m A B / (4 * m) ≤ (1 / 4 : ℚ) := by
  have hp : (0 : ℚ) < 4 * m := by positivity
  apply (div_le_iff₀ hp).mpr
  have hb := expectedYield_le m A B
  linarith

/-- The advertised rates stay separated from the actual per-card yield by fixed
positive gaps, uniformly in the deck size and hand positions. -/
theorem advertised_rate_gaps (m : ℕ) (hm : 0 < m) (A B : Finset (Fin (4 * m))) :
    (1 / 32 : ℚ) ≤ 9 / 32 - expectedYield m A B / (4 * m) ∧
    (17 / 256 : ℚ) ≤ 81 / 256 - expectedYield m A B / (4 * m) := by
  have hb := normalizedYield_le m hm A B
  constructor <;> linarith

/-- Both constants advertised per n=4m cards exceed the universal output bound.
This refutes the constants for arbitrary positive m, rather than one finite deal. -/
theorem advertised_rates_exceed_bound (m : ℕ) (hm : 0 < m)
    (A B : Finset (Fin (4 * m))) :
    expectedYield m A B < (9 / 32 : ℚ) * (4 * m) ∧
    expectedYield m A B < (81 / 256 : ℚ) * (4 * m) := by
  have hp : (0 : ℚ) < m := by exact_mod_cast hm
  have hb := expectedYield_le m A B
  constructor <;> linarith

/-- Theorem 5.1's reverse protocol publishes a deterministic function of Alice's
hand. Given Bob's dealt card 0, hand (1,3) and message X are dependent.
The joint count times the conditioning count is 6, while the marginal-count
product is 2. This is the division-free conditional-independence test. -/
theorem reverse_message_leakage :
    (Finset.univ.filter fun k => shuffle k 0 = 1 ∧ shuffle k 1 = 3 ∧
      shuffle k 2 = 0 ∧ message k = 0).card *
      (Finset.univ.filter fun k => shuffle k 2 = 0).card ≠
    (Finset.univ.filter fun k => shuffle k 0 = 1 ∧ shuffle k 1 = 3 ∧
      shuffle k 2 = 0).card *
      (Finset.univ.filter fun k => shuffle k 2 = 0 ∧ message k = 0).card := by decide

end Cslib.Crypto.Tetrahedral
