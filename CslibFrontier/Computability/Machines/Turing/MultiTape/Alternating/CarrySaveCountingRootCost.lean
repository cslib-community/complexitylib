/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveCountingCost
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveCountingRoot
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# Canonical count-root queries with a separate predicate cost

The same physical root layout and bit-independent traversal bound apply to the native evaluator
compiled from a plain resource certificate. Its clock remains linear in the context length,
polynomial in the short local fields, and linear in the supplied primitive predicate-time bound.
The bound explicitly covers all paths allowed by the shared size budget; no endpoint lookup or
initial storage construction is supplied for free.
-/

public section

namespace Turing.MultiTapeATM.CarrySaveCountingRootCost

open MultiTapeTM Cslib.Circuits.Boolean.CarrySaveQuery
open CarrySaveCountingRoot

/-- A common clock for all root-component bits and both claims at the supplied predicate bound. -/
@[expose] def clock (c d : ℕ) (context : List Bool) (n w predicateTime : ℕ) : ℕ :=
  clockOfLeaf
    (CarrySaveLeafCost.clock c d context (encNat n) (encNat w) (sizeBudget n w) predicateTime)
    n w

/-- One finite native family answers every bounded canonical count-root query. The predicate
certificate and a bound for its runtime are the only external computational assumptions. -/
theorem exists_evaluator (predicate : List Bool × ℕ → Bool) {T W : List Bool × ℕ → ℕ}
    (hp : ComputableInO predicate (encPair encBits encNat) encBool T W) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S)
      (atm : Bool → Bool → MultiTapeATM (k + 12) Bool S) (c d : ℕ),
      ∀ (input context : List Bool) (n w : ℕ) (bit : Fin w) (carry claim : Bool)
        (predicateTime : ℕ),
        (∀ path : List Bool, path.length ≤ sizeBudget n w →
          T (context, Cslib.BitString.binaryValue path) ≤ predicateTime) →
        let cfg := (initial k input context n w bit.val).withState
          (some (atm carry claim).toPTM.toNTM.q₀)
        (atm carry claim).HaltsWithin (clock c d context n w predicateTime) cfg ∧
          ((atm carry claim).AcceptsWithin (clock c d context n w predicateTime) cfg ↔
            component (Counting.rootPair n w (fun j => predicate (context, j))) carry bit =
              claim) := by
  obtain ⟨k, S, hS, atm, c, d, h⟩ := CarrySaveCountingCost.exists_evaluator predicate hp
  refine ⟨k, S, hS, atm, c, d, ?_⟩
  intro input context n w bit carry claim predicateTime hpTime
  apply spec_of_stream predicate input context n w bit carry claim
    (CarrySaveLeafCost.clock c d context (encNat n) (encNat w) (sizeBudget n w) predicateTime)
  exact h input context (encNat n) (encNat w)
    (encNat (Nat.clog 2 n)) (encNat bit.val) [] (encUnary (Nat.clog 2 n))
    (Nat.clog 2 n) 0 false carry claim (sizeBudget n w) predicateTime hpTime
    (initial_frontier n) (initial_size_le n w bit) (Cslib.BitString.lsbValue_bits _) (by simp)

end Turing.MultiTapeATM.CarrySaveCountingRootCost
