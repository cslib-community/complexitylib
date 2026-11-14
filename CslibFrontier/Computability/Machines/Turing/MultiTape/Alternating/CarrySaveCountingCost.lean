/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveCounting
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeafCost

/-!
# Counting traversal with a separate primitive predicate cost

One finite alternating machine evaluates physical carry-save queries with the stream controller's
amortized clock. The context contributes linearly to the leaf clock, local counters contribute a
polynomial in their lengths, and a separate bound covers primitive predicate evaluation at every
bounded path. Claim checking reuses the exact native leaf contract and adds no transitions.
-/

public noncomputable section

namespace Turing.MultiTapeATM.CarrySaveCountingCost

open MultiTapeTM Cslib.Circuits.Boolean.CarrySaveQuery
open CarrySaveCounting

/-- Native leaves satisfy both physical stream contracts while retaining a separate bound on
the primitive predicate. The bound covers every path admitted by the controller's size budget. -/
theorem exists_leaves (predicate : List Bool × ℕ → Bool) {T W : List Bool × ℕ → ℕ}
    (hp : ComputableInO predicate (encPair encBits encNat) encBool T W) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S)
      (leaf : Bool → Bool → MultiTapeATM (k + 12) Bool S) (c d : ℕ),
      ∀ (input context count width : List Bool) (sizeBudget predicateTime : ℕ),
        (∀ path : List Bool, path.length ≤ sizeBudget →
          T (context, Cslib.BitString.binaryValue path) ≤ predicateTime) →
        CarrySaveStream.LeafBound leaf
          (CarrySaveLeafCost.clock c d context count width sizeBudget predicateTime)
          sizeBudget input (CarrySaveLeaf.scratch k context count width) ∧
        CarrySaveStream.LeafCorrect (leaves predicate context count width) leaf
          (CarrySaveLeafCost.clock c d context count width sizeBudget predicateTime)
          sizeBudget input (CarrySaveLeaf.scratch k context count width) := by
  obtain ⟨k, S, hS, native, c, d, hr⟩ := CarrySaveLeafCost.exists_counting predicate hp
  refine ⟨k, S, hS, claimLeaf native, c, d, ?_⟩
  intro input context count width sizeBudget predicateTime htime
  apply leaf_contracts native predicate input context count width
    (CarrySaveLeafCost.clock c d context count width sizeBudget predicateTime) sizeBudget
  intro height bits path unary frontier status carry hsize
  exact hr input context count width height bits path unary frontier status carry
    sizeBudget predicateTime (by omega) (htime path (by omega))

/-- A primitive plain resource certificate yields one finite carry-save counting evaluator.
Its exact common clock charges the whole traversal plus context-linear serialization, local
counter arithmetic and the supplied primitive-time bound. Preparing the initial tapes remains
a separate operation. No whole-query polynomial envelope is introduced. -/
theorem exists_evaluator (predicate : List Bool × ℕ → Bool) {T W : List Bool × ℕ → ℕ}
    (hp : ComputableInO predicate (encPair encBits encNat) encBool T W) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S)
      (atm : Bool → Bool → MultiTapeATM (k + 12) Bool S) (c d : ℕ),
      ∀ (input context count width height bits path unary : List Bool)
        (depth : ℕ) (frontier : ℤ) (status carry claim : Bool)
        (sizeBudget predicateTime : ℕ),
        (∀ path : List Bool, path.length ≤ sizeBudget →
          T (context, Cslib.BitString.binaryValue path) ≤ predicateTime) →
        CarrySaveStream.Frontier unary frontier depth →
        height.length + bits.length + path.length + depth ≤ sizeBudget →
        Cslib.BitString.lsbValue height = depth →
        Cslib.BitString.lsbValue bits < ofBits width →
        let cfg := (CarrySaveLeaf.initial k input context count width height bits path unary
          frontier status).withState (some (atm carry claim).toPTM.toNTM.q₀)
        let time := CarrySaveStream.budget
          (CarrySaveLeafCost.clock c d context count width sizeBudget predicateTime)
          depth height bits
        (atm carry claim).HaltsWithin time cfg ∧
        ((atm carry claim).AcceptsWithin time cfg ↔
          value (leaves predicate context count width)
            ⟨path, depth, carry, Cslib.BitString.lsbValue bits⟩ = claim) := by
  obtain ⟨k, S, hS, leaf, c, d, hl⟩ := exists_leaves predicate hp
  let := hS
  let := Fintype.ofFinite S
  refine ⟨k, CarrySaveStream.State S, inferInstance, CarrySaveStream.machine leaf, c, d, ?_⟩
  intro input context count width height bits path unary depth frontier status carry claim
    sizeBudget predicateTime htime hfront hsize hheight hbits
  obtain ⟨ht, ha⟩ := hl input context count width sizeBudget predicateTime htime
  exact spec_of_leaves leaf predicate input context count width _ sizeBudget ht ha height bits
    path unary depth frontier status carry claim hfront hsize hheight hbits

end Turing.MultiTapeATM.CarrySaveCountingCost
