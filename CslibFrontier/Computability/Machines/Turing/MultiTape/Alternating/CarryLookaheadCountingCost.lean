/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCounting
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CountingTerminalCost

/-!
# Ordinary count bits with a separate predicate cost

The complete native finishing adder preserves the quantitative carry-save root certificate.
Long context serialization and the supplied predicate runtime enter additively, while the
routing overhead depends only on short metadata. No semantic operand bits are supplied.
-/

public section

namespace Turing.MultiTapeATM.CarryLookaheadCountingCost

open MultiTapeTM Cslib.Circuits.Boolean.CarrySaveQuery

/-- Finishing-adder overhead plus the native carry-save root clock at the predicate bound. -/
@[expose] def clock (c d cRoot dRoot : ℕ) (context : List Bool)
    (n w predicateTime : ℕ) : ℕ :=
  CarryLookaheadCounting.clockOfRoot c d w
    (CarrySaveCountingRootCost.clock cRoot dRoot context n w predicateTime)

/-- Context length and primitive runtime contribute linearly to the complete count clock. -/
theorem clock_eq_empty (c d cRoot dRoot : ℕ) (context : List Bool)
    (n w predicateTime : ℕ) :
    clock c d cRoot dRoot context n w predicateTime =
      clock c d cRoot dRoot [] n w 0 + (cRoot + 4) * context.length + cRoot * predicateTime := by
  simp only [clock, CarryLookaheadCounting.clockOfRoot, CarrySaveCountingRootCost.clock,
    CarrySaveCountingRoot.clockOfLeaf, CarrySaveLeafCost.clock, List.length_nil]
  ring

/-- A single finite native machine answers all count bits with the primitive predicate cost kept
separate. The supplied numeric bound covers every path allowed by the canonical root budget. -/
theorem exists_evaluator (predicate : List Bool × ℕ → Bool) {T W : List Bool × ℕ → ℕ}
    (hp : ComputableInO predicate (encPair encBits encNat) encBool T W) :
    ∃ (k r q : ℕ) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM (CarryLookaheadCountingLayout.size k r q) Bool S)
      (c d cRoot dRoot : ℕ),
      ∀ (input context : List Bool) (n w : ℕ) (bit : Fin w) (claim : Bool)
        (predicateTime : ℕ),
        (∀ path : List Bool, path.length ≤ CarrySaveCountingRoot.sizeBudget n w →
          T (context, Cslib.BitString.binaryValue path) ≤ predicateTime) →
        let start :=
          (CarryLookaheadCounting.initial k r q input context n w bit.val claim).withState
            (some atm.toPTM.initial)
        atm.HaltsWithin (clock c d cRoot dRoot context n w predicateTime) start ∧
          (atm.AcceptsWithin (clock c d cRoot dRoot context n w predicateTime) start ↔
            Counting.count n w (fun j => predicate (context, j)) bit = claim) := by
  obtain ⟨k, r, SL, hSL, terminal, cP, dP, cRoot, dRoot, hterminal⟩ :=
    CountingTerminalCost.exists_evaluator predicate hp
  let : Finite SL := hSL
  obtain ⟨q, S, hS, atm, c, d, h⟩ :=
    CarryLookaheadCounting.exists_evaluator_of_terminal predicate terminal cP dP
  refine ⟨k, r, q, S, hS, atm, c, d, cRoot, dRoot, ?_⟩
  intro input context n w bit claim predicateTime hpTime
  exact h input context n w (CarrySaveCountingRootCost.clock cRoot dRoot context n w predicateTime)
    (fun p hw => hterminal input context n w p hw predicateTime hpTime) bit claim

end Turing.MultiTapeATM.CarryLookaheadCountingCost
