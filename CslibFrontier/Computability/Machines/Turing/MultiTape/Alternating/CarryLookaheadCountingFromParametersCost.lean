/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingFromParameters
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingCost

/-!
# Quantitative count bits from raw parameters

The same native initializer feeds the count evaluator compiled from a primitive resource
certificate. Context serialization remains linear and the numeric predicate bound stays
separate from the polynomial work on short metadata. The initial storage contains just the
context and raw parameters; constructing those from an external input remains a separate phase.
-/

public section

namespace Turing.MultiTapeATM.CarryLookaheadCountingFromParametersCost

open MultiTapeTM Cslib.Circuits.Boolean.CarryLookahead.Query

/-- Native raw-parameter preparation followed by the quantitative complete count evaluator. -/
@[expose] def clock (cInit dInit c d cRoot dRoot : ℕ) (context : List Bool)
    (a : CountingInput.Input) (predicateTime : ℕ) : ℕ :=
  CarryLookaheadCountingFromParameters.clockOfEvaluator cInit dInit a
    (CarryLookaheadCountingCost.clock c d cRoot dRoot context a.count a.query.width predicateTime)

/-- Native initialization adds no context-dependent or predicate-time overhead. -/
theorem clock_eq_empty (cInit dInit c d cRoot dRoot : ℕ) (context : List Bool)
    (a : CountingInput.Input) (predicateTime : ℕ) :
    clock cInit dInit c d cRoot dRoot context a predicateTime =
      clock cInit dInit c d cRoot dRoot [] a 0 +
        (cRoot + 4) * context.length + cRoot * predicateTime := by
  unfold clock CarryLookaheadCountingFromParameters.clockOfEvaluator
  rw [CarryLookaheadCountingCost.clock_eq_empty]
  omega

/-- One finite native count-bit machine constructs its physical fields and retains the separate
primitive runtime bound. Every derived field starts blank, and all native phases are charged. -/
theorem exists_evaluator (predicate : List Bool × ℕ → Bool) {T W : List Bool × ℕ → ℕ}
    (hp : ComputableInO predicate (encPair encBits encNat) encBool T W) :
    ∃ (scratch k r q : ℕ) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch k r q) Bool S)
      (cInit dInit c d cRoot dRoot : ℕ),
      ∀ (input context : List Bool) (n w : ℕ) (bit : Fin w) (claim : Bool)
        (predicateTime : ℕ),
        (∀ path : List Bool, path.length ≤ CarrySaveCountingRoot.sizeBudget n w →
          T (context, Cslib.BitString.binaryValue path) ≤ predicateTime) →
        let a : CountingInput.Input := ⟨n, ⟨w, bit.val, claim⟩⟩
        let start := (CarryLookaheadCountingPrepare.initial scratch k r q input context a).withState
          (some atm.toPTM.initial)
        atm.HaltsWithin (clock cInit dInit c d cRoot dRoot context a predicateTime) start ∧
          (atm.AcceptsWithin (clock cInit dInit c d cRoot dRoot context a predicateTime) start ↔
            Cslib.Circuits.Boolean.CarrySaveQuery.Counting.count n w
              (fun j => predicate (context, j)) bit = claim) := by
  obtain ⟨k, r, q, S, hS, evaluator, c, d, cRoot, dRoot, hevaluator⟩ :=
    CarryLookaheadCountingCost.exists_evaluator predicate hp
  let : Finite S := hS
  obtain ⟨scratch, Q, hQ, atm, cInit, dInit, h⟩ :=
    CarryLookaheadCountingFromParameters.exists_evaluator_of_evaluator predicate evaluator
  refine ⟨scratch, k, r, q, Q, hQ, atm, cInit, dInit, c, d, cRoot, dRoot, ?_⟩
  intro input context n w bit claim predicateTime hpTime
  exact h input context n w bit claim
    (CarryLookaheadCountingCost.clock c d cRoot dRoot context n w predicateTime)
    (hevaluator input context n w bit claim predicateTime hpTime)

end Turing.MultiTapeATM.CarryLookaheadCountingFromParametersCost
