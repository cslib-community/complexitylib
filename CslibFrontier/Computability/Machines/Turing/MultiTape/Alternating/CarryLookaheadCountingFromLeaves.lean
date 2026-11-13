/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingClockBound
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# Complete native counting with alternating leaf continuations

A fixed family of actual alternating leaf machines can be used directly by the carry-save
controller, terminal dispatcher, finishing adder and raw-parameter initializer. Its running time
is added once, with coefficient one. No deterministic predicate compiler or normalization is
inserted around the supplied alternating continuation.

The leaf contracts describe the existing physical zero-layer layout, including padded counters,
path, frontier, and private storage. The machine is chosen before runtime data, leaf clocks, and
these contracts. This interface permits future recursive endpoint verifiers; it does not construct
such verifiers or supply the complete simulation's recursive resource analysis.
-/

public section

namespace Turing.MultiTapeATM.CarryLookaheadCountingFromLeaves

open MultiTapeTM Cslib.Circuits.Boolean.CarryLookahead.Query

/-- All raw preparation, finishing-adder, and carry-save traversal costs before the leaf. -/
@[expose] def overhead (cInit dInit c d : ℕ) (a : CountingInput.Input) : ℕ :=
  CarryLookaheadCountingFromParameters.clockOfEvaluator cInit dInit a
    (CarryLookaheadCounting.clockOfRoot c d a.query.width
      (CarrySaveCountingRoot.clockOfLeaf 0 a.count a.query.width))

/-- Native composition retains the leaf clock with coefficient exactly one. -/
theorem clock_eq_overhead_add (cInit dInit c d : ℕ) (a : CountingInput.Input)
    (leafTime : ℕ) :
    CarryLookaheadCountingFromParameters.clockOfEvaluator cInit dInit a
      (CarryLookaheadCounting.clockOfRoot c d a.query.width
        (CarrySaveCountingRoot.clockOfLeaf leafTime a.count a.query.width)) =
      overhead cInit dInit c d a + leafTime := by
  simp only [overhead, CarryLookaheadCountingFromParameters.clockOfEvaluator,
    CarryLookaheadCounting.clockOfRoot, CarrySaveCountingRoot.clockOfLeaf]
  omega

/-- The nonleaf cost is polynomial only in the binary count and precision lengths. -/
theorem exists_overhead_le (cInit dInit c d : ℕ) :
    ∃ A D : ℕ, ∀ (a : CountingInput.Input), a.query.bit < a.query.width →
      overhead cInit dInit c d a ≤ A * (a.count.size + a.query.width.size + 1) ^ D := by
  obtain ⟨A, D, h⟩ :=
    CarryLookaheadCountingFromParametersCost.exists_clock_le cInit dInit c d 0 0
  refine ⟨A, D, fun a ha => ?_⟩
  have hb := h [] a 0 ha
  have hm : overhead cInit dInit c d a ≤
      CarryLookaheadCountingFromParametersCost.clock cInit dInit c d 0 0 [] a 0 := by
    simp only [overhead, CarryLookaheadCountingFromParameters.clockOfEvaluator,
      CarryLookaheadCounting.clockOfRoot, CarrySaveCountingRoot.clockOfLeaf,
      CarryLookaheadCountingFromParametersCost.clock, CarryLookaheadCountingCost.clock,
      CarrySaveCountingRootCost.clock, CarrySaveLeafCost.clock, Nat.zero_mul]
    omega
  exact hm.trans (by simpa only [List.length_nil, Nat.zero_add, Nat.add_zero] using hb)

private theorem root_spec {k : ℕ} {S : Type}
    (leaf : Bool → Bool → MultiTapeATM (k + 12) Bool S)
    (predicate : List Bool × ℕ → Bool) (input context : List Bool) (n w leafTime : ℕ)
    (ht : CarrySaveStream.LeafBound leaf leafTime (CarrySaveCountingRoot.sizeBudget n w) input
      (CarrySaveLeaf.scratch k context (encNat n) (encNat w)))
    (ha : CarrySaveStream.LeafCorrect
      (CarrySaveCounting.leaves predicate context (encNat n) (encNat w)) leaf leafTime
      (CarrySaveCountingRoot.sizeBudget n w) input
      (CarrySaveLeaf.scratch k context (encNat n) (encNat w)))
    (bit : Fin w) (carry claim : Bool) :
    let roots := CarrySaveStream.machine leaf
    let cfg := (CarrySaveCountingRoot.initial k input context n w bit.val).withState
      (some (roots carry claim).toPTM.initial)
    (roots carry claim).HaltsWithin (CarrySaveCountingRoot.clockOfLeaf leafTime n w) cfg ∧
      ((roots carry claim).AcceptsWithin (CarrySaveCountingRoot.clockOfLeaf leafTime n w) cfg ↔
        Cslib.Circuits.Boolean.CarrySaveQuery.component
          (Cslib.Circuits.Boolean.CarrySaveQuery.Counting.rootPair n w
            (fun j => predicate (context, j))) carry bit = claim) := by
  apply CarrySaveCountingRoot.spec_of_stream predicate input context n w bit carry claim leafTime
  exact CarrySaveCounting.spec_of_leaves leaf predicate input context (encNat n) (encNat w)
    leafTime (CarrySaveCountingRoot.sizeBudget n w) ht ha
    (encNat (Nat.clog 2 n)) (encNat bit.val) [] (encUnary (Nat.clog 2 n))
    (Nat.clog 2 n) 0 false carry claim (CarrySaveCountingRoot.initial_frontier n)
    (CarrySaveCountingRoot.initial_size_le n w bit) (Cslib.BitString.lsbValue_bits _)
    (by simpa only [encNat_apply, Cslib.BitString.lsbValue_bits, ofBits_bits] using bit.isLt)

/-- One common finite machine counts through actual alternating leaves. Every field is prepared
from the raw record, and the supplied leaf clock is charged once after the fixed native overhead. -/
theorem exists_evaluator_exact (predicate : List Bool × ℕ → Bool) {k : ℕ} {S : Type}
    [Finite S] (leaf : Bool → Bool → MultiTapeATM (k + 12) Bool S) :
    ∃ (scratch r q : ℕ) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch k r q) Bool Q)
      (cInit dInit c d : ℕ),
      ∀ (input context : List Bool) (n w : ℕ) (bit : Fin w) (claim : Bool) (leafTime : ℕ),
        CarrySaveStream.LeafBound leaf leafTime (CarrySaveCountingRoot.sizeBudget n w) input
          (CarrySaveLeaf.scratch k context (encNat n) (encNat w)) →
        CarrySaveStream.LeafCorrect
          (CarrySaveCounting.leaves predicate context (encNat n) (encNat w)) leaf leafTime
          (CarrySaveCountingRoot.sizeBudget n w) input
          (CarrySaveLeaf.scratch k context (encNat n) (encNat w)) →
        let a : CountingInput.Input := ⟨n, ⟨w, bit.val, claim⟩⟩
        let start := (CarryLookaheadCountingPrepare.initial scratch k r q input context a).withState
          (some atm.toPTM.initial)
        atm.HaltsWithin (overhead cInit dInit c d a + leafTime) start ∧
          (atm.AcceptsWithin (overhead cInit dInit c d a + leafTime) start ↔
            Cslib.Circuits.Boolean.CarrySaveQuery.Counting.count n w
              (fun j => predicate (context, j)) bit = claim) := by
  let := Fintype.ofFinite S
  let roots := CarrySaveStream.machine leaf
  obtain ⟨r, ST, hST, terminal, cP, dP, hterminal⟩ :=
    CountingTerminal.exists_evaluator_of_root predicate roots
  let : Finite ST := hST
  obtain ⟨q, SE, hSE, evaluator, c, d, hevaluator⟩ :=
    CarryLookaheadCounting.exists_evaluator_of_terminal predicate terminal cP dP
  let : Finite SE := hSE
  obtain ⟨scratch, Q, hQ, atm, cInit, dInit, h⟩ :=
    CarryLookaheadCountingFromParameters.exists_evaluator_of_evaluator predicate evaluator
  refine ⟨scratch, r, q, Q, hQ, atm, cInit, dInit, c, d, ?_⟩
  intro input context n w bit claim leafTime ht ha
  have hr := hterminal input context n w (CarrySaveCountingRoot.clockOfLeaf leafTime n w)
    (root_spec leaf predicate input context n w leafTime ht ha)
  have he := hevaluator input context n w (CarrySaveCountingRoot.clockOfLeaf leafTime n w)
    hr bit claim
  have hf := h input context n w bit claim
    (CarryLookaheadCounting.clockOfRoot c d w
      (CarrySaveCountingRoot.clockOfLeaf leafTime n w)) he
  dsimp only at hf ⊢
  rwa [clock_eq_overhead_add] at hf

/-- The complete raw-parameter machine retains a supplied alternating leaf clock additively,
with polynomial overhead in binary parameter length. Its acceptance is the actual sum bit. -/
theorem exists_evaluator (predicate : List Bool × ℕ → Bool) {k : ℕ} {S : Type}
    [Finite S] (leaf : Bool → Bool → MultiTapeATM (k + 12) Bool S) :
    ∃ (scratch r q : ℕ) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch k r q) Bool Q) (A D : ℕ),
      ∀ (input context : List Bool) (n w : ℕ) (bit : Fin w) (claim : Bool) (leafTime : ℕ),
        CarrySaveStream.LeafBound leaf leafTime (CarrySaveCountingRoot.sizeBudget n w) input
          (CarrySaveLeaf.scratch k context (encNat n) (encNat w)) →
        CarrySaveStream.LeafCorrect
          (CarrySaveCounting.leaves predicate context (encNat n) (encNat w)) leaf leafTime
          (CarrySaveCountingRoot.sizeBudget n w) input
          (CarrySaveLeaf.scratch k context (encNat n) (encNat w)) →
        let a : CountingInput.Input := ⟨n, ⟨w, bit.val, claim⟩⟩
        let start := (CarryLookaheadCountingPrepare.initial scratch k r q input context a).withState
          (some atm.toPTM.initial)
        let time := A * (n.size + w.size + 1) ^ D + leafTime
        atm.HaltsWithin time start ∧
          (atm.AcceptsWithin time start ↔
            (∑ j ∈ Finset.range n, (predicate (context, j)).toNat).testBit bit.val = claim) := by
  obtain ⟨scratch, r, q, Q, hQ, atm, cInit, dInit, c, d, h⟩ :=
    exists_evaluator_exact predicate leaf
  obtain ⟨A, D, hbound⟩ := exists_overhead_le cInit dInit c d
  refine ⟨scratch, r, q, Q, hQ, atm, A, D, ?_⟩
  intro input context n w bit claim leafTime ht ha
  obtain ⟨hh, hv⟩ := h input context n w bit claim leafTime ht ha
  have hb := Nat.add_le_add_right (hbound ⟨n, ⟨w, bit.val, claim⟩⟩ bit.isLt) leafTime
  refine ⟨hh.mono hb, ?_⟩
  rw [Cslib.Circuits.Boolean.CarrySaveQuery.Counting.count_apply] at hv
  exact ⟨fun h => hv.mp (h.of_halted_stepCoins hh), fun h => (hv.mpr h).mono hb⟩

end Turing.MultiTapeATM.CarryLookaheadCountingFromLeaves
