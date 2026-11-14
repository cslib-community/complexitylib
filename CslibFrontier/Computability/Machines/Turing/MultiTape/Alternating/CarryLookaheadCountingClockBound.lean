/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingFromParametersCost

/-!
# A binary-length bound for the complete native count clock

The clock for preparation, the finishing adder and the carry-save traversal is linear in the
context length and the separately supplied primitive predicate time. Its remaining cost is a
polynomial in the binary lengths of the count and precision. The queried bit is below the
precision, so its encoding does not introduce another size parameter.

The final corollary gives one finite native machine with this bound and the actual predicate
sum's bit as its acceptance condition, including counts that exceed the requested precision.
It does not supply the predicate's endpoint-access bound or the external construction of the
context and raw parameter words.
-/

public section

namespace Turing.MultiTapeATM.CarryLookaheadCountingFromParametersCost

open MultiTapeTM Cslib.Circuits.Boolean.CarryLookahead.Query

/-- For any fixed compiler constants, the complete native clock is linear in context and
primitive predicate time, with a polynomial overhead in the count and width's binary lengths. -/
theorem exists_clock_le (cInit dInit c d cRoot dRoot : ℕ) :
    ∃ A D : ℕ, ∀ (context : List Bool) (a : CountingInput.Input) (predicateTime : ℕ),
      a.query.bit < a.query.width →
      clock cInit dInit c d cRoot dRoot context a predicateTime ≤
        A * (context.length + (a.count.size + a.query.width.size + 1) ^ D + predicateTime) := by
  let P := fun m : ℕ => cInit * (4 * m + 5) ^ dInit +
    (2 * m + 6) * (c * (10 * m + 27) ^ d + 2) + c * (10 * m + 27) ^ d +
      (58 * m + 23 + cRoot * ((3 * m + 2) ^ dRoot + 1)) + 1
  have hpoly : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
  obtain ⟨A, D, hP⟩ := Cslib.polynomiallyBounded_iff_le.mp hpoly
  have hempty (a : CountingInput.Input) (hbit : a.query.bit < a.query.width) :
      clock cInit dInit c d cRoot dRoot [] a 0 ≤ P (a.count.size + a.query.width.size) := by
    let m := a.count.size + a.query.width.size
    have hn : Nat.clog 2 a.count ≤ a.count.size :=
      Nat.clog_le_of_le_pow (Nat.lt_size_self a.count).le
    have hh : (Nat.clog 2 a.count).size ≤ a.count.size :=
      (Nat.size_le_self _).trans hn
    have hw : Nat.clog 2 (a.query.width + 1) ≤ a.query.width.size :=
      Nat.clog_le_of_le_pow (Nat.succ_le_of_lt (Nat.lt_size_self a.query.width))
    have hb : CarrySaveCountingRoot.sizeBudget a.count a.query.width ≤ 2 * m := by
      unfold CarrySaveCountingRoot.sizeBudget m
      omega
    have hrpow : (a.count.size + a.query.width.size +
        CarrySaveCountingRoot.sizeBudget a.count a.query.width + 2) ^ dRoot ≤
          (3 * m + 2) ^ dRoot :=
      Nat.pow_le_pow_left (by dsimp only [m] at *; omega) dRoot
    have hrmul := Nat.mul_le_mul_left cRoot (Nat.add_le_add_right hrpow 1)
    have hroot : CarrySaveCountingRootCost.clock cRoot dRoot [] a.count a.query.width 0 ≤
        58 * m + 23 + cRoot * ((3 * m + 2) ^ dRoot + 1) := by
      simp only [CarrySaveCountingRootCost.clock, CarrySaveCountingRoot.clockOfLeaf,
        CarrySaveLeafCost.clock, List.length_nil, encNat_apply, Nat.size_eq_bits_len,
        Nat.zero_add, Nat.add_zero]
      dsimp only [m] at *
      omega
    have ho : CarryLookaheadCounting.overhead c d a.query.width ≤ c * (10 * m + 27) ^ d := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      unfold CarryLookaheadCounting.metadataBound m
      omega
    have hsteps : (2 * Nat.clog 2 (a.query.width + 1) + 6) *
        (CarryLookaheadCounting.overhead c d a.query.width + 2) ≤
          (2 * m + 6) * (c * (10 * m + 27) ^ d + 2) :=
      Nat.mul_le_mul (by dsimp only [m]; omega) (Nat.add_le_add_right ho 2)
    have hi : cInit * ((CountingInput.encInput a).length + 1) ^ dInit ≤
        cInit * (4 * m + 5) ^ dInit := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      have he := CountingInput.length_encInput_le a hbit
      dsimp only [m]
      omega
    simp only [clock, CarryLookaheadCountingFromParameters.clockOfEvaluator,
      CarryLookaheadCountingCost.clock, CarryLookaheadCounting.clockOfRoot]
    dsimp only [P, m] at *
    omega
  refine ⟨A + cRoot + 4, D, ?_⟩
  intro context a predicateTime hbit
  rw [clock_eq_empty]
  have hbase := (hempty a hbit).trans (hP (a.count.size + a.query.width.size))
  have hp := Nat.mul_le_mul_right ((a.count.size + a.query.width.size + 1) ^ D)
    (show A ≤ A + cRoot + 4 by omega)
  have hc := Nat.mul_le_mul_right context.length (show cRoot + 4 ≤ A + cRoot + 4 by omega)
  have ht := Nat.mul_le_mul_right predicateTime (show cRoot ≤ A + cRoot + 4 by omega)
  calc
    _ ≤ (A + cRoot + 4) * (a.count.size + a.query.width.size + 1) ^ D +
        (A + cRoot + 4) * context.length + (A + cRoot + 4) * predicateTime :=
      Nat.add_le_add (Nat.add_le_add (hbase.trans hp) hc) ht
    _ = _ := by ring

/-- One finite native machine tests each bit of the actual predicate sum, with time linear in
context length and the primitive predicate bound, plus polynomial binary-parameter overhead.
The machine and both bounding constants are independent of all runtime inputs and claims. -/
theorem exists_evaluator_testBit (predicate : List Bool × ℕ → Bool)
    {T W : List Bool × ℕ → ℕ}
    (hp : ComputableInO predicate (encPair encBits encNat) encBool T W) :
    ∃ (scratch k r q : ℕ) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch k r q) Bool S) (A D : ℕ),
      ∀ (input context : List Bool) (n w : ℕ) (bit : Fin w) (claim : Bool)
        (predicateTime : ℕ),
        (∀ path : List Bool, path.length ≤ CarrySaveCountingRoot.sizeBudget n w →
          T (context, Cslib.BitString.binaryValue path) ≤ predicateTime) →
        let a : CountingInput.Input := ⟨n, ⟨w, bit.val, claim⟩⟩
        let start := (CarryLookaheadCountingPrepare.initial scratch k r q input context a).withState
          (some atm.toPTM.initial)
        let time := A * (context.length + (n.size + w.size + 1) ^ D + predicateTime)
        atm.HaltsWithin time start ∧
          (atm.AcceptsWithin time start ↔
            (∑ j ∈ Finset.range n, (predicate (context, j)).toNat).testBit bit.val = claim) := by
  obtain ⟨scratch, k, r, q, S, hS, atm, cInit, dInit, c, d, cRoot, dRoot, h⟩ :=
    exists_evaluator predicate hp
  obtain ⟨A, D, hbound⟩ := exists_clock_le cInit dInit c d cRoot dRoot
  refine ⟨scratch, k, r, q, S, hS, atm, A, D, ?_⟩
  intro input context n w bit claim predicateTime htime
  obtain ⟨hh, ha⟩ := h input context n w bit claim predicateTime htime
  have hb := hbound context ⟨n, ⟨w, bit.val, claim⟩⟩ predicateTime bit.isLt
  refine ⟨hh.mono hb, ?_⟩
  rw [Cslib.Circuits.Boolean.CarrySaveQuery.Counting.count_apply] at ha
  exact ⟨fun h => ha.mp (h.of_halted_stepCoins hh), fun h => (ha.mpr h).mono hb⟩

end Turing.MultiTapeATM.CarryLookaheadCountingFromParametersCost
