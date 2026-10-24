/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.Bitwise.Projection
public import Complexity.Computability.WordRAM.Notation

/-!
# Checked correction boundaries

After finding the highest differing position, fusion-node correction replaces the query's
suffix by a sibling-subtree extreme. Both extremes and the original query bit are computed
without constructing the overflowing word `2^w`.

## Main definitions

* `BoundaryProgram.query`, `BoundaryProgram.position`, `BoundaryProgram.one`,
  `BoundaryProgram.next`, `BoundaryProgram.power`, `BoundaryProgram.low`, `BoundaryProgram.stem`,
  `BoundaryProgram.lower`, `BoundaryProgram.upper`, `BoundaryProgram.bit`: register indices for
  boundary computation.
* `BoundaryProgram.code`, `BoundaryProgram.result`: ten standard instructions computing both
  correction boundaries and the resulting machine state.

## Main results

* `BoundaryProgram.exec`: exact checked execution, including the top-bit case.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.BoundaryProgram

open Cslib.WordRAM Cslib.BitString

/-- Original query, preserved. -/
abbrev query : Fin 10 := 0
/-- Highest differing bit position, preserved. -/
abbrev position : Fin 10 := 1
/-- Constant one. -/
abbrev one : Fin 10 := 2
/-- Position immediately above the differing bit. -/
abbrev next : Fin 10 := 3
/-- The differing bit's power of two. -/
abbrev power : Fin 10 := 4
/-- Mask below the differing bit. -/
abbrev low : Fin 10 := 5
/-- Common stem followed by zeros. -/
abbrev stem : Fin 10 := 6
/-- All-ones extreme in the lower sibling subtree. -/
abbrev lower : Fin 10 := 7
/-- All-zeros extreme in the upper sibling subtree. -/
abbrev upper : Fin 10 := 8
/-- Zero or one according to the query's differing bit. -/
abbrev bit : Fin 10 := 9

/-- Compute both extremes and the bit selecting the correction convention. -/
def code : Code .standard 10 := ram[
  one ← #1;
  next ← position + one;
  power ← one <<< position;
  low ← power - one;
  stem ← query >>> next;
  stem ← stem <<< next;
  lower ← stem ||| low;
  upper ← stem ||| power;
  bit ← query >>> position;
  bit ← bit &&& one ]

/-- The precise output state, including all scratch registers. -/
def result (x : Data 10) (q p : ℕ) : Data 10 :=
  let a := (q >>> (p + 1)) <<< (p + 1)
  ((((((((((x.set one 1).set next (p + 1)).set power (2 ^ p)).set low
    (2 ^ p - 1)).set stem (q >>> (p + 1))).set stem a).set lower
    (lowerBoundary q p)).set upper (upperBoundary q p)).set bit (q >>> p)).set bit
    ((q >>> p) &&& 1))

/-- Ten checked instructions compute both sibling extremes and the selecting bit. The
position may be `w-1`; the program never materializes `2^w`. Query, position, and memory
are preserved. Finding the differing position is a separate operation. -/
theorem exec {w q p : ℕ} (x : Data 10) (hq : Fits w q) (hp : p < w)
    (hxq : x.regs query = q) (hxp : x.regs position = p) :
    Exec w code x (result x q p) 10 ∧
      (result x q p).regs lower = lowerBoundary q p ∧
      (result x q p).regs upper = upperBoundary q p ∧
      (result x q p).regs bit = ((q >>> p) &&& 1) ∧
      (result x q p).mem = x.mem := by
  have hw : 0 < w := by omega
  have h1 : Fits w 1 := by
    exact (by decide : 1 < 2 ^ 1).trans_le (Nat.pow_le_pow_right (by decide) hw)
  have hn : Fits w (p + 1) :=
    (show p + 1 ≤ w by omega).trans_lt Nat.lt_two_pow_self
  have hpower : Fits w (2 ^ p) := Nat.pow_lt_pow_right (by decide) hp
  have hlow : Fits w (2 ^ p - 1) := hpower.of_le (Nat.sub_le _ _)
  have hshift : Fits w (q >>> (p + 1)) := hq.of_le (by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_le_self _ _)
  have hprefix : Fits w ((q >>> (p + 1)) <<< (p + 1)) := hq.of_le (by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    exact Nat.div_mul_le_self _ _)
  have hlower : Fits w (lowerBoundary q p) := Nat.or_lt_two_pow hprefix hlow
  have hupper : Fits w (upperBoundary q p) := Nat.or_lt_two_pow hprefix hpower
  have hbitshift : Fits w (q >>> p) := hq.of_le (by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_le_self _ _)
  have hbit : Fits w ((q >>> p) &&& 1) := hbitshift.of_le Nat.and_le_left
  simp only [lowerBoundary, upperBoundary, Nat.shiftLeft_eq] at hprefix hlower hupper
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · ram_eval [code, result, hxq, hxp, lowerBoundary, upperBoundary,
      h1, hn, hpower, hlow, hshift, hprefix, hlower, hupper, hbitshift, hbit,
      Nat.shiftLeft_eq, one_mul]
  · simp +decide [result, one, next, power, low, stem, lower, upper, bit]
  · simp +decide [result, one, next, power, low, stem, lower, upper, bit]
  · simp +decide [result, one, next, power, low, stem, lower, upper, bit]

end Cslib.Algorithms.WordRAM.FusionTree.BoundaryProgram
