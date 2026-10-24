/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
public import Complexity.Algorithms.Lean.FusionTree.Correction
import Mathlib.Algebra.BigOperators.Fin

/-!
# Two-child node search

Below the large-width fusion threshold, the tree branches in two. Direct comparison of
the two child minima supplies a uniform constant-time fallback. The eighteen-word header
and interleaved key/pointer table use the same layout as larger nodes.

## Main definitions

* `BinaryNodeProgram.registers`, `BinaryNodeProgram.query`, `BinaryNodeProgram.pointer`,
  `BinaryNodeProgram.out`, `BinaryNodeProgram.two`, `BinaryNodeProgram.offset`,
  `BinaryNodeProgram.address`, `BinaryNodeProgram.first`, `BinaryNodeProgram.second`: register
  allocation for the two-child node search.
* `BinaryNodeProgram.code`: actual two-child node search.
* `BinaryNodeProgram.rank`, `BinaryNodeProgram.result`: the inclusive rank among two keys and the
  resulting machine data.

## Main results

* `BinaryNodeProgram.exec`: execution in at most eleven standard instructions.
* `BinaryNodeProgram.rank_eq`: the computed value is the inclusive full-key rank.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.BinaryNodeProgram

open Cslib.WordRAM
open Cslib.Algorithms.Lean.FusionTree

/-- The register interface agrees with the larger fusion-node query. -/
abbrev registers : ℕ := 1024
/-- Bounded query, preserved. -/
abbrev query : Fin registers := 0
/-- Record base, preserved. -/
abbrev pointer : Fin registers := 1
/-- Final inclusive rank, zero, one, or two. -/
abbrev out : Fin registers := 2
/-- Distance between the two child minima. -/
abbrev two : Fin registers := 3
/-- Offset of the child table. -/
abbrev offset : Fin registers := 4
/-- Address scratch. -/
abbrev address : Fin registers := 5
/-- First child minimum. -/
abbrev first : Fin registers := 6
/-- Second child minimum. -/
abbrev second : Fin registers := 7

/-- Two direct full-key comparisons, with charged constants and memory loads. -/
def code : Code .standard registers := ram[
  two ← #2;
  offset ← #18;
  address ← pointer + offset;
  first ← *address;
  address ← address + two;
  second ← *address;
  if query < first then [ out ← #0 ] else [
    if query < second then [ out ← #1 ] else [ out ← #2 ]
  ] ]

/-- The inclusive rank among two increasing full keys. -/
def rank (q a b : ℕ) : ℕ := if q < a then 0 else if q < b then 1 else 2

/-- Exact data after reading both minima and returning their rank. -/
def result (x : Data registers) : Data registers :=
  let p := x.regs pointer
  let a := x.mem (p + 18)
  let b := x.mem (p + 20)
  (((((((x.set two 2).set offset 18).set address (p + 18)).set first a).set address
    (p + 20)).set second b).set out (rank (x.regs query) a b))

/-- The direct comparison expression equals inclusive rank, with equality counted. -/
theorem rank_eq {q a b : ℕ} (hab : a < b) : rank q a b = upperRank ![a, b] q := by
  simp only [rank, upperRank, Finset.card_filter, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases ha : q < a
  · have hb := ha.trans hab
    simp [ha, Nat.not_le.mpr ha, Nat.not_le.mpr hb]
  · have hqa : a ≤ q := by omega
    by_cases hb : q < b
    · simp [ha, hb, hqa, Nat.not_le.mpr hb]
    · have hqb : b ≤ q := by omega
      simp [ha, hb, hqa, hqb]

/-- Eleven instructions suffice for the binary fallback. All address and constant bounds
follow from the address of the second key; all memory, query, and record base are preserved.
Only registers two through seven change. -/
theorem exec {w : ℕ} (x : Data registers) (ha : Fits w (x.regs pointer + 20)) :
    ExecWithin w code x (result x) 11 ∧ (result x).mem = x.mem ∧
      (result x).regs out = rank (x.regs query)
        (x.mem (x.regs pointer + 18)) (x.mem (x.regs pointer + 20)) := by
  have h0 := fits_zero w
  have h1 : Fits w 1 := ha.of_le (by omega)
  have h2 : Fits w 2 := ha.of_le (by omega)
  have h18 : Fits w 18 := ha.of_le (by omega)
  have hp18 : Fits w (x.regs pointer + 18) := ha.of_le (by omega)
  have hp20 : Fits w (x.regs pointer + 18 + 2) := by simpa only [Nat.add_assoc] using ha
  have hresult : (result x).regs out = rank (x.regs query)
      (x.mem (x.regs pointer + 18)) (x.mem (x.regs pointer + 20)) := by
    simp only [result, Data.set_regs, Function.update_self]
  refine ⟨?_, rfl, hresult⟩
  by_cases hfirst : x.regs query < x.mem (x.regs pointer + 18)
  · refine ⟨8, by omega, ?_⟩
    ram_eval [code, result, rank, h0, h1, h2, h18, hp18, hp20, hfirst, Nat.add_assoc]
  · by_cases hsecond : x.regs query < x.mem (x.regs pointer + 20)
    · refine ⟨10, by omega, ?_⟩
      ram_eval [code, result, rank, h0, h1, h2, h18, hp18, hp20, hfirst, hsecond, Nat.add_assoc]
    · refine ⟨11, le_rfl, ?_⟩
      ram_eval [code, result, rank, h0, h1, h2, h18, hp18, hp20, hfirst, hsecond, Nat.add_assoc]

end Cslib.Algorithms.WordRAM.FusionTree.BinaryNodeProgram
