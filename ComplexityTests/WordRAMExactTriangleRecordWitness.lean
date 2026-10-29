/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.SourceBounds

/-!
# Actual candidate-consumer executions at valid thin geometry

These sparse-memory fixtures execute the full descriptor/root/query/verifier consumer at
`D=16`, `n=16^18`. They supply a post-product memory fixture, not a full producer/product run.
The initialized composition client is separate. No enormous encoder run is evaluated here.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMExactTriangleRecordWitness

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

private def side : ℕ := 16 ^ 18
private def queryBase : ℕ := 8 + 6 * (side * side)
private def records : ℕ := 23 + 12 * (side * side)
private def heap : ℕ := records + 6 + 2 * (side * 16)
private def answers : ℕ := heap + 100

private def fixture (success zeroAnswers : Bool) : Data 400 :=
  { regs := fun i => if i.val = 39 then records else if i.val = 42 then heap
      else if i.val = 64 then 0 else if i.val = 65 then answers else 77
    mem := fun a =>
      if a = 1 then 16 else if a = 2 then 1 else if a = 3 then side else if a = 4 then 3
      else if 5 ≤ a && a < 5 + side * side then
        if a = 5 + (side - 1) * side + (side - 2) ||
            a = 5 + (side - 1) * side + (side - 1) then 0 else Signed.encode 1
      else if 5 + side * side ≤ a && a < 5 + 2 * (side * side) then
        if success then 0 else Signed.encode 3
      else if records ≤ a && a < records + 6 then
        [0, 0, queryBase, 2, records + 6, records + 6 + side * 16].getD (a - records) 0
      else if a = queryBase then side - 1 else if a = queryBase + 1 then side - 2
      else if a = queryBase + 2 then side - 1 else if a = queryBase + 3 then side - 1
      else if a = answers || a = answers + 1 then if zeroAnswers then 0 else Signed.encode 4
      else if a = answers + 2 then 99 else 0 }

private def observe (success zeroAnswers : Bool) : Option (List ℕ × Bool × Bool) :=
  (RecordWitness.consume.eval 512 64 (fixture success zeroAnswers)).map fun (y, t) =>
    ([y.regs RecordWitness.Reg.found, y.regs RecordWitness.Reg.witnessA,
      y.regs RecordWitness.Reg.witnessB, y.regs RecordWitness.Reg.witnessC,
      y.regs RecordWitness.Reg.scans, y.regs RecordWitness.Reg.index, y.mem (answers + 2)],
      decide (t ≤ 20 + 16 + 196 * y.regs RecordWitness.Reg.scans + 52),
      decide (∀ j : Fin 320, y.regs (RecordWitness.productBank j) =
        (fixture success zeroAnswers).regs (RecordWitness.productBank j)))

-- The first pair succeeds; the second candidate incurs no further original-weight scan.
#guard observe true false == some ([1, side - 1, side - 2, 3, 1, 2, 99], true, true)

-- Both accepted modular candidates have original sum three, and both scans fail.
#guard observe false false == some ([0, 0, 0, 0, 2, 2, 99], true, true)

-- Zero answer words produce no verifier call, even though original weights have zero sums.
#guard observe true true == some ([0, 0, 0, 0, 0, 2, 99], true, true)

#guard side ≥ 16 ^ 18
#guard ¬(16 ≥ 16 ^ 18)

private def zeroWeights (N : ℕ) : List ℤ := List.replicate (3 * (N * N)) 0
private def width (N : ℕ) : ℕ := RecordWitness.admissionWidth N (D 2) 1 3 0

/-- All original-input premises are discharged at valid positive depth. The real initialized
producer/product/verifier returns an actual original witness in the same state as prefix and
halt. This symbolic kernel proof does not evaluate the enormous positive-depth encoder. -/
private theorem initialized_zero (N : ℕ) (hgeo : D 2 ^ 18 ≤ N) :
    ∃ y : Data 400, ∃ t S : ℕ,
      Runs (width N) (RecordWitness.entryProgram.program RecordWitness.Reg.found)
        (State.init (PreparationInput.input N (D 2) 1 3 (zeroWeights N)))
        ⟨RecordWitness.entryProgram.size, y⟩ t ∧
      Executes (width N) (RecordWitness.entryProgram.program RecordWitness.Reg.found)
        (State.init (PreparationInput.input N (D 2) 1 3 (zeroWeights N))) 1 (t + 1) ∧
      y.regs RecordWitness.Reg.found = 1 ∧ y.regs RecordWitness.Reg.scans = S ∧ S ≤ 1 ∧
      ∃ u v c : Fin N, y.regs RecordWitness.Reg.witnessA = u.val ∧
        y.regs RecordWitness.Reg.witnessB = v.val ∧ y.regs RecordWitness.Reg.witnessC = c.val := by
  have hprime : 3 ∈ Nat.sqrtPrimeWindow (D 2) :=
    Nat.mem_sqrtPrimeWindow_iff_sq.mpr ⟨by decide, by decide, by decide⟩
  have hmag : ∀ z ∈ zeroWeights N, z.natAbs ≤ 0 := by
    intro z hz
    have he : z = 0 := List.eq_of_mem_replicate hz
    subst z
    decide
  obtain ⟨hi, a, idx, ha, hout, hidx, hord, y, t, S, ht, hr, he, yb, ys, yf,
    hS, yiff, yw, frame, regs⟩ := RecordWitness.runs_input (m := 2) (n := N)
      (g := 1) (p := 3) (A := 0) (W := width N) (zeroWeights N)
      (by simp only [zeroWeights, List.length_replicate]) (by decide) (by decide)
      hprime hgeo hmag le_rfl
  let V := fun q => (zeroWeights N).getD q 0
  let wAB := fun u v : Fin N => V (pairIndex (u, v))
  let wBC := fun v c : Fin N => V (N * N + pairIndex (v, c))
  let wAC := fun u c : Fin N => V (2 * (N * N) + pairIndex (u, c))
  have hvalues (q : ℕ) : V q = 0 := by
    change (List.replicate (3 * (N * N)) (0 : ℤ))[q]?.getD 0 = 0
    exact List.getElem?_getD_replicate_default_eq _ _ _
  have hN : D 2 ≤ N := (Nat.le_self_pow (by decide : 18 ≠ 0) (D 2)).trans hgeo
  have hn : 0 < N := lt_of_lt_of_le (by decide : 0 < D 2) hN
  have hk := ((mem_instanceIndices wAB idx).mp hidx).1
  have hQ := RecordProduct.recordQueryCount_pos V (by decide : 3 ≠ 0)
    (by decide : 1 ≤ D 2) hN idx hidx
  have hcard := QuerySpec.card_residueClass wAB (by decide : 3 ≠ 0)
    (fun q => (V q % (3 : ℤ)).toNat) (by intro pair; rfl) idx.1
  have hpairs := (RecordProduct.output_query_coordinates V wAB (by decide)
    (by intro u v; rfl) (by decide) hN hout idx.1 idx.2.1 hk).2
  rw [hcard] at hpairs
  obtain ⟨pair, hpair, -⟩ := hpairs 0 hQ
  have hkzero : idx.2.2 = 0 := by
    exact (Nat.add_eq_zero_iff.mp hord).2
  let c : Fin N := ⟨0, hn⟩
  have hc : c ∈ piece N (D 2) 1 idx.2.2 := by
    rw [mem_piece, hkzero]
    exact Nat.zero_div _
  have hz : weightSum wAB wBC wAC pair.1 pair.2 c = 0 := by
    simp only [weightSum, wAB, wBC, wAC, hvalues, zero_add]
  have hfound : y.regs RecordWitness.Reg.found = 1 := yiff.mpr
    ⟨pair, hpair.1, c, hc, hz⟩
  have hfalse : falsePositiveCount wAB wBC wAC 3 = 0 := by
    simp only [falsePositiveCount, IsFalsePositive, weightSum, wAB, wBC, wAC, hvalues,
      zero_add, ne_eq, not_true_eq_false, false_and, Finset.filter_false, Finset.card_empty]
  obtain ⟨u, v, c, hu, hv, hc, -⟩ := yw hfound
  change S ≤ falsePositiveCount wAB wBC wAC 3 + y.regs RecordWitness.Reg.found at hS
  refine ⟨y, t, S, hr, ?_, hfound, ys, ?_, u, v, c, hu, hv, hc⟩
  · simpa only [hfound] using he
  · simpa only [hfalse, hfound, zero_add] using hS

example : ∃ y : Data 400, ∃ t S : ℕ,
    Runs (width side) (RecordWitness.entryProgram.program RecordWitness.Reg.found)
      (State.init (PreparationInput.input side (D 2) 1 3 (zeroWeights side)))
      ⟨RecordWitness.entryProgram.size, y⟩ t ∧
    Executes (width side) (RecordWitness.entryProgram.program RecordWitness.Reg.found)
      (State.init (PreparationInput.input side (D 2) 1 3 (zeroWeights side))) 1 (t + 1) ∧
    y.regs RecordWitness.Reg.found = 1 ∧ y.regs RecordWitness.Reg.scans = S ∧ S ≤ 1 ∧
    ∃ u v c : Fin side, y.regs RecordWitness.Reg.witnessA = u.val ∧
      y.regs RecordWitness.Reg.witnessB = v.val ∧ y.regs RecordWitness.Reg.witnessC = c.val :=
  initialized_zero side le_rfl

end ComplexityTests.WordRAMExactTriangleRecordWitness
