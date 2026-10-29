/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Spec
import Complexity.Computability.WordRAM.RegisterFrame

/-!
# Real coordinate delivery, verifier calls and witness returns

The internal call rule invokes the complete native signed-weight verifier, preserves the
controller and old product bank, and returns its original zero-sum vertex. Query delivery
loads the actual interleaved words and increments the actual scan counter. No run or witness
routine is supplied by a caller.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM

private abbrev Stable (i : Fin 400) : Prop :=
  i.val < 326 ∨ i = Reg.one ∨ i = Reg.zero ∨
    (345 ≤ i.val ∧ i.val ≤ 348) ∨ (351 ≤ i.val ∧ i.val ≤ 352)

-- These closed checks enumerate only the finite caller bank and loop-free delivery/return code.
set_option maxRecDepth 4096 in
private theorem deliverPair_preserves : ∀ i : Fin 400, Stable i → deliverPair.Preserves i := by
  decide

-- The same finite controller-frame check, without unfolding the verifier program.
set_option maxRecDepth 4096 in
private theorem receiveWitness_preserves : ∀ i : Fin 400, Stable i →
    receiveWitness.Preserves i := by decide

private theorem scanBank_injective : Function.Injective scanBank := by
  intro i j h
  apply Fin.ext
  simpa only [scanBank, Nat.add_left_cancel_iff] using congrArg Fin.val h

/-- Execute the real original-weight verifier on the disjoint bank. Every scanned weight
comes from the original arrays; a nonzero product answer supplies no original-weight witness. -/
theorem exec_scan {w U n first length out queries count a b : ℕ}
    (AB BC AC : ℕ → ℕ → ℤ) (x : Data 400)
    (hx : Fixed n first length out queries count x)
    (hargA : x.regs (scanBank WitnessScan.Reg.a) = a)
    (hargB : x.regs (scanBank WitnessScan.Reg.b) = b)
    (ha : a < n) (hb : b < n) (hc : first + length ≤ n)
    (hmem : ∀ i < n, ∀ j < n,
      x.mem (5 + (i * n + j)) = Signed.encode (AB i j) ∧
      x.mem (5 + n * n + (i * n + j)) = Signed.encode (BC i j) ∧
      x.mem (5 + n * n + n * n + (i * n + j)) = Signed.encode (AC i j))
    (hmag : ∀ i < n, ∀ j < n,
      (AB i j).natAbs ≤ U ∧ (BC i j).natAbs ≤ U ∧ (AC i j).natAbs ≤ U)
    (hU : GenericRAM.Signed.Fits w (2 * U : ℕ))
    (hfit : Fits (w + 2) (6 * (n * n) + n + first + length + 24)) :
    ∃ y, ExecWithin (w + 2) scan x y (42 * length + 17) ∧
      Fixed n first length out queries count y ∧ y.mem = x.mem ∧
      y.regs (scanBank WitnessScan.Reg.a) = a ∧
      y.regs (scanBank WitnessScan.Reg.b) = b ∧
      (y.regs (scanBank WitnessScan.Reg.found) = 0 ∨
        y.regs (scanBank WitnessScan.Reg.found) = 1) ∧
      (y.regs (scanBank WitnessScan.Reg.found) = 1 ↔
        ∃ c, first ≤ c ∧ c < first + length ∧ AB a b + BC b c + AC a c = 0) ∧
      (y.regs (scanBank WitnessScan.Reg.found) = 1 →
        first ≤ y.regs (scanBank WitnessScan.Reg.witness) ∧
        y.regs (scanBank WitnessScan.Reg.witness) < first + length ∧
        AB a b + BC b (y.regs (scanBank WitnessScan.Reg.witness)) +
          AC a (y.regs (scanBank WitnessScan.Reg.witness)) = 0) ∧
      ∀ i : Fin 400, i.val < 336 ∨ 368 ≤ i.val → y.regs i = x.regs i := by
  let A : WitnessScan.Args := ⟨5, 5 + n * n, 5 + n * n + n * n, n, a, b, first, length⟩
  have hargs : A.InRegisters (x.comap scanBank) :=
    ⟨hx.ab, hx.bc, hx.ac, hx.scanSize, hargA, hargB, hx.scanFirst, hx.scanLength⟩
  obtain ⟨s, hs, sa, sm, sf, si, sw⟩ := WitnessScan.exec A AB BC AC (x.comap scanBank)
    hargs ha hb hc hmem hmag hU (hfit.of_le (by
      dsimp only [A, WitnessScan.Args.addressBound]; omega))
  let y := s.extend scanBank x
  have he : ExecWithin (w + 2) scan x y (42 * length + 17) := hs.rename scanBank_injective
  have yr (i : Fin 32) : y.regs (scanBank i) = s.regs i :=
    scanBank_injective.extend_apply _ _ i
  have frame (i : Fin 400) (hi : i.val < 336 ∨ 368 ≤ i.val) : y.regs i = x.regs i := by
    apply he.regs_eq
    apply Code.preserves_rename_of_forall_ne
    intro j hj
    have hv := congrArg Fin.val hj
    change 336 + j.val = i.val at hv
    have hj := j.isLt
    omega
  obtain ⟨sab, sbc, sac, sn, sa', sb', sfirst, slength⟩ := sa
  refine ⟨y, he, ?_, sm, (yr _).trans sa', (yr _).trans sb', ?_, ?_, ?_, frame⟩
  · exact
      { output := (frame _ (by decide)).trans hx.output
        queries := (frame _ (by decide)).trans hx.queries
        count := (frame _ (by decide)).trans hx.count
        size := (frame _ (by decide)).trans hx.size
        first := (frame _ (by decide)).trans hx.first
        length := (frame _ (by decide)).trans hx.length
        one := (frame _ (by decide)).trans hx.one
        zero := (frame _ (by decide)).trans hx.zero
        ab := (yr _).trans sab
        bc := (yr _).trans sbc
        ac := (yr _).trans sac
        scanSize := (yr _).trans sn
        scanFirst := (yr _).trans sfirst
        scanLength := (yr _).trans slength }
  · simpa only [yr] using sf
  · simpa only [yr] using si
  · simpa only [yr] using sw

/-- Load the actual query occurrence into the verifier arguments and increment the native
scan count. No query enumeration or pair supplied as an algorithm argument replaces the loads. -/
theorem exec_deliverPair {W n first length out queries count i scans a b : ℕ} (x : Data 400)
    (hx : Fixed n first length out queries count x)
    (hi : x.regs Reg.index = i) (hs : x.regs Reg.scans = scans)
    (ha : x.mem (queries + 2 * i) = a) (hb : x.mem (queries + 2 * i + 1) = b)
    (hfit : Fits W (queries + 2 * i + scans + 8)) :
    ∃ y, ExecWithin W deliverPair x y 6 ∧ Fixed n first length out queries count y ∧
      y.mem = x.mem ∧ y.regs (scanBank WitnessScan.Reg.a) = a ∧
      y.regs (scanBank WitnessScan.Reg.b) = b ∧ y.regs Reg.scans = scans + 1 ∧
      y.regs Reg.index = i ∧ y.regs Reg.found = x.regs Reg.found ∧
      ∀ j : Fin 400, j.val < 326 ∨ j = Reg.one ∨ j = Reg.zero ∨
        (345 ≤ j.val ∧ j.val ≤ 348) ∨ (351 ≤ j.val ∧ j.val ≤ 352) →
        y.regs j = x.regs j := by
  have hd : Fits W (i + i) := hfit.of_le (by omega)
  have hp : Fits W (i + i + queries) := hfit.of_le (by omega)
  have hp1 : Fits W (i + i + queries + 1) := hfit.of_le (by omega)
  have hs1 : Fits W (scans + 1) := hfit.of_le (by omega)
  have hreadA : x.mem (i + i + queries) = a := by simpa only [two_mul, Nat.add_comm] using ha
  have hreadB : x.mem (i + i + queries + 1) = b := by
    simpa only [two_mul, Nat.add_comm] using hb
  let y := x.set Reg.address (i + i) |>.set Reg.address (i + i + queries)
    |>.set (scanBank WitnessScan.Reg.a) a |>.set Reg.address (i + i + queries + 1)
    |>.set (scanBank WitnessScan.Reg.b) b |>.set Reg.scans (scans + 1)
  have he : ExecWithin W deliverPair x y 6 := by
    ram_eval [deliverPair, y, hi, hs, hx.queries, hx.one, hreadA, hreadB,
      hd, hp, hp1, hs1, Reg.address, Reg.index, Reg.queries, Reg.one, Reg.scans,
      scanBank, WitnessScan.Reg.a, WitnessScan.Reg.b]
  have frame (j : Fin 400) (hj : Stable j) : y.regs j = x.regs j :=
    he.regs_eq (deliverPair_preserves j hj)
  refine ⟨y, he, hx.of_frame frame, rfl, ?_, ?_, ?_, ?_, ?_, frame⟩
  · rfl
  · rfl
  · rfl
  · exact (he.regs_eq (by decide)).trans hi
  · exact he.regs_eq (by decide)

/-- Copy back only a genuinely reported verifier success and its actual original coordinates.
This is a charged native branch, preserving all fixed arguments, memory and the scan count. -/
theorem exec_receiveWitness {W n first length out queries count flag a b c : ℕ} (x : Data 400)
    (hx : Fixed n first length out queries count x)
    (hf : x.regs (scanBank WitnessScan.Reg.found) = flag)
    (ha : x.regs (scanBank WitnessScan.Reg.a) = a)
    (hb : x.regs (scanBank WitnessScan.Reg.b) = b)
    (hc : x.regs (scanBank WitnessScan.Reg.witness) = c) :
    ∃ y, ExecWithin W receiveWitness x y 5 ∧ Fixed n first length out queries count y ∧
      y.mem = x.mem ∧ y.regs Reg.found = (if flag = 1 then 1 else x.regs Reg.found) ∧
      y.regs Reg.witnessA = (if flag = 1 then a else x.regs Reg.witnessA) ∧
      y.regs Reg.witnessB = (if flag = 1 then b else x.regs Reg.witnessB) ∧
      y.regs Reg.witnessC = (if flag = 1 then c else x.regs Reg.witnessC) ∧
      y.regs Reg.scans = x.regs Reg.scans ∧ y.regs Reg.index = x.regs Reg.index ∧
      ∀ j : Fin 400, j.val < 326 ∨ j = Reg.one ∨ j = Reg.zero ∨
        (345 ≤ j.val ∧ j.val ≤ 348) ∨ (351 ≤ j.val ∧ j.val ≤ 352) →
        y.regs j = x.regs j := by
  let y := if flag = 1 then x.set Reg.found 1 |>.set Reg.witnessA a
      |>.set Reg.witnessB b |>.set Reg.witnessC c
    else x.set Reg.found (x.regs Reg.found)
  dsimp only [scanBank, WitnessScan.Reg.found, WitnessScan.Reg.a,
    WitnessScan.Reg.b, WitnessScan.Reg.witness] at hf ha hb hc
  have he : ExecWithin W receiveWitness x y 5 := by
    by_cases h : flag = 1 <;>
      ram_eval [receiveWitness, y, h, hf, ha, hb, hc, hx.one, Reg.one, Reg.found,
        Reg.witnessA, Reg.witnessB, Reg.witnessC, scanBank, WitnessScan.Reg.found,
        WitnessScan.Reg.a, WitnessScan.Reg.b, WitnessScan.Reg.witness]
  have frame (j : Fin 400) (hj : Stable j) : y.regs j = x.regs j :=
    he.regs_eq (receiveWitness_preserves j hj)
  refine ⟨y, he, hx.of_frame frame, ?_, ?_, ?_, ?_, ?_,
    he.regs_eq (by decide), he.regs_eq (by decide), frame⟩
  all_goals
    dsimp only [y]
    split_ifs <;> rfl

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
