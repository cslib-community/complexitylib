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
# Actual record and interval-header execution

These internal rules read the producer's real scalar/record words and run the existing native
square-root loop. Record and piece metadata are never supplied as predecoded algorithm inputs.
The original producer/product bank and all memory are preserved.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM
open Cslib.Algorithms.ExactTriangle

-- Closed preservation checks enumerate the four-hundred-register caller bank.
set_option maxRecDepth 4096 in
private theorem readRecord_preserves : ∀ i : Fin 400, i.val < 320 → readRecord.Preserves i := by
  decide

private theorem sqrtBank_injective : Function.Injective sqrtBank := by
  intro i j h
  apply Fin.ext
  simpa only [sqrtBank, Nat.add_left_cancel_iff] using congrArg Fin.val h

private theorem squareRoot_preserves (i : Fin 400) (hi : i.val < 336 ∨ 342 ≤ i.val) :
    squareRoot.Preserves i := by
  apply Code.preserves_rename_of_forall_ne
  intro j hj
  have hv := congrArg Fin.val hj
  change 336 + j.val = i.val at hv
  have hj := j.isLt
  omega

/-- Read the original dimension/divisor and this actual six-word record, then reset the
per-record search state. The record address is computed from the native selected ordinal. -/
theorem exec_readRecord {W n D g i records heap out : ℕ} (x : Data 400) (v : Fin 6 → ℕ)
    (hD : x.mem 1 = D) (hg : x.mem 2 = g) (hn : x.mem 3 = n)
    (hi : x.regs (productBank RecordProduct.Reg.ordinal) = i)
    (hrecords : x.regs (productBank (RecordProduct.producerBank Instances.output)) = records)
    (hout : x.regs (productBank RecordProduct.Reg.result) = out)
    (hrec : records + i * (6 + 2 * (n * D)) + 6 ≤ heap)
    (hv : ∀ j : Fin 6, x.mem (records + i * (6 + 2 * (n * D)) + j.val) = v j)
    (hfit : Fits W (heap + 2 * (n * D) + D + n + g + 128)) :
    ∃ y, ExecWithin W readRecord x y 28 ∧ y.mem = x.mem ∧
      y.regs (sqrtBank NatSqrt.arg) = D ∧ y.regs Reg.size = n ∧
      y.regs Reg.divisor = g ∧ y.regs Reg.output = out ∧
      y.regs Reg.piece = v 1 ∧ y.regs Reg.queries = v 2 ∧ y.regs Reg.count = v 3 ∧
      y.regs Reg.found = 0 ∧ y.regs Reg.witnessA = 0 ∧ y.regs Reg.witnessB = 0 ∧
      y.regs Reg.witnessC = 0 ∧ y.regs Reg.scans = 0 ∧ y.regs Reg.index = 0 ∧
      y.regs Reg.one = 1 ∧ y.regs Reg.zero = 0 ∧
      ∀ j : Fin 400, j.val < 320 → y.regs j = x.regs j := by
  let stride := n * D + n * D + 6
  let r := records + i * stride
  have heq : stride = 6 + 2 * (n * D) := by dsimp only [stride]; omega
  have hrange : r + 6 ≤ heap := by simpa only [r, heq] using hrec
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have h2 : Fits W 2 := hfit.of_le (by omega)
  have h3 : Fits W 3 := hfit.of_le (by omega)
  have h6 : Fits W 6 := hfit.of_le (by omega)
  have harea : Fits W (n * D) := hfit.of_le (by omega)
  have htwice : Fits W (n * D + n * D) := hfit.of_le (by omega)
  have hstride : Fits W stride := hfit.of_le (by dsimp only [stride]; omega)
  have hmul : Fits W (i * stride) := hfit.of_le (by dsimp only [r] at hrange; omega)
  have hr : Fits W r := hfit.of_le (by omega)
  have hr1 : Fits W (r + 1) := hfit.of_le (by omega)
  have hr2 : Fits W (r + 1 + 1) := hfit.of_le (by omega)
  have hr3 : Fits W (r + 1 + 1 + 1) := hfit.of_le (by omega)
  have hv1 : x.mem (r + 1) = v 1 := by simpa +decide [r, heq] using hv ⟨1, by decide⟩
  have hv2 : x.mem (r + 1 + 1) = v 2 := by
    change x.mem (r + 2) = v 2
    simpa +decide [r, heq] using hv ⟨2, by decide⟩
  have hv3 : x.mem (r + 1 + 1 + 1) = v 3 := by
    change x.mem (r + 3) = v 3
    simpa +decide [r, heq] using hv ⟨3, by decide⟩
  dsimp only [productBank, RecordProduct.producerBank, RecordProduct.Reg.ordinal,
    RecordProduct.Reg.result, Instances.output, Fin.castLE] at hi hrecords hout
  dsimp only [r, stride] at hstride hmul hr hr1 hr2 hr3 hv1 hv2 hv3
  let y := x.set Reg.one 1 |>.set Reg.zero 0 |>.set Reg.address 3 |>.set Reg.size n
    |>.set Reg.address 1 |>.set Reg.temp D |>.set (sqrtBank NatSqrt.arg) D
    |>.set Reg.address 2 |>.set Reg.divisor g |>.set Reg.output out
    |>.set Reg.temp (n * D) |>.set Reg.temp (n * D + n * D) |>.set Reg.piece 6
    |>.set Reg.temp stride |>.set Reg.address (i * stride) |>.set Reg.address r
    |>.set Reg.address (r + 1) |>.set Reg.piece (v 1)
    |>.set Reg.address (r + 1 + 1) |>.set Reg.queries (v 2)
    |>.set Reg.address (r + 1 + 1 + 1) |>.set Reg.count (v 3)
    |>.set Reg.found 0 |>.set Reg.witnessA 0 |>.set Reg.witnessB 0 |>.set Reg.witnessC 0
    |>.set Reg.scans 0 |>.set Reg.index 0
  have he : ExecWithin W readRecord x y 28 := by
    ram_eval [readRecord, y, r, stride, hD, hg, hn, hi, hrecords, hout, hv1, hv2, hv3,
      h1, h2, h3, h6, harea, htwice, hstride, hmul, hr, hr1, hr2, hr3,
      Reg.one, Reg.zero, Reg.address, Reg.size, Reg.temp, Reg.divisor, Reg.output,
      Reg.piece, Reg.queries, Reg.count, Reg.found, Reg.witnessA, Reg.witnessB,
      Reg.witnessC, Reg.scans, Reg.index, productBank, sqrtBank, RecordProduct.producerBank,
      RecordProduct.Reg.ordinal, RecordProduct.Reg.result, Instances.output, NatSqrt.arg,
      Fin.castLE]
  refine ⟨y, he, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact fun j hj => he.regs_eq (readRecord_preserves j hj)
    | simp +decide [y, Reg.one, Reg.zero, Reg.address, Reg.size, Reg.temp, Reg.divisor,
        Reg.output, Reg.piece, Reg.queries, Reg.count, Reg.found, Reg.witnessA,
        Reg.witnessB, Reg.witnessC, Reg.scans, Reg.index, sqrtBank, NatSqrt.arg]

/-- The local interval decoder executes the actual square-root loop, preserving the complete
old bank and controller registers. Its result is derived, not a square-root certificate. -/
theorem exec_squareRoot {W D : ℕ} (x : Data 400)
    (hD : x.regs (sqrtBank NatSqrt.arg) = D) (hfit : Fits W (4 * D + 4)) :
    ∃ y, ExecWithin W squareRoot x y (5 * Nat.sqrt D + 7) ∧
      y.regs (sqrtBank NatSqrt.root) = Nat.sqrt D ∧ y.mem = x.mem ∧
      ∀ i : Fin 400, i.val < 336 ∨ 342 ≤ i.val → y.regs i = x.regs i := by
  obtain ⟨y, hy, hr, -, hm, -⟩ := NatSqrt.exec_rename sqrtBank sqrtBank_injective x (by
    rw [hD]; exact hfit)
  refine ⟨y, ?_, ?_, hm, fun i hi => hy.regs_eq (squareRoot_preserves i hi)⟩
  · simpa only [squareRoot, hD] using hy
  · simpa only [hD] using hr

-- Closed preservation over the finite controller and old product bank.
set_option maxRecDepth 4096 in
private theorem finishHeader_preserves : ∀ i : Fin 400,
    i.val < 324 ∨ i = Reg.index ∨ i = Reg.one ∨ i = Reg.piece ∨
      i = Reg.divisor ∨ 392 ≤ i.val → finishHeader.Preserves i := by decide

/-- Compute the actual interval and original signed-array pointers after the real root loop.
All query/output metadata and success/counter initialization are preserved. -/
theorem exec_finishHeader {W n S g k : ℕ} (x : Data 400)
    (hroot : x.regs (sqrtBank NatSqrt.root) = S) (hn : x.regs Reg.size = n)
    (hg : x.regs Reg.divisor = g) (hk : x.regs Reg.piece = k)
    (h1 : x.regs Reg.one = 1) (hc : k * (S ⌈/⌉ g) ≤ n)
    (hfit : Fits W (S + g + 3 * (n * n) + n + 64)) :
    let B := S ⌈/⌉ g
    let first := k * B
    let length := min B (n - first)
    ∃ y, ExecWithin W finishHeader x y 15 ∧ y.mem = x.mem ∧
      y.regs Reg.blockLength = B ∧ y.regs Reg.first = first ∧ y.regs Reg.length = length ∧
      y.regs (scanBank WitnessScan.Reg.ab) = 5 ∧
      y.regs (scanBank WitnessScan.Reg.bc) = 5 + n * n ∧
      y.regs (scanBank WitnessScan.Reg.ac) = 5 + n * n + n * n ∧
      y.regs (scanBank WitnessScan.Reg.size) = n ∧
      y.regs (scanBank WitnessScan.Reg.first) = first ∧
      y.regs (scanBank WitnessScan.Reg.length) = length ∧
      ∀ i : Fin 400, i.val < 324 ∨ i = Reg.index ∨ i = Reg.one ∨ i = Reg.piece ∨
        i = Reg.divisor ∨ 392 ≤ i.val → y.regs i = x.regs i := by
  let B := S ⌈/⌉ g
  let first := k * B
  let length := min B (n - first)
  have hquot : (S + g - 1) / g = B := by simp only [B, Nat.ceilDiv_eq_add_pred_div]
  have hsum : Fits W (S + g) := hfit.of_le (by omega)
  have hsub : Fits W (S + g - 1) := hsum.of_le (Nat.sub_le ..)
  have hB : Fits W B := by rw [← hquot]; exact hsub.of_le (Nat.div_le_self ..)
  have hfirst : Fits W first := hfit.of_le (by change k * B ≤ n at hc; dsimp only [first]; omega)
  have hlen : Fits W (n - first) := hfit.of_le (by omega)
  have harea : Fits W (n * n) := hfit.of_le (by omega)
  have h5 : Fits W 5 := hfit.of_le (by omega)
  have hbc : Fits W (5 + n * n) := hfit.of_le (by omega)
  have hac : Fits W (5 + n * n + n * n) := hfit.of_le (by omega)
  dsimp only [sqrtBank, NatSqrt.root] at hroot
  let y := x.set Reg.blockLength (S + g) |>.set Reg.blockLength (S + g - 1)
    |>.set Reg.blockLength B |>.set Reg.first first |>.set Reg.length (n - first)
    |>.set Reg.length length |>.set (scanBank WitnessScan.Reg.ab) 5
    |>.set Reg.temp (n * n) |>.set (scanBank WitnessScan.Reg.bc) (5 + n * n)
    |>.set (scanBank WitnessScan.Reg.ac) (5 + n * n + n * n)
    |>.set (scanBank WitnessScan.Reg.size) n |>.set (scanBank WitnessScan.Reg.first) first
    |>.set (scanBank WitnessScan.Reg.length) length
  have he : ExecWithin W finishHeader x y 15 := by
    by_cases hlt : B < n - first
    · have hl : length = B := min_eq_left hlt.le
      ram_eval [finishHeader, y, hroot, hn, hg, hk, h1, hquot, hlt, hl,
        hsum, hsub, hB, hfirst, hlen, harea, h5, hbc, hac, B, first, length,
        Reg.blockLength, Reg.divisor, Reg.one, Reg.piece, Reg.first, Reg.length, Reg.size,
        Reg.temp, scanBank, sqrtBank, WitnessScan.Reg.ab, WitnessScan.Reg.bc, WitnessScan.Reg.ac,
        WitnessScan.Reg.size, WitnessScan.Reg.first, WitnessScan.Reg.length, NatSqrt.root]
    · have hl : length = n - first := min_eq_right (by omega)
      ram_eval [finishHeader, y, hroot, hn, hg, hk, h1, hquot, hlt, hl,
        hsum, hsub, hB, hfirst, hlen, harea, h5, hbc, hac, B, first, length,
        Reg.blockLength, Reg.divisor, Reg.one, Reg.piece, Reg.first, Reg.length, Reg.size,
        Reg.temp, scanBank, sqrtBank, WitnessScan.Reg.ab, WitnessScan.Reg.bc, WitnessScan.Reg.ac,
        WitnessScan.Reg.size, WitnessScan.Reg.first, WitnessScan.Reg.length, NatSqrt.root]
  refine ⟨y, he, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact fun i hi => he.regs_eq (finishHeader_preserves i hi)
    | rfl

/-- Complete charged local setup from real scalar and descriptor reads. The computed original
piece interval and all verifier arguments are conclusions of the actual code. -/
theorem exec_header {W n D g i records heap out : ℕ} (x : Data 400) (v : Fin 6 → ℕ)
    (hD : x.mem 1 = D) (hg : x.mem 2 = g) (hn : x.mem 3 = n)
    (hi : x.regs (productBank RecordProduct.Reg.ordinal) = i)
    (hrecords : x.regs (productBank (RecordProduct.producerBank Instances.output)) = records)
    (hout : x.regs (productBank RecordProduct.Reg.result) = out)
    (hrec : records + i * (6 + 2 * (n * D)) + 6 ≤ heap)
    (hv : ∀ j : Fin 6, x.mem (records + i * (6 + 2 * (n * D)) + j.val) = v j)
    (hfirst : v 1 * pieceSize D g ≤ n)
    (hfit : Fits W (heap + 4 * D + 2 * (n * D) + 3 * (n * n) + n + g + 512)) :
    let first := v 1 * pieceSize D g
    let length := min (pieceSize D g) (n - first)
    ∃ y, ExecWithin W header x y (5 * Nat.sqrt D + 50) ∧
      Fixed n first length out (v 2) (v 3) y ∧ y.mem = x.mem ∧
      y.regs Reg.found = 0 ∧ y.regs Reg.witnessA = 0 ∧ y.regs Reg.witnessB = 0 ∧
      y.regs Reg.witnessC = 0 ∧ y.regs Reg.scans = 0 ∧ y.regs Reg.index = 0 ∧
      ∀ j : Fin 400, j.val < 320 → y.regs j = x.regs j := by
  obtain ⟨a, ha, am, aD, an, ag, ao, ak, aq, aQ, af, aa, ab, ac, as, ai, a1, a0, ar⟩ :=
    exec_readRecord x v hD hg hn hi hrecords hout hrec hv (hfit.of_le (by omega))
  obtain ⟨b, hb, bS, bm, br⟩ := exec_squareRoot a aD (hfit.of_le (by omega))
  have bn : b.regs Reg.size = n := (br _ (by decide)).trans an
  have bg : b.regs Reg.divisor = g := (br _ (by decide)).trans ag
  have bk : b.regs Reg.piece = v 1 := (br _ (by decide)).trans ak
  have b1 : b.regs Reg.one = 1 := (br _ (by decide)).trans a1
  have hsqrt := Nat.sqrt_le_self D
  obtain ⟨y, hy, ym, yB, yf, yl, yab, ybc, yac, yn, yfirst, ylength, yr⟩ :=
    exec_finishHeader b bS bn bg bk b1 hfirst (hfit.of_le (by omega))
  refine ⟨y, (ha.seq (hb.seq hy)).mono (by omega), ?_, ym.trans (bm.trans am),
    (yr _ (by decide)).trans ((br _ (by decide)).trans af),
    (yr _ (by decide)).trans ((br _ (by decide)).trans aa),
    (yr _ (by decide)).trans ((br _ (by decide)).trans ab),
    (yr _ (by decide)).trans ((br _ (by decide)).trans ac),
    (yr _ (by decide)).trans ((br _ (by decide)).trans as),
    (yr _ (by decide)).trans ((br _ (by decide)).trans ai), ?_⟩
  · exact
      { output := (yr _ (by decide)).trans ((br _ (by decide)).trans ao)
        queries := (yr _ (by decide)).trans ((br _ (by decide)).trans aq)
        count := (yr _ (by decide)).trans ((br _ (by decide)).trans aQ)
        size := (yr _ (by decide)).trans bn
        first := yf
        length := yl
        one := (yr _ (by decide)).trans b1
        zero := (yr _ (by decide)).trans ((br _ (by decide)).trans a0)
        ab := yab
        bc := ybc
        ac := yac
        scanSize := yn
        scanFirst := yfirst
        scanLength := ylength }
  · intro j hj
    exact (yr j (Or.inl (by omega))).trans ((br j (Or.inl (by omega))).trans (ar j hj))

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
