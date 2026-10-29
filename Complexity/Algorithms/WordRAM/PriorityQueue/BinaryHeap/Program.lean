/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PriorityQueue.Basic
public import Complexity.Algorithms.WordRAM.PriorityQueue.BinaryHeap.Model

/-!
# Indexed Binary Min-Heap: Exact-Basis Word-RAM Program

This file defines the structured word-RAM code (`Cslib.WordRAM.Code .exact 25`) and `PQCode`
calling convention for the standalone indexed binary min-heap on `rBin = 25` registers.

Registers `0..4` (`baseReg`, `nReg`, `hb`, `pb`, `sz`) are persistent (`input = false`); registers
`5..24` (`frontierReg`, tags, arguments, outputs, constants, and sift scratch registers) are
caller-overwritable (`input = true`). Parent positions are computed via `p ← k >>> one`
(`k >>> 1 = k / 2`), so no constant larger than `1` is ever loaded and all operations succeed at
every word width `w` with `Fits w (base + space n)` and `Fits w K_max` (including `n = 0, w = 1`).

## Main definitions

* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.rBin`: register count (`25`).
* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.siftUp`,
  `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.siftDown`: heap-order restoration loops.
* `Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.pqCode`: packaged `PQCode .exact rBin`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap

open Cslib.WordRAM

/-- Total register count of the standalone binary heap (`5` persistent + `20` caller/scratch). -/
abbrev rBin : ℕ := 25

namespace Reg

/-- Persistent base address `base` of the `key` array (`[base, base + n)`). -/
abbrev baseReg : Fin rBin := 0
/-- Persistent handle bound `n`. -/
abbrev nReg : Fin rBin := 1
/-- Persistent `heap` array base `base + n` (slots `1..sz` at `base + n + i`). -/
abbrev hb : Fin rBin := 2
/-- Persistent `pos` array base `base + 2 * n + 1`. -/
abbrev pb : Fin rBin := 3
/-- Persistent current heap size `sz ≤ n`. -/
abbrev sz : Fin rBin := 4
/-- Bump-allocation frontier register. -/
abbrev frontierReg : Fin rBin := 5
/-- High operation-tag bit (`1` iff `extractMin`). -/
abbrev tag2 : Fin rBin := 6
/-- Middle operation-tag bit (`1` iff `insert` or `decreaseKey`). -/
abbrev tag1 : Fin rBin := 7
/-- Low operation-tag bit. -/
abbrev tag0 : Fin rBin := 8
/-- Input handle argument `v.val`. -/
abbrev argV : Fin rBin := 9
/-- Input key argument `k`. -/
abbrev argK : Fin rBin := 10
/-- Output status/presence flag (`output` register). -/
abbrev outFlag : Fin rBin := 11
/-- Output handle register (`extractMin`). -/
abbrev outV : Fin rBin := 12
/-- Output key register (`getKey`, `extractMin`). -/
abbrev outK : Fin rBin := 13
/-- Scratch constant `0` (also `zeroReg` for `SubroutineCode.zeroFillCode`). -/
abbrev zero : Fin rBin := 14
/-- Scratch constant `1` (also `oneReg` for `SubroutineCode.zeroFillCode`). -/
abbrev one : Fin rBin := 15
/-- Scratch address / comparison register (also `curReg` for `SubroutineCode.zeroFillCode`). -/
abbrev t : Fin rBin := 16
/-- Current 1-based heap position during `siftUp` / `siftDown`. -/
abbrev k : Fin rBin := 17
/-- Parent or chosen child position during `siftUp` / `siftDown`. -/
abbrev p : Fin rBin := 18
/-- Handle at position `k` (or right child during `siftDownChoose`). -/
abbrev vk : Fin rBin := 19
/-- Handle at position `p`. -/
abbrev vp : Fin rBin := 20
/-- Key of `vk`. -/
abbrev dk : Fin rBin := 21
/-- Key of `vp`. -/
abbrev dp : Fin rBin := 22
/-- Left child `2 * k` during `siftDown`. -/
abbrev l : Fin rBin := 23
/-- `sz + 1` bound during `siftDown`. -/
abbrev szp : Fin rBin := 24

end Reg

open Reg

/-- Register classification: `0..4` are persistent (`false`), `5..24` are caller/scratch (`true`).
-/
def inputMask (i : Fin rBin) : Bool := decide (5 ≤ i.val)

/-- Bump-allocate `space n = 3 * n + 1` words at `frontierReg`, recording `baseReg`, `hb`, and `pb`.
-/
def allocSpan : Code .exact rBin := ram_exact[
  one ← #1;
  baseReg ← frontierReg;
  hb ← baseReg + nReg;
  pb ← hb + nReg;
  pb ← pb + one;
  frontierReg ← pb + nReg ]

/-- Initialize `hb := base + n`, `pb := base + 2 * n + 1`, and `sz := 0` assuming
`[base, base + space n)` is already zero-filled. -/
def initSetup : Code .exact rBin := ram_exact[
  one ← #1;
  hb ← baseReg + nReg;
  pb ← hb + nReg;
  pb ← pb + one;
  sz ← #0 ]

/-- Swap heap entries at positions `k` (handle `vk`) and `p` (handle `vp`), updating `pos`. -/
def swapCode : Code .exact rBin := ram_exact[
  t ← hb + k; *t ← vp;
  t ← hb + p; *t ← vk;
  t ← pb + vp; *t ← k;
  t ← pb + vk; *t ← p ]

/-- Set `t := 1` iff `IndexedMinPQ.RawPrioLT (vA, dA) (vB, dB)`, else `t := 0`. -/
abbrev cmpEntries (vA dA vB dB : Fin rBin) : Code .exact rBin := ram_exact[
  if dA < dB then [ t ← one ] else [
    if dA = dB then [
      if vA < vB then [ t ← one ] else [ t ← zero ] ]
    else [ t ← zero ] ] ]

/-- Set `t := 1` iff `IndexedMinPQ.RawPrioLT (vk, dk) (vp, dp)`, else `t := 0`. -/
abbrev cmpKP : Code .exact rBin := cmpEntries vk dk vp dp

/-- Set `t := 1` iff `IndexedMinPQ.RawPrioLT (vp, dp) (vk, dk)`, else `t := 0`. -/
abbrev cmpPK : Code .exact rBin := cmpEntries vp dp vk dk

/-- One iteration of `siftUp` from `k ≥ 2`, using `k >>> one = k / 2` for the parent position. -/
def siftUpBody : Code .exact rBin := ram_exact[
  p ← k >>> one;
  t ← hb + k; vk ← *t; t ← baseReg + vk; dk ← *t;
  t ← hb + p; vp ← *t; t ← baseReg + vp; dp ← *t;
  ⟪cmpKP⟫;
  if zero < t then [ ⟪swapCode⟫; k ← p ] else [ k ← one ] ]

/-- Repair upward from position `k`. -/
def siftUp : Code .exact rBin := ram_exact[
  while one < k do [ ⟪siftUpBody⟫ ] ]

/-- Choose the lexicographically smaller child of `k` (`l` vs `l + 1`) into `(p, vp, dp)`. -/
def siftDownChoose : Code .exact rBin := ram_exact[
  p ← l;
  t ← hb + l; vp ← *t; t ← baseReg + vp; dp ← *t;
  t ← l + one;
  if t < szp then [
    t ← hb + t; vk ← *t; t ← baseReg + vk; dk ← *t;
    ⟪cmpKP⟫;
    if zero < t then [ p ← l + one; vp ← vk; dp ← dk ] else [ p ← p ] ]
  else [ p ← p ] ]

/-- Swap `k` with chosen child `(p, vp, dp)` if `IndexedMinPQ.RawPrioLT (vp, dp) (vk, dk)`, else
stop `siftDown`. -/
def siftDownSink : Code .exact rBin := ram_exact[
  t ← hb + k; vk ← *t; t ← baseReg + vk; dk ← *t;
  ⟪cmpPK⟫;
  if zero < t then [ ⟪swapCode⟫; k ← p; l ← k + k ] else [ l ← szp ] ]

/-- One iteration of `siftDown`. -/
def siftDownBody : Code .exact rBin := ram_exact[
  ⟪siftDownChoose⟫; ⟪siftDownSink⟫ ]

/-- Repair downward from position `k`. -/
def siftDown : Code .exact rBin := ram_exact[
  l ← k + k; szp ← sz + one;
  while l < szp do [ ⟪siftDownBody⟫ ] ]

/-- Handle `isEmpty`: `outFlag := 1` when `sz = 0`, `outFlag := 0` otherwise. -/
def doIsEmpty : Code .exact rBin := ram_exact[
  if sz = zero then [ outFlag ← one ] else [ outFlag ← zero ] ]

/-- Handle `getKey v`: sets `outFlag := 0` if `pos[v] = 0`, else `outFlag := 1` and
`outK := key[v]`. -/
def doGetKey : Code .exact rBin := ram_exact[
  t ← pb + argV; p ← *t;
  if p = zero then [ outFlag ← zero ]
  else [ outFlag ← one; t ← baseReg + argV; outK ← *t ] ]

/-- Handle `insert v k`: stores `key[v] := argK`, appends `v` at `sz + 1`, and sifts up. -/
def doInsert : Code .exact rBin := ram_exact[
  t ← baseReg + argV; *t ← argK;
  sz ← sz + one;
  t ← hb + sz; *t ← argV;
  t ← pb + argV; *t ← sz;
  k ← sz; ⟪siftUp⟫ ]

/-- Handle `decreaseKey v k`: updates `key[v] := argK`, reads `k := pos[v]`, and sifts up. -/
def doDecreaseKey : Code .exact rBin := ram_exact[
  t ← baseReg + argV; *t ← argK;
  t ← pb + argV; k ← *t;
  ⟪siftUp⟫ ]

/-- Non-empty branch of `extractMin`: reads root into `(outV, outK)`, clears `pos[outV]`, moves last
entry to root when `sz - 1 > 0`, and sifts down. -/
def doExtractNonEmpty : Code .exact rBin := ram_exact[
  outFlag ← one;
  t ← hb + one; outV ← *t;
  t ← baseReg + outV; outK ← *t;
  t ← pb + outV; *t ← zero;
  t ← hb + sz; vk ← *t;
  sz ← sz - one;
  if zero < sz then [
    t ← hb + one; *t ← vk;
    t ← pb + vk; *t ← one;
    k ← one; ⟪siftDown⟫ ]
  else [ k ← k ] ]

/-- Handle `extractMin`: sets `outFlag := 0` if empty, otherwise runs `doExtractNonEmpty`. -/
def doExtractMin : Code .exact rBin := ram_exact[
  if sz = zero then [ outFlag ← zero ] else [ ⟪doExtractNonEmpty⟫ ] ]

/-- Dispatch a single `IndexedMinPQ.Op` encoded in `(tag2, tag1, tag0, argV, argK)`. -/
def opCode : Code .exact rBin := ram_exact[
  zero ← #0; one ← #1;
  if tag2 = zero then [
    if tag1 = zero then [
      if tag0 = zero then [ ⟪doIsEmpty⟫ ] else [ ⟪doGetKey⟫ ] ]
    else [
      if tag0 = zero then [ ⟪doInsert⟫ ] else [ ⟪doDecreaseKey⟫ ] ] ]
  else [ ⟪doExtractMin⟫ ] ]

/-- Packaged `PQCode .exact rBin` for the standalone binary heap. -/
def pqCode : PQCode .exact rBin where
  allocSpan := allocSpan
  initSetup := initSetup
  code := opCode
  frontierReg := frontierReg
  baseReg := baseReg
  initParams := ![nReg]
  curReg := t
  zeroReg := zero
  oneReg := one
  incCur := .exactBin .add t t one
  input := inputMask
  output := outFlag
  nReg := nReg
  tag2 := tag2
  tag1 := tag1
  tag0 := tag0
  argV := argV
  argK := argK
  outFlag := outFlag
  outV := outV
  outK := outK
  initParams_eq := rfl
  nReg_ne_frontier := by decide
  args_nodup := by decide
  tag2_input := by decide
  tag1_input := by decide
  tag0_input := by decide
  argV_input := by decide
  argK_input := by decide
  output_eq := rfl

end Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap
