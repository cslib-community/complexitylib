/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.Node.Registers
public import Complexity.Algorithms.WordRAM.FusionTree.Node.Semantics
import Mathlib.Tactic.FinCases

/-!
# Composing compression and packed ranks

All transfers into the two fixed workspaces are charged. Only the actual loaded header
values supply node-dependent constants. The caller's registers and all memory are framed.

## Main definitions

* `NodeProgram.compressionInputs`, `NodeProgram.compress`: workspace transfers and multiplier
  compression routine.
* `NodeProgram.rankInputs`, `NodeProgram.rank`, `NodeProgram.sketchCut`,
  `NodeProgram.sketchQuery`: workspace transfers, packed-rank routine, mathematical sketch
  cut, and combined compression-plus-rank query.

## Main results

* `NodeProgram.exec_compress`: a bounded word is compressed in 102 instructions.
* `NodeProgram.exec_rank`: a compressed query is ranked in 17 instructions.

## References

* [FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.NodeProgram

open Cslib.WordRAM Cslib.WordRAM.Multiword Lean.FusionTree

/-- Seven charged transfers into the compression workspace. -/
def compressionInputs : List (Fin registers × Fin registers) :=
  [(compressBank 16, argument), (compressBank 17, parameter 0),
    (compressBank 18, parameter 4), (compressBank 19, parameter 13),
    (compressBank 7, parameter 1), (compressBank 8, parameter 2),
    (compressBank 9, parameter 3)]

/-- Prepare the compression workspace and run the actual multiplier program. -/
def compress : Code .standard registers :=
  .seq (moves compressionInputs) (CompressProgram.code.rename compressBank)

/-- Seven transfers plus the terminal self-copy and 94 arithmetic instructions. -/
theorem exec_compress {w n q : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (hw : 2 ≤ w) (hn : 0 < n) (hnB : n ≤ branching w) (hlarge : 9 ≤ Nat.log 2 w)
    (x : Data registers) (hx : Prepared p x) (hq : Fits w q)
    (hxq : x.regs argument = q) :
    ∃ y, Exec w compress x y 102 ∧ y.regs (compressBank 20) = p.compressed q ∧
      Frame x y := by
  let u := moved compressionInputs x
  have hframe : Frame x u := frame_moved _ _ (by
    simp [compressionInputs, compressBank, bank])
  have huq : (u.comap compressBank).regs CompressProgram.query = q := by
    simpa +decide [u, moved, compressionInputs, Data.comap, CompressProgram.query,
      parameter, headerBank, compressBank, bank] using hxq
  have huc : (u.comap compressBank).regs CompressProgram.positions = p.C := by
    simpa +decide [u, moved, compressionInputs, Data.comap, CompressProgram.positions,
      parameter, headerBank, compressBank, bank, NodeParameters.words] using hx.words_eq 0
  have hud : (u.comap compressBank).regs CompressProgram.retained = p.D := by
    simpa +decide [u, moved, compressionInputs, Data.comap, CompressProgram.retained,
      parameter, headerBank, compressBank, bank, NodeParameters.words] using hx.words_eq 4
  have huo : (u.comap compressBank).regs CompressProgram.offset = w - 2 * (w / 2) := by
    simpa +decide [u, moved, compressionInputs, Data.comap, CompressProgram.offset,
      parameter, headerBank, compressBank, bank, NodeParameters.words] using hx.words_eq 13
  have hdigit (i : Fin 3) :
      ((u.comap compressBank).comap CompressProgram.embed).regs ⟨7 + i.val, by omega⟩ =
        p.digits i := by
    fin_cases i <;> first
      | simpa +decide [u, moved, compressionInputs, Data.comap, CompressProgram.embed,
          parameter, headerBank, compressBank, bank, NodeParameters.words] using hx.words_eq 1
      | simpa +decide [u, moved, compressionInputs, Data.comap, CompressProgram.embed,
          parameter, headerBank, compressBank, bank, NodeParameters.words] using hx.words_eq 2
      | simpa +decide [u, moved, compressionInputs, Data.comap, CompressProgram.embed,
          parameter, headerBank, compressBank, bank, NodeParameters.words] using hx.words_eq 3
  have hb : Multiword.Bounded (radix w) ((u.comap compressBank).comap CompressProgram.embed)
      (Schoolbook.rightRegs 3 3) := by
    intro i hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    exact (hdigit j).trans_lt (p.digits_lt j)
  have hm : Multiword.value (radix w) ((u.comap compressBank).comap CompressProgram.embed)
      (Schoolbook.rightRegs 3 3) = p.M := by
    change Nat.ofDigits (radix w)
      [((u.comap compressBank).comap CompressProgram.embed).regs 7,
       ((u.comap compressBank).comap CompressProgram.embed).regs 8,
       ((u.comap compressBank).comap CompressProgram.embed).regs 9] = p.M
    have hd0 : ((u.comap compressBank).comap CompressProgram.embed).regs 7 = p.digits 0 :=
      hdigit 0
    have hd1 : ((u.comap compressBank).comap CompressProgram.embed).regs 8 = p.digits 1 :=
      hdigit 1
    have hd2 : ((u.comap compressBank).comap CompressProgram.embed).regs 9 = p.digits 2 :=
      hdigit 2
    rw [hd0, hd1, hd2]
    exact p.digits_value
  obtain ⟨v, hev, hv, hmem, _⟩ := CompressProgram.exec (L := p.b) hw
    (u.comap compressBank) (huq ▸ hq) hb hm huo (hud ▸ p.D_lt) (p.window hn hnB hlarge)
  let y := v.extend compressBank u
  refine ⟨y, ?_, ?_, hframe.trans (frame_extend _ (by decide) u v hmem)⟩
  · exact (exec_moves w compressionInputs x).seq (hev.rename (bank_injective _))
  · change Function.extend compressBank v.regs u.regs (compressBank 20) = _
    rw [(bank_injective _).extend_apply, hv, huq, huc, hud]
    rfl

/-- Transfer a compressed query and seven stored constants to a packed-rank workspace.
The Boolean selects strict rank (original packed sketches) or inclusive rank (complements). -/
def rankInputs (strict : Bool) : List (Fin registers × Fin registers) :=
  [(rankBank 0, compressBank 20), (rankBank 1, parameter (if strict then 7 else 6)),
    (rankBank 2, parameter 5), (rankBank 3, parameter 8), (rankBank 4, parameter 9),
    (rankBank 5, parameter 10), (rankBank 6, parameter 11),
    (rankBank 7, if strict then count else parameter 12)]

/-- Eight charged transfers followed by the chosen eight-instruction rank program. -/
def rank (strict : Bool) : Code .standard registers :=
  .seq (moves (rankInputs strict))
    ((if strict then LowerRankProgram.code else RankProgram.code).rename rankBank)

/-- Perfect-sketch comparison count with the chosen convention. -/
def sketchCut {n : ℕ} (strict : Bool) (w : ℕ) (keys : Fin n → ℕ) (q : ℕ) : ℕ :=
  if strict then lowerRank (fun i => Cslib.BitString.sketch (relevantBits w keys) (keys i))
    (Cslib.BitString.sketch (relevantBits w keys) q) else sketchRank w keys q

/-- The rank call includes every transfer and preserves the caller and memory. -/
theorem exec_rank {w n q : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (strict : Bool) (hn : 0 < n) (hs : StrictMono keys) (hk : ∀ i, keys i < 2 ^ w)
    (hnB : n ≤ branching w) (hlarge : 9 ≤ Nat.log 2 w)
    (x : Data registers) (hx : Prepared p x)
    (hxq : x.regs (compressBank 20) = p.compressed q) :
    ∃ y, Exec w (rank strict) x y 17 ∧
      y.regs (rankBank 9) = sketchCut strict w keys q ∧ Frame x y := by
  let u := moved (rankInputs strict) x
  have hf : Frame x u := frame_moved _ _ (by
    cases strict <;> simp [rankInputs, rankBank, bank])
  have hwords := hx.words_eq
  have hcount := hx.count_eq
  cases strict with
  | false =>
    have hin :
        (u.comap rankBank).regs 0 = p.compressed q ∧
        (u.comap rankBank).regs 1 = p.packedComplement ∧
        (u.comap rankBank).regs 2 = p.copies ∧
        (u.comap rankBank).regs 3 = p.guards ∧
        (u.comap rankBank).regs 4 = p.b ∧
        (u.comap rankBank).regs 5 = p.middle ∧
        (u.comap rankBank).regs 6 = p.radix ∧
        (u.comap rankBank).regs 7 = p.maximum := by
      exact ⟨hxq, hwords 6, hwords 5, hwords 8, hwords 9,
        hwords 10, hwords 11, hwords 12⟩
    obtain ⟨he, hout, hm⟩ := RankProgram.exec p.sketches (u.comap rankBank) hn
      (p.count_lt_radix hs hk) (fun i _ => p.sketches_lt i) (p.compressed_lt q)
      (p.packed_width hnB hlarge) hin.1 hin.2.1 hin.2.2.1 hin.2.2.2.1
      hin.2.2.2.2.1 hin.2.2.2.2.2.1 hin.2.2.2.2.2.2.1 hin.2.2.2.2.2.2.2
    let v := RankProgram.result (u.comap rankBank) p.b n p.sketches (p.compressed q)
    refine ⟨v.extend rankBank u, (exec_moves w _ x).seq (he.rename (bank_injective _)), ?_,
      hf.trans (frame_extend _ (by decide) u v hm)⟩
    change Function.extend rankBank v.regs u.regs (rankBank 9) = _
    rw [(bank_injective _).extend_apply, hout]
    exact (upperRankExpr_eq_card p.sketches hn (p.count_lt_radix hs hk)
      (fun i _ => p.sketches_lt i) (p.compressed_lt q)).symm.trans
        (NodeSemantics.upperRank_eq p hn hs hk q)
  | true =>
    have hin :
        (u.comap rankBank).regs 0 = p.compressed q ∧
        (u.comap rankBank).regs 1 = p.packed ∧
        (u.comap rankBank).regs 2 = p.copies ∧
        (u.comap rankBank).regs 3 = p.guards ∧
        (u.comap rankBank).regs 4 = p.b ∧
        (u.comap rankBank).regs 5 = p.middle ∧
        (u.comap rankBank).regs 6 = p.radix ∧
        (u.comap rankBank).regs 7 = n := by
      exact ⟨hxq, hwords 7, hwords 5, hwords 8, hwords 9,
        hwords 10, hwords 11, hcount⟩
    obtain ⟨he, hout, hm⟩ := LowerRankProgram.exec p.sketches (u.comap rankBank) hn
      (p.count_lt_radix hs hk) (fun i _ => p.sketches_lt i) (p.compressed_lt q)
      (p.packed_width hnB hlarge) hin.1 hin.2.1 hin.2.2.1 hin.2.2.2.1
      hin.2.2.2.2.1 hin.2.2.2.2.2.1 hin.2.2.2.2.2.2.1 hin.2.2.2.2.2.2.2
    let v := LowerRankProgram.result (u.comap rankBank) p.b n p.sketches (p.compressed q)
    refine ⟨v.extend rankBank u, (exec_moves w _ x).seq (he.rename (bank_injective _)), ?_,
      hf.trans (frame_extend _ (by decide) u v hm)⟩
    change Function.extend rankBank v.regs u.regs (rankBank 9) = _
    rw [(bank_injective _).extend_apply, hout]
    exact (LowerRankProgram.countGuards_complement p.sketches hn (p.count_lt_radix hs hk)
      (fun i _ => p.sketches_lt i) (p.compressed_lt q)).symm.trans
        (NodeSemantics.lowerRank_eq p hn hs hk q)

/-- Compression followed by the requested sketch-rank convention. -/
def sketchQuery (strict : Bool) : Code .standard registers := .seq compress (rank strict)

/-- A complete sketch query, including all register transfers, takes 119 instructions. -/
theorem exec_sketchQuery {w n q : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (strict : Bool) (hw : 2 ≤ w) (hn : 0 < n) (hs : StrictMono keys)
    (hk : ∀ i, keys i < 2 ^ w) (hnB : n ≤ branching w) (hlarge : 9 ≤ Nat.log 2 w)
    (x : Data registers) (hx : Prepared p x) (hq : Fits w q)
    (hxq : x.regs argument = q) :
    ∃ y, Exec w (sketchQuery strict) x y 119 ∧
      y.regs (rankBank 9) = sketchCut strict w keys q ∧ Frame x y := by
  obtain ⟨u, heu, hu, hfu⟩ := exec_compress p hw hn hnB hlarge x hx hq hxq
  obtain ⟨y, hey, hy, hfy⟩ := exec_rank p strict hn hs hk hnB hlarge u (hx.frame hfu) hu
  exact ⟨y, heu.seq hey, hy, hfu.trans hfy⟩

end Cslib.Algorithms.WordRAM.FusionTree.NodeProgram
