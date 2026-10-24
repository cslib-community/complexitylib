/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.Node.Initial
public import Complexity.Algorithms.WordRAM.FusionTree.Node.Correction
import Batteries.Data.Nat.Bitwise.Lemmas

/-!
# Constant-time full-key fusion-node queries

This width-indexed standard-basis RAM program returns the true inclusive rank of every
bounded query in a sorted internal node. Its constants are actual preprocessing witnesses,
loaded from the contiguous eighteen-word header. The program charges header loads, all
register transfers, both stride-two full-key neighbor loads, multiword highest-bit arithmetic,
and the second compression and rank. Memory and the original query and pointer are preserved.

The large-width branch assumes `2 ≤ n ≤ branching w` and `9 ≤ Nat.log 2 w`. Leaves,
small-width binary nodes and tree traversal are separate. No preprocessing-time bound is
claimed. No correctness or execution oracle is a parameter of the representation.

## Main definitions

* `NodeProgram.boundaryQuery`, `NodeProgram.correction`, `NodeProgram.finish`: second sketch-rank
  query at the prefix boundary, neighbor correction and output writeback stages.
* `NodeProgram.code`: the actual node query, depending only on physical width.

## Main results

* `NodeProgram.exec`: true inclusive full-key rank within 201000 standard instructions.
* `NodeProgram.exists_preprocessing`: actual fitting preprocessing witnesses for this query.

## References

* [FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.NodeProgram

open Cslib.WordRAM Cslib.BitString Lean.FusionTree

/-- The zero query bit needs a strict upper-boundary rank; the one bit needs an inclusive
lower-boundary rank. Both calls include query compression and all transfers. -/
def boundaryQuery : Code .standard registers :=
  .branch (.eq (boundaryBank 9) zero)
    (secondQuery true (boundaryBank 8)) (secondQuery false (boundaryBank 7))

/-- On a miss, compute the highest differing bit and query its sibling boundary. -/
def correction (w : ℕ) : Code .standard registers :=
  .seq (highest w) (.seq boundaries boundaryQuery)

/-- Exact hits return the first cut. Misses execute the actual full-key correction. -/
def finish (w : ℕ) : Code .standard registers :=
  .branch (.eq divergence zero) (.op (.copy out cut)) (correction w)

/-- Complete width-indexed internal-node query. Node-dependent constants occur only in RAM. -/
def code (w : ℕ) : Code .standard registers := .seq readHeader (.seq initial (finish w))

/-- One width-independent code-size bound includes both branches of every conditional. -/
theorem size_code (w : ℕ) : (code w).size ≤ 201000 := by
  have hm := MSB.Program.size_scalarCode w
  have hh : ReadHeaderProgram.code.size = 54 := rfl
  have hn : NeighborProgram.code.size = 21 := rfl
  have hb : BoundaryProgram.code.size = 10 := rfl
  have hr : RankProgram.code.size = 8 := rfl
  have hl : LowerRankProgram.code.size = 8 := rfl
  simp only [code, readHeader, initial, finish, correction, highest, boundaries,
    boundaryQuery, secondQuery, sketchQuery, compress, rank, neighbors, neighborAddress,
    saveNeighbor, Code.size, Code.size_rename, size_moves, hh, hn, hb, hr, hl,
    CompressProgram.size_code, compressionInputs, rankInputs, neighborInputs, boundaryInputs,
    List.length_cons, List.length_nil, Bool.false_eq_true, ↓reduceIte]
  omega

/-- Registers 31 through 38 belong to the outer traversal. They are outside every node
workspace; the terminal self-copy used by `moves` occupies register 39 instead. -/
private theorem preserves_caller (w : ℕ) (i : Fin registers) (hlo : 31 ≤ i.val)
    (hhi : i.val < 39) : (code w).Preserves i := by
  have hh (c : Code .standard 21) : (c.rename headerBank).Preserves i :=
    preserves_bank _ c i (Or.inr (by omega))
  have hc (c : Code .standard 21) : (c.rename compressBank).Preserves i :=
    preserves_bank _ c i (Or.inl (by omega))
  have hr (c : Code .standard 10) : (c.rename rankBank).Preserves i :=
    preserves_bank _ c i (Or.inl (by omega))
  have hn (c : Code .standard 17) : (c.rename neighborBank).Preserves i :=
    preserves_bank _ c i (Or.inl (by omega))
  have hb (c : Code .standard 10) : (c.rename boundaryBank).Preserves i :=
    preserves_bank _ c i (Or.inl (by omega))
  have hm (c : Code .standard (Cslib.WordRAM.Multiword.Bank.capacity 44 + 4)) :
      (c.rename msbBank).Preserves i := preserves_bank _ c i (Or.inl (by omega))
  simp only [code, readHeader, initial, finish, correction, highest, boundaries,
    boundaryQuery, secondQuery, sketchQuery, compress, rank, neighbors, neighborAddress,
    saveNeighbor, moves, compressionInputs, rankInputs, neighborInputs, boundaryInputs,
    Code.Preserves, hh, hc, hr, hn, hb, hm, true_and, and_true, Bool.false_eq_true,
    ↓reduceIte, Op.dest, ne_eq, Option.some.injEq, Fin.ext_iff]
  dsimp only [query, pointer, out, argument, cut, zero, chosen, divergence, position,
    headerBank, compressBank, rankBank, neighborBank, boundaryBank, msbBank, bank,
    Cslib.WordRAM.Multiword.Bank.inputReg, MSB.Program.output]
  norm_num [registers, Op.bin, Op.dest, Fin.ext_iff]
  omega

/-- Every actual execution frames the caller's eight traversal registers. -/
theorem caller_regs_eq {w t : ℕ} {x y : Data registers} (he : Exec w (code w) x y t)
    (i : Fin registers) (hlo : 31 ≤ i.val) (hhi : i.val < 39) : y.regs i = x.regs i :=
  he.regs_eq (preserves_caller w i hlo hhi)

/-- A miss executes the concrete highest-bit and boundary programs, returning the
mathematical sibling-boundary rank. All incoming workspace registers may be arbitrary. -/
private theorem exec_correction {w n q a : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (hw : 3 ≤ w) (hn : 0 < n) (hs : StrictMono keys) (hk : ∀ i, keys i < 2 ^ w)
    (hnB : n ≤ branching w) (hlarge : 9 ≤ Nat.log 2 w)
    (x : Data registers) (hx : Ready p q a x) (hq : Fits w q) (j : Fin n)
    (hj : keys j ≠ q) (hd : x.regs divergence = keys j ^^^ q) (hz : x.regs zero = 0) :
    ∃ y, ExecWithin w (correction w) x y 200138 ∧
      y.regs out = boundaryRank w keys q j ∧ Ready p q a y ∧ y.mem = x.mem := by
  let d := highestDiff w (keys j) q
  have hdiv : Fits w (keys j ^^^ q) := Nat.xor_lt_two_pow (hk j) hq
  obtain ⟨u, heu, hu, hum, hup⟩ := exec_highest hw x hdiv hd
  have hru : Ready p q a u := hx.except_scratch position (by decide) (by decide) hum hup
  have hpos : u.regs position = d :=
    hu.trans (highestDiff_eq_log2_xor (hk j) hq hj).symm
  have hdw : d < w := (highestDiff_spec (hk j) hq hj).1
  obtain ⟨v, hev, hfv, hl, hh, hb⟩ := exec_boundaries u hq hdw hru.query_eq hpos
  have hrv := hru.frame hfv
  have hvzero : v.regs zero = 0 :=
    (hfv.2 zero (by decide)).trans ((hup zero (by decide) (by decide)).trans hz)
  obtain ⟨hlfit, hhfit⟩ := boundary_fits hq hdw
  by_cases hbit : q.testBit d = false
  · have htest : (Cond.eq (boundaryBank 9) zero).Holds v := by
      simp only [Cond.holds_eq, hb, hvzero]
      exact (bit_eq_zero_iff q d).mpr hbit
    obtain ⟨y, hey, hy, hry, hym⟩ := exec_secondQuery p true (boundaryBank 8)
      (by omega) hn hs hk hnB hlarge v hrv hhfit hh
    refine ⟨y, heu.seq (hev.within.seq
      ((ExecWithin.branch_pos (neg := secondQuery false (boundaryBank 7)) htest hey.within).mono
        (by decide : 122 ≤ 123))), ?_, hry, hym.trans (hfv.1.trans hum)⟩
    have hb0 : q.testBit (highestDiff w (keys j) q) = false := hbit
    simpa [sketchCut, boundaryRank, hb0] using hy
  · have hbit' : q.testBit d = true := by cases he : q.testBit d <;> simp_all
    have htest : ¬(Cond.eq (boundaryBank 9) zero).Holds v := by
      simp only [Cond.holds_eq, hb, hvzero]
      exact fun h => hbit ((bit_eq_zero_iff q d).mp h)
    obtain ⟨y, hey, hy, hry, hym⟩ := exec_secondQuery p false (boundaryBank 7)
      (by omega) hn hs hk hnB hlarge v hrv hlfit hl
    refine ⟨y, heu.seq (hev.within.seq
      (ExecWithin.branch_neg (pos := secondQuery true (boundaryBank 8)) htest hey.within)),
      ?_, hry, hym.trans (hfv.1.trans hum)⟩
    have hb1 : q.testBit (highestDiff w (keys j) q) = true := hbit'
    simpa [sketchCut, boundaryRank, hb1, sketchRank] using hy

/-- Every bounded query receives its true inclusive full-key rank. The physical program
depends only on `w`, and 201000 bounds the actual instruction count uniformly in `w`, `n`,
the keys, their preprocessing witnesses and the query. Registers 0 and 1 and all memory
are preserved. The address premise covers the last full key in the stride-two table. -/
theorem exec {w n q a : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (hn : 2 ≤ n) (hs : StrictMono keys) (hk : ∀ i, keys i < 2 ^ w)
    (hnB : n ≤ branching w) (hlarge : 9 ≤ Nat.log 2 w)
    (x : Data registers) (hr : Rep p a x.mem) (hq : Fits w q)
    (ha : Fits w (a + 18 + (n - 1) * 2))
    (hxq : x.regs query = q) (hxa : x.regs pointer = a) :
    ∃ y, ExecWithin w (code w) x y 201000 ∧ y.regs out = upperRank keys q ∧
      y.mem = x.mem ∧ y.regs query = q ∧ y.regs pointer = a := by
  have hn0 : 0 < n := by omega
  have hw : 3 ≤ w := by
    have hb := branching_capacity hlarge
    have hB := two_le_branching w
    have hp : branching w ≤ branching w ^ 5 := Nat.le_self_pow (by decide) _
    omega
  obtain ⟨u, heu, hru, hum⟩ := exec_readHeader p x hr (ha.of_le (by omega)) hxq hxa
  obtain ⟨v, hev, hrv, hvm, hcut, hz, j, hj, hd, hnear, hbest⟩ :=
    exec_initial p (by omega) hn0 hs hk hnB hlarge u hru hq ha
  have hcorrect := NodeSemantics.correct hs hk hq j hbest
  by_cases hhit : keys j = q
  · have htest : (Cond.eq divergence zero).Holds v := by
      simp only [Cond.holds_eq, hd, hz, hhit, Nat.xor_self]
    let y := v.set out (sketchRank w keys q)
    have hey : Exec (B := .standard) w (.op (.copy out cut)) v y 1 := by
      simpa only [hcut] using (Exec.copy (B := .standard) (w := w) (d := out) (s := cut) (x := v))
    have hefinish := Exec.branch_pos (neg := correction w) htest hey
    have hry : Ready p q a y := hrv.set_scratch out _ (by decide) (by decide)
    refine ⟨y, (heu.within.seq (hev.seq hefinish.within)).mono (by decide), ?_,
      hvm.trans hum, hry.query_eq, hry.pointer_eq⟩
    simpa only [y, Data.set_regs, Function.update_self, hhit, ↓reduceIte] using hcorrect
  · have htest : ¬(Cond.eq divergence zero).Holds v := by
      simp only [Cond.holds_eq, hd, hz]
      exact fun h => hhit (Nat.xor_eq_zero_iff.mp h)
    obtain ⟨y, hey, hy, hry, hym⟩ := exec_correction p hw hn0 hs hk hnB hlarge v hrv hq j
      hhit hd hz
    have hefinish := ExecWithin.branch_neg (pos := .op (.copy out cut)) htest hey
    refine ⟨y, (heu.within.seq (hev.seq hefinish)).mono (by decide), ?_,
      hym.trans (hvm.trans hum), hry.query_eq, hry.pointer_eq⟩
    exact hy.trans (by simpa only [ite_eq_right hhit] using hcorrect)

/-- Real preprocessing witnesses exist, all fifteen stored words fit, and the same
width-indexed program answers every bounded query on every memory realizing those witnesses.
The witness construction has no preprocessing-time assertion. -/
theorem exists_preprocessing {w n : ℕ} {keys : Fin n → ℕ}
    (hn : 2 ≤ n) (hs : StrictMono keys) (hk : ∀ i, keys i < 2 ^ w)
    (hnB : n ≤ branching w) (hlarge : 9 ≤ Nat.log 2 w) :
    ∃ p : NodeParameters w keys, (∀ j, Fits w (p.words j)) ∧
      ∀ (q a : ℕ) (x : Data registers), Rep p a x.mem → Fits w q →
        Fits w (a + 18 + (n - 1) * 2) → x.regs query = q → x.regs pointer = a →
        ∃ y, ExecWithin w (code w) x y 201000 ∧ y.regs out = upperRank keys q ∧
          y.mem = x.mem ∧ y.regs query = q ∧ y.regs pointer = a := by
  obtain ⟨p⟩ := NodeParameters.exists_parameters hn hs hk hnB hlarge
  exact ⟨p, p.words_fit hn hs hk hnB hlarge,
    fun _ _ x hr hq ha hxq hxa => exec p hn hs hk hnB hlarge x hr hq ha hxq hxa⟩

end Cslib.Algorithms.WordRAM.FusionTree.NodeProgram
