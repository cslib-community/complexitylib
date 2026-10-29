/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandHeader
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandCount
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandRoot
public import Complexity.Algorithms.MatrixMultiplication.Schonhage.BandBounds

/-!
# Complete computed scalar parameters for native bands

## Main results

* `BandPreparation.exec_countCode`: compute binomial count, block count and band count
  from actual scalar parameters, retaining the previously computed header layout.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Registers containing the persistent header and concrete layout. -/
def headerRegisters : Finset (Fin 96) :=
  {levels, inner, rows, columns, outerSize, masks, cells, leaves, prefixSize,
    snapshot, inverse, table, catalogue, zero, one, two, three, four, seven, ten}

/-- The concrete layout survives any native execution that preserves its scalar registers. -/
theorem headerPost_reframe {L m N : ℕ} {x y : Data 96} (hx : HeaderPost L m N x)
    (h : ∀ i ∈ headerRegisters, y.regs i = x.regs i) : HeaderPost L m N y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(h _ (by decide)).trans hx.fixed.levels, (h _ (by decide)).trans hx.fixed.inner,
      (h _ (by decide)).trans hx.fixed.rows, (h _ (by decide)).trans hx.fixed.zero,
      (h _ (by decide)).trans hx.fixed.one, (h _ (by decide)).trans hx.fixed.two,
      (h _ (by decide)).trans hx.fixed.three, (h _ (by decide)).trans hx.fixed.four,
      (h _ (by decide)).trans hx.fixed.seven, (h _ (by decide)).trans hx.fixed.ten⟩
  all_goals first
    | exact (h _ (by decide)).trans hx.columns
    | exact (h _ (by decide)).trans hx.outerSize
    | exact (h _ (by decide)).trans hx.masks
    | exact (h _ (by decide)).trans hx.cells
    | exact (h _ (by decide)).trans hx.leaves
    | exact (h _ (by decide)).trans hx.prefixSize
    | exact (h _ (by decide)).trans hx.snapshot
    | exact (h _ (by decide)).trans hx.inverse
    | exact (h _ (by decide)).trans hx.table
    | exact (h _ (by decide)).trans hx.catalogue

/-- Persistent concrete layout and the additional scalar results actually computed by
the mask-count/root/band-count code. No fit or execution bound is bundled here. -/
structure BandParameters (L m N : ℕ) (x : Data 96) : Prop extends HeaderPost L m N x where
  /-- Computed floor square root of the binomial count. -/
  root : x.regs root = K0 L m
  /-- Number of selected subset masks. -/
  square : x.regs square = K0 L m * K0 L m
  /-- Computed number of shared bands per side. -/
  bands : x.regs bands = numBands L m N

/-- All scalar parameters retained throughout preparation and encoder calls. -/
def parameterRegisters : Finset (Fin 96) := headerRegisters ∪ {root, square, bands}

/-- Preserve the computed parameters by preserving their actual registers. -/
theorem parameters_reframe {L m N : ℕ} {x y : Data 96} (hx : BandParameters L m N x)
    (h : ∀ i ∈ parameterRegisters, y.regs i = x.regs i) : BandParameters L m N y := by
  refine ⟨headerPost_reframe hx.toHeaderPost (fun i hi => h i (Finset.mem_union_left _ hi)),
    (h _ (by decide)).trans hx.root, (h _ (by decide)).trans hx.square,
    (h _ (by decide)).trans hx.bands⟩

/-- A convenient local numerical bound, derived from the original global word budget. -/
theorem local_fits {w L m N : ℕ} (hfit : Fits w (wordBudget L m N)) :
    Fits w (16 * (L + N + N * D m + 2 ^ L + 10 ^ L + 1)) := by
  apply hfit.of_le
  unfold wordBudget
  nlinarith only [Nat.zero_le L, Nat.zero_le N, Nat.zero_le (N * D m),
    Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L),
    Nat.zero_le (2 * numBands L m N * 10 ^ L)]

/-- Compute the root and band counts with the actual native loops. -/
theorem exec_countCode {w L m N : ℕ} (x : Data 96)
    (hx : HeaderPost L m N x) (hfit : Fits w (wordBudget L m N)) :
    ∃ y, ExecWithin w countCode x y ((6 * L + 16) * 2 ^ L + 14) ∧
      BandParameters L m N y ∧ y.mem = x.mem := by
  have hl := local_fits hfit
  have hK : K L m ≤ 2 ^ L := Nat.choose_le_two_pow _ _
  obtain ⟨c, hc, hcount, _, hcmem, _⟩ := exec_countMasks L m x hx.fixed.levels hx.fixed.inner
    hx.masks hx.fixed.one hx.fixed.two (hl.of_le (by
      nlinarith only [Nat.zero_le L, Nat.zero_le N, Nat.zero_le (N * D m),
        Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L)]))
  have hcp : HeaderPost L m N c := headerPost_reframe hx (by
    intro i hi
    apply hc.regs_eq
    have hp : ∀ i ∈ headerRegisters, countMasks.Preserves i := by
      simp only [countMasks, countBody, populationCode, Code.Preserves, Op.dest, Op.bin]
      decide
    exact hp i hi)
  obtain ⟨r, hr, hroot, hsquare, hrmem, _⟩ := exec_root (K L m) c hcount hcp.fixed.one
    (hl.of_le (by
      nlinarith only [hK, Nat.zero_le L, Nat.zero_le N,
        Nat.zero_le (N * D m), Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L)]))
  have hrp : HeaderPost L m N r := headerPost_reframe hcp (by
    intro i hi
    apply hr.regs_eq
    have hp : ∀ i ∈ headerRegisters, rootCode.Preserves i := by
      simp only [rootCode, rootBody, Code.Preserves, Op.dest, Op.bin]
      decide
    exact hp i hi)
  have hB : bandSize L m ≤ 7 ^ L := bandSize_le_seven_pow L m
  have h7 : 7 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  have hbfit : Fits w (bandSize L m) := hl.of_le (by
    nlinarith only [hB, h7, Nat.zero_le L, Nat.zero_le N,
      Nat.zero_le (N * D m), Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L)])
  have hnfit : Fits w (N + bandSize L m) := hl.of_le (by
    nlinarith only [hB, h7, Nat.zero_le L, Nat.zero_le N,
      Nat.zero_le (N * D m), Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L)])
  have hnsubfit : Fits w (N + bandSize L m - 1) :=
    hnfit.of_le (Nat.sub_le _ _)
  have hdivfit : Fits w ((N + bandSize L m - 1) / bandSize L m) :=
    hnsubfit.of_le (Nat.div_le_self _ _)
  let y := (((r.set temporary (bandSize L m)).set bands (N + bandSize L m)).set
    bands (N + bandSize L m - 1)).set bands (numBands L m N)
  have hroot0 : r.regs root = K0 L m := by simpa only [K0] using hroot
  simp only [bandSize] at hbfit hnfit hnsubfit hdivfit
  have hy : ExecWithin w bandCount r y 4 := by
    ram_eval [bandCount, y, hroot0, hrp.outerSize, hrp.fixed.rows, hrp.fixed.one,
      bandSize, numBands, hbfit, hnfit, hnsubfit, hdivfit,
      temporary, root, outerSize, bands, rows, one, Fin.mk.injEq]
  have he : ExecWithin w countCode x y ((6 * L + 16) * 2 ^ L + 14) := by
    apply (hc.seq (hr.seq hy)).mono
    have hsqrt : Nat.sqrt (K L m) ≤ 2 ^ L := (Nat.sqrt_le_self _).trans hK
    nlinarith
  have hyp : HeaderPost L m N y := headerPost_reframe hx (by
    intro i hi
    apply he.regs_eq
    have hp : ∀ i ∈ headerRegisters, countCode.Preserves i := by
      simp only [countCode, countMasks, countBody, populationCode, rootCode, rootBody,
        bandCount, Code.Preserves, Op.dest, Op.bin]
      decide
    exact hp i hi)
  refine ⟨y, he, ⟨hyp, ?_, ?_, ?_⟩, hrmem.trans hcmem⟩
  · simpa [y, temporary, bands, root] using hroot0
  · simpa [y, temporary, bands, square, K0] using hsquare
  · simp [y]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
