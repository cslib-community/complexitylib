/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Program
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Meaning
public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Tiling

/-!
# Native routing of one wanted position

## Main results

* `Wanted.exec_route`: actual divisions, selected-mask lookup and digit packing return
  exactly the tile and `outStrOfPos` code for an original matrix position.

The table contract is an ordinary memory equation supplied by the actual computed-table
routine. It supplies neither an output string nor an execution or time certificate.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Scalar values read by the one-query router. The table may be relocated by its caller. -/
structure RouteParameters (L m N tab : ℕ) (x : Data 96) : Prop where
  /-- Original depth. -/
  levels : x.regs BandPreparation.levels = L
  /-- Compressed outer dimension. -/
  outerSize : x.regs BandPreparation.outerSize = N0 L m
  /-- Computed root of the valid-subset count. -/
  root : x.regs BandPreparation.root = K0 L m
  /-- Computed band width. -/
  bandWidth : x.regs bandWidth = bandSize L m
  /-- Computed band count. -/
  bands : x.regs BandPreparation.bands = numBands L m N
  /-- Actual forward-table base. -/
  table : x.regs BandPreparation.table = tab

/-- Numeric bound for all arithmetic performed by one router and its digit kernel. -/
def routeBudget (L m N tab : ℕ) : ℕ :=
  64 * (L + N + tab + numBands L m N ^ 2 + 10 ^ L + 2 ^ L + 1)

/-- Only the packer bank and three computed routing registers are written. -/
def RouteLocal (i : Fin 96) : Prop := i.val < 16 ∨ i = rowBand ∨ i = colBand ∨ i = tile

instance (i : Fin 96) : Decidable (RouteLocal i) :=
  inferInstanceAs (Decidable (i.val < 16 ∨ i = rowBand ∨ i = colBand ∨ i = tile))

private theorem route_preserves (i : Fin 96) (hi : ¬RouteLocal i) : routeCode.Preserves i := by
  revert i
  decide +kernel

/-- The register map embeds the packer without identifying any pair of registers. -/
theorem packRegisters_injective : Function.Injective packRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 96 => i.val) h)

/-- Actual routing on one admitted original position. Original row/column words, all
persistent parameters and all memory survive; only the declared local registers change. -/
theorem exec_route {w L m N tab : ℕ} (hm : m ≤ L) (I J : Fin N) (x : Data 96)
    (hx : RouteParameters L m N tab x)
    (hI : x.regs queryRow = I.val) (hJ : x.regs queryCol = J.val)
    (htable : ∀ gh : Fin (K0 L m) × Fin (K0 L m),
      x.mem (tab + (MaskTable.pairRank gh).val) = (MaskTable.selectedMask gh).val)
    (hfit : Fits w (routeBudget L m N tab)) :
    ∃ y, ExecWithin w routeCode x y (15 * L + 25) ∧
      y.regs rowBand = bandOf L m I.val ∧ y.regs colBand = bandOf L m J.val ∧
      y.regs tile = bandOf L m I.val * numBands L m N + bandOf L m J.val ∧
      y.regs (packRegisters code) =
        (PrunedQuery.queryIndex (outStrOfPos (MaskTable.layout hm) I J)).val ∧
      y.mem = x.mem ∧ (∀ i, ¬RouteLocal i → y.regs i = x.regs i) := by
  let lay := MaskTable.layout hm
  let g := blockOf lay I
  let h := blockOf lay J
  let a := (MaskTable.selectedMask (g, h)).val
  let r := I.val % N0 L m
  let c := J.val % N0 L m
  let β := bandOf L m I.val
  let γ := bandOf L m J.val
  let b := numBands L m N
  let k := β * b + γ
  let u := I.val / N0 L m
  let v := J.val / N0 L m
  let rank := g.val * K0 L m + h.val
  have hβ : β < b := bandOf_lt_numBands hm N I I.isLt
  have hγ : γ < b := bandOf_lt_numBands hm N J J.isLt
  have hk : k < b ^ 2 := by
    dsimp [k]
    nlinarith only [Nat.mul_le_mul_right b (Nat.succ_le_of_lt hβ), hγ]
  have hbb : b ≤ b ^ 2 := by nlinarith only [hβ]
  have h2 : 2 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  have hu : u ≤ N := (Nat.div_le_self _ _).trans I.isLt.le
  have hv : v ≤ N := (Nat.div_le_self _ _).trans J.isLt.le
  have hg : g.val < K0 L m := g.isLt
  have hh : h.val < K0 L m := h.isLt
  have hrank : rank < 2 ^ L := by
    have hp : rank = (MaskTable.pairRank (g, h)).val := by
      change g.val * K0 L m + h.val = h.val + K0 L m * g.val
      ring
    rw [hp]
    exact (MaskTable.pairRank (g, h)).isLt.trans_le (Nat.choose_le_two_pow L m)
  have hmul : g.val * K0 L m ≤ rank := by dsimp [rank]; omega
  have ha : a < 2 ^ L := (MaskTable.selectedMask (g, h)).isLt
  have hr : r ≤ N := (Nat.mod_le _ _).trans I.isLt.le
  have hc : c ≤ N := (Nat.mod_le _ _).trans J.isLt.le
  have hbfit (v : ℕ) (hv : v ≤ L + N + tab + b ^ 2 + 10 ^ L + 2 ^ L + 1) :
      Fits w v := hfit.of_le (by
        change v ≤ 64 * (L + N + tab + b ^ 2 + 10 ^ L + 2 ^ L + 1)
        omega)
  have hfβ : Fits w β := hbfit _ (by omega)
  have hfγ : Fits w γ := hbfit _ (by omega)
  have hfprod : Fits w (β * b) := hbfit _ (by dsimp [k] at hk; omega)
  have hfk : Fits w k := hbfit _ (by omega)
  have hfr : Fits w r := hbfit _ (by omega)
  have hfc : Fits w c := hbfit _ (by omega)
  have hfu : Fits w u := hbfit _ (by omega)
  have hfv : Fits w v := hbfit _ (by omega)
  have hfg : Fits w g.val := hbfit _ (by
    have hle : g.val ≤ u := Nat.mod_le _ _
    omega)
  have hfh : Fits w h.val := hbfit _ (by
    have hle : h.val ≤ v := Nat.mod_le _ _
    omega)
  have hfgmul : Fits w (g.val * K0 L m) := hbfit _ (by omega)
  have hfrank : Fits w rank := hbfit _ (by omega)
  have hfaddr : Fits w (tab + rank) := hbfit _ (by omega)
  have hload : x.mem (tab + rank) = a := by
    convert htable (g, h) using 1
    congr 1
    change tab + rank = tab + (h.val + K0 L m * g.val)
    dsimp [rank]
    ring
  let y := (((((((((((((((x.set rowBand β).set colBand γ).set tile (β * b)).set
    tile k).set (packRegisters depth) L).set (packRegisters row) r).set
    (packRegisters col) c).set (packRegisters mask) u).set (packRegisters mask) g.val).set
    (packRegisters mask) (g.val * K0 L m)).set (packRegisters temporary) v).set
    (packRegisters temporary) h.val).set (packRegisters mask) rank).set
    (packRegisters temporary) (tab + rank)).set (packRegisters mask) a)
  have he : ExecWithin w routeHead x y 15 := by
    dsimp only [β, γ, b, k, bandOf] at hfβ hfγ hfprod hfk
    dsimp only [r, c, u, v, g, h, blockOf, lay] at hfr hfc hfu hfv hfg hfh
    dsimp only [rank, g, h, blockOf, lay] at hfgmul hfrank hfaddr hload
    ram_eval [routeHead, tileCode, y, hx.bandWidth, hx.bands, hx.levels, hx.outerSize,
      hx.root, hx.table, hI, hJ, hfβ, hfγ, hfprod, hfk, hfr, hfc, hfu, hfv, hfg, hfh,
      hfgmul, hfrank, hfaddr, hload, β, γ, b, k, r, c, u, v, rank, g, h, blockOf,
      lay, bandOf, packRegisters, depth, mask, row, col, temporary,
      queryRow, queryCol, rowBand, colBand, tile, BandPreparation.levels,
      BandPreparation.outerSize, BandPreparation.root, BandPreparation.table,
      BandPreparation.bands, bandWidth, Fin.reduceFinMk, Fin.mk.injEq]
  have hpackfit : Fits w (a + r + c + L + 32 * 10 ^ L + 32) := hfit.of_le (by
    change a + r + c + L + 32 * 10 ^ L + 32 ≤
      64 * (L + N + tab + b ^ 2 + 10 ^ L + 2 ^ L + 1)
    omega)
  obtain ⟨z, hz, hcode, _, hmem⟩ := exec_pack L a r c (y.comap packRegisters)
    (by simp [y, packRegisters, depth, row, col, mask, temporary, rowBand, colBand, tile])
    (by simp [y, packRegisters, mask])
    (by simp [y, packRegisters, row, col, mask, temporary, depth])
    (by simp [y, packRegisters, col, mask, temporary, depth]) hpackfit
  have hrun : ExecWithin w routeCode x (z.extend packRegisters y) (15 * L + 25) := by
    exact (he.seq (hz.rename packRegisters_injective)).mono (by omega)
  refine ⟨z.extend packRegisters y, hrun, ?_, ?_, ?_, ?_, hmem, ?_⟩
  · have hp : (packCode.rename packRegisters).Preserves rowBand := by decide +kernel
    exact ((hz.rename packRegisters_injective).regs_eq hp).trans (by simp [y, rowBand,
      colBand, tile, packRegisters, depth, row, col, mask, temporary, β])
  · have hp : (packCode.rename packRegisters).Preserves colBand := by decide +kernel
    exact ((hz.rename packRegisters_injective).regs_eq hp).trans (by simp [y, rowBand,
      colBand, tile, packRegisters, depth, row, col, mask, temporary, γ])
  · have hp : (packCode.rename packRegisters).Preserves tile := by decide +kernel
    exact ((hz.rename packRegisters_injective).regs_eq hp).trans (by simp [y, rowBand,
      colBand, tile, packRegisters, depth, row, col, mask, temporary]; rfl)
  · have hout := congrArg (fun q : Data 16 => q.regs code)
      (Data.comap_extend packRegisters_injective z y)
    exact hout.trans (hcode.trans (pack_outStrOfPos hm I J))
  · intro i hi
    exact hrun.regs_eq (route_preserves i hi)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
