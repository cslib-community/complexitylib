/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexity.Foundations.Combinatorics.PacketPacking

public section

open Cslib.PacketPacking
open Finset

namespace Cslib.Tests.PacketPacking

/-! ### Packing for given labels

Here `a = 2`, so packets have `L = 4` slots. Three edges share the pair of labels
`((0, 1), (0, 0))`: coordinate `0` has equal symbols and coordinate `1` unequal ones. A packet
holds two slots of each orientation, told apart by slot digit `0`, the low digit of the class
number. The third edge, with class number `2`, goes to a second packet of the same block,
distinguished by digit `1` of its class number. A fourth edge has the opposite orientation
`((0, 0), (0, 1))` and shares the first packet. -/

def rowOf (e : Fin 4) : Fin 2 := if e.val < 3 then 0 else 1
def colOf (e : Fin 4) : Fin 2 := if e.val < 3 then 0 else 1
def ρ : Fin 2 → Fin 2 → Fin 2 := ![![0, 1], ![0, 0]]
def κ : Fin 2 → Fin 2 → Fin 2 := ![![0, 0], ![0, 1]]

abbrev P := Packing.ofLabels rowOf colOf ρ κ

/-- The class numbers, the largest class, the blocks, and the slots: the slot digit in the equal
coordinate `0` is the low digit of the class number, and in the unequal coordinate `1` it is the
orientation, `1` when the row symbol is the larger. There are `1 * 4 ^ 2` packets. -/
example :
    List.ofFn (classIndex rowOf colOf ρ κ) = [0, 1, 2, 0] ∧
    maxLoad rowOf colOf ρ κ = 3 ∧ numBlocks rowOf colOf ρ κ = 1 ∧
    P.numPackets = 16 ∧
    List.ofFn (fun e => (P.slot e : ℕ)) = [2, 3, 2, 0] := by
  decide +kernel

/-- Edges `0`, `1` and `3` share a packet; edge `2` is in another. -/
example : P.packet 0 = P.packet 1 ∧ P.packet 0 = P.packet 3 ∧ P.packet 0 ≠ P.packet 2 := by
  decide +kernel

/-- The packet's sorted pairs of symbols, with digit `1` of the slot orienting coordinate `1`. -/
example : P.symbols (P.packet 0) 0 = (0, 0) ∧ P.symbols (P.packet 0) 1 = (0, 1) := by
  decide +kernel

/-! ### Labels by conditional expectations

A perfect matching of two edges with `a = 1` and `r = 2`. Independent uniform labels give the
two edges the same pair of labels with probability `1 / 4`. The pass labels row `0` first (all
labels tie), then gives row `1` the other label, after which the edges cannot collide and the
columns keep the first label. -/

def matchRow (e : Fin 2) : Fin 2 := e
def matchCol (e : Fin 2) : Fin 2 := e

example :
    List.ofFn (fun v => List.ofFn (rowLabels matchRow matchCol 1 2 v)) = [[0], [1]] ∧
    List.ofFn (fun w => List.ofFn (colLabels matchRow matchCol 1 2 w)) = [[0], [0]] := by
  decide +kernel

example :
    pairLabel matchRow matchCol (rowLabels matchRow matchCol 1 2)
      (colLabels matchRow matchCol 1 2) 0 ≠
    pairLabel matchRow matchCol (rowLabels matchRow matchCol 1 2)
      (colLabels matchRow matchCol 1 2) 1 := by
  decide +kernel

/-! ### The hypotheses (D.6) are satisfiable

A perfect matching on `32` edges, with `a = 1`, `r = 2` (so `D = 4` and `L = 2`) and maximum
degree `Δ = 1`, meets `2 Δ D² ≤ M` and `L D ≤ M` with equality. Lemma D.3 then gives at most
`48` packets and at most `32` ports of each symbol in each coordinate on each side. -/

def bigRow (e : Fin 32) : Fin 32 := e
def bigCol (e : Fin 32) : Fin 32 := e

theorem bigRow_degree : ∀ v, #{e | bigRow e = v} ≤ 1 := by decide +kernel
theorem bigCol_degree : ∀ w, #{e | bigCol e = w} ≤ 1 := by decide +kernel

example : (packing bigRow bigCol 1 2).numPackets * 2 ^ 1 ≤ 3 * 32 := by
  simpa using numPackets_packing_mul_le bigRow bigCol 1 2 bigRow_degree bigCol_degree
    (by simp) (by simp)

example (i : Fin 1) (σ : Fin 2) :
    2 * #{e | (packing bigRow bigCol 1 2).rowLabel (bigRow e) i = σ} ≤ 2 * 32 ∧
    2 * #{e | (packing bigRow bigCol 1 2).colLabel (bigCol e) i = σ} ≤ 2 * 32 := by
  constructor
  · simpa using row_ports_packing_le bigRow bigCol 1 2 bigRow_degree bigCol_degree (by simp) i σ
  · simpa using col_ports_packing_le bigRow bigCol 1 2 bigRow_degree bigCol_degree (by simp) i σ

example : ∃ P : Packing bigRow bigCol 1 2, P.numPackets * 2 ≤ 96 := by
  obtain ⟨P, hP, -⟩ := exists_packing bigRow bigCol 1 2 bigRow_degree bigCol_degree
    (by simp) (by simp)
  exact ⟨P, by simpa using hP⟩

end Cslib.Tests.PacketPacking
