/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PolyTime.PacketPacking

/-! Regression tests for `Complexity.Computability.PolyTime.PacketPacking`. -/

namespace ComplexityTests.PacketPackingNative

open Finset Cslib.PacketPacking Cslib.BalancedSchedules

/-! ### A perfect matching with two edges

With `a = 1` and `r = 2`, the pass gives row `0` the first label (all labels tie) and row `1` the
other one, and the columns keep the first label, as `Cslib.PacketPacking.rowLabels` does. The two
edges have class number `0`, so there is one block of `2 ^ 1` slots and `1 * 4 ^ 1` packets. Edge
`0` has equal symbols and slot `0`; edge `1` has row symbol `1 > 0` and slot `1`. -/

example : nativePacking 2 2 1 2 [(0, 0), (1, 1)] =
    (([[0], [1]], [[0], [0]]), 4, [(0, 0), (1, 1)]) := by
  decide +kernel

/-! ### Two labels per vertex: the complete bipartite graph `K₂,₂`

With `a = 2` and `r = 2` there are `r ^ a = 4` candidate labels for the four edges, streamed in
radix order `00, 10, 01, 11` (digit `0` first). Row `1` takes `10`, the first label that avoids
row `0`'s pairs; in lexicographic order it would take `01`. Edges `1` and `2` have the same
unordered pairs of symbols, oriented oppositely in coordinate `0`, so they share packet `1` in
slots `0` and `1`. The native output is `packing` by `nativePacking_eq`. -/

def k22Row (e : Fin 4) : Fin 2 := ⟨e.val / 2, by omega⟩
def k22Col (e : Fin 4) : Fin 2 := ⟨e.val % 2, Nat.mod_lt _ (by omega)⟩

example : edgeList k22Row k22Col = [(0, 0), (0, 1), (1, 0), (1, 1)] := by decide +kernel

example : nativePacking 2 2 2 2 [(0, 0), (0, 1), (1, 0), (1, 1)] =
    (([[0, 0], [1, 0]], [[0, 0], [1, 0]]), 16, [(0, 0), (1, 0), (1, 1), (3, 0)]) := by
  decide +kernel

/-- Packet `1` pairs the symbols `0` and `1` in coordinate `0`, and `0` with itself in
coordinate `1`; packet `3` pairs `1` with itself. -/
example : packetSymbols 2 2 1 0 = (0, 1) ∧ packetSymbols 2 2 1 1 = (0, 0) ∧
    packetSymbols 2 2 3 0 = (1, 1) := by
  decide +kernel

example (p : Fin (packing k22Row k22Col 2 2).numPackets) (i : Fin 2) :
    packetSymbols 2 2 p i = ((((packing k22Row k22Col 2 2).symbols p i).1 : ℕ),
      (((packing k22Row k22Col 2 2).symbols p i).2 : ℕ)) :=
  packetSymbols_eq k22Row k22Col _ _ p i

/-! ### Lemma D.3 for the native output

A perfect matching on `32` edges, with `a = 1`, `r = 2` and maximum degree `1`, meets (D.6). Its
native packing has at most `3M / L = 48` packets, and in each coordinate at most `2M / r = 32`
row ports of each symbol. -/

def bigRow (e : Fin 32) : Fin 32 := e
def bigCol (e : Fin 32) : Fin 32 := e

theorem bigRow_degree : ∀ v, #{e | bigRow e = v} ≤ 1 := by decide +kernel
theorem bigCol_degree : ∀ w, #{e | bigCol e = w} ≤ 1 := by decide +kernel

theorem big_hK : 2 ^ 1 ≤ 32 := pow_le_card_of_packing (by norm_num) (by norm_num)

example : (nativePacking 32 32 1 2 (edgeList bigRow bigCol)).2.1 * 2 ^ 1 ≤ 3 * 32 :=
  numPackets_nativePacking_mul_le bigRow bigCol bigRow_degree bigCol_degree (by norm_num)
    (by norm_num)

example (i : Fin 1) (σ : Fin 2) :
    2 * #{e | ((nativePacking 32 32 1 2 (edgeList bigRow bigCol)).1.1.getD (bigRow e) []).getD i 0
      = σ} ≤ 2 * 32 := by
  rw [nativePacking_eq bigRow bigCol big_hK]
  have h := row_ports_packing_le bigRow bigCol 1 2 bigRow_degree bigCol_degree (by simp) i σ
  rw [Fintype.card_fin] at h
  refine le_of_eq_of_le ?_ h
  congr 2
  refine Finset.filter_congr fun e _ => ?_
  simp only [List.getD_ofFn, scheduleToWord, Fin.val_inj]

end ComplexityTests.PacketPackingNative
