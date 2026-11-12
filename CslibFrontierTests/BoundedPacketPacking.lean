/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Foundations.Combinatorics.BoundedPacketPacking

open Cslib.PacketPacking Cslib.BalancedSchedules Finset

/- Two copies of every edge of K₂,₂, with one-coordinate identity labels. -/
private def row (e : Fin 8) : Fin 2 := ⟨e.val / 2 % 2, Nat.mod_lt _ (by decide)⟩
private def col (e : Fin 8) : Fin 2 := ⟨e.val / 4 % 2, Nat.mod_lt _ (by decide)⟩
private def word (v : Fin 2) : Fin 1 → Fin 2 := fun _ => v

private theorem class_bound : ∀ γ,
    occupancy (pairLabel row col word word) γ * 2 ^ (2 * 1) ≤ 2 * Fintype.card (Fin 8) := by
  decide

private def padded := Packing.ofLabelsBounded row col word word class_bound

/- Known capacity allocates eight packets; max-load-based packing allocates only four.
The extra empty packets are intentional and require no maximum query. -/
example : padded.numPackets = 8 := by decide
example : (Packing.ofLabels row col word word).numPackets = 4 := by decide
example : padded.numPackets * 2 ≤ 3 * 8 := by decide

/- Parallel edges share a packet but occupy different slots. -/
example : padded.packet 0 = padded.packet 1 ∧ padded.slot 0 ≠ padded.slot 1 := by decide

/- The whole padded placement remains injective, including all four endpoint-label classes. -/
example : Function.Injective (fun e : Fin 8 => (padded.packet e, padded.slot e)) :=
  padded.injective

/- The quantitative API applies to this nonempty one-coordinate example. -/
example : padded.numPackets * 2 ^ 1 ≤ 3 * Fintype.card (Fin 8) :=
  Packing.numPackets_ofLabelsBounded_mul_le row col word word class_bound (by decide)

example (σ : Fin 2) :
    2 * #{e : Fin 8 | padded.rowLabel (row e) 0 = σ} ≤ 2 * Fintype.card (Fin 8) :=
  Packing.row_ports_ofLabelsBounded_le row col word word class_bound 0 σ

/- Rounding cases: a residual half-block and the empty graph. -/
example : capacityBlocks 1 2 10 = 3 := by decide
example : capacityBlocks 3 64 0 = 0 := by decide
