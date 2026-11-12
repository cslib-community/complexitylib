/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.PacketPacking

/-!
# Packet packing with a known capacity

For `M` edges, label-pair count `D = r^(2a)` and slot count `L = 2^a`, an occupancy bound
`Xγ D ≤ 2M` supplies the fixed block count `ceil(floor(2M/D)/L)`. Using this capacity in the
existing rank-based placement removes the need to compute the largest class load. Under
`LD ≤ M`, the same `3M/L` packet bound holds; empty slots and packets are allowed.

`Packing.ofLabelsBounded` uses only the known capacity, an edge's class rank and its endpoint
words to place that edge. Its proof reuses the original packing's injectivity and orientation,
but its data fields do not compute the maximum load. Native rank access and running-time
bounds remain separate obligations.
-/

public section

namespace Cslib.PacketPacking

open Cslib.BalancedSchedules Finset

/-- Whole blocks sufficient for every class of size at most `floor(2M / r^(2a))`. -/
@[expose] def capacityBlocks (a r M : ℕ) : ℕ :=
  (2 * M / r ^ (2 * a) + (2 ^ a - 1)) / 2 ^ a

/-- Rounding the known class capacity up to blocks covers that capacity. -/
theorem capacity_le_blocks_mul (a r M : ℕ) :
    2 * M / r ^ (2 * a) ≤ capacityBlocks a r M * 2 ^ a := by
  have h := Nat.lt_div_mul_add
    (a := 2 * M / r ^ (2 * a) + (2 ^ a - 1)) (Nat.two_pow_pos a)
  simp only [capacityBlocks]
  omega

/-- Known-capacity padding retains the original `3M` total slot bound. -/
theorem capacityBlocks_mul_le (a r M : ℕ)
    (hL : 2 ^ a * r ^ (2 * a) ≤ M) :
    capacityBlocks a r M * r ^ (2 * a) * 2 ^ a ≤ 3 * M := by
  have hround : capacityBlocks a r M * 2 ^ a ≤ 2 * M / r ^ (2 * a) + 2 ^ a := by
    have h := Nat.div_mul_le_self (2 * M / r ^ (2 * a) + (2 ^ a - 1)) (2 ^ a)
    have hpos := Nat.two_pow_pos a
    simp only [capacityBlocks]
    omega
  have h := Nat.mul_le_mul_right (r ^ (2 * a)) hround
  have hdiv := Nat.div_mul_le_self (2 * M) (r ^ (2 * a))
  rw [Nat.add_mul] at h
  rw [Nat.mul_right_comm]
  omega

variable {E R C : Type*} [Fintype E] [LinearOrder E]
  (rowOf : E → R) (colOf : E → C) {a r : ℕ} [NeZero r]
  (ρ : R → Fin a → Fin r) (κ : C → Fin a → Fin r)
  (hocc : ∀ γ, occupancy (pairLabel rowOf colOf ρ κ) γ * r ^ (2 * a) ≤
    2 * Fintype.card E)

/-- A packing with a fixed, occupancy-certified capacity. Class ranks are unchanged; the
packet universe is padded without querying `maxLoad` or `numBlocks`. -/
@[expose] def Packing.ofLabelsBounded
    (hocc : ∀ γ, occupancy (pairLabel rowOf colOf ρ κ) γ * r ^ (2 * a) ≤
      2 * Fintype.card E) : Packing rowOf colOf a r where
  rowLabel := ρ
  colLabel := κ
  numPackets := capacityBlocks a r (Fintype.card E) * (r * r) ^ a
  packet e := packetEquiv _ a r
    (⟨(packetData rowOf colOf ρ κ e).1, by
      have hD : 0 < r ^ (2 * a) := pow_pos (Nat.pos_of_neZero r) _
      have hrank := classIndex_lt_occupancy rowOf colOf ρ κ e
      have hclass := (Nat.le_div_iff_mul_le hD).mpr (hocc (pairLabel rowOf colOf ρ κ e))
      have hcap := capacity_le_blocks_mul a r (Fintype.card E)
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)⟩,
      (packetData rowOf colOf ρ κ e).2)
  slot e := BitString.equivFin a (slotBits rowOf colOf ρ κ e)
  symbols p i :=
    let q := ((packetEquiv _ a r).symm p).2 i
    (min q.1 q.2, max q.1 q.2)
  injective := by
    intro e e' h
    have hp := (packetEquiv _ a r).injective (congrArg Prod.fst h)
    have hs := congrArg Prod.snd h
    apply (Packing.ofLabels rowOf colOf ρ κ).injective
    apply Prod.ext
    · apply congrArg (packetEquiv _ a r)
      apply Prod.ext
      · exact Fin.ext (congrArg (fun p => p.1.val) hp)
      · have hparts := congrArg Prod.snd hp
        exact hparts
    · exact hs
  labels_eq := by
    intro e i
    simpa only [Packing.ofLabels, Equiv.symm_apply_apply] using
      (Packing.ofLabels rowOf colOf ρ κ).labels_eq e i

/-- The bounded-capacity packing still uses at most `3M/L` packets under `LD ≤ M`. -/
theorem Packing.numPackets_ofLabelsBounded_mul_le
    (hL : 2 ^ a * r ^ (2 * a) ≤ Fintype.card E) :
    (Packing.ofLabelsBounded rowOf colOf ρ κ hocc).numPackets * 2 ^ a ≤
      3 * Fintype.card E := by
  change capacityBlocks a r (Fintype.card E) * (r * r) ^ a * 2 ^ a ≤ _
  rw [← sq, ← pow_mul]
  exact capacityBlocks_mul_le a r (Fintype.card E) hL

/-- Padding the packet universe does not change any row symbol or its port count. -/
theorem Packing.row_ports_ofLabelsBounded_le (i : Fin a) (σ : Fin r) :
    r * #{e | (Packing.ofLabelsBounded rowOf colOf ρ κ hocc).rowLabel (rowOf e) i = σ} ≤
      2 * Fintype.card E :=
  Packing.row_ports_ofLabels_le rowOf colOf ρ κ hocc i σ

/-- Padding the packet universe does not change any column symbol or its port count. -/
theorem Packing.col_ports_ofLabelsBounded_le (i : Fin a) (σ : Fin r) :
    r * #{e | (Packing.ofLabelsBounded rowOf colOf ρ κ hocc).colLabel (colOf e) i = σ} ≤
      2 * Fintype.card E :=
  Packing.col_ports_ofLabels_le rowOf colOf ρ κ hocc i σ

end Cslib.PacketPacking
