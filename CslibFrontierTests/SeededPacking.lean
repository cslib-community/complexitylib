/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Foundations.Combinatorics.SeededPacking
import Mathlib.Tactic.NormNum

open Cslib.PacketPacking Cslib.BalancedSchedules Finset

/- A one-coordinate word reads its six-bit code as the radix-64 symbol. -/
example : Seeded.wordEquiv 1 ⟨37, by norm_num⟩ 0 = 37 := by decide

/- The empty word has only one code. -/
example (x : Fin (2 ^ (6 * 0))) : Seeded.wordEquiv 0 x = Fin.elim0 := by
  funext i
  exact Fin.elim0 i

/- For alphabet64 and one coordinate, Kₙ,ₙ with n=2·64⁴ meets the variance condition
with equality. No edge enumeration or hash evaluation is performed in this proof. -/
private abbrev sideSize : ℕ := 2 * 64 ^ 4

private def vertexNumber : Fin sideSize ⊕ Fin sideSize ↪ Fin (sideSize + sideSize) :=
  finSumFinEquiv.toEmbedding

local instance : LinearOrder (Fin sideSize × Fin sideSize) :=
  LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective

private theorem row_degree (v : Fin sideSize) :
    #{e : Fin sideSize × Fin sideSize | e.1 = v} ≤ sideSize := by
  have hset : ({e : Fin sideSize × Fin sideSize | e.1 = v} : Finset _) = {v} ×ˢ univ := by
    ext ⟨x, y⟩
    simp [eq_comm]
  rw [hset]
  simp
private theorem col_degree (v : Fin sideSize) :
    #{e : Fin sideSize × Fin sideSize | e.2 = v} ≤ sideSize := by
  have hset : ({e : Fin sideSize × Fin sideSize | e.2 = v} : Finset _) = univ ×ˢ {v} := by
    ext ⟨x, y⟩
    simp [eq_comm]
  rw [hset]
  simp
private theorem variance_size : 2 * sideSize * (64 ^ (2 * 1)) ^ 2 ≤
    Fintype.card (Fin sideSize × Fin sideSize) := by
  norm_num [sideSize]
private theorem packet_size :
    2 ^ 1 * 64 ^ (2 * 1) ≤ Fintype.card (Fin sideSize × Fin sideSize) := by
  norm_num [sideSize]

example : ∃ seed : SeededLabels.Seed (sideSize + sideSize) 6,
    let P := Seeded.packing (sideSize + sideSize) 1 vertexNumber
      (Prod.fst : Fin sideSize × Fin sideSize → Fin sideSize) Prod.snd seed
    P.numPackets * 2 ≤ 3 * sideSize ^ 2 ∧
      (∀ i σ, 64 * #{e : Fin sideSize × Fin sideSize | P.rowLabel e.1 i = σ} ≤
        2 * sideSize ^ 2) ∧
      (∀ i σ, 64 * #{e : Fin sideSize × Fin sideSize | P.colLabel e.2 i = σ} ≤
        2 * sideSize ^ 2) := by
  have h := Seeded.exists_packing (sideSize + sideSize) 1 vertexNumber
    Prod.fst Prod.snd row_degree col_degree variance_size packet_size
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_one, Nat.mul_one, pow_two] using h

/- The same tight graph also has a certified seed for the fixed-capacity construction. -/
example : ∃ (seed : SeededLabels.Seed (sideSize + sideSize) 6)
    (h : Seeded.Balanced (sideSize + sideSize) 1 vertexNumber
      (Prod.fst : Fin sideSize × Fin sideSize → Fin sideSize) Prod.snd seed),
    let P := Seeded.boundedPacking (sideSize + sideSize) 1 vertexNumber
      (Prod.fst : Fin sideSize × Fin sideSize → Fin sideSize) Prod.snd seed h
    P.numPackets * 2 ≤ 3 * sideSize ^ 2 ∧
      (∀ i σ, 64 * #{e : Fin sideSize × Fin sideSize | P.rowLabel e.1 i = σ} ≤
        2 * sideSize ^ 2) ∧
      (∀ i σ, 64 * #{e : Fin sideSize × Fin sideSize | P.colLabel e.2 i = σ} ≤
        2 * sideSize ^ 2) := by
  have h := Seeded.exists_boundedPacking (sideSize + sideSize) 1 vertexNumber
    Prod.fst Prod.snd row_degree col_degree variance_size packet_size
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_one, Nat.mul_one, pow_two] using h

