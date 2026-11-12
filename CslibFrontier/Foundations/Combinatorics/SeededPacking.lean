/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SeededPacketLabels
public import CslibFrontier.Foundations.Combinatorics.BoundedPacketPacking

/-!
# Packet packings determined by short seeds

The four-coefficient seed of `SeededLabels` supplies words over the alphabet `Fin 64` by
splitting its `6 * a` output bits into `a` symbols. Applying the existing `Packing.ofLabels`
construction gives an actual injective, oriented packet placement for every seed. Under the
same two size hypotheses (D.6) as the original packing lemma, some seed simultaneously has
at most `3M / 2^a` packets and at most `2M / 64` ports of each symbol on either side.

`packing` uses the original maximum-load capacity. `boundedPacking` instead uses the known
capacity from a `Balanced` seed certificate, eliminating the maximum query while preserving
all bounds. Both use class ranks. No native running-time claim is made for computing ranks,
checking the certificate, or selecting the seed.
-/

@[expose] public section

namespace Cslib.PacketPacking.Seeded

open Cslib.BalancedSchedules Finset

/-- The radix-64 representation of a `6 * a`-bit output as a word of length `a`. -/
def wordEquiv (a : ℕ) : Fin (2 ^ (6 * a)) ≃ (Fin a → Fin 64) :=
  (finCongr (by rw [show (64 : ℕ) = 2 ^ 6 by norm_num, pow_mul])).trans
    finFunctionFinEquiv.symm

/-- All coordinates of a vertex word come from the same short seed. -/
noncomputable def label (U a : ℕ) (seed : SeededLabels.Seed U (6 * a))
    (v : Fin U) : Fin a → Fin 64 :=
  wordEquiv a (SeededLabels.label U (6 * a) seed v)

/-- Every pair-label class has at most twice the uniform-average load for this fixed seed. -/
def Balanced {E R C : Type*} [Fintype E]
    (U a : ℕ) (vertex : R ⊕ C ↪ Fin U) (rowOf : E → R) (colOf : E → C)
    (seed : SeededLabels.Seed U (6 * a)) : Prop :=
  ∀ γ, occupancy (pairLabel rowOf colOf
    (fun r => label U a seed (vertex (.inl r)))
    (fun c => label U a seed (vertex (.inr c)))) γ * 64 ^ (2 * a) ≤
      2 * Fintype.card E

/-- The existing rank-based packing applied to the labels decoded from one seed. -/
noncomputable def packing {E R C : Type*} [Fintype E] [LinearOrder E]
    (U a : ℕ) (vertex : R ⊕ C ↪ Fin U) (rowOf : E → R) (colOf : E → C)
    (seed : SeededLabels.Seed U (6 * a)) : Packing rowOf colOf a 64 :=
  Packing.ofLabels rowOf colOf
    (fun r => label U a seed (vertex (.inl r)))
    (fun c => label U a seed (vertex (.inr c)))

/-- A certified seed defines a packing with capacity determined by the edge count and
label parameters, without computing the largest class load. -/
noncomputable def boundedPacking {E R C : Type*} [Fintype E] [LinearOrder E]
    (U a : ℕ) (vertex : R ⊕ C ↪ Fin U) (rowOf : E → R) (colOf : E → C)
    (seed : SeededLabels.Seed U (6 * a)) (h : Balanced U a vertex rowOf colOf seed) :
    Packing rowOf colOf a 64 :=
  Packing.ofLabelsBounded rowOf colOf
    (fun r => label U a seed (vertex (.inl r)))
    (fun c => label U a seed (vertex (.inr c))) h

/-- Four-wise independent short seeds supply the occupancy certificate needed by both
packing constructions. Only the variance size hypothesis is needed at this stage. -/
theorem exists_balanced_labels {E R C : Type*} [Fintype E]
    [Finite R] [DecidableEq R] [Finite C] [DecidableEq C]
    (U a : ℕ) (vertex : R ⊕ C ↪ Fin U) (rowOf : E → R) (colOf : E → C) {Δ : ℕ}
    (hrow : ∀ v, #{e | rowOf e = v} ≤ Δ) (hcol : ∀ v, #{e | colOf e = v} ≤ Δ)
    (hM : 2 * Δ * (64 ^ (2 * a)) ^ 2 ≤ Fintype.card E) :
    ∃ seed : SeededLabels.Seed U (6 * a), Balanced U a vertex rowOf colOf seed := by
  have hh := ((SeededLabels.fourWise U (6 * a)).map_equiv (wordEquiv a)).comp vertex.injective
  have hcard : Fintype.card ((Fin a → Fin 64) × (Fin a → Fin 64)) = 64 ^ (2 * a) := by
    simp [← pow_add, two_mul]
  obtain ⟨seed, hseed⟩ := exists_occupancy_le_of_fourWise rowOf colOf hh
    (fun e => hrow (rowOf e)) (fun e => hcol (colOf e)) (hcard ▸ hM)
  have hocc : ∀ γ, occupancy (pairLabel rowOf colOf
      (fun r => label U a seed (vertex (.inl r)))
      (fun c => label U a seed (vertex (.inr c)))) γ * 64 ^ (2 * a) ≤
        2 * Fintype.card E := by
    intro γ
    change occupancy (fun e =>
      (label U a seed (vertex (.inl (rowOf e))), label U a seed (vertex (.inr (colOf e))))) γ *
        64 ^ (2 * a) ≤ _
    have h := hseed γ
    change occupancy (fun e =>
      (label U a seed (vertex (.inl (rowOf e))), label U a seed (vertex (.inr (colOf e))))) γ *
        Fintype.card ((Fin a → Fin 64) × (Fin a → Fin 64)) ≤ _ at h
    simpa only [hcard] using h
  exact ⟨seed, hocc⟩

/-- A short seed gives the full packet and port bounds under (D.6), with injectivity and
orientation already supplied by `packing`. The order on edges fixes the class-rank convention. -/
theorem exists_packing {E R C : Type*} [Fintype E] [LinearOrder E]
    [Finite R] [DecidableEq R] [Finite C] [DecidableEq C]
    (U a : ℕ) (vertex : R ⊕ C ↪ Fin U) (rowOf : E → R) (colOf : E → C) {Δ : ℕ}
    (hrow : ∀ v, #{e | rowOf e = v} ≤ Δ) (hcol : ∀ v, #{e | colOf e = v} ≤ Δ)
    (hM : 2 * Δ * (64 ^ (2 * a)) ^ 2 ≤ Fintype.card E)
    (hL : 2 ^ a * 64 ^ (2 * a) ≤ Fintype.card E) :
    ∃ seed : SeededLabels.Seed U (6 * a),
      (packing U a vertex rowOf colOf seed).numPackets * 2 ^ a ≤ 3 * Fintype.card E ∧
      (∀ i σ, 64 * #{e | (packing U a vertex rowOf colOf seed).rowLabel (rowOf e) i = σ} ≤
        2 * Fintype.card E) ∧
      (∀ i σ, 64 * #{e | (packing U a vertex rowOf colOf seed).colLabel (colOf e) i = σ} ≤
        2 * Fintype.card E) := by
  obtain ⟨seed, hocc⟩ := exists_balanced_labels U a vertex rowOf colOf hrow hcol hM
  exact ⟨seed, Packing.numPackets_ofLabels_mul_le rowOf colOf _ _ hocc hL,
    Packing.row_ports_ofLabels_le rowOf colOf _ _ hocc,
    Packing.col_ports_ofLabels_le rowOf colOf _ _ hocc⟩

/-- The same short seed existence gives the bounded-capacity packing with all original
packet and port bounds. The occupancy certificate is retained for subsequent rank queries. -/
theorem exists_boundedPacking {E R C : Type*} [Fintype E] [LinearOrder E]
    [Finite R] [DecidableEq R] [Finite C] [DecidableEq C]
    (U a : ℕ) (vertex : R ⊕ C ↪ Fin U) (rowOf : E → R) (colOf : E → C) {Δ : ℕ}
    (hrow : ∀ v, #{e | rowOf e = v} ≤ Δ) (hcol : ∀ v, #{e | colOf e = v} ≤ Δ)
    (hM : 2 * Δ * (64 ^ (2 * a)) ^ 2 ≤ Fintype.card E)
    (hL : 2 ^ a * 64 ^ (2 * a) ≤ Fintype.card E) :
    ∃ (seed : SeededLabels.Seed U (6 * a)) (h : Balanced U a vertex rowOf colOf seed),
      let P := boundedPacking U a vertex rowOf colOf seed h
      P.numPackets * 2 ^ a ≤ 3 * Fintype.card E ∧
        (∀ i σ, 64 * #{e | P.rowLabel (rowOf e) i = σ} ≤ 2 * Fintype.card E) ∧
        (∀ i σ, 64 * #{e | P.colLabel (colOf e) i = σ} ≤ 2 * Fintype.card E) := by
  obtain ⟨seed, hocc⟩ := exists_balanced_labels U a vertex rowOf colOf hrow hcol hM
  exact ⟨seed, hocc, Packing.numPackets_ofLabelsBounded_mul_le rowOf colOf _ _ hocc hL,
    Packing.row_ports_ofLabelsBounded_le rowOf colOf _ _ hocc,
    Packing.col_ports_ofLabelsBounded_le rowOf colOf _ _ hocc⟩

end Cslib.PacketPacking.Seeded

