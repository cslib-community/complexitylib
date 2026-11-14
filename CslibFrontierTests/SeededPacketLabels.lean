/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Foundations.Combinatorics.SeededPacketLabels
import CslibFrontier.Probability.KWiseIndependent.Trinomial

/-! Short seeds instantiate the packing condition at its tight K₃₂,₃₂ size threshold.
The seed has 24 bits, compared with 64 bits for the table of one label per vertex. -/

open Cslib.BalancedSchedules Cslib.Probability Finset

example : 4 * trinomialDeg 64 1 = 24 := by
  have htwo : trinomialStepAux 2 = 0 := by
    rw [trinomialStepAux]
    norm_num
  have hsix : trinomialStepAux 6 = 1 := by
    rw [trinomialStepAux]
    norm_num [htwo]
  have hlog : Nat.clog 2 64 = 6 := by decide
  norm_num [trinomialDeg, trinomialStep, trinomialTargetBits, hlog, hsix]

example : ∃ seed : SeededLabels.Seed 64 1, ∀ γ,
    occupancy (incidenceLabel (Prod.fst : Fin 32 × Fin 32 → Fin 32) Prod.snd
      (fun r => SeededLabels.label 64 1 seed
        ((finSumFinEquiv : Fin 32 ⊕ Fin 32 ≃ Fin 64) (.inl r)))
      (fun c => SeededLabels.label 64 1 seed
        ((finSumFinEquiv : Fin 32 ⊕ Fin 32 ≃ Fin 64) (.inr c)))) γ * 4 ≤ 2048 := by
  have hrow (e : Fin 32 × Fin 32) :
      #{e' : Fin 32 × Fin 32 | e'.1 = e.1} ≤ 32 := by
    have hset : ({e' : Fin 32 × Fin 32 | e'.1 = e.1} : Finset _) = {e.1} ×ˢ univ := by
      ext ⟨x, y⟩
      simp [eq_comm]
    rw [hset]
    simp
  have hcol (e : Fin 32 × Fin 32) :
      #{e' : Fin 32 × Fin 32 | e'.2 = e.2} ≤ 32 := by
    have hset : ({e' : Fin 32 × Fin 32 | e'.2 = e.2} : Finset _) = univ ×ˢ {e.2} := by
      ext ⟨x, y⟩
      simp [eq_comm]
    rw [hset]
    simp
  have hsize : 2 * 32 * (2 ^ 1 * 2 ^ 1) ^ 2 ≤ Fintype.card (Fin 32 × Fin 32) := by
    norm_num
  have h := SeededLabels.exists_balanced_seed 64 1
    (finSumFinEquiv : Fin 32 ⊕ Fin 32 ≃ Fin 64).toEmbedding
    Prod.fst Prod.snd hrow hcol hsize
  simpa using h

/- The empty universe still has a well-defined hash family and a nonempty seed space. -/
example : Nonempty (SeededLabels.Seed 0 0) := inferInstance

example : Fintype.card (SeededLabels.Seed 0 0) = 256 := by
  rw [SeededLabels.card_seed]
  have hone : trinomialStepAux 1 = 0 := by
    rw [trinomialStepAux]
    norm_num
  have hlog : Nat.clog 2 2 = 1 := by decide
  norm_num [trinomialDeg, trinomialStep, trinomialTargetBits, hlog, hone]
