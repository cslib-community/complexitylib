/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Foundations.Combinatorics.CollisionSchedules
import Mathlib.Tactic.NormNum

open Cslib.BalancedSchedules Finset
open scoped BigOperators

/- Full label tables instantiate the transfer hypothesis, including shared endpoints. This
checks the contract without claiming that these tables are short seeds. -/
example {E R C L : Type*} [Fintype E] [Fintype R] [DecidableEq R]
    [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L] [Nonempty L]
    (rowOf : E → R) (colOf : E → C) {Δ : ℕ}
    (hrow : ∀ e, #{e' | rowOf e' = rowOf e} ≤ Δ)
    (hcol : ∀ e, #{e' | colOf e' = colOf e} ≤ Δ)
    (hsize : 2 * Δ * Fintype.card (L × L) ^ 2 ≤ Fintype.card E) :
    ∃ s : (R → L) × (C → L), ∀ γ,
      occupancy (incidenceLabel rowOf colOf s.1 s.2) γ * Fintype.card (L × L) ≤
        2 * Fintype.card E := by
  apply exists_occupancy_le_of_collision rowOf colOf Prod.fst Prod.snd ?_ hrow hcol hsize
  intro e e'
  rw [show (𝔼 s : (R → L) × (C → L),
      if incidenceLabel rowOf colOf s.1 s.2 e = incidenceLabel rowOf colOf s.1 s.2 e'
      then (1 : ℚ) else 0) =
      𝔼 ρ : R → L, 𝔼 κ : C → L,
        if incidenceLabel rowOf colOf ρ κ e = incidenceLabel rowOf colOf ρ κ e'
        then (1 : ℚ) else 0 from by
    simpa only [univ_product_univ] using expect_product univ univ
      (fun (s : (R → L) × (C → L)) =>
        if incidenceLabel rowOf colOf s.1 s.2 e = incidenceLabel rowOf colOf s.1 s.2 e'
        then (1 : ℚ) else 0)]
  exact expect_incidenceLabel_collision rowOf colOf e e'

/- A constant seed family does not meet the collision contract for two disjoint edges. -/
example :
    (𝔼 _ : Unit, if ((false, false) : Bool × Bool) = (false, false) then (1 : ℚ) else 0) ≠
      (if (false : Bool) = true then 1 else 1 / (Fintype.card Bool : ℚ)) *
        (if (false : Bool) = true then 1 else 1 / (Fintype.card Bool : ℚ)) := by
  norm_num

/- Shared endpoints are not independent fresh labels; parallel edges collide with certainty. -/
example :
    (𝔼 ρ : Unit → Bool, 𝔼 κ : Unit → Bool,
      if incidenceLabel (fun _ : Bool => ()) (fun _ : Bool => ()) ρ κ false =
        incidenceLabel (fun _ : Bool => ()) (fun _ : Bool => ()) ρ κ true
      then (1 : ℚ) else 0) = 1 := by
  rw [expect_incidenceLabel_collision]
  norm_num

/- On K₃₂,₃₂ the size hypothesis is tight for Boolean labels: 2·32·4² = 1024. -/
example : ∃ label : Fin 32 ⊕ Fin 32 → Bool, ∀ γ,
    occupancy (incidenceLabel (Prod.fst : Fin 32 × Fin 32 → Fin 32) Prod.snd
      (fun r => label (.inl r)) (fun c => label (.inr c))) γ * 4 ≤ 2048 := by
  have hrow (e : Fin 32 × Fin 32) : #{e' : Fin 32 × Fin 32 | e'.1 = e.1} ≤ 32 := by
    have hset : ({e' : Fin 32 × Fin 32 | e'.1 = e.1} : Finset _) = {e.1} ×ˢ univ := by
      ext ⟨x, y⟩
      simp [eq_comm]
    rw [hset]
    simp
  have hcol (e : Fin 32 × Fin 32) : #{e' : Fin 32 × Fin 32 | e'.2 = e.2} ≤ 32 := by
    have hset : ({e' : Fin 32 × Fin 32 | e'.2 = e.2} : Finset _) = univ ×ˢ {e.2} := by
      ext ⟨x, y⟩
      simp [eq_comm]
    rw [hset]
    simp
  have hsize : 2 * 32 * Fintype.card (Bool × Bool) ^ 2 ≤
      Fintype.card (Fin 32 × Fin 32) := by norm_num
  have h := exists_occupancy_le_of_fourWise Prod.fst Prod.snd
    (Cslib.Probability.isKWiseIndependentHash_id (X := Fin 32 ⊕ Fin 32) (Y := Bool) 4)
    hrow hcol hsize
  simpa using h
