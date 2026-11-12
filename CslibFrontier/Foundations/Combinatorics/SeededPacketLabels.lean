/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.CollisionSchedules
public import CslibFrontier.Probability.KWiseIndependent.Trinomial

/-!
# Short seeds for balanced packet labels

The existing trinomial polynomial hash family supplies four-wise independent labels for the
tagged vertices of a bipartite multigraph. The collision-moment bound then gives one seed
whose every label-pair class has at most twice its average load. A seed has four field
coefficients and fits in `12 * max (clog 2 (max U 2)) (max bits 1)` bits.

The same seed is used on both sides and for all edges. This replaces the existence argument
behind the sequential label pass; it does not implement a native selector, certify the cost
of hash evaluation, or prove that a seed can be verified within an alternating time budget.
-/

public section

namespace Cslib.BalancedSchedules.SeededLabels

open Cslib.Probability Finset

/-- Four coefficients, each a fixed-width binary code in the chosen trinomial field. -/
abbrev Seed (U bits : ℕ) := Fin 4 → Fin (2 ^ trinomialDeg U bits)

/-- A fixed seed labels a vertex number by the low `bits` bits of its polynomial hash. -/
@[expose] noncomputable def label (U bits : ℕ) : Seed U bits → Fin U → Fin (2 ^ bits) :=
  trinomialPolyHash (trinomialStep U bits) 4 U bits

/-- The selected field supports the entire vertex universe and requested output width. -/
theorem fourWise (U bits : ℕ) : IsKWiseIndependentHash 4 (label U bits) :=
  isKWiseIndependentHash_trinomialPolyHash (le_two_pow_trinomialDeg U bits)
    (le_trinomialDeg U bits)

/-- The coefficient-vector seed space has exactly this many binary codes. -/
theorem card_seed (U bits : ℕ) :
    Fintype.card (Seed U bits) = 2 ^ (4 * trinomialDeg U bits) := by
  simp [Seed, ← pow_mul, Nat.mul_comm]

/-- Four fixed-width coefficients use only a constant times the larger index or label width. -/
theorem seed_bits_le (U bits : ℕ) :
    4 * trinomialDeg U bits ≤
      12 * max (Nat.clog 2 (max U 2)) (max bits 1) := by
  have := trinomialDeg_le_three_mul U bits
  omega

/-- A single short seed simultaneously balances every pair-label class. The degree condition
is the same variance condition as for the full-independent packing argument. -/
theorem exists_balanced_seed {E R C : Type*} [Fintype E] [Finite R] [DecidableEq R]
    [Finite C] [DecidableEq C] (U bits : ℕ) (vertex : R ⊕ C ↪ Fin U)
    (rowOf : E → R) (colOf : E → C) {Δ : ℕ}
    (hrow : ∀ e, #{e' | rowOf e' = rowOf e} ≤ Δ)
    (hcol : ∀ e, #{e' | colOf e' = colOf e} ≤ Δ)
    (hsize : 2 * Δ * (2 ^ bits * 2 ^ bits) ^ 2 ≤ Fintype.card E) :
    ∃ seed : Seed U bits, ∀ γ,
      occupancy (incidenceLabel rowOf colOf
        (fun r => label U bits seed (vertex (.inl r)))
        (fun c => label U bits seed (vertex (.inr c)))) γ *
          (2 ^ bits * 2 ^ bits) ≤ 2 * Fintype.card E := by
  have hh := (fourWise U bits).comp vertex.injective
  have hs : 2 * Δ * Fintype.card (Fin (2 ^ bits) × Fin (2 ^ bits)) ^ 2 ≤
      Fintype.card E := by simpa using hsize
  simpa using exists_occupancy_le_of_fourWise rowOf colOf hh hrow hcol hs

end Cslib.BalancedSchedules.SeededLabels
