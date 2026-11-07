/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Matching.MVV

/-! The Mulmuley–Vazirani–Vazirani core on the complete bipartite graph on two vertices: an
isolating weight recovers the matching from the determinant and the adjugate, equal weights make
the determinant vanish, the success probability bound at `N = 2 |E|`, and axiom guards. -/

namespace ComplexityTests.MVVMatching

open Finset Matrix Equiv Cslib.Algorithms.Matching Cslib.Circuits.BipartiteMatching

/-- The complete bipartite graph on `Fin 2`. -/
def complete : Fin 2 × Fin 2 → Bool := fun _ => true

/-- Weight `1` on the edges `(0, 0)` and `(1, 1)`, weight `2` on the others: the identity
matching has weight `2` and the other matching weight `4`. -/
def w (e : Fin 2 × Fin 2) : ℕ := if e.1 = e.2 then 1 else 2

/-- The identity is the unique minimum-weight perfect matching. -/
theorem isUniqueMinMatching_one : IsUniqueMinMatching complete w 1 := by
  refine ⟨mem_perfectMatchings.2 fun _ => rfl, fun σ _ hσ => ?_⟩
  have hs : σ = swap 0 1 := by
    revert σ; decide
  subst hs
  simp [matchingWeight, Fin.sum_univ_two, w]

/-- The weighted Edmonds matrix has determinant `2 · 2 - 4 · 4 = -12`. -/
theorem det_eq : (weightedEdmonds complete w).det = -12 := by
  simp [det_fin_two, weightedEdmonds_apply, complete, w]

/-- The `2`-adic valuation of `-12` is the weight `2` of the isolated matching. -/
example : padicValInt 2 (-12) = 2 := by
  rw [← det_eq, ← matchingWeight_eq_padicValInt_det isUniqueMinMatching_one]
  simp [matchingWeight, w]

/-- The divisibility test keeps the edge `(0, 0)` of the isolated matching... -/
example : ¬ (2 : ℤ) ^ (2 + 1) ∣
    weightedEdmonds complete w 0 0 * adjugate (weightedEdmonds complete w) 0 0 := by
  have h := ((two_pow_dvd_mul_adjugate_weightedEdmonds isUniqueMinMatching_one 0 0).2).1 rfl
  simpa [matchingWeight, Fin.sum_univ_two, w] using h

/-- ...and rejects the edge `(0, 1)`. -/
example : (2 : ℤ) ^ (2 + 1) ∣
    weightedEdmonds complete w 0 1 * adjugate (weightedEdmonds complete w) 1 0 := by
  have h := mt ((two_pow_dvd_mul_adjugate_weightedEdmonds isUniqueMinMatching_one 0 1).2).2
    (by decide)
  simpa [matchingWeight, Fin.sum_univ_two, w] using h

/-- With equal weights the two perfect matchings tie and the determinant vanishes, so no
minimum-weight perfect matching is unique. -/
example : (weightedEdmonds complete fun _ => 1).det = 0 ∧
    ¬ ∃ σ₀, IsUniqueMinMatching complete (fun _ => 1) σ₀ := by
  have h : (weightedEdmonds complete fun _ => 1).det = 0 := by
    simp [det_fin_two, weightedEdmonds_apply, complete]
  exact ⟨h, fun ⟨_, hσ₀⟩ => det_weightedEdmonds_ne_zero hσ₀ h⟩

/-- `complete` has four edges. -/
theorem card_edges : Fintype.card (Edges complete) = 4 := by
  simp [Edges, complete]

/-- `complete` has a perfect matching. -/
theorem hasPerfectMatching_complete : HasPerfectMatching complete := ⟨1, fun _ => rfl⟩

/-- `8 = 2 |E|`. -/
theorem two_mul_card_edges_le : 2 * Fintype.card (Edges complete) ≤ 8 := by rw [card_edges]

/-- With weights uniform on `{1, …, 8}`, `8 = 2 |E|`, the procedure returns a perfect matching
for at least half of the weight functions. -/
example : 1 / 2 ≤ dens (univ.filter fun w : Edges complete → Fin 8 =>
    ∃ σ ∈ perfectMatchings complete, ∀ i j, σ i = j ↔
      ¬ (2 : ℤ) ^ (padicValInt 2 (weightedEdmonds complete (extendWeight w)).det + 1) ∣
        weightedEdmonds complete (extendWeight w) i j *
          adjugate (weightedEdmonds complete (extendWeight w)) j i) :=
  -- `convert` reconciles the concrete `Decidable` instances on `Fin 2` with the generic ones.
  by convert half_le_dens_mvv (N := 8) hasPerfectMatching_complete two_mul_card_edges_le

/-! ### Axiom guards -/

/-- info: 'Cslib.Algorithms.Matching.two_pow_dvd_mul_adjugate_weightedEdmonds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_pow_dvd_mul_adjugate_weightedEdmonds

/-- info: 'Cslib.Algorithms.Matching.half_le_dens_mvv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms half_le_dens_mvv

end ComplexityTests.MVVMatching
