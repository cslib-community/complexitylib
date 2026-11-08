/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the Mulmuley–Vazirani–Vazirani core)

import CslibFrontier.Algorithms.Matching.MVV

/-! The Mulmuley–Vazirani–Vazirani core on the complete bipartite graph on two vertices, checked as
a `module` client through the public characterization lemmas: an isolating weight recovers the
matching from the determinant and the adjugate, the procedure `mvvOutput` outputs exactly that
matching, equal weights make the determinant vanish, and the success probability bound at
`N = 2 |E|` applies with `exact`. -/

set_option linter.privateModule false

namespace ComplexityTests.MVVMatching

open Finset Matrix Equiv Cslib.Algorithms.Matching Cslib.Circuits.BipartiteMatching

/-- The complete bipartite graph on `Fin 2`. -/
def complete : Fin 2 × Fin 2 → Bool := fun _ => true

/-- Weight `1` on the edges `(0, 0)` and `(1, 1)`, weight `2` on the others: the identity
matching has weight `2` and the other matching weight `4`. -/
def w (e : Fin 2 × Fin 2) : ℕ := if e.1 = e.2 then 1 else 2

/-- The identity matching has weight `2`. -/
theorem matchingWeight_one : matchingWeight w 1 = 2 := by
  simp [matchingWeight_def, w]

/-- The identity is the unique minimum-weight perfect matching. -/
theorem isUniqueMinMatching_one : IsUniqueMinMatching complete w 1 := by
  refine isUniqueMinMatching_iff.2 ⟨mem_perfectMatchings.2 fun _ => rfl, fun σ _ hσ => ?_⟩
  have hall : ∀ τ : Perm (Fin 2), τ ≠ 1 → τ = swap 0 1 := by decide
  obtain rfl := hall σ hσ
  simp [matchingWeight_def, Fin.sum_univ_two, w]

/-- The weighted Edmonds matrix has determinant `2 · 2 - 4 · 4 = -12`. -/
theorem det_eq : (weightedEdmonds complete w).det = -12 := by
  simp [det_fin_two, weightedEdmonds_apply, complete, w]

/-- The `2`-adic valuation of `-12` is the weight `2` of the isolated matching. -/
example : padicValInt 2 (-12) = 2 := by
  rw [← det_eq, ← matchingWeight_eq_padicValInt_det isUniqueMinMatching_one, matchingWeight_one]

/-- The divisibility test keeps the edge `(0, 0)` of the isolated matching... -/
example : ¬ (2 : ℤ) ^ (2 + 1) ∣
    weightedEdmonds complete w 0 0 * adjugate (weightedEdmonds complete w) 0 0 := by
  have h := (apply_eq_iff_not_two_pow_succ_dvd_mul_adjugate isUniqueMinMatching_one 0 0).1 rfl
  rwa [matchingWeight_one] at h

/-- ...and rejects the edge `(0, 1)`. -/
example : (2 : ℤ) ^ (2 + 1) ∣
    weightedEdmonds complete w 0 1 * adjugate (weightedEdmonds complete w) 1 0 := by
  have h := mt (apply_eq_iff_not_two_pow_succ_dvd_mul_adjugate isUniqueMinMatching_one 0 1).2
    (by decide)
  rwa [matchingWeight_one, not_not] at h

/-- The procedure outputs exactly the pairs of the identity matching. -/
example (i j : Fin 2) : mvvOutput complete w i j ↔ i = j :=
  mvvOutput_iff_apply_eq isUniqueMinMatching_one i j

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

/-- On the edge `(0, 1)`, the label `3 : Fin 8` is the weight `4`. -/
example (v : Edges complete → Fin 8) (hv : v ⟨(0, 1), rfl⟩ = 3) :
    extendWeight v (0, 1) = 4 := by
  rw [extendWeight_of_edge v rfl, hv]
  rfl

/-- The edges of the identity matching are the two diagonal pairs. -/
example : (⟨(0, 0), rfl⟩ : Edges complete) ∈ matchingEdges complete 1 ∧
    (⟨(0, 1), rfl⟩ : Edges complete) ∉ matchingEdges complete 1 := by
  rw [mem_matchingEdges, mem_matchingEdges]
  decide

/-- With weights uniform on `{1, …, 8}`, `8 = 2 |E|`, the procedure returns a perfect matching
for at least half of the weight functions. -/
example : 1 / 2 ≤ dens (univ.filter fun v : Edges complete → Fin 8 =>
    MVVSucceeds complete (extendWeight v)) :=
  half_le_dens_mvv hasPerfectMatching_complete (by rw [card_edges])

end ComplexityTests.MVVMatching
