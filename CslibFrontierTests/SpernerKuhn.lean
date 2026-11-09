/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Combinatorics.Sperner.Kuhn
import CslibFrontier.Foundations.Combinatorics.Sperner
import Mathlib.Tactic.IntervalCases

/-! Sperner's lemma on the Kuhn-triangulated hypergrid: exact panchromatic counts on concrete
colourings in dimensions `0` to `3`, agreement with the two-dimensional grid of
`Cslib.Sperner.triangles`, a colouring satisfying the Sperner boundary condition that is not a valid
colouring of Chen, Deng and Teng, a colouring violating the boundary condition, and the adjacency
of the triangulation. -/

namespace CslibFrontierTests.SpernerKuhn

open Cslib Cslib.Sperner Cslib.Sperner.KuhnSimplex Finset

/-! ### The triangulation -/

-- The `3 × 3` square grid has `2 · 9` triangles, as in `Cslib.Sperner.triangles`.
example : #(kuhnSimplices 2 ![3, 3]) = 18 := by decide

-- The unit cube is cut into `3! = 6` simplices.
example : #(kuhnSimplices 3 ![1, 1, 1]) = 6 := by decide

-- Crossing an interior facet and then crossing back returns to the original simplex.
example : across (⟨![0, 0], 1⟩ : KuhnSimplex 2) 1 = ⟨![0, 0], Equiv.swap 0 1⟩ := by decide

example : across (across (⟨![0, 0], 1⟩ : KuhnSimplex 2) 1) (mate 1) = ⟨![0, 0], 1⟩ := by decide

example : (across (⟨![1, 0], 1⟩ : KuhnSimplex 2) 0).base = ![0, 0] := by decide

/-! ### Dimension one -/

/-- An alternating colouring of the segment `[0, 3]`. -/
private def c1 (p : Fin 1 → ℕ) : Fin 2 := if p 0 % 2 = 0 then 1 else 0

private theorem c1_isHypergridSperner : IsHypergridSperner ![3] c1 := by
  intro p hp i
  fin_cases i
  have h := hp 0
  simp only [Fin.isValue, Matrix.cons_val_fin_one] at h ⊢
  interval_cases hp0 : p 0 <;> simp [c1, hp0]

example : Odd #{s ∈ kuhnSimplices 1 ![3] | IsPanchromatic c1 s} :=
  c1_isHypergridSperner.odd_card_isPanchromatic

-- All three segments are panchromatic.
example : #{s ∈ kuhnSimplices 1 ![3] | IsPanchromatic c1 s} = 3 := by decide

/-! ### Dimension two: agreement with `Cslib.Sperner.triangles` -/

-- In dimension two the boundary colouring is `Cslib.Sperner.boundaryColor`.
example (p : Fin 2 → ℕ) : hypergridBoundaryColor p = boundaryColor (p 0, p 1) := by
  by_cases h1 : p 1 = 0 <;> by_cases h0 : p 0 = 0 <;>
    simp [hypergridBoundaryColor, boundaryColor, Fin.init, h0, h1]

/-- The Sperner colouring of the `3 × 3` grid of `CslibFrontierTests.Sperner` with seven
trichromatic
triangles. -/
private def c3 (p : ℕ × ℕ) : Fin 3 :=
  if p = (1, 1) then 0 else if p = (1, 2) ∨ p = (2, 1) then 1 else if p = (2, 2) then 2
  else boundaryColor p

-- The Kuhn triangulation and `Cslib.Sperner.triangles` give the same count.
example : #{s ∈ kuhnSimplices 2 ![3, 3] | IsPanchromatic (fun p => c3 (p 0, p 1)) s} = 7 := by
  decide

example : #{t ∈ triangles 3 3 | Trichromatic c3 t} = 7 := by decide

/-! ### The boundary condition is weaker than validity -/

/-- A colouring of the `2 × 2` grid that gives the boundary point `(0, 1)` colour `2` instead of its
boundary colour `1`. -/
private def cg (p : Fin 2 → ℕ) : Fin 3 :=
  if p 0 = 0 ∧ p 1 = 1 then 2 else hypergridBoundaryColor p

private theorem cg_isHypergridSperner : IsHypergridSperner ![2, 2] cg := by
  intro p hp i
  obtain ⟨a, b, rfl⟩ : ∃ a b, p = ![a, b] := ⟨p 0, p 1, by ext j; fin_cases j <;> rfl⟩
  have ha := hp 0
  have hb := hp 1
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at ha hb
  interval_cases a <;> interval_cases b <;> fin_cases i <;> decide

example : ¬IsValidColoring ![2, 2] cg := fun h => by
  have := h ![0, 1] (by intro i; fin_cases i <;> decide) ⟨0, .inl rfl⟩
  revert this
  decide

example : ∃ s ∈ kuhnSimplices 2 ![2, 2], IsPanchromatic cg s :=
  cg_isHypergridSperner.exists_isPanchromatic

example : #{s ∈ kuhnSimplices 2 ![2, 2] | IsPanchromatic cg s} = 1 := by decide

/-! ### The boundary condition is needed -/

-- A constant colouring violates the boundary condition and has no panchromatic simplex.
example : ¬IsHypergridSperner ![2, 2] (fun _ => (0 : Fin 3)) := fun h =>
  absurd ((h ![0, 0] (by intro i; fin_cases i <;> decide) 0).1 rfl) (by decide)

example : #{s ∈ kuhnSimplices 2 ![2, 2] | IsPanchromatic (fun _ => (0 : Fin 3)) s} = 0 := by
  decide

/-! ### Dimensions zero and three; valid colourings -/

-- The single point is a panchromatic simplex.
example : #{s ∈ kuhnSimplices 0 ![] | IsPanchromatic (fun _ => (0 : Fin 1)) s} = 1 := by decide

example : #{s ∈ kuhnSimplices 3 ![2, 2, 2] | IsPanchromatic hypergridBoundaryColor s} = 1 := by
  decide

-- The boundary colouring is itself a valid colouring, so the hypotheses are satisfiable.
example : IsHypergridSperner ![2, 3, 1] hypergridBoundaryColor :=
  IsValidColoring.isHypergridSperner (fun _ _ _ => rfl) (by decide)

example : ∃ p : Fin 3 → ℕ, (∀ i, p i < ![2, 3, 1] i) ∧ ∃ P : Finset (Fin 3 → ℕ),
    (∀ q ∈ P, ∀ i, q i = p i ∨ q i = p i + 1) ∧ #P = 4 ∧
      Set.InjOn (hypergridBoundaryColor (n := 3)) P :=
  IsValidColoring.exists_panchromatic (fun _ _ _ => rfl) (by decide)

end CslibFrontierTests.SpernerKuhn
