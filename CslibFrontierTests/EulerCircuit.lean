/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.Euler.Circuit

/-!
# Worked Euler-circuit examples

These kernel-checked examples (using no `native_decide`) exercise
`Cslib.Algorithms.Lean.Euler.eulerCircuit` and Euler's theorem:

1. The bowtie: two triangles sharing vertex `2`. The greedy walk from `0` closes the first
   triangle at once, and Hierholzer's splicing inserts the second triangle at `2`.
2. A multigraph with parallel edges and a self-loop: two parallel edges `0 - 1`, a self-loop at
   `1` (counted twice in the degree), and the triangle `0 - 1 - 2`, whose last edge is listed
   reversed.
3. Odd degrees: the path `0 - 1 - 2` has no Euler circuit (`exists_isEulerCircuit_iff`).
4. Disconnection: two disjoint triangles have even degrees but no Euler circuit, because the edge
   `3 - 4` is not connected to `0`.
5. The empty multigraph: its Euler circuit is the single vertex.
-/

public section

namespace CslibFrontierTests.EulerCircuit

open Cslib.Algorithms.Lean.Euler

/-! ### 1. The bowtie -/

/-- Two triangles `0 - 1 - 2` and `2 - 3 - 4` sharing vertex `2`. -/
abbrev bowtie : List (Fin 5 × Fin 5) := [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 2)]

example : (walkFrom bowtie.length bowtie 0).1 = [0, 1, 2, 0] := by decide

example : eulerCircuit bowtie 0 = [0, 1, 2, 3, 4, 2, 0] := by decide

example : IsEulerCircuit bowtie 0 [0, 1, 2, 3, 4, 2, 0] := ⟨rfl, rfl, by decide⟩

/-! ### 2. Parallel edges and a self-loop -/

/-- Two parallel edges `0 - 1`, a self-loop at `1`, and the triangle `0 - 1 - 2` with its last
edge listed as `(0, 2)`. -/
abbrev multi : List (Fin 3 × Fin 3) := [(0, 1), (1, 0), (1, 1), (0, 1), (1, 2), (0, 2)]

example : degree multi 1 = 6 ∧ degree multi 0 = 4 ∧ degree multi 2 = 2 := by decide

example : eulerCircuit multi 0 = [0, 1, 0, 1, 1, 2, 0] := by decide

example : IsEulerCircuit multi 0 (eulerCircuit multi 0) := ⟨rfl, rfl, by decide⟩

/-! ### 3. Odd degrees rule out an Euler circuit -/

example : ¬ ∃ w, IsEulerCircuit [((0 : Fin 3), (1 : Fin 3)), (1, 2)] 0 w := by
  rw [exists_isEulerCircuit_iff]
  rintro ⟨h, -⟩
  exact Nat.not_even_one (by simpa [degree, ends] using h 0)

/-! ### 4. Disconnection rules out an Euler circuit -/

/-- Two disjoint triangles `0 - 1 - 2` and `3 - 4 - 5`. -/
abbrev twoTriangles : List (Fin 6 × Fin 6) := [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]

example : ∀ x, Even (degree twoTriangles x) := by decide

/-- The edges of `twoTriangles` never join `{0, 1, 2}` to `{3, 4, 5}`. -/
theorem lt_three_iff_of_eqvGen {a b : Fin 6}
    (h : Relation.EqvGen (fun a b => (a, b) ∈ twoTriangles) a b) : (a < 3 ↔ b < 3) := by
  induction h with
  | rel a b hab =>
    revert a b
    decide
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

example : ¬ ∃ w, IsEulerCircuit twoTriangles 0 w := by
  rw [exists_isEulerCircuit_iff]
  rintro ⟨-, h⟩
  have := lt_three_iff_of_eqvGen (h (3, 4) (by decide))
  simp at this

/-! ### 5. The empty multigraph -/

example : eulerCircuit ([] : List (Fin 2 × Fin 2)) 1 = [1] := by decide

example : IsEulerCircuit ([] : List (Fin 2 × Fin 2)) 1 [1] := ⟨rfl, rfl, by decide⟩

end CslibFrontierTests.EulerCircuit
