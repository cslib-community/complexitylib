/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.KCenter.DominatingSet
public import CslibFrontier.Algorithms.Lean.KCenter.Gonzalez
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Worked k-center examples

These kernel-checked examples (using no `native_decide`) exercise Gonzalez's farthest-first
traversal `Cslib.Algorithms.Lean.KCenter.gonzalez`, the k-center optimum
`Cslib.Algorithms.Lean.KCenter.optRadius` and the dominating-set gap:

1. Three points on a line at `0, 1, 2` with one center: Gonzalez picks the endpoint `0` and has
   radius `2`, while the middle point has radius `1`. The factor `2` of the 2-approximation is
   attained. With two centers, Gonzalez is optimal.
2. The packing lower bound pins the optimum without enumerating center sets.
3. Without the triangle inequality the ratio is unbounded: a distance with `d 0 2 = 100` makes
   Gonzalez pay `100` against an optimum of `1`.
4. With a distance vanishing between distinct points, the centers repeat: the hypotheses of
   `nodup_gonzalez` cannot be dropped.
5. Instantiation with Mathlib's `dist` on `ℝ`.
6. The path `0 - 1 - 2` as a dominating-set instance: `{1}` dominates, Gonzalez's `{0}` does not,
   and Gonzalez's radius is exactly twice the optimum, so the gap theorem needs `ρ < 2`. The empty
   graph on two vertices has no dominating vertex and optimum `2`.
-/

public section

namespace ComplexityTests.KCenter

open Cslib.Algorithms.Lean.KCenter

/-! ### 1. Three points on a line attain the factor 2 -/

/-- Three points on a line at `0, 1, 2`. -/
def lineDist (i j : Fin 3) : ℕ := max i.val j.val - min i.val j.val

theorem lineDist_symm (i j : Fin 3) : lineDist i j = lineDist j i := by
  unfold lineDist
  rw [max_comm, min_comm]

theorem lineDist_triangle (i j l : Fin 3) : lineDist i l ≤ lineDist i j + lineDist j l := by
  revert i j l
  decide

/-- With one center, Gonzalez picks the first point, `0`. -/
example : gonzalez lineDist (List.finRange 3) 1 = [0] := by decide

/-- With two centers, it adds the farthest point, `2`; with three, the remaining point `1`. -/
example : gonzalez lineDist (List.finRange 3) 2 = [0, 2] := by decide

example : gonzalez lineDist (List.finRange 3) 3 = [0, 2, 1] := by decide

/-- Gonzalez's radius with one center is `2`. -/
example : radius lineDist (gonzalez lineDist (List.finRange 3) 1).toFinset = (2 : ℕ) := by decide

/-- The optimal radius with one center is `1`, at the middle point: the factor `2` is attained. -/
example : optRadius lineDist 1 = (1 : ℕ) := by decide

example : radius lineDist {1} = (1 : ℕ) := by decide

/-- With two centers Gonzalez is optimal. -/
example : radius lineDist (gonzalez lineDist (List.finRange 3) 2).toFinset = (1 : ℕ) := by decide

example : optRadius lineDist 2 = (1 : ℕ) := by decide

/-- No centers give radius `⊤`. -/
example : optRadius lineDist 0 = ⊤ := optRadius_zero lineDist

/-- The theorem gives the bound `2 * 1` with one center from the bound `1` on the optimum. -/
example :
    radius lineDist (gonzalez lineDist (List.finRange 3) 1).toFinset ≤ ((2 * 1 : ℕ) : WithTop ℕ) :=
  radius_gonzalez_le_two_mul lineDist_symm lineDist_triangle List.mem_finRange
    (optRadius_le_radius (S := {1}) (by decide) |>.trans (by decide))

/-- The centers are distinct, since `lineDist` vanishes exactly on the diagonal. -/
example : (gonzalez lineDist (List.finRange 3) 3).Nodup :=
  nodup_gonzalez (by decide) (by decide) (by decide)

/-! ### 2. The packing lower bound -/

/-- The endpoints `0` and `2` are farther than `2 * 0` apart, so one center has radius above `0`. -/
example : ((0 : ℕ) : WithTop ℕ) < optRadius lineDist 1 :=
  lt_optRadius_of_pairwise_lt lineDist_symm lineDist_triangle (M := [0, 2]) (by decide) (by decide)

/-- All three points are farther than `2 * 0` apart, so two centers have radius above `0`. -/
example : ((0 : ℕ) : WithTop ℕ) < optRadius lineDist 2 :=
  lt_optRadius_of_pairwise_lt lineDist_symm lineDist_triangle (M := [0, 1, 2]) (by decide)
    (by decide)

/-! ### 3. Without the triangle inequality -/

/-- Three points with `d 0 1 = d 1 2 = 1` but `d 0 2 = 100`: symmetric, not a metric. -/
def badDist (i j : Fin 3) : ℕ :=
  if i = j then 0 else if i.val + j.val = 2 then 100 else 1

example : ¬ ∀ i j l : Fin 3, badDist i l ≤ badDist i j + badDist j l := by decide

/-- Gonzalez pays `100` with one center against an optimum of `1`. -/
example : radius badDist (gonzalez badDist (List.finRange 3) 1).toFinset = (100 : ℕ) := by decide

example : optRadius badDist 1 = (1 : ℕ) := by decide

/-! ### 4. Repeated centers under a pseudometric -/

/-- Two points at distance `0`: a pseudometric that does not separate them. -/
def zeroDist (_ _ : Fin 2) : ℕ := 0

/-- Gonzalez picks the first point twice; the optimum is still met. -/
example : gonzalez zeroDist (List.finRange 2) 2 = [0, 0] := by decide

example : ¬ (gonzalez zeroDist (List.finRange 2) 2).Nodup := by decide

/-! ### 5. Mathlib's distance on `ℝ` -/

/-- Real points `0, 1, 2` with one competing center at `1` covering within `1`: Gonzalez's center
is within `2 * 1` of every point. -/
example {v : ℝ} (hv : v ∈ [0, 1, 2]) :
    centerDist dist (gonzalez dist [(0 : ℝ), 1, 2] 1).toFinset v ≤ ((2 * 1 : ℝ) : WithTop ℝ) := by
  refine centerDist_gonzalez_le_two_mul dist_comm dist_triangle (C := {1}) (by simp) ?_ hv
  intro w hw
  refine ⟨1, Finset.mem_singleton_self 1, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> norm_num [Real.dist_eq]

/-! ### 6. Dominating sets -/

/-- The path `0 - 1 - 2`. -/
def path3 : SimpleGraph (Fin 3) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

instance : DecidableRel path3.Adj := fun i j =>
  inferInstanceAs (Decidable (i.val + 1 = j.val ∨ j.val + 1 = i.val))

example : path3.IsDominatingSet ({1} : Finset (Fin 3)) := by decide

example : ¬ path3.IsDominatingSet ({0} : Finset (Fin 3)) := by decide

/-- A dominating vertex exists, so the optimum is `1`. -/
example : optRadius (domDist (α := ℕ) path3) 1 ≤ (1 : ℕ) :=
  optRadius_domDist_le_one_iff.2 ⟨{1}, by decide, by decide⟩

/-- Gonzalez starts at the endpoint `0`, which does not dominate: radius exactly `2`. -/
example : gonzalez (domDist (α := ℕ) path3) (List.finRange 3) 1 = [0] := by decide

example : radius (domDist (α := ℕ) path3)
    (gonzalez (domDist (α := ℕ) path3) (List.finRange 3) 1).toFinset = (2 : ℕ) := by decide

/-- A center set of radius less than `2` dominates: the radius of `{1}` is `1`. -/
example : path3.IsDominatingSet ({1} : Finset (Fin 3)) :=
  radius_domDist_lt_two_iff (α := ℕ).1 (by decide)

/-- Gonzalez's single center `{0}` is exactly `2`-approximate on the path, and the path has the
dominating vertex `1`: the decision criterion of the gap theorem needs `ρ < 2`. -/
example : ¬ ((∃ T : Finset (Fin 3), T.card ≤ 1 ∧ path3.IsDominatingSet T) ↔
    path3.IsDominatingSet ((gonzalez (domDist (α := ℕ) path3) (List.finRange 3) 1).toFinset :
      Finset (Fin 3))) := by
  decide

/-- The approximation hypothesis of the gap theorem holds with `ρ = 2` for Gonzalez's output, by
the 2-approximation theorem, and the conclusion fails: the hypothesis `ρ < 2` is necessary. -/
example : (∀ r : ℕ, optRadius (domDist (α := ℕ) path3) 1 ≤ (r : WithTop ℕ) →
      radius (domDist (α := ℕ) path3)
        (gonzalez (domDist (α := ℕ) path3) (List.finRange 3) 1).toFinset ≤
          ((2 * r : ℕ) : WithTop ℕ)) ∧
    ¬ path3.IsDominatingSet
      ((gonzalez (domDist (α := ℕ) path3) (List.finRange 3) 1).toFinset : Set (Fin 3)) :=
  ⟨fun _ hr => radius_gonzalez_le_two_mul domDist_symm domDist_triangle List.mem_finRange hr,
    by decide⟩

/-- The approximation hypothesis of the gap theorem is satisfiable with `ρ = 1`: the optimal
center `{1}`, whose single vertex dominates the path. -/
example : path3.IsDominatingSet ({1} : Finset (Fin 3)) := by
  refine isDominatingSet_of_radius_le_mul (α := ℕ) (k := 1) (ρ := 1) (by decide) ?_
    ⟨{1}, by decide, by decide⟩
  intro r hr
  have h1 : radius (domDist (α := ℕ) path3) ({1} : Finset (Fin 3)) = (1 : ℕ) := by decide
  have h2 : optRadius (domDist (α := ℕ) path3) 1 = (1 : ℕ) := by decide
  rw [h1, one_mul]
  rw [h2] at hr
  exact hr

/-- More rounds than points: Gonzalez repeats a center once every point is chosen. -/
example : gonzalez (domDist (α := ℕ) path3) (List.finRange 3) 5 = [0, 2, 1, 0, 0] := by decide

/-- On the three-point path, the optimum over at most `2` centers is attained by exactly `2`. -/
example : ∃ S : Finset (Fin 3), S.card = 2 ∧
    radius (domDist (α := ℕ) path3) S = optRadius (domDist (α := ℕ) path3) 2 :=
  exists_card_eq_radius_eq_optRadius _ (by decide)

/-- On the empty graph with two vertices no vertex dominates, so one center has optimum `2`. -/
example : optRadius (domDist (α := ℕ) (⊥ : SimpleGraph (Fin 2))) 1 = (2 : ℕ) :=
  optRadius_domDist_eq_two Nat.one_pos (by decide)

end ComplexityTests.KCenter
