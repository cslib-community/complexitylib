/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.Macrocell
public import Complexity.Foundations.Geometry.Orthogonal.Separation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Paired ports of a fixed square cell

Each side of `[0,240]²` has two ports, at offsets 110 and 130. Sides are ordered
left, right, bottom, top. Lane zero always has the smaller coordinate; translation
to an adjacent cell preserves the lane. Straight access routes end 20 units inside.

## Main definitions

* `boundaryPort`, `variablePosition`, `accessRoute`: the eight paired accesses.
* `oppositeSide`, `neighbor`: matching sides and adjacent cell displacements.

## Main results

* `boundaryPort_shared`: adjacent cells share the same port in the same lane.
* `access_disjoint`, `access_boundary_isolation`: continuous access separation.

## References

This fixed geometric interface is original.
-/

@[expose] public section

namespace Cslib.Orthogonal.PairedPorts

/-- A side and its lower- or higher-coordinate lane. -/
abbrev Port := Fin 4 × Fin 2

/-- The two lane coordinates. -/
def offset (l : Fin 2) : ℤ := 110 + 20 * (l : ℕ)

/-- Paired boundary ports, in left/right/bottom/top side order. -/
def boundaryPort (s : Fin 4) (l : Fin 2) : Point :=
  if s = 0 then (0, offset l) else if s = 1 then (240, offset l)
    else if s = 2 then (offset l, 0) else (offset l, 240)

/-- The corresponding inner positions on the perimeter of `[20,220]²`. -/
def variablePosition (s : Fin 4) (l : Fin 2) : Point :=
  if s = 0 then (20, offset l) else if s = 1 then (220, offset l)
    else if s = 2 then (offset l, 20) else (offset l, 220)

/-- Straight access from one boundary port to its corresponding inner position. -/
def accessRoute (s : Fin 4) (l : Fin 2) : Route :=
  [boundaryPort s l, variablePosition s l]

/-- Opposite sides of neighboring cells. -/
def oppositeSide (s : Fin 4) : Fin 4 :=
  if s = 0 then 1 else if s = 1 then 0 else if s = 2 then 3 else 2

/-- Displacement to the neighboring cell on the indicated side. -/
def neighbor (s : Fin 4) : Point :=
  if s = 0 then (-1, 0) else if s = 1 then (1, 0)
    else if s = 2 then (0, -1) else (0, 1)

/-- Taking the opposite side twice recovers the original side. -/
theorem oppositeSide_involutive : Function.Involutive oppositeSide := by
  change ∀ s, oppositeSide (oppositeSide s) = s
  decide +kernel

/-- Adjacent cells match ports without reversing the lane. -/
theorem boundaryPort_shared (p : Point) (s : Fin 4) (l : Fin 2) :
    cellOrigin 120 p + boundaryPort s l =
      cellOrigin 120 (p + neighbor s) + boundaryPort (oppositeSide s) l := by
  fin_cases s <;> fin_cases l <;> ext <;>
    simp [cellOrigin, boundaryPort, oppositeSide, neighbor, offset] <;> ring

/-- All eight boundary positions are distinct. -/
theorem boundaryPort_injective : Function.Injective (fun p : Port => boundaryPort p.1 p.2) := by
  decide +kernel

/-- All eight inner positions are distinct. -/
theorem variablePosition_injective :
    Function.Injective (fun p : Port => variablePosition p.1 p.2) := by decide +kernel

/-- Every inner position lies in the smaller core square. -/
theorem variable_bounds : ∀ s l,
    20 ≤ (variablePosition s l).1 ∧ (variablePosition s l).1 ≤ 220 ∧
      20 ≤ (variablePosition s l).2 ∧ (variablePosition s l).2 ≤ 220 := by decide +kernel

/-- Every access is orthogonal, with its prescribed boundary and inner endpoints. -/
theorem access_endpoints : ∀ s l, IsOrthogonal (accessRoute s l) ∧
    (accessRoute s l).head? = some (boundaryPort s l) ∧
      (accessRoute s l).getLast? = some (variablePosition s l) := by decide +kernel

/-- Every access is simple over its full real support. -/
theorem access_isSimple (s : Fin 4) (l : Fin 2) : IsSimple (accessRoute s l) := by
  constructor
  · fin_cases s <;> fin_cases l <;> decide
  · intro a ha b hb hne
    have ht : (accessRoute s l).consecutivePairs =
        [(boundaryPort s l, variablePosition s l)] := rfl
    rw [ht, List.mem_singleton] at ha hb
    exact False.elim (hne (ha.trans hb.symm))

/-- Each access has one segment and 20 units of Manhattan length. -/
theorem access_route_sizes : ∀ s l, (accessRoute s l).consecutivePairs.length = 1 ∧
    wireLength (accessRoute s l) = 20 := by decide +kernel

/-- Finite certificate separating every pair of distinct accesses. -/
theorem access_disjoint_check : ∀ p q : Port, p ≠ q →
    routeContactCheck [] (accessRoute p.1 p.2) (accessRoute q.1 q.2) = true := by decide +kernel

/-- Distinct accesses have disjoint full real supports. -/
theorem access_disjoint {p q : Port} (h : p ≠ q) :
    Disjoint (support (accessRoute p.1 p.2)) (support (accessRoute q.1 q.2)) :=
  disjoint_support_of_routeContactCheck (access_disjoint_check p q h)

/-- An access stays in the cell and touches its boundary only at the designated port. -/
theorem access_boundary_isolation {s : Fin 4} {l : Fin 2} {p : ℝ × ℝ}
    (hp : p ∈ support (accessRoute s l)) :
    0 ≤ p.1 ∧ p.1 ≤ 240 ∧ 0 ≤ p.2 ∧ p.2 ≤ 240 ∧
      (p.1 = 0 ∨ p.1 = 240 ∨ p.2 = 0 ∨ p.2 = 240 → p = realPoint (boundaryPort s l)) := by
  unfold accessRoute at hp
  rw [mem_support_pair] at hp
  fin_cases s <;> fin_cases l <;>
    simp only [boundaryPort, variablePosition, offset, Orthogonal.segment, realPoint] at hp ⊢
  all_goals
    norm_num [mem_horizontal, mem_vertical, Set.mem_uIcc] at hp ⊢
    rcases hp with ⟨heq, hlo, hhi⟩
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    intro h
    rcases h with h | h | h | h <;> apply Prod.ext <;> norm_num <;> linarith

end Cslib.Orthogonal.PairedPorts
