/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Mathlib.Data.Fintype.Basic

/-!
# The finite crossover relation

The 26 clauses formalize Lichtenstein’s crossover [Lichtenstein1982, Figs. 4–5], drawn on a
grid by MIT–ULB CompGeom Group [Tromino2025, Fig. 8(b)]. The Lean table is adapted from
`edemaine/lean-trominoes` at `6d5b36c15cec6cb18d30137b7f1c7fb92ea24332`,
[PlanarThreeSATGadgets.lean](https://github.com/edemaine/lean-trominoes/blob/6d5b36c15cec6cb18d30137b7f1c7fb92ea24332/LeanTrominoes/SAT/Planar/PlanarThreeSATGadgets.lean).
This file uses the ordinary CNF semantics. Geometry and local degree reduction are separate.

## Main definitions

* `Cslib.Logic.PL.CNF.Crossover.formula`: the fixed 13-variable, 26-clause formula.

## Main results

* `Cslib.Logic.PL.CNF.Crossover.extends_iff`: opposite boundary values agree independently.
* `Cslib.Logic.PL.CNF.Crossover.terminal_occurrences`: each terminal has two internal incidences,
  leaving capacity for one external implication under the degree-three bound.

## References

* David Lichtenstein, *Planar Formulae and Their Uses*, Figs. 4–5 [Lichtenstein1982].
* MIT–ULB CompGeom Group, *Undecidability of Tiling with a Tromino*, Fig. 8(b) [Tromino2025].

The clause table and truth-table certificate adapt the Lean source cited above.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.Crossover

/-- Variables named by their role in the fixed crossover. -/
inductive Variable
  | aLeft
  | aInnerLeft
  | upperLeft
  | lowerLeft
  | bTop
  | bInnerTop
  | center
  | bInnerBottom
  | bBottom
  | upperRight
  | lowerRight
  | aInnerRight
  | aRight
  deriving DecidableEq, Repr

/-- Explicit enumeration avoids relying on generated metaprogram data for the finite certificate. -/
instance : Fintype Variable where
  elems := {.aLeft, .aInnerLeft, .upperLeft, .lowerLeft, .bTop, .bInnerTop, .center,
    .bInnerBottom, .bBottom, .upperRight, .lowerRight, .aInnerRight, .aRight}
  complete v := by cases v <;> simp

/-- The fixed crossover clauses, in the source figure's order. -/
def formula : CNF Variable :=
  [[(.aLeft, true), (.aInnerLeft, false)],
    [(.aLeft, false), (.aInnerLeft, true)],
    [(.aInnerLeft, false), (.upperLeft, false),
        (.bInnerTop, true)],
    [(.aInnerLeft, false), (.lowerLeft, false),
        (.bInnerBottom, false)],
    [(.aInnerLeft, true), (.upperLeft, true)],
    [(.upperLeft, true), (.lowerLeft, true)],
    [(.aInnerLeft, true), (.lowerLeft, true)],
    [(.bTop, false), (.bInnerTop, true)],
    [(.upperLeft, true), (.bInnerTop, false)],
    [(.upperLeft, false), (.lowerLeft, false), (.center, false)],
    [(.lowerLeft, true), (.bInnerBottom, true)],
    [(.bTop, true), (.bInnerTop, false)],
    [(.upperLeft, true), (.upperRight, true)],
    [(.lowerLeft, true), (.lowerRight, true)],
    [(.bInnerBottom, false), (.bBottom, true)],
    [(.bInnerTop, false), (.upperRight, true)],
    [(.center, true), (.upperRight, false), (.lowerRight, false)],
    [(.bInnerBottom, true), (.lowerRight, true)],
    [(.bInnerBottom, true), (.bBottom, false)],
    [(.upperRight, true), (.aInnerRight, false)],
    [(.upperRight, true), (.lowerRight, true)],
    [(.lowerRight, true), (.aInnerRight, false)],
    [(.bInnerTop, true), (.upperRight, false),
        (.aInnerRight, true)],
    [(.bInnerBottom, false), (.lowerRight, false),
        (.aInnerRight, true)],
    [(.aInnerRight, true), (.aRight, false)],
    [(.aInnerRight, false), (.aRight, true)]]

/-- Assemble four boundary values and nine internal values into an assignment. -/
def assignment
    (aLeft aRight bTop bBottom
      aInnerLeft upperLeft lowerLeft bInnerTop center bInnerBottom
      upperRight lowerRight aInnerRight : Bool) :
    Variable → Bool
  | .aLeft => aLeft
  | .aInnerLeft => aInnerLeft
  | .upperLeft => upperLeft
  | .lowerLeft => lowerLeft
  | .bTop => bTop
  | .bInnerTop => bInnerTop
  | .center => center
  | .bInnerBottom => bInnerBottom
  | .bBottom => bBottom
  | .upperRight => upperRight
  | .lowerRight => lowerRight
  | .aInnerRight => aInnerRight
  | .aRight => aRight

/-- A boundary assignment extends to all nine internal crossover variables. -/
def Extends (aLeft aRight bTop bBottom : Bool) : Prop :=
  ∃ aInnerLeft upperLeft lowerLeft bInnerTop center bInnerBottom
      upperRight lowerRight aInnerRight : Bool,
    formula.eval
      (assignment aLeft aRight bTop bBottom
        aInnerLeft upperLeft lowerLeft bInnerTop center bInnerBottom
        upperRight lowerRight aInnerRight) = true

instance (aLeft aRight bTop bBottom : Bool) :
    Decidable (Extends aLeft aRight bTop bBottom) := by
  unfold Extends
  exact Fintype.decidableExistsFintype

/-- Exhaustive certificate for Lichtenstein’s crossover [Lichtenstein1982, Figs. 4–5],
as drawn in [Tromino2025, Fig. 8(b)]: horizontal and vertical values propagate independently. -/
theorem extends_iff (aLeft aRight bTop bBottom : Bool) :
    Extends aLeft aRight bTop bBottom ↔
      aLeft = aRight ∧ bTop = bBottom := by
  cases aLeft <;> cases aRight <;> cases bTop <;> cases bBottom <;>
    decide +kernel

/-- Every satisfying assignment to the crossover propagates each boundary
value to the opposite port.  This is the soundness direction needed when a
crossover embedded in a larger formula is projected back to its two original
wires. -/
theorem boundary_eq_of_holds
    {σ : Variable → Bool}
    (holds : formula.eval σ = true) :
    σ .aLeft = σ .aRight ∧
      σ .bTop = σ .bBottom := by
  apply (extends_iff
    (σ .aLeft) (σ .aRight)
    (σ .bTop) (σ .bBottom)).mp
  refine ⟨σ .aInnerLeft, σ .upperLeft,
    σ .lowerLeft, σ .bInnerTop, σ .center,
    σ .bInnerBottom, σ .upperRight,
    σ .lowerRight, σ .aInnerRight, ?_⟩
  have assignment_eq :
      assignment
        (σ .aLeft) (σ .aRight)
        (σ .bTop) (σ .bBottom)
        (σ .aInnerLeft) (σ .upperLeft)
        (σ .lowerLeft) (σ .bInnerTop)
        (σ .center) (σ .bInnerBottom)
        (σ .upperRight) (σ .lowerRight)
        (σ .aInnerRight) = σ := by
    funext x
    cases x <;> rfl
  rw [assignment_eq]
  exact holds

/-- Conversely, two independently propagated boundary values can always be
extended to a satisfying assignment of the whole crossover. -/
theorem exists_holds_of_boundary_eq
    {aLeft aRight bTop bBottom : Bool}
    (horizontal : aLeft = aRight) (vertical : bTop = bBottom) :
    ∃ σ : Variable → Bool,
      formula.eval σ = true ∧
        σ .aLeft = aLeft ∧
        σ .aRight = aRight ∧
        σ .bTop = bTop ∧
        σ .bBottom = bBottom := by
  have hExtends :
      Extends aLeft aRight bTop bBottom :=
    (extends_iff aLeft aRight bTop bBottom).mpr
      ⟨horizontal, vertical⟩
  rcases hExtends with
    ⟨aInnerLeft, upperLeft, lowerLeft, bInnerTop, center, bInnerBottom,
      upperRight, lowerRight, aInnerRight, holds⟩
  refine ⟨assignment aLeft aRight bTop bBottom
    aInnerLeft upperLeft lowerLeft bInnerTop center bInnerBottom
    upperRight lowerRight aInnerRight, holds, ?_⟩
  simp [assignment]

/-- The four boundary variables, in left/right/top/bottom order. -/
def terminal : Fin 4 → Variable
  | 0 => .aLeft
  | 1 => .aRight
  | 2 => .bTop
  | 3 => .bBottom

/-- The formula has exactly 26 clauses. -/
theorem length_formula : formula.length = 26 := by decide

/-- Every clause has width at most three. -/
theorem width_formula : ∀ c ∈ formula, c.length ≤ 3 := by decide +kernel

/-- Original internal variables have degree at most six, before local splitting. -/
theorem occurrences_le_six : ∀ v, formula.occurrences v ≤ 6 := by decide +kernel

/-- A terminal uses two internal incidences, leaving one external clause incidence. -/
theorem terminal_occurrences : ∀ i, formula.occurrences (terminal i) = 2 := by decide +kernel

end Cslib.Logic.PL.CNF.Crossover
