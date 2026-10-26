/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Planar.Crossover
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Card
import Complexity.Logics.Propositional.CNF.ImplicationCycle

/-!
# A fixed degree-three crossover

Each of the eight degree-six internal variables is replaced by six cyclically ordered copies,
with one directed implication between each consecutive pair. The four boundary variables and
central variable retain their two occurrences. This is a fixed template, not a generic splitter.

## Main definitions

* `Cslib.Logic.PL.CNF.Crossover.SplitVariable`: the 53 variables of the template.
* `Cslib.Logic.PL.CNF.Crossover.splitFormula`: its 74 clauses.

## Main results

* `Cslib.Logic.PL.CNF.Crossover.split_occurrences_le_three`: internal degree bound.
* `Cslib.Logic.PL.CNF.Crossover.split_terminal_occurrences`: degree-two attachment ports.

## References

* David Lichtenstein, *Planar Formulae and Their Uses*, Figs. 4–5 [Lichtenstein1982].
* MIT–ULB CompGeom Group, *Undecidability of Tiling with a Tromino*, Fig. 8(b) [Tromino2025].

The fixed local six-copy replacement is original.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.Crossover

/-- The eight original internal variables that need local splitting. -/
inductive Internal
  | aInnerLeft
  | upperLeft
  | lowerLeft
  | bInnerTop
  | bInnerBottom
  | upperRight
  | lowerRight
  | aInnerRight
  deriving DecidableEq, Repr

instance : Fintype Internal where
  elems := {.aInnerLeft, .upperLeft, .lowerLeft, .bInnerTop, .bInnerBottom,
    .upperRight, .lowerRight, .aInnerRight}
  complete v := by cases v <;> simp

/-- The five unsplit variables and six local copies of each degree-six variable. -/
inductive SplitVariable
  | aLeft | aRight | bTop | bBottom | center
  | copy (v : Internal) (i : Fin 6)
  deriving DecidableEq, Repr

instance : Fintype SplitVariable where
  elems := {.aLeft, .aRight, .bTop, .bBottom, .center} ∪
    Finset.univ.biUnion fun v : Internal => Finset.univ.image (SplitVariable.copy v)
  complete v := by cases v <;> simp

/-- The original variable represented by a split variable. -/
def SplitVariable.origin : SplitVariable → Variable
  | .aLeft => .aLeft
  | .aRight => .aRight
  | .bTop => .bTop
  | .bBottom => .bBottom
  | .center => .center
  | .copy .aInnerLeft _ => .aInnerLeft
  | .copy .upperLeft _ => .upperLeft
  | .copy .lowerLeft _ => .lowerLeft
  | .copy .bInnerTop _ => .bInnerTop
  | .copy .bInnerBottom _ => .bInnerBottom
  | .copy .upperRight _ => .upperRight
  | .copy .lowerRight _ => .lowerRight
  | .copy .aInnerRight _ => .aInnerRight

/-- A distinguished representative of every original variable. -/
def representative : Variable → SplitVariable
  | .aLeft => .aLeft
  | .aRight => .aRight
  | .bTop => .bTop
  | .bBottom => .bBottom
  | .center => .center
  | .aInnerLeft => .copy .aInnerLeft 0
  | .upperLeft => .copy .upperLeft 0
  | .lowerLeft => .copy .lowerLeft 0
  | .bInnerTop => .copy .bInnerTop 0
  | .bInnerBottom => .copy .bInnerBottom 0
  | .upperRight => .copy .upperRight 0
  | .lowerRight => .copy .lowerRight 0
  | .aInnerRight => .copy .aInnerRight 0

/-- The original 26 clauses, using the cyclic copy determined by each local incidence ray. -/
def splitClauses : CNF SplitVariable :=
  [[(.aLeft, true), (.copy .aInnerLeft 5, false)],
   [(.aLeft, false), (.copy .aInnerLeft 4, true)],
   [(.copy .aInnerLeft 0, false), (.copy .upperLeft 0, false), (.copy .bInnerTop 5, true)],
   [(.copy .aInnerLeft 3, false), (.copy .lowerLeft 4, false), (.copy .bInnerBottom 5, false)],
   [(.copy .aInnerLeft 1, true), (.copy .upperLeft 5, true)],
   [(.copy .upperLeft 4, true), (.copy .lowerLeft 0, true)],
   [(.copy .aInnerLeft 2, true), (.copy .lowerLeft 5, true)],
   [(.bTop, false), (.copy .bInnerTop 0, true)],
   [(.copy .upperLeft 1, true), (.copy .bInnerTop 4, false)],
   [(.copy .upperLeft 3, false), (.copy .lowerLeft 1, false), (.center, false)],
   [(.copy .lowerLeft 3, true), (.copy .bInnerBottom 0, true)],
   [(.bTop, true), (.copy .bInnerTop 1, false)],
   [(.copy .upperLeft 2, true), (.copy .upperRight 5, true)],
   [(.copy .lowerLeft 2, true), (.copy .lowerRight 5, true)],
   [(.copy .bInnerBottom 4, false), (.bBottom, true)],
   [(.copy .bInnerTop 3, false), (.copy .upperRight 0, true)],
   [(.center, true), (.copy .upperRight 4, false), (.copy .lowerRight 0, false)],
   [(.copy .bInnerBottom 1, true), (.copy .lowerRight 4, true)],
   [(.copy .bInnerBottom 3, true), (.bBottom, false)],
   [(.copy .upperRight 2, true), (.copy .aInnerRight 0, false)],
   [(.copy .upperRight 3, true), (.copy .lowerRight 1, true)],
   [(.copy .lowerRight 2, true), (.copy .aInnerRight 5, false)],
   [(.copy .bInnerTop 2, true), (.copy .upperRight 1, false), (.copy .aInnerRight 1, true)],
   [(.copy .bInnerBottom 2, false), (.copy .lowerRight 3, false), (.copy .aInnerRight 4, true)],
   [(.copy .aInnerRight 2, true), (.aRight, false)],
   [(.copy .aInnerRight 3, false), (.aRight, true)]]

/-- The six implications around one fixed local square, in cyclic order. -/
def ring (v : Internal) : CNF SplitVariable :=
  [ [(.copy v 0, false), (.copy v 1, true)],
    [(.copy v 1, false), (.copy v 2, true)],
    [(.copy v 2, false), (.copy v 3, true)],
    [(.copy v 3, false), (.copy v 4, true)],
    [(.copy v 4, false), (.copy v 5, true)],
    [(.copy v 5, false), (.copy v 0, true)] ]

/-- Fixed ordered list of the eight local split squares. -/
def internalList : List Internal :=
  [.aInnerLeft, .upperLeft, .lowerLeft, .bInnerTop, .bInnerBottom,
    .upperRight, .lowerRight, .aInnerRight]

/-- The degree-three crossover: original split clauses followed by eight implication rings. -/
def splitFormula : CNF SplitVariable := splitClauses ++ internalList.flatMap ring

/-- The four attachment variables, ordered left/right/top/bottom. -/
def splitTerminal : Fin 4 → SplitVariable
  | 0 => .aLeft
  | 1 => .aRight
  | 2 => .bTop
  | 3 => .bBottom

/-- Every original clause is recovered by forgetting its local copy index. -/
theorem relabel_splitClauses : splitClauses.relabel SplitVariable.origin = formula := by decide

/-- There are exactly 53 variable names. -/
theorem card_splitVariable : Fintype.card SplitVariable = 53 := by decide

/-- There are exactly 74 clauses. -/
theorem length_splitFormula : splitFormula.length = 74 := by decide

/-- Every clause has width at most three. -/
theorem width_splitFormula : ∀ c ∈ splitFormula, c.length ≤ 3 := by decide +kernel

/-- No clause repeats a variable, so literal-incidence degree equals clause occurrence degree. -/
theorem splitClauses_distinct_variables :
    ∀ c ∈ splitFormula, (c.map Prod.fst).Nodup := by decide +kernel

/-- Every variable occurs in at most three clauses. -/
theorem split_occurrences_le_three : ∀ v, splitFormula.occurrences v ≤ 3 := by decide +kernel

/-- Each boundary variable has two internal occurrences and capacity for one external clause. -/
theorem split_terminal_occurrences :
    ∀ i, splitFormula.occurrences (splitTerminal i) = 2 := by decide +kernel

/-- A local implication ring forces all six copies to agree. -/
theorem eval_ring_iff (σ : SplitVariable → Bool) (v : Internal) :
    (ring v).eval σ = true ↔ ∀ i, σ (.copy v i) = σ (.copy v 0) := by
  have hr : ring v = CNF.implicationCycle (List.ofFn (SplitVariable.copy v)) := rfl
  rw [hr, CNF.eval_implicationCycle]
  constructor
  · intro h i
    exact h _ (List.mem_ofFn.mpr ⟨i, rfl⟩) _ (List.mem_ofFn.mpr ⟨0, rfl⟩)
  · intro h x hx y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    exact (h i).trans (h j).symm

/-- Every internal variable belongs to the fixed ordered list. -/
theorem mem_internalList (v : Internal) : v ∈ internalList := by cases v <;> decide

/-- Once each local ring agrees, evaluation is exactly evaluation of the original clauses. -/
theorem eval_splitClauses_of_agree (σ : SplitVariable → Bool)
    (h : ∀ v i, σ (.copy v i) = σ (.copy v 0)) :
    splitClauses.eval σ = formula.eval (σ ∘ representative) := by
  rw [← relabel_splitClauses, CNF.eval_relabel]
  apply CNF.eval_congr
  intro v _
  cases v with
  | aLeft | aRight | bTop | bBottom | center => rfl
  | copy v i => cases v <;> exact h _ i

/-- Exact semantics of the fixed degree-three template. -/
theorem eval_splitFormula_iff (σ : SplitVariable → Bool) :
    splitFormula.eval σ = true ↔
      formula.eval (σ ∘ representative) = true ∧
        ∀ v i, σ (.copy v i) = σ (.copy v 0) := by
  simp only [splitFormula, CNF.eval_append, Bool.and_eq_true,
    CNF.eval_flatMap_eq_true_iff, eval_ring_iff]
  constructor
  · rintro ⟨hc, hr⟩
    have h : ∀ v i, σ (.copy v i) = σ (.copy v 0) := fun v => hr v (mem_internalList v)
    exact ⟨(eval_splitClauses_of_agree σ h) ▸ hc, h⟩
  · rintro ⟨hc, h⟩
    exact ⟨(eval_splitClauses_of_agree σ h).symm ▸ hc, fun v _ => h v⟩

/-- Any original satisfying assignment lifts by assigning its value to every local copy. -/
theorem eval_splitFormula_lift (σ : Variable → Bool) (h : formula.eval σ = true) :
    splitFormula.eval (σ ∘ SplitVariable.origin) = true := by
  apply (eval_splitFormula_iff _).2
  constructor
  · have heq : (σ ∘ SplitVariable.origin) ∘ representative = σ := by
      funext v
      cases v <;> rfl
    rwa [heq]
  · intro v i
    cases v <;> rfl

/-- Satisfying the split crossover forces the two pairs of opposite ports to agree. -/
theorem split_boundary_eq_of_holds {σ : SplitVariable → Bool}
    (h : splitFormula.eval σ = true) :
    σ .aLeft = σ .aRight ∧ σ .bTop = σ .bBottom :=
  boundary_eq_of_holds (eval_splitFormula_iff σ |>.1 h).1

/-- Two arbitrary independent Boolean signals extend to a satisfying degree-three crossover. -/
theorem exists_split_holds (a b : Bool) :
    ∃ σ : SplitVariable → Bool, splitFormula.eval σ = true ∧
      σ .aLeft = a ∧ σ .aRight = a ∧ σ .bTop = b ∧ σ .bBottom = b := by
  obtain ⟨σ, hs, hl, hr, ht, hb⟩ := exists_holds_of_boundary_eq
    (aLeft := a) (aRight := a) (bTop := b) (bBottom := b) rfl rfl
  exact ⟨σ ∘ SplitVariable.origin, eval_splitFormula_lift σ hs, hl, hr, ht, hb⟩

end Cslib.Logic.PL.CNF.Crossover
