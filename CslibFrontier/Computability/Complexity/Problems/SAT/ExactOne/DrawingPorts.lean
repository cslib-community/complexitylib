/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.DrawingSource
public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.GeometryCollarData
public import CslibFrontier.Computability.Complexity.Problems.SAT.Incidence
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.GetD

/-!
# Cardinal port selection for actual source incidences

The side convention agrees with the finite collar tables. Any zero, one, two, or three distinct
prescribed source exits extends to one of the twenty-four ordered three-port assignments.

## Main definitions

* `directionSide`, `sideDirection`: cardinal-vector and collar-side conversion.
* `choosePorts`: finite deterministic completion of a partial source exit assignment.

## Main results

* `sideDirection_directionSide`: cardinal directions are preserved exactly.
* `portsMatch_iff`: matching is equality at every present indexed port.
* `choosePorts_spec`: the selected ports are distinct and retain every present source exit.

## References

These finite collar-selection and geometric indexing proofs are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

/-- Collar sides are numbered left, right, bottom, top. -/
def sideDirection (s : Fin 4) : Point :=
  if s = 0 then (-1, 0) else if s = 1 then (1, 0) else if s = 2 then (0, -1) else (0, 1)

/-- Classify a cardinal direction using the collar side convention. -/
def directionSide (v : Point) : Fin 4 :=
  if v = (-1, 0) then 0 else if v = (1, 0) then 1 else if v = (0, -1) then 2 else 3

/-- Converting a unit direction to its collar side and back recovers it. -/
theorem sideDirection_directionSide {v : Point} (hv : UnitVector v) :
    sideDirection (directionSide v) = v := by
  rcases hv with rfl | rfl | rfl | rfl <;> decide

/-- Distinct unit vectors are classified as distinct collar sides. -/
theorem directionSide_injective {v w : Point} (hv : UnitVector v) (hw : UnitVector w)
    (he : directionSide v = directionSide w) : v = w := by
  rw [← sideDirection_directionSide hv, ← sideDirection_directionSide hw, he]

/-- Check the source exits that are present in a clause of the indicated length. -/
def portsMatch (n : Fin 4) (a b c : Fin 4) (s : PortAssignment) : Bool :=
  (if 0 < n.val then s.side 0 == a else true) &&
    (if 1 < n.val then s.side 1 == b else true) &&
    (if 2 < n.val then s.side 2 == c else true)

/-- Matching constrains exactly the indexed ports that are present in the source clause. -/
theorem portsMatch_iff (n : Fin 4) (a b c : Fin 4) (s : PortAssignment) :
    portsMatch n a b c s = true ↔
      ∀ j : Fin 3, j.val < n.val → s.side j = PortAssignment.side (a, b, c) j := by
  fin_cases n <;> simp [portsMatch, Fin.forall_fin_succ, PortAssignment.side, and_assoc]

/-- Select the first ordered collar assignment extending the present source exits. -/
def choosePorts (n : Fin 4) (a b c : Fin 4) : PortAssignment :=
  (collarAssignments.find? (portsMatch n a b c)).getD (0, 1, 2)

/-- A partial source assignment needs pairwise distinct exits exactly at its present positions. -/
def PresentDirectionsDistinct (n : Fin 4) (a b c : Fin 4) : Prop :=
  (2 ≤ n.val → a ≠ b) ∧ (3 ≤ n.val → a ≠ c ∧ b ≠ c)

instance (n : Fin 4) (a b c : Fin 4) : Decidable (PresentDirectionsDistinct n a b c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Every admissible partial exit assignment has a deterministic distinct collar completion. -/
theorem choosePorts_spec (n : Fin 4) (a b c : Fin 4)
    (h : PresentDirectionsDistinct n a b c) :
    (choosePorts n a b c).Distinct ∧ portsMatch n a b c (choosePorts n a b c) = true := by
  have hall : ∀ (n : Fin 4) (a b c : Fin 4), PresentDirectionsDistinct n a b c →
      (choosePorts n a b c).Distinct ∧ portsMatch n a b c (choosePorts n a b c) = true := by
    decide +kernel
  exact hall n a b c h

/-- Each prescribed exit is retained by the selected collar assignment. -/
theorem choosePorts_matches (n : Fin 4) (a b c : Fin 4)
    (h : PresentDirectionsDistinct n a b c) (j : Fin 3) (hj : j.val < n.val) :
    (choosePorts n a b c).side j = PortAssignment.side (a, b, c) j :=
  (portsMatch_iff n a b c _).mp (choosePorts_spec n a b c h).2 j hj

/-- A literal position identifies its own incidence, including repeated literals. -/
def sourceOccurrence (φ : CNF ℕ) (i j : ℕ) : Occurrence ℕ :=
  ⟨i, j, (φ.getD i []).getD j (0, true)⟩

/-- The actual source edge position of a clause/literal occurrence. -/
def sourceEdgeIndex (φ : CNF ℕ) (i j : ℕ) : ℕ :=
  (Cslib.Logic.PL.occurrences φ).idxOf (sourceOccurrence φ i j)

/-- The actual cardinal exit of one source literal. -/
def literalSide (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) (i j : ℕ) : Fin 4 :=
  directionSide (sourceDirection (SAT.incidenceGraph φ) d (sourceEdgeIndex φ i j))

/-- Complete the present exits to a deterministic ordered collar. -/
def clausePorts (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) (i : ℕ) : PortAssignment :=
  choosePorts ⟨min (φ.getD i []).length 3, by omega⟩
    (literalSide φ d i 0) (literalSide φ d i 1) (literalSide φ d i 2)

/-- Existing clause and literal indices identify an actual source occurrence. -/
theorem sourceOccurrence_mem (φ : CNF ℕ) {i j : ℕ} (hi : i < φ.length)
    (hj : j < φ[i].length) : sourceOccurrence φ i j ∈ Cslib.Logic.PL.occurrences φ := by
  rw [sourceOccurrence, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  exact Cslib.Logic.PL.mem_occurrences.mpr ⟨hi, hj, rfl⟩

/-- Every actual source occurrence has a valid incidence-list index. -/
theorem sourceEdgeIndex_lt (φ : CNF ℕ) {i j : ℕ} (hi : i < φ.length)
    (hj : j < φ[i].length) : sourceEdgeIndex φ i j < (SAT.incidenceGraph φ).2.length := by
  have h := List.idxOf_lt_length_of_mem (sourceOccurrence_mem φ hi hj)
  simpa only [sourceEdgeIndex, SAT.incidenceGraph, List.length_map] using h

/-- Source edge lookup recovers the actual variable and clause endpoints. -/
theorem sourceEdgeIndex_edge (φ : CNF ℕ) {i j : ℕ} (hi : i < φ.length)
    (hj : j < φ[i].length) :
    (SAT.incidenceGraph φ).2.getD (sourceEdgeIndex φ i j) (0, 0) =
      (φ.distinctVars.idxOf φ[i][j].1, φ.distinctVars.length + i) := by
  have hm := sourceOccurrence_mem φ hi hj
  have hindex := List.idxOf_lt_length_of_mem hm
  unfold sourceEdgeIndex
  rw [SAT.incidenceGraph, List.getD_eq_getElem _ _ (by simpa using hindex), List.getElem_map]
  rw [List.getElem_idxOf hindex]
  simp only [sourceOccurrence,
    List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]

/-- Distinct source literal positions have distinct listed source edges. -/
theorem sourceEdgeIndex_ne (φ : CNF ℕ) {i j k : ℕ} (hi : i < φ.length)
    (hj : j < φ[i].length) (_hk : k < φ[i].length) (hjk : j ≠ k) :
    sourceEdgeIndex φ i j ≠ sourceEdgeIndex φ i k := by
  intro he
  have he' := (List.idxOf_inj (sourceOccurrence_mem φ hi hj)).mp he
  exact hjk (congrArg (fun o : Occurrence ℕ => o.pos) he')

/-- Actual source literal exits at the same clause have distinct collar sides. -/
theorem literalSide_ne {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i j k : ℕ}
    (hi : i < φ.length) (hj : j < φ[i].length) (hk : k < φ[i].length) (hjk : j ≠ k) :
    literalSide φ d i j ≠ literalSide φ d i k := by
  intro he
  have hdij := sourceDirection_ne hd (sourceEdgeIndex_lt φ hi hj) (sourceEdgeIndex_lt φ hi hk)
    (sourceEdgeIndex_ne φ hi hj hk hjk) (by
      have h₁ := congrArg Prod.snd (sourceEdgeIndex_edge φ hi hj)
      have h₂ := congrArg Prod.snd (sourceEdgeIndex_edge φ hi hk)
      rw [List.getD_eq_getElem _ _ (sourceEdgeIndex_lt φ hi hj)] at h₁
      rw [List.getD_eq_getElem _ _ (sourceEdgeIndex_lt φ hi hk)] at h₂
      exact h₁.trans h₂.symm)
  exact hdij (directionSide_injective (sourceDirection_unit _ _ _) (sourceDirection_unit _ _ _) he)

/-- A valid source drawing supplies a distinct ordered collar for every actual clause. -/
theorem clausePorts_spec {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length) :
    (clausePorts φ d i).Distinct ∧
      portsMatch ⟨min (φ.getD i []).length 3, by omega⟩
        (literalSide φ d i 0) (literalSide φ d i 1) (literalSide φ d i 2)
        (clausePorts φ d i) = true := by
  apply choosePorts_spec
  constructor
  · intro hn
    change 2 ≤ min (φ.getD i []).length 3 at hn
    rw [List.getD_eq_getElem _ _ hi] at hn
    exact literalSide_ne hd hi (by omega) (by omega) (by decide)
  · intro hn
    change 3 ≤ min (φ.getD i []).length 3 at hn
    rw [List.getD_eq_getElem _ _ hi] at hn
    exact ⟨literalSide_ne hd hi (by omega) (by omega) (by decide),
      literalSide_ne hd hi (by omega) (by omega) (by decide)⟩

/-- Each present source literal uses its actual cardinal side in the selected collar. -/
theorem clausePorts_side {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length) (j : Fin 3) (hj : j.val < φ[i].length) :
    (clausePorts φ d i).side j = literalSide φ d i j.val := by
  have hn : j.val < min (φ.getD i []).length 3 := by
    rw [List.getD_eq_getElem _ _ hi]
    omega
  have hm := (portsMatch_iff _ _ _ _ _).mp (clausePorts_spec hd hi).2 j hn
  fin_cases j <;> simpa [PortAssignment.side] using hm

/-- A collar's midpoint is its center plus its cardinal radius vector. -/
theorem collarOuterPort_eq_center_add : ∀ s : Fin 4,
    collarOuterPort s = (270000, 270000) + (270000 : ℕ) • sideDirection s := by
  decide +kernel

end Cslib.Complexity.SAT.ExactOne
