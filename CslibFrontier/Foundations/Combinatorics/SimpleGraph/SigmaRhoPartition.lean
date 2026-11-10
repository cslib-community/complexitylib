/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.DegreePartition
import Mathlib.Tactic.FinCases

/-!
# Degree-rule sets as two labeled classes

Label zero is the selected set; label one is its complement. Only counts into label zero are
restricted. This supplies the ordinary-set correspondence used by native degree-rule extrema.

## Main definitions

* `SimpleGraph.sigmaRhoMatrix`: the fixed two-class degree constraint matrix.
* `SimpleGraph.selectedPartition`: selected class followed by its complement.

## Main results

* `SimpleGraph.isDegreePartition_selectedPartition`: the selected-set correspondence.
* `SimpleGraph.IsDegreePartition.isSigmaRhoSet`: recover the selected set from any
  feasible partition.
-/

public section

namespace SimpleGraph

/-- Fixed two-class rules; only degrees into the selected class are constrained. -/
@[expose] def sigmaRhoMatrix (σ ρ : Set ℕ) (i j : Fin 2) : Set ℕ :=
  if j = 0 then if i = 0 then σ else ρ else Set.univ

/-- Actual selected class at label zero, followed by its unique complementary class. -/
@[expose] def selectedPartition {n : ℕ} (S : Set (Fin n)) (i : Fin 2) : Set (Fin n) :=
  if i = 0 then S else Sᶜ

/-- Every sigma-rho set gives a feasible labeled partition with the same selected cardinality. -/
theorem isDegreePartition_selectedPartition {n : ℕ} (G : SimpleGraph (Fin n))
    (σ ρ : Set ℕ) (S : Set (Fin n)) (hS : G.IsSigmaRhoSet σ ρ S) :
    G.IsDegreePartition (sigmaRhoMatrix σ ρ) (selectedPartition S) := by
  refine ⟨?_, ?_⟩
  · intro u
    by_cases hu : u ∈ S
    · refine ⟨0, by simpa [selectedPartition] using hu, ?_⟩
      intro j hj
      fin_cases j <;> simp_all [selectedPartition]
    · refine ⟨1, by simpa [selectedPartition] using hu, ?_⟩
      intro j hj
      fin_cases j <;> simp_all [selectedPartition]
  · intro i j u hu
    fin_cases i <;> fin_cases j
    · exact (hS u).1 (by simpa [selectedPartition] using hu)
    · simp [sigmaRhoMatrix]
    · exact (hS u).2 (by simpa [selectedPartition] using hu)
    · simp [sigmaRhoMatrix]

/-- Any feasible two-class partition yields its original sigma-rho selected set. -/
theorem IsDegreePartition.isSigmaRhoSet {n : ℕ} {G : SimpleGraph (Fin n)} {σ ρ : Set ℕ}
    {S : Fin 2 → Set (Fin n)} (hS : G.IsDegreePartition (sigmaRhoMatrix σ ρ) S) :
    G.IsSigmaRhoSet σ ρ (S 0) := by
  intro u
  constructor
  · intro hu
    simpa [sigmaRhoMatrix] using hS.2 0 0 u hu
  · intro hu
    have hc : u ∈ S 1 := by
      obtain ⟨j, hj, _⟩ := hS.1 u
      fin_cases j
      · exact False.elim (hu hj)
      · exact hj
    simpa [sigmaRhoMatrix] using hS.2 1 0 u hc

end SimpleGraph
