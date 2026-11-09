/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.SimpleGraph.DegreeRules
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Labeled partitions with a fixed neighbor-degree matrix

This is the ordinary ordered-set-family semantics of [ChenJiangZhu2027], Theorem 7.3,
equation (28) (PDF p.25). Every vertex has exactly one label. Empty classes are permitted;
there is no connectivity requirement or quotient by label permutations.
-/

public section

namespace SimpleGraph

/-- Ordinary labeled degree partitions. Every source and target class has its own count rule. -/
@[expose] def IsDegreePartition {n q : ℕ} (G : SimpleGraph (Fin n))
    (M : Fin q → Fin q → Set ℕ) (S : Fin q → Set (Fin n)) : Prop :=
  (∀ u, ∃! i, u ∈ S i) ∧ ∀ i j u, u ∈ S i → G.selectedDegree (S j) u ∈ M i j

/-- Input class-size bounds apply to the actual original vertex sets, including empty classes. -/
@[expose] def InClassBounds {n q : ℕ} (lo hi : Fin q → ℕ) (S : Fin q → Set (Fin n)) : Prop :=
  ∀ i, lo i ≤ Nat.card (S i) ∧ Nat.card (S i) ≤ hi i

open Classical in
/-- Every fixed finite/cofinite degree matrix has one common positive cutoff and finite tables.
This compiles fixed problem data; it supplies no graph-instance information. -/
theorem exists_degreeMatrixRules {q : ℕ} (M : Fin q → Fin q → Set ℕ)
    (hM : ∀ i j, (M i j).Finite ∨ (M i j)ᶜ.Finite) :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ R : Fin q → Fin q → DegreeRule D,
      ∀ i j, (R i j).counts = M i j := by
  choose ds hpos htail using fun p : Fin q × Fin q => exists_degreeCutoff (M p.1 p.2) (hM p.1 p.2)
  let D := max 1 (Finset.univ.sup ds)
  have hd (i j : Fin q) : ds (i, j) ≤ D :=
    (Finset.le_sup (Finset.mem_univ (i, j))).trans (le_max_right _ _)
  refine ⟨D, le_max_left _ _, fun i j => DegreeRule.ofSet D (M i j), ?_⟩
  intro i j
  ext c
  exact DegreeRule.ofSet_accepts D (M i j) (fun b hb =>
    (htail (i, j) b ((hd i j).trans hb)).trans (htail (i, j) D (hd i j)).symm) c

end SimpleGraph
