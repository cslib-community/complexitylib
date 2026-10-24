/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Boolean
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pi

/-!
# Graph cover transference

Rows and columns are supplied sets for bipartite graphs. When vertices are bit strings, each
literal is a union of rows or columns. Consequently every graph witness is a Boolean literal
witness, and a Boolean pair cover is already a graph pair cover, with the same length.

We use a pair of length-`n` bit strings for the Boolean input of length `2n`. This is just the
usual two-block encoding; the graph and Boolean problems share their ambient type. The result
holds for every admissibility predicate, including semi-ultrafilters, and for trivial graphs.

## Main definitions

* `Cslib.Circuits.Fusion.Graph.sources`: all rows followed by all columns.
* `Cslib.Circuits.Fusion.Graph.literals`: positive and negative literals on two bit-string blocks.

## Main results

* `Cslib.Circuits.Fusion.Graph.pairCoverComplexity_le_literals`: graph cover bounds transfer
  without loss to Boolean literal cover bounds.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*][CavalarOliveira2025], Lemmas 39 and 48.
-/

@[expose] public section

namespace Cslib.Circuits.Fusion

namespace Graph

variable {V : Type*} [Fintype V]

/-- All rows, then all columns, of the complete bipartite ambient space. -/
def sources : Fin (Fintype.card V + Fintype.card V) → Set (V × V) :=
  Fin.addCases (fun i => {x | x.1 = (Fintype.equivFin V).symm i})
    (fun i => {x | x.2 = (Fintype.equivFin V).symm i})

/-- Each row is a supplied graph source. -/
theorem row_source (v : V) : sources (Fin.castAdd (Fintype.card V) (Fintype.equivFin V v)) =
    {x : V × V | x.1 = v} := by
  simp only [sources, Fin.addCases_left, Equiv.symm_apply_apply]

/-- Each column is a supplied graph source. -/
theorem column_source (v : V) : sources (Fin.natAdd (Fintype.card V) (Fintype.equivFin V v)) =
    {x : V × V | x.2 = v} := by
  simp only [sources, Fin.addCases_right, Equiv.symm_apply_apply]

/-- The four literal blocks: positive left, positive right, negative left, negative right. -/
def literals {n : ℕ} (x : (Fin n → Bool) × (Fin n → Bool)) : Fin ((n + n) + (n + n)) → Bool :=
  Fin.addCases (Fin.addCases x.1 x.2) (Fin.addCases (fun i => !x.1 i) (fun i => !x.2 i))

/-- Every literal containing a pair contains its row or its column. -/
private theorem literals_sourceRefinement {n : ℕ} (x : (Fin n → Bool) × (Fin n → Bool))
    (i : Fin ((n + n) + (n + n))) (hi : literals x i = true) :
    ∃ j, x ∈ sources j ∧ sources j ⊆ {y | literals y i = true} := by
  let r := Fin.castAdd (Fintype.card (Fin n → Bool)) (Fintype.equivFin _ x.1)
  let c := Fin.natAdd (Fintype.card (Fin n → Bool)) (Fintype.equivFin _ x.2)
  have hr : sources r = {y | y.1 = x.1} := row_source x.1
  have hc : sources c = {y | y.2 = x.2} := column_source x.2
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i hi
  · refine Fin.addCases (fun k hk => ?_) (fun k hk => ?_) j
    · refine ⟨r, hr ▸ rfl, ?_⟩
      intro y hy
      have hy' : y.1 = x.1 := by simpa only [hr, Set.mem_ofPred_eq] using hy
      simpa only [literals, Fin.addCases_left, Fin.addCases_right, Set.mem_ofPred_eq, hy'] using hk
    · refine ⟨c, hc ▸ rfl, ?_⟩
      intro y hy
      have hy' : y.2 = x.2 := by simpa only [hc, Set.mem_ofPred_eq] using hy
      simpa only [literals, Fin.addCases_left, Fin.addCases_right, Set.mem_ofPred_eq, hy'] using hk
  · refine Fin.addCases (fun k hk => ?_) (fun k hk => ?_) j
    · refine ⟨r, hr ▸ rfl, ?_⟩
      intro y hy
      have hy' : y.1 = x.1 := by simpa only [hr, Set.mem_ofPred_eq] using hy
      simpa only [literals, Fin.addCases_left, Fin.addCases_right, Set.mem_ofPred_eq, hy'] using hk
    · refine ⟨c, hc ▸ rfl, ?_⟩
      intro y hy
      have hy' : y.2 = x.2 := by simpa only [hc, Set.mem_ofPred_eq] using hy
      simpa only [literals, Fin.addCases_left, Fin.addCases_right, Set.mem_ofPred_eq, hy'] using hk

/-- Cavalar–Oliveira's graph-to-Boolean cover transfer (Lemmas 39 and 48). The arbitrary
admissibility predicate includes both unrestricted semifilters and semi-ultrafilters. -/
theorem pairCoverComplexity_le_literals {n : ℕ} (graph : Set ((Fin n → Bool) × (Fin n → Bool)))
    (admissible : Semifilter ↥(graphᶜ) → Prop := fun _ => True) :
    pairCoverComplexity graph sources admissible ≤
      pairCoverComplexity graph (fun i => {x | literals x i = true}) admissible :=
  pairCoverComplexity_le_of_sourceRefinement admissible
    (fun x _ i hi => literals_sourceRefinement x i hi)

end Graph
end Cslib.Circuits.Fusion
