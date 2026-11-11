/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Parameterized.LongPathKernel

/-!
# Tests: k-Path has no polynomial kernel unless `coNP ⊆ NP/poly`

The cross-composition of `HamPath` into k-Path on concrete lists. The edge `1 — 2` has a
Hamiltonian path from `1` to `2`, while the same two vertices without the edge, and the edge with
an undeclared start `5`, have none. Lists of these related instances give yes- and no-instances of
k-Path according to whether some entry is a yes-instance, and an undeclared start does not spoil a
yes-entry. The empty list gives a no-instance, outside the scope of the OR property. Equal length
is a polynomial equivalence relation on bit strings by `IsPolyEquivalence.of_key`, and so is
equality of unary numbers. The hypotheses of the cross-composition theorem hold for k-Path, so the
kernel lower bound is conditional only on `coNP ⊄ NP/poly`.
-/

namespace CslibFrontierTests.LongPathKernel

open Cslib Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-- The edge `1 — 2`. -/
def edge : Graph := ([1, 2], [(1, 2)])

/-- The vertices `1` and `2` without edges. -/
def noEdge : Graph := ([1, 2], [])

/-- The edge `1 — 2` has a Hamiltonian path from `1` to `2`. -/
theorem edge_mem_HamPath : (edge, 1, 2) ∈ HamPath := by
  rw [mem_HamPath_iff]
  refine ⟨[1, 2], by decide, fun _ => Iff.rfl, rfl, rfl, ?_⟩
  rw [List.isChain_cons_cons, Graph.toSimpleGraph_adj]
  exact ⟨⟨by decide, Or.inl (List.mem_singleton_self _)⟩, List.isChain_singleton _⟩

/-- Two vertices without edges have no Hamiltonian path. -/
theorem noEdge_not_mem_HamPath : (noEdge, 1, 2) ∉ HamPath := by
  rw [mem_HamPath_iff]
  rintro ⟨p, -, hcov, -, -, hch⟩
  match p, hcov, hch with
  | [], hcov, _ => exact List.not_mem_nil ((hcov 1).2 (by simp [noEdge]))
  | [a], hcov, _ =>
    have h1 := (hcov 1).2 (by simp [noEdge])
    have h2 := (hcov 2).2 (by simp [noEdge])
    simp only [List.mem_singleton] at h1 h2
    omega
  | a :: b :: _, _, hch =>
    have h := (List.isChain_cons_cons.1 hch).1
    rw [Graph.toSimpleGraph_adj] at h
    simp [noEdge] at h

/-- An undeclared start rules out a Hamiltonian path. -/
theorem undeclared_not_mem_HamPath : (edge, 5, 2) ∉ HamPath := by
  rw [mem_HamPath_iff]
  rintro ⟨p, -, hcov, hs, -, -⟩
  have h5 := (hcov 5).1 (List.mem_of_head? hs)
  simp [edge] at h5

/-! ### The cross-composition on concrete lists -/

/-- A yes-entry gives a yes-instance of k-Path, whatever the other related entries. -/
example : HamPath.toLongPath [(noEdge, 1, 2), (edge, 1, 2)] ∈ LongPath :=
  (HamPath.toLongPath_mem_iff (List.cons_ne_nil _ _)
    (by simp [edge, noEdge, Graph.length_distinctVertices])).2
    ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), edge_mem_HamPath⟩

/-- An entry with an undeclared start does not spoil a yes-entry. -/
example : HamPath.toLongPath [(edge, 5, 2), (edge, 1, 2)] ∈ LongPath :=
  (HamPath.toLongPath_mem_iff (List.cons_ne_nil _ _) (by simp)).2
    ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), edge_mem_HamPath⟩

/-- Related no-entries give a no-instance of k-Path. -/
example : HamPath.toLongPath [(noEdge, 1, 2), (edge, 5, 2)] ∉ LongPath := by
  rw [HamPath.toLongPath_mem_iff (List.cons_ne_nil _ _)
    (by simp [edge, noEdge, Graph.length_distinctVertices])]
  rintro ⟨x, hx, hxH⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact noEdge_not_mem_HamPath hxH
  · exact undeclared_not_mem_HamPath hxH

/-- On one instance the cross-composition is the reduction showing that k-Path is `NP`-hard. -/
example : HamPath.toLongPath [(edge, 1, 2)] ∈ LongPath ∧
    HamPath.toLongPath [(noEdge, 1, 2)] ∉ LongPath := by
  refine ⟨(HamPath.toLongPath_mem_iff (List.cons_ne_nil _ _) (by simp)).2
    ⟨_, List.mem_singleton_self _, edge_mem_HamPath⟩, ?_⟩
  rw [HamPath.toLongPath_mem_iff (List.cons_ne_nil _ _) (by simp)]
  rintro ⟨x, hx, hxH⟩
  rw [List.mem_singleton.1 hx] at hxH
  exact noEdge_not_mem_HamPath hxH

/-- On the empty list, outside the scope of the OR property, the output is the empty graph with
target `2`, a no-instance. -/
example : HamPath.toLongPath [] ∉ LongPath :=
  not_mem_LongPath_of_lt (by decide)

/-! ### Polynomial equivalence relations by keys -/

/-- Equal length is a polynomial equivalence relation on bit strings: equal keys, for the length
computed in unary. -/
example : IsPolyEquivalence encBits fun p : List Bool × List Bool =>
    decide (p.1.length = p.2.length) :=
  IsPolyEquivalence.of_key length_bits

/-- Equality of unary numbers is a polynomial equivalence relation. -/
example : IsPolyEquivalence encUnary fun p : ℕ × ℕ => decide (p.1 = p.2) :=
  isPolyEquivalence_eq_unary

/-! ### The hypotheses of the cross-composition theorem -/

/-- The hypotheses of the cross-composition theorem hold for k-Path: `HamPath` is `NP`-hard and
OR-cross-composes into k-Path, so the kernel lower bound assumes only `coNP ⊄ NP/poly`. -/
example : NPHard (encPair encGraph (encPair encNat encNat)) HamPath ∧
    ORCrossComposes (encPair encGraph (encPair encNat encNat)) HamPath (encPair encGraph encNat)
      Prod.snd LongPath :=
  ⟨HamPath_npHard, HamPath.orCrossComposes_LongPath⟩

/-- The kernel lower bound for k-Path, under `coNP ⊄ NP/poly` for formulas. -/
example (h : ¬ coNP encCNF ⊆ NPPoly encCNF) :
    ¬ HasPolyKernel (encPair encGraph encNat) Prod.snd LongPath :=
  not_hasPolyKernel_LongPath h

end CslibFrontierTests.LongPathKernel
