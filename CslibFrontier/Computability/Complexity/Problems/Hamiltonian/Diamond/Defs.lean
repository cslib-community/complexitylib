/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Hamiltonian

/-!
# Diamond graph definitions, membership, and size bounds

This file defines the diamond graph (`Cslib.Complexity.Diamond.graph`) and closed diamond graph
(`Cslib.Complexity.Diamond.cycleGraph`) used in the reduction of satisfiability to directed
Hamiltonian paths and cycles [Sipser, Theorem 7.46][Sipser2013], along with vertex and arc
membership characterizations and size formulas.

## Main definitions

* `Cslib.Complexity.Diamond.Detour`: a detour through a clause node across a slot of a row.
* `Cslib.Complexity.Diamond.topNode`, `Cslib.Complexity.Diamond.rowNode`,
  `Cslib.Complexity.Diamond.clauseNode`: vertex labels of a diamond graph.
* `Cslib.Complexity.Diamond.graph`, `Cslib.Complexity.Diamond.cycleGraph`: diamond graphs and
  closed diamond graphs.
* `Cslib.Complexity.Diamond.WellFormed`, `Cslib.Complexity.Diamond.Satisfiable`.

## Main results

* `Cslib.Complexity.Diamond.mem_vertices`, `Cslib.Complexity.Diamond.mem_arcs`: membership in the
  vertex and arc lists.
* `Cslib.Complexity.Diamond.length_vertices`, `Cslib.Complexity.Diamond.length_arcs`: the size of a
  diamond graph.
* `Cslib.Complexity.Diamond.notMem_arcs_topNode_zero`: no arc enters the top of the first diamond.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

namespace Diamond

/-! ### Diamond graphs -/

/-- A detour through the node of clause `clause`, across `slot` of `row`, left to right when
`leftToRight` is true and right to left otherwise. -/
@[ext] structure Detour : Type where
  /-- The clause index visited by the detour. -/
  clause : ℕ
  /-- The row index containing the slot. -/
  row : ℕ
  /-- The slot index within the row. -/
  slot : ℕ
  /-- Whether the detour traverses the slot from left to right. -/
  leftToRight : Bool
  deriving DecidableEq, Inhabited

/-- The top of diamond `i`, which is also the bottom of diamond `i - 1`. -/
def topNode (i : ℕ) : ℕ := Nat.pair 0 i

/-- Node `a` of the row of diamond `i`. -/
def rowNode (i a : ℕ) : ℕ := Nat.pair 1 (Nat.pair i a)

/-- The node of clause `j`. -/
def clauseNode (j : ℕ) : ℕ := Nat.pair 2 j

/-- The number of nodes in row `i`: a pair of nodes for each slot, separators between and around
the pairs, and the two ends. -/
def rowLength (slots : ℕ → ℕ) (i : ℕ) : ℕ := 3 * slots i + 3

/-- The arcs of diamond `i`: from its top to both ends of its row, from both ends to its bottom,
and both ways between consecutive row nodes. -/
def diamondArcs (slots : ℕ → ℕ) (i : ℕ) : List (ℕ × ℕ) :=
  [(topNode i, rowNode i 0), (topNode i, rowNode i (rowLength slots i - 1)),
    (rowNode i 0, topNode (i + 1)), (rowNode i (rowLength slots i - 1), topNode (i + 1))] ++
    (List.range (rowLength slots i - 1)).flatMap fun a =>
      [(rowNode i a, rowNode i (a + 1)), (rowNode i (a + 1), rowNode i a)]

/-- The arcs of the detour `d`. -/
def detourArcs (d : Detour) : List (ℕ × ℕ) :=
  if d.leftToRight then
    [(rowNode d.row (3 * d.slot + 2), clauseNode d.clause),
      (clauseNode d.clause, rowNode d.row (3 * d.slot + 3))]
  else
    [(rowNode d.row (3 * d.slot + 3), clauseNode d.clause),
      (clauseNode d.clause, rowNode d.row (3 * d.slot + 2))]

/-- The arcs of the diamond graph: the diamonds and the detours. -/
def arcs (N : ℕ) (slots : ℕ → ℕ) (D : List Detour) : List (ℕ × ℕ) :=
  (List.range N).flatMap (diamondArcs slots) ++ D.flatMap detourArcs

/-- The vertices of the diamond graph: the tops, the rows and the clause nodes. -/
def vertices (N : ℕ) (slots : ℕ → ℕ) (M : ℕ) : List ℕ :=
  (List.range (N + 1)).map topNode ++
    (List.range N).flatMap (fun i => (List.range (rowLength slots i)).map (rowNode i)) ++
    (List.range M).map clauseNode

/-- The diamond graph with `N` diamonds whose rows have `slots i` slots, `M` clause nodes and the
detours `D`. -/
def graph (N : ℕ) (slots : ℕ → ℕ) (M : ℕ) (D : List Detour) : Graph :=
  (vertices N slots M, arcs N slots D)

/-- The diamond graph closed by an arc from the bottom of the last diamond to the top of the
first. -/
def cycleGraph (N : ℕ) (slots : ℕ → ℕ) (M : ℕ) (D : List Detour) : Graph :=
  (vertices N slots M, (topNode N, topNode 0) :: arcs N slots D)

/-- The detours go through declared nodes, and the detours across each slot all belong to one
clause. -/
structure WellFormed (N : ℕ) (slots : ℕ → ℕ) (M : ℕ) (D : List Detour) : Prop where
  clause_lt : ∀ d ∈ D, d.clause < M
  row_lt : ∀ d ∈ D, d.row < N
  slot_lt : ∀ d ∈ D, d.slot < slots d.row
  clause_eq : ∀ d ∈ D, ∀ d' ∈ D, d.row = d'.row → d.slot = d'.slot → d.clause = d'.clause

/-- Some directions of the rows give every clause `j < M` a detour in the direction of its row. -/
def Satisfiable (M : ℕ) (D : List Detour) : Prop :=
  ∃ dir : ℕ → Bool, ∀ j < M, ∃ d ∈ D, d.clause = j ∧ dir d.row = d.leftToRight

/-! ### Vertices and arcs -/

@[simp] theorem topNode_inj {i i' : ℕ} : topNode i = topNode i' ↔ i = i' := by
  simp [topNode, Nat.pair_eq_pair]

@[simp] theorem rowNode_inj {i i' a a' : ℕ} : rowNode i a = rowNode i' a' ↔ i = i' ∧ a = a' := by
  simp [rowNode, Nat.pair_eq_pair]

@[simp] theorem clauseNode_inj {j j' : ℕ} : clauseNode j = clauseNode j' ↔ j = j' := by
  simp [clauseNode, Nat.pair_eq_pair]

@[simp] theorem topNode_ne_rowNode (i i' a : ℕ) : topNode i ≠ rowNode i' a := by
  simp [topNode, rowNode, Nat.pair_eq_pair]

@[simp] theorem rowNode_ne_topNode (i i' a : ℕ) : rowNode i' a ≠ topNode i :=
  (topNode_ne_rowNode i i' a).symm

@[simp] theorem topNode_ne_clauseNode (i j : ℕ) : topNode i ≠ clauseNode j := by
  simp [topNode, clauseNode, Nat.pair_eq_pair]

@[simp] theorem clauseNode_ne_topNode (i j : ℕ) : clauseNode j ≠ topNode i :=
  (topNode_ne_clauseNode i j).symm

@[simp] theorem rowNode_ne_clauseNode (i a j : ℕ) : rowNode i a ≠ clauseNode j := by
  simp [rowNode, clauseNode, Nat.pair_eq_pair]

@[simp] theorem clauseNode_ne_rowNode (i a j : ℕ) : clauseNode j ≠ rowNode i a :=
  (rowNode_ne_clauseNode i a j).symm

theorem rowLength_sub_one (slots : ℕ → ℕ) (i : ℕ) : rowLength slots i - 1 = 3 * slots i + 2 := by
  simp only [rowLength]
  omega

variable {N : ℕ} {slots : ℕ → ℕ} {M : ℕ} {D : List Detour}

theorem mem_vertices {v : ℕ} :
    v ∈ vertices N slots M ↔ (∃ i ≤ N, v = topNode i) ∨
      (∃ i < N, ∃ a < rowLength slots i, v = rowNode i a) ∨ (∃ j < M, v = clauseNode j) := by
  simp only [vertices, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    Nat.lt_succ_iff]
  constructor
  · rintro ((⟨i, hi, rfl⟩ | ⟨i, hi, a, ha, rfl⟩) | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr (Or.inl ⟨i, hi, a, ha, rfl⟩)
    · exact Or.inr (Or.inr ⟨j, hj, rfl⟩)
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, a, ha, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl (Or.inl ⟨i, hi, rfl⟩)
    · exact Or.inl (Or.inr ⟨i, hi, a, ha, rfl⟩)
    · exact Or.inr ⟨j, hj, rfl⟩

theorem mem_arcs {u v : ℕ} :
    (u, v) ∈ arcs N slots D ↔
      (∃ i < N,
        (u = topNode i ∧ (v = rowNode i 0 ∨ v = rowNode i (rowLength slots i - 1))) ∨
        ((u = rowNode i 0 ∨ u = rowNode i (rowLength slots i - 1)) ∧ v = topNode (i + 1)) ∨
        (∃ a < rowLength slots i - 1, (u = rowNode i a ∧ v = rowNode i (a + 1)) ∨
          (u = rowNode i (a + 1) ∧ v = rowNode i a))) ∨
      (∃ d ∈ D,
        (d.leftToRight = true ∧ ((u = rowNode d.row (3 * d.slot + 2) ∧ v = clauseNode d.clause) ∨
          (u = clauseNode d.clause ∧ v = rowNode d.row (3 * d.slot + 3)))) ∨
        (d.leftToRight = false ∧ ((u = rowNode d.row (3 * d.slot + 3) ∧ v = clauseNode d.clause) ∨
          (u = clauseNode d.clause ∧ v = rowNode d.row (3 * d.slot + 2))))) := by
  simp only [arcs, List.mem_append, List.mem_flatMap, List.mem_range]
  refine or_congr ?_ (exists_congr fun d => and_congr_right fun _ => ?_)
  · refine exists_congr fun i => and_congr_right fun _ => ?_
    simp only [diamondArcs, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
      Prod.mk.injEq, List.not_mem_nil, or_false]
    constructor
    · rintro ((h | h | h | h) | ⟨a, ha, h | h⟩)
      · exact Or.inl ⟨h.1, Or.inl h.2⟩
      · exact Or.inl ⟨h.1, Or.inr h.2⟩
      · exact Or.inr (Or.inl ⟨Or.inl h.1, h.2⟩)
      · exact Or.inr (Or.inl ⟨Or.inr h.1, h.2⟩)
      · exact Or.inr (Or.inr ⟨a, ha, Or.inl h⟩)
      · exact Or.inr (Or.inr ⟨a, ha, Or.inr h⟩)
    · rintro (⟨h₁, h₂ | h₂⟩ | ⟨h₁ | h₁, h₂⟩ | ⟨a, ha, h | h⟩)
      · exact Or.inl (Or.inl ⟨h₁, h₂⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨h₁, h₂⟩))
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨h₁, h₂⟩)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨h₁, h₂⟩)))
      · exact Or.inr ⟨a, ha, Or.inl h⟩
      · exact Or.inr ⟨a, ha, Or.inr h⟩
  · unfold detourArcs
    cases hb : d.leftToRight <;> simp

/-- The number of vertices of a diamond graph, counted as listed. -/
theorem length_vertices (N : ℕ) (slots : ℕ → ℕ) (M : ℕ) :
    (vertices N slots M).length = 4 * N + 3 * ((List.range N).map slots).sum + M + 1 := by
  simp only [vertices, List.length_append, List.length_map, List.length_range,
    List.length_flatMap, rowLength]
  rw [List.sum_map_add, List.sum_map_mul_left]
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  ring

/-- The number of arcs of a diamond graph, counted as listed. -/
theorem length_arcs (N : ℕ) (slots : ℕ → ℕ) (D : List Detour) :
    (arcs N slots D).length = 8 * N + 6 * ((List.range N).map slots).sum + 2 * D.length := by
  have h₁ : ∀ i, (diamondArcs slots i).length = 6 * slots i + 8 := fun i => by
    simp only [diamondArcs, List.length_append, List.length_cons, List.length_nil,
      List.length_flatMap, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul,
      rowLength_sub_one]
    ring
  have h₂ : ∀ d, (detourArcs d).length = 2 := fun d => by
    unfold detourArcs
    split_ifs <;> rfl
  simp only [arcs, List.length_append, List.length_flatMap, h₁, h₂]
  rw [List.sum_map_add, List.sum_map_mul_left]
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  ring

/-- No arc enters the top of the first diamond. -/
theorem notMem_arcs_topNode_zero (u : ℕ) : (u, topNode 0) ∉ arcs N slots D := fun h => by
  rcases mem_arcs.1 h with
      ⟨i, -, ⟨-, h₂ | h₂⟩ | ⟨-, h₂⟩ | ⟨a, -, ⟨-, h₂⟩ | ⟨-, h₂⟩⟩⟩ |
      ⟨d, -, ⟨-, ⟨-, h₂⟩ | ⟨-, h₂⟩⟩ | ⟨-, ⟨-, h₂⟩ | ⟨-, h₂⟩⟩⟩ <;> simp at h₂

end Diamond

end Cslib.Complexity
