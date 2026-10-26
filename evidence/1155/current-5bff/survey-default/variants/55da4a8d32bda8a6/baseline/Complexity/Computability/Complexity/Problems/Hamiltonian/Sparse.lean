/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Hamiltonian.Diamond
public import Complexity.Computability.Complexity.Problems.Hamiltonian.Undirected
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Logics.Propositional.CNF.ModelCount
import Complexity.Computability.Complexity.Problems.Hamiltonian.Directed
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# A reduction of linear size to Hamiltonian cycles

Sipser's diamond reduction `Cslib.Complexity.SAT.toDirHamPath` gives every row a pair of nodes for
each clause, so its graph has `Θ(m ^ 2)` vertices and arcs on formulas with `m` clauses of three
literals. `SAT.toSparseDirHamPath` is the diamond graph (`Cslib.Complexity.Diamond.graph`) with one
diamond for each distinct variable of the formula, whose row has a slot for each occurrence of the
variable and no other. The occurrence at position `p` of `φ.vars`, a literal `(x, b)` of clause
`j`, adds a detour through the node of clause `j` across its slot in the row of `x`, left to right
when `b` is true. The detours across a slot belong to a single occurrence, so the graph is
well formed, and directions of the rows satisfying every clause are satisfying assignments: the
graph has a Hamiltonian path exactly when the formula is satisfiable
(`Cslib.Complexity.SAT.toSparseDirHamPath_mem_iff`).

The graph has at most `23 L + m + 1` vertices and arcs in total, for `L` occurrences of variables
(`Cslib.Complexity.SAT.length_sparseDiamondGraph_le_length_vars`), so at most `(23 k + 1) m + 1` on
formulas with clauses of at most `k` literals (`Cslib.Complexity.SAT.length_sparseDiamondGraph_le`).
Closing the path with an arc back to the first top (`Cslib.Complexity.SAT.toSparseDirHamCycle`,
`Cslib.Complexity.Diamond.mem_DirHamCycle_iff`) gives directed Hamiltonian cycles, and splitting
every vertex into three (`Cslib.Complexity.Graph.split`) gives undirected Hamiltonian cycles
(`Cslib.Complexity.SAT.toSparseHamCycle`), still of linear size.

## Main definitions

* `Cslib.Complexity.SAT.occurrencePositions`: the positions of the occurrences of a variable.
* `Cslib.Complexity.SAT.sparseSlots`, `Cslib.Complexity.SAT.sparseDetours`,
  `Cslib.Complexity.SAT.sparseDiamondGraph`: the layout of the rows and the graph.
* `Cslib.Complexity.SAT.toSparseDirHamPath`, `Cslib.Complexity.SAT.toSparseDirHamCycle`,
  `Cslib.Complexity.SAT.toSparseHamCycle`: the reductions.

## Main results

* `Cslib.Complexity.SAT.toSparseDirHamPath_mem_iff`,
  `Cslib.Complexity.SAT.toSparseDirHamCycle_mem_iff`,
  `Cslib.Complexity.SAT.toSparseHamCycle_mem_iff`: correctness.
* `Cslib.Complexity.SAT.computableInPolyTime_toSparseDirHamPath`,
  `Cslib.Complexity.SAT.computableInPolyTime_toSparseDirHamCycle`,
  `Cslib.Complexity.SAT.computableInPolyTime_toSparseHamCycle`: the reductions are
  polynomial-time.
* `Cslib.Complexity.SAT.length_sparseDiamondGraph_le_length_vars`,
  `Cslib.Complexity.SAT.length_sparseDiamondGraph_le`,
  `Cslib.Complexity.SAT.length_toSparseDirHamCycle_le`,
  `Cslib.Complexity.SAT.length_toSparseHamCycle_le`: the graphs have linear size.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableTidilyInPolyTime Diamond

namespace SAT

/-! ### The graph -/

/-- The positions in `φ.vars` of the occurrences of the variable `x`. -/
def occurrencePositions (φ : CNF ℕ) (x : ℕ) : List ℕ :=
  (List.range φ.vars.length).filter fun q => φ.vars.getD q 0 = x

/-- The number of slots of row `i`: the number of occurrences of variable `i` of
`φ.distinctVars`. -/
def sparseSlots (φ : CNF ℕ) (i : ℕ) : ℕ :=
  (occurrencePositions φ (φ.distinctVars.getD i 0)).length

/-- The detours: the occurrence at position `p` of `φ.vars`, a literal `(x, b)` of clause `j`,
goes through the node of clause `j` across its slot in the row of `x`, in the direction `b`. -/
def sparseDetours (φ : CNF ℕ) : List Detour :=
  (occurrences φ).zipIdx.map fun o => (o.1.1, φ.distinctVars.idxOf o.1.2.2.1,
    (occurrencePositions φ o.1.2.2.1).idxOf o.2, o.1.2.2.2)

/-- The diamond graph with one diamond for each distinct variable of `φ` and a slot for each
occurrence. -/
def sparseDiamondGraph (φ : CNF ℕ) : Graph :=
  graph φ.distinctVars.length (sparseSlots φ) φ.length (sparseDetours φ)

/-- The reduction from `SAT` to `DirHamPath` of linear size: the sparse diamond graph of `φ`,
from the top of the first diamond to the bottom of the last. -/
def toSparseDirHamPath (φ : CNF ℕ) : Graph × ℕ × ℕ :=
  (sparseDiamondGraph φ, Diamond.topNode 0, Diamond.topNode φ.distinctVars.length)

/-- The reduction from `SAT` to `DirHamCycle` of linear size: the sparse diamond graph of `φ` with
an arc from the bottom of the last diamond back to the top of the first. -/
def toSparseDirHamCycle (φ : CNF ℕ) : Graph :=
  cycleGraph φ.distinctVars.length (sparseSlots φ) φ.length (sparseDetours φ)

/-- The reduction from `SAT` to `HamCycle` of linear size: the vertex-splitting graph of the
closed sparse diamond graph. -/
def toSparseHamCycle (φ : CNF ℕ) : Graph := (toSparseDirHamCycle φ).split

/-! ### Correctness -/

section Correctness

variable {φ : CNF ℕ}

private theorem mem_vars_of_mem_occurrences {o : Occurrence ℕ} (ho : o ∈ occurrences φ) :
    o.2.2.1 ∈ φ.vars := by
  rw [← map_occurrences]
  exact List.mem_map_of_mem ho

private theorem mem_occurrencePositions {x q : ℕ} :
    q ∈ occurrencePositions φ x ↔ q < φ.vars.length ∧ φ.vars.getD q 0 = x := by
  simp [occurrencePositions]

/-- The detours come from occurrences, numbered by their positions. -/
private theorem mem_sparseDetours {d : Detour} :
    d ∈ sparseDetours φ ↔ ∃ o p, (occurrences φ)[p]? = some o ∧
      d = (o.1, φ.distinctVars.idxOf o.2.2.1, (occurrencePositions φ o.2.2.1).idxOf p,
        o.2.2.2) := by
  simp only [sparseDetours, List.mem_map]
  constructor
  · rintro ⟨⟨o, p⟩, h, rfl⟩
    exact ⟨o, p, List.mem_zipIdx_iff_getElem?.1 h, rfl⟩
  · rintro ⟨o, p, h, rfl⟩
    exact ⟨(o, p), List.mem_zipIdx_iff_getElem?.2 h, rfl⟩

/-- The position of an occurrence is a position of its variable. -/
private theorem mem_occurrencePositions_of_getElem? {o : Occurrence ℕ} {p : ℕ}
    (h : (occurrences φ)[p]? = some o) : p ∈ occurrencePositions φ o.2.2.1 := by
  have hp := (List.getElem?_eq_some_iff.1 h).1
  have hlen := length_occurrences φ
  rw [mem_occurrencePositions]
  refine ⟨hlen ▸ hp, ?_⟩
  rw [← map_occurrences, List.getD_eq_getElem?_getD, List.getElem?_map, h]
  rfl

/-- The sparse diamond graph is well formed. -/
theorem wellFormed_sparseDetours :
    WellFormed φ.distinctVars.length (sparseSlots φ) φ.length (sparseDetours φ) where
  clause_lt d hd := by
    obtain ⟨o, p, h, rfl⟩ := mem_sparseDetours.1 hd
    exact (mem_occurrences.1 (List.mem_of_getElem? h)).1
  row_lt d hd := by
    obtain ⟨o, p, h, rfl⟩ := mem_sparseDetours.1 hd
    exact List.idxOf_lt_length_iff.2
      (CNF.mem_distinctVars.2 (mem_vars_of_mem_occurrences (List.mem_of_getElem? h)))
  slot_lt d hd := by
    obtain ⟨o, p, h, rfl⟩ := mem_sparseDetours.1 hd
    simp only [sparseSlots]
    rw [List.getD_idxOf (CNF.mem_distinctVars.2
      (mem_vars_of_mem_occurrences (List.mem_of_getElem? h))) 0]
    exact List.idxOf_lt_length_iff.2 (mem_occurrencePositions_of_getElem? h)
  clause_eq d hd d' hd' hrow hslot := by
    obtain ⟨o, p, h, rfl⟩ := mem_sparseDetours.1 hd
    obtain ⟨o', p', h', rfl⟩ := mem_sparseDetours.1 hd'
    simp only at hrow hslot ⊢
    rw [List.idxOf_inj (CNF.mem_distinctVars.2
      (mem_vars_of_mem_occurrences (List.mem_of_getElem? h)))] at hrow
    rw [hrow, List.idxOf_inj (hrow ▸ mem_occurrencePositions_of_getElem? h)] at hslot
    rw [hslot, h'] at h
    rw [Option.some_injective _ h]

/-- Directions of the rows satisfying every clause are satisfying assignments. -/
theorem satisfiable_sparseDetours_iff :
    Satisfiable φ.length (sparseDetours φ) ↔ φ ∈ SAT := by
  constructor
  · rintro ⟨dir, hdir⟩
    refine ⟨fun x => dir (φ.distinctVars.idxOf x),
      (CNF.eval_eq_true_iff _ _).2 fun c hc => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨d, hd, hdj, hdd⟩ := hdir j hj
    obtain ⟨o, p, h, rfl⟩ := mem_sparseDetours.1 hd
    obtain ⟨hi, hk, hl⟩ := mem_occurrences.1 (List.mem_of_getElem? h)
    simp only at hdj hdd
    subst hdj
    rw [Clause.eval_eq_true_iff]
    exact ⟨o.2.2, by rw [hl]; exact List.getElem_mem hk, hdd⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨fun i => σ (φ.distinctVars.getD i 0), fun j hj => ?_⟩
    obtain ⟨l, hl, hσl⟩ := (Clause.eval_eq_true_iff _ _).1
      ((CNF.eval_eq_true_iff _ _).1 hσ φ[j] (List.getElem_mem hj))
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
    have ho : ((j, k, φ[j][k]) : Occurrence ℕ) ∈ occurrences φ := mem_occurrences.2 ⟨hj, hk, rfl⟩
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 ho
    refine ⟨_, mem_sparseDetours.2 ⟨_, p, hp, rfl⟩, rfl, ?_⟩
    simp only
    rw [List.getD_idxOf (CNF.mem_distinctVars.2 (mem_vars_of_mem_occurrences ho)) 0]
    exact hσl

end Correctness

/-- **Correctness of the sparse diamond construction.** A formula is satisfiable exactly when its
sparse diamond graph has a Hamiltonian path from the top of the first diamond to the bottom of the
last. -/
theorem toSparseDirHamPath_mem_iff (φ : CNF ℕ) : toSparseDirHamPath φ ∈ DirHamPath ↔ φ ∈ SAT :=
  (mem_DirHamPath_iff wellFormed_sparseDetours).trans satisfiable_sparseDetours_iff

/-- **Correctness of the closed sparse diamond construction.** A formula is satisfiable exactly
when its closed sparse diamond graph has a Hamiltonian cycle. -/
theorem toSparseDirHamCycle_mem_iff (φ : CNF ℕ) : toSparseDirHamCycle φ ∈ DirHamCycle ↔ φ ∈ SAT :=
  (mem_DirHamCycle_iff wellFormed_sparseDetours).trans satisfiable_sparseDetours_iff

/-- **Correctness of the undirected construction.** A formula is satisfiable exactly when the
vertex-splitting graph of its closed sparse diamond graph has a Hamiltonian cycle. -/
theorem toSparseHamCycle_mem_iff (φ : CNF ℕ) : toSparseHamCycle φ ∈ HamCycle ↔ φ ∈ SAT :=
  (Graph.split_mem_HamCycle_iff _).trans (toSparseDirHamCycle_mem_iff φ)

/-! ### Size -/

/-- The rows have at most as many slots in total as `φ` has occurrences of variables. -/
theorem sum_sparseSlots_le (φ : CNF ℕ) :
    ((List.range φ.distinctVars.length).map (sparseSlots φ)).sum ≤ φ.vars.length := by
  have hnd := φ.nodup_distinctVars
  rw [show ((List.range φ.distinctVars.length).map (sparseSlots φ)).sum =
      ((List.range φ.distinctVars.length).flatMap
        fun i => occurrencePositions φ (φ.distinctVars.getD i 0)).length by
    rw [List.length_flatMap]
    rfl]
  refine le_of_le_of_eq (List.Nodup.length_le_of_subset ?_ (l₂ := List.range φ.vars.length)
    fun q hq => ?_) List.length_range
  · refine List.nodup_flatMap.2 ⟨fun i _ => List.nodup_range.filter _,
      List.nodup_range.pairwise_of_forall_ne fun i hi i' hi' hii' q hq hq' => hii' ?_⟩
    rw [mem_occurrencePositions] at hq hq'
    rw [List.mem_range] at hi hi'
    rw [List.getD_eq_getElem _ _ hi] at hq
    rw [List.getD_eq_getElem _ _ hi'] at hq'
    exact (hnd.getElem_inj_iff).1 (hq.2.symm.trans hq'.2)
  · obtain ⟨i, -, hq⟩ := List.mem_flatMap.1 hq
    exact List.mem_range.2 (mem_occurrencePositions.1 hq).1

/-- **The sparse diamond graph has linear size.** It has at most `23 L + m + 1` vertices and arcs
in total, counted as listed, for `L` occurrences of variables and `m` clauses. -/
theorem length_sparseDiamondGraph_le_length_vars (φ : CNF ℕ) :
    (sparseDiamondGraph φ).1.length + (sparseDiamondGraph φ).2.length ≤
      23 * φ.vars.length + φ.length + 1 := by
  have hS := sum_sparseSlots_le φ
  have hn : φ.distinctVars.length ≤ φ.vars.length := by
    rw [CNF.length_distinctVars]
    exact CNF.numVars_le_length_vars φ
  have hD : (sparseDetours φ).length = φ.vars.length := by
    rw [sparseDetours, List.length_map, List.length_zipIdx, length_occurrences]
  simp only [sparseDiamondGraph, graph, Diamond.length_vertices, Diamond.length_arcs, hD]
  omega

/-- **The sparse diamond graph has linear size.** On formulas with `m` clauses of at most `k`
literals, it has at most `(23 k + 1) m + 1` vertices and arcs in total, counted as listed. -/
theorem length_sparseDiamondGraph_le {k : ℕ} {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ k) :
    (sparseDiamondGraph φ).1.length + (sparseDiamondGraph φ).2.length ≤
      (23 * k + 1) * φ.length + 1 := by
  have h := length_sparseDiamondGraph_le_length_vars φ
  have hL := CNF.length_vars_le_mul_length hφ
  nlinarith

/-- The closed sparse diamond graph has linear size. -/
theorem length_toSparseDirHamCycle_le {k : ℕ} {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ k) :
    (toSparseDirHamCycle φ).1.length + (toSparseDirHamCycle φ).2.length ≤
      (23 * k + 1) * φ.length + 2 := by
  have h := length_sparseDiamondGraph_le hφ
  simp only [sparseDiamondGraph, graph] at h
  simp only [toSparseDirHamCycle, cycleGraph, List.length_cons]
  omega

/-- **The undirected reduction has linear size.** On formulas with `m` clauses of at most `k`
literals, the graph of `toSparseHamCycle` has at most `(115 k + 5) m + 10` vertices and edges in
total, counted as listed. -/
theorem length_toSparseHamCycle_le {k : ℕ} {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ k) :
    (toSparseHamCycle φ).1.length + (toSparseHamCycle φ).2.length ≤
      (115 * k + 5) * φ.length + 10 := by
  have h := length_toSparseDirHamCycle_le hφ
  rw [toSparseHamCycle, Graph.length_split_fst, Graph.length_split_snd]
  nlinarith

/-! ### Polynomial-time reductions -/

/-- The positions of the occurrences of a variable are computable in polynomial time. -/
theorem computableInPolyTime_occurrencePositions :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => occurrencePositions p.1 p.2)
      (encPair encCNF encNat) (encList encUnary) := by
  refine .of_tidy ?_
  have hvars := computableInPolyTime_vars.tidy
  have htest : ComputableTidilyInPolyTime
      (fun p : (CNF ℕ × ℕ) × ℕ => decide (p.1.1.vars.getD p.2 0 = p.1.2))
      (encPair (encPair encCNF encNat) encUnary) encBool := by
    have hget : ComputableTidilyInPolyTime (fun p : (CNF ℕ × ℕ) × ℕ => p.1.1.vars.getD p.2 0)
        (encPair (encPair encCNF encNat) encUnary) encNat :=
      (listGetD (encA := encNat) (encL := encList encNat) 0).comp
        ((hvars.comp ((fst _ _).comp (fst _ _))).prod (snd _ _))
    exact hget.decide_eq' ((snd _ _).comp (fst _ _))
  have hrange : ComputableTidilyInPolyTime (fun p : CNF ℕ × ℕ => List.range p.1.vars.length)
      (encPair encCNF encNat) (encList encUnary) :=
    range.comp ((length_list encNat).comp (hvars.comp (fst _ _)))
  unfold occurrencePositions
  exact filterWithInput hrange htest

/-- The numbers of slots are computable in polynomial time, in unary. -/
theorem computableInPolyTime_sparseSlots :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => sparseSlots p.1 p.2)
      (encPair encCNF encUnary) encUnary := by
  refine .of_tidy ?_
  have hdv := computableInPolyTime_distinctVars.tidy
  have hpos := computableInPolyTime_occurrencePositions.tidy
  unfold sparseSlots
  fun_prop

/-- The detours are computable in polynomial time. -/
theorem computableInPolyTime_sparseDetours :
    ComputableInPolyTime sparseDetours encCNF (encList encDetour) := by
  refine .of_tidy ?_
  have hdv := computableInPolyTime_distinctVars.tidy
  have hpos := computableInPolyTime_occurrencePositions.tidy
  have hocc := computableInPolyTime_occurrences.tidy
  unfold encOccurrence Cslib.Logic.PL.encOccurrence at hocc
  unfold sparseDetours
  fun_prop

private theorem computableTidilyInPolyTime_numDiamonds :
    ComputableTidilyInPolyTime (fun φ : CNF ℕ => φ.distinctVars.length) encCNF
      encUnary :=
  (length_list encNat).comp computableInPolyTime_distinctVars.tidy

/-- The sparse diamond graph is computable in polynomial time: node labels are computed in unary
from diamond, row, clause and occurrence indices, then converted to binary. -/
@[fun_prop]
theorem computableInPolyTime_sparseDiamondGraph :
    ComputableInPolyTime sparseDiamondGraph encCNF encGraph :=
  (computableInPolyTime_graph (.of_tidy computableTidilyInPolyTime_numDiamonds)
    computableInPolyTime_sparseSlots (.of_tidy (length_list _)) computableInPolyTime_sparseDetours)

/-- The reduction `toSparseDirHamPath` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toSparseDirHamPath :
    ComputableInPolyTime toSparseDirHamPath encCNF
      (encPair encGraph (encPair encNat encNat)) := by
  have hgraph := computableInPolyTime_sparseDiamondGraph.tidy
  have htop := Diamond.computableInPolyTime_topNode.tidy
  have hvars := SAT.computableInPolyTime_distinctVars.tidy
  refine .of_tidy ?_
  have hn := computableTidilyInPolyTime_numDiamonds
  unfold toSparseDirHamPath
  fun_prop

/-- The reduction `toSparseDirHamCycle` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toSparseDirHamCycle :
    ComputableInPolyTime toSparseDirHamCycle encCNF encGraph :=
  (computableInPolyTime_cycleGraph (.of_tidy computableTidilyInPolyTime_numDiamonds)
    computableInPolyTime_sparseSlots (.of_tidy (length_list _)) computableInPolyTime_sparseDetours)

/-- The reduction `toSparseHamCycle` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toSparseHamCycle :
    ComputableInPolyTime toSparseHamCycle encCNF encGraph :=
  Graph.computableInPolyTime_split.comp computableInPolyTime_toSparseDirHamCycle

end SAT

end Cslib.Complexity
