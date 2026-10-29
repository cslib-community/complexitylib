/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Hamiltonian.Diamond
public import Complexity.Computability.Complexity.Problems.ThreeSAT
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Directed Hamiltonian paths and cycles are NP-hard

`SAT.toDirHamPath` is the diamond construction of [Sipser, Theorem 7.46][Sipser2013]. Each
variable occurrence of `φ`, in order of occurrence, gets a diamond: a top node, a bottom node (the
top of the next diamond), and a row of `3 * φ.length + 3` nodes joined both ways in a line. The
top has arcs to both ends of the row, and both ends have arcs to the bottom. Clause `j` owns the
pair of row nodes `3 * j + 2` and `3 * j + 3`, and the nodes `3 * j + 1` separate the pairs. A
literal `(x, b)` of clause `j` adds a detour through the node of clause `j` across the pair of `j`
in the diamond of the first occurrence of `x`: left to right when `b` is true, right to left when
it is false. The instance asks for a Hamiltonian path from the first top to the last bottom.

A satisfying assignment gives a path that traverses each row rightwards or leftwards according to
the value of its variable and visits each clause node by the detour of the first true literal of
the clause. Conversely, in a Hamiltonian path every separator has its two row neighbours as
predecessor and successor, a detour must return to the pair it left, so all separators of a row
point the same way, and the node of a clause is entered from a pair whose row points the way of
a true literal. Diamonds of repeated occurrences of a variable carry no detours and can be
traversed either way. This argument is carried out for diamond graphs with any layout of the rows
(`Cslib.Complexity.Diamond.mem_DirHamPath_iff`); the graph here has a slot for each clause in every
row (`SAT.toDirHamPath_eq`). Clauses of every width, including the empty clause, are handled, so
the reduction is from `SAT`; it also reduces `ThreeSAT` after rejecting clauses with more than
three literals.

`Graph.mem_DirHamCycle_cons_iff` closes Hamiltonian paths into cycles with an arc back to a start
vertex that no arc enters. The top of the first diamond is such a vertex
(`Diamond.mem_DirHamCycle_iff`), which gives `SAT.toDirHamCycle`.

## Main definitions

* `Cslib.Complexity.SAT.diamondDetours`, `Cslib.Complexity.SAT.diamondGraph`: the diamond graph,
  with the node labels of `Cslib.Complexity.Diamond.graph`.
* `Cslib.Complexity.SAT.toDirHamPath`, `Cslib.Complexity.SAT.toDirHamCycle`.

## Main results

* `Cslib.Complexity.SAT.toDirHamPath_eq`: the graph as a diamond graph.
* `Cslib.Complexity.SAT.toDirHamPath_mem_iff`: `toDirHamPath φ ∈ DirHamPath ↔ φ ∈ SAT`.
* `Cslib.Complexity.SAT.toDirHamCycle_mem_iff`: `toDirHamCycle φ ∈ DirHamCycle ↔ φ ∈ SAT`.
* `Cslib.Complexity.SAT.computableInPolyTime_toDirHamPath`,
  `Cslib.Complexity.SAT.computableInPolyTime_toDirHamCycle`: the reductions are
  polynomial-time.
* `Cslib.Complexity.polyTimeReducible_SAT_DirHamPath`,
  `Cslib.Complexity.polyTimeReducible_ThreeSAT_DirHamPath`, `Cslib.Complexity.DirHamPath_npHard`,
  `Cslib.Complexity.polyTimeReducible_SAT_DirHamCycle`, `Cslib.Complexity.DirHamCycle_npHard`.
* `Cslib.Complexity.DirHamPath_npComplete`, `Cslib.Complexity.DirHamCycle_npComplete`: the
  directed problems are `NP`-complete.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

namespace SAT

/-! ### The diamond graph -/

/-- The detours of the diamond graph: the literal `l` of clause `j` goes through the node of
clause `j` across slot `j` of the row of the first occurrence of its variable, left to right when
`l` is positive. -/
def diamondDetours (φ : CNF ℕ) : List Diamond.Detour :=
  φ.zipIdx.flatMap fun c => c.1.map fun l => (c.2, φ.vars.idxOf l.1, c.2, l.2)

/-- The diamond graph of `φ` (`Cslib.Complexity.Diamond.graph`): a diamond for each variable
occurrence, in order of occurrence, a slot for each clause in every row, and the detours of the
literals. -/
def diamondGraph (φ : CNF ℕ) : Graph :=
  Diamond.graph φ.vars.length (fun _ => φ.length) φ.length (diamondDetours φ)

/-- The reduction from `SAT` to `DirHamPath` [Sipser, Theorem 7.46][Sipser2013]: the diamond
graph of `φ`, from the top of the first diamond to the bottom of the last. -/
def toDirHamPath (φ : CNF ℕ) : Graph × ℕ × ℕ :=
  (diamondGraph φ, Diamond.topNode 0, Diamond.topNode φ.vars.length)

/-- The reduction from `SAT` to `DirHamCycle`: the diamond graph of `φ` with an arc from the
bottom of the last diamond back to the top of the first. -/
def toDirHamCycle (φ : CNF ℕ) : Graph :=
  Diamond.cycleGraph φ.vars.length (fun _ => φ.length) φ.length (diamondDetours φ)

/-- The diamond graph of `φ` as a diamond graph with a slot for each clause in every row. -/
theorem toDirHamPath_eq (φ : CNF ℕ) : toDirHamPath φ =
    (Diamond.graph φ.vars.length (fun _ => φ.length) φ.length (diamondDetours φ),
      Diamond.topNode 0, Diamond.topNode φ.vars.length) := rfl

/-! ### Correctness -/

private theorem fst_mem_vars {φ : CNF ℕ} {j : ℕ} {l : Literal ℕ} (hj : j < φ.length)
    (hl : l ∈ φ[j]) : l.1 ∈ φ.vars :=
  List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨_, List.getElem_mem hj, hl⟩, rfl⟩

private theorem mem_diamondDetours {φ : CNF ℕ} {d : Diamond.Detour} :
    d ∈ diamondDetours φ ↔ ∃ (j : ℕ) (hj : j < φ.length), ∃ l ∈ φ[j],
      d = (j, φ.vars.idxOf l.1, j, l.2) := by
  simp only [diamondDetours, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨c, j⟩, hc, l, hl, rfl⟩
    obtain ⟨hj, hcj⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hc)
    exact ⟨j, hj, l, by rw [hcj]; exact hl, rfl⟩
  · rintro ⟨j, hj, l, hl, rfl⟩
    exact ⟨(φ[j], j), List.mem_zipIdx_iff_getElem?.2 (by simp [hj]), l, hl, rfl⟩

/-- The diamond graph is well formed: the detours across slot `j` all belong to clause `j`. -/
private theorem wellFormed_diamondDetours (φ : CNF ℕ) :
    Diamond.WellFormed φ.vars.length (fun _ => φ.length) φ.length (diamondDetours φ) where
  clause_lt d hd := by
    obtain ⟨j, hj, l, hl, rfl⟩ := mem_diamondDetours.1 hd
    exact hj
  row_lt d hd := by
    obtain ⟨j, hj, l, hl, rfl⟩ := mem_diamondDetours.1 hd
    exact List.idxOf_lt_length_iff.2 (fst_mem_vars hj hl)
  slot_lt d hd := by
    obtain ⟨j, hj, l, hl, rfl⟩ := mem_diamondDetours.1 hd
    exact hj
  clause_eq d hd d' hd' _ hslot := by
    obtain ⟨j, hj, l, hl, rfl⟩ := mem_diamondDetours.1 hd
    obtain ⟨j', hj', l', hl', rfl⟩ := mem_diamondDetours.1 hd'
    exact hslot

/-- Directions of the rows satisfying every clause are satisfying assignments. -/
theorem satisfiable_diamondDetours_iff (φ : CNF ℕ) :
    Diamond.Satisfiable φ.length (diamondDetours φ) ↔ φ ∈ SAT := by
  constructor
  · rintro ⟨dir, hdir⟩
    refine ⟨fun x => dir (φ.vars.idxOf x), (CNF.eval_eq_true_iff _ _).2 fun c hc => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨d, hd, hdj, hdd⟩ := hdir j hj
    obtain ⟨j', hj', l, hl, rfl⟩ := mem_diamondDetours.1 hd
    simp only at hdj hdd
    subst hdj
    exact (Clause.eval_eq_true_iff _ _).2 ⟨l, hl, hdd⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨fun i => σ (φ.vars.getD i 0), fun j hj => ?_⟩
    obtain ⟨l, hl, hσl⟩ := (Clause.eval_eq_true_iff _ _).1
      ((CNF.eval_eq_true_iff _ _).1 hσ φ[j] (List.getElem_mem hj))
    have hlt := List.idxOf_lt_length_iff.2 (fst_mem_vars hj hl)
    refine ⟨_, mem_diamondDetours.2 ⟨j, hj, l, hl, rfl⟩, rfl, ?_⟩
    simp only
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
      List.getElem_idxOf hlt]
    exact hσl

/-- **Correctness of the diamond construction.** A formula is satisfiable exactly when its
diamond graph has a Hamiltonian path from the top of the first diamond to the bottom of the last.
-/
theorem toDirHamPath_mem_iff (φ : CNF ℕ) : toDirHamPath φ ∈ DirHamPath ↔ φ ∈ SAT := by
  rw [toDirHamPath_eq]
  exact (Diamond.mem_DirHamPath_iff (wellFormed_diamondDetours φ)).trans
    (satisfiable_diamondDetours_iff φ)

/-- A Hamiltonian path of the diamond graph yields a satisfying assignment. -/
theorem mem_SAT_of_toDirHamPath_mem {φ : CNF ℕ} (h : toDirHamPath φ ∈ DirHamPath) :
    φ ∈ SAT :=
  (toDirHamPath_mem_iff φ).1 h

end SAT

namespace SAT

/-! ### Polynomial-time reductions -/

/-- The detours of the diamond graph are computable in polynomial time. -/
private theorem computableInPolyTime_diamondDetours :
    ComputableInPolyTime diamondDetours encCNF (encList Diamond.encDetour) := by
  have hvars := computableInPolyTime_vars
  unfold diamondDetours encCNF
  fun_prop

/-- The diamond graph is computable in polynomial time: node labels are computed in unary from
diamond, row, clause and first-occurrence indices, then converted to binary. -/
@[fun_prop]
theorem computableInPolyTime_diamondGraph :
    ComputableInPolyTime diamondGraph encCNF encGraph :=
  Diamond.computableInPolyTime_graph
    ((length_list encNat).comp computableInPolyTime_vars)
    ((length_list _).comp (fst _ _)) (length_list _)
    computableInPolyTime_diamondDetours

/-- The reduction `toDirHamPath` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toDirHamPath :
    ComputableInPolyTime toDirHamPath encCNF (encPair encGraph (encPair encNat encNat)) := by
  have hvars := computableInPolyTime_vars
  have hlen : ComputableInPolyTime (fun φ : CNF ℕ => φ.vars.length) encCNF encUnary :=
    (length_list encNat).comp hvars
  unfold toDirHamPath
  fun_prop

/-- **Correctness of the cycle construction.** A formula is satisfiable exactly when its closed
diamond graph has a Hamiltonian cycle. -/
theorem toDirHamCycle_mem_iff (φ : CNF ℕ) : toDirHamCycle φ ∈ DirHamCycle ↔ φ ∈ SAT :=
  (Diamond.mem_DirHamCycle_iff (wellFormed_diamondDetours φ)).trans
    (satisfiable_diamondDetours_iff φ)

/-- The closed diamond graph is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toDirHamCycle :
    ComputableInPolyTime toDirHamCycle encCNF encGraph :=
  Diamond.computableInPolyTime_cycleGraph
    ((length_list encNat).comp computableInPolyTime_vars)
    ((length_list _).comp (fst _ _)) (length_list _)
    computableInPolyTime_diamondDetours

end SAT

/-- `SAT` reduces to `DirHamPath` in polynomial time via `SAT.toDirHamPath`. -/
theorem polyTimeReducible_SAT_DirHamPath :
    PolyTimeReducible encCNF (encPair encGraph (encPair encNat encNat)) SAT DirHamPath :=
  ⟨SAT.toDirHamPath, SAT.computableInPolyTime_toDirHamPath,
    fun φ => (SAT.toDirHamPath_mem_iff φ).symm⟩

/-- `ThreeSAT` reduces to `DirHamPath` in polynomial time: a formula with a clause of more than
three literals is mapped to the diamond graph of the empty clause, which has no Hamiltonian
path. -/
theorem polyTimeReducible_ThreeSAT_DirHamPath :
    PolyTimeReducible encCNF (encPair encGraph (encPair encNat encNat)) ThreeSAT DirHamPath := by
  refine ⟨fun φ => if φ.all (fun c => decide (c.length ≤ 3)) then SAT.toDirHamPath φ
    else SAT.toDirHamPath [[]], by fun_prop, fun φ => ?_⟩
  simp only [ThreeSAT, Set.mem_ofPred_eq]
  split_ifs with h
  · rw [SAT.toDirHamPath_mem_iff, mem_SAT]
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩
  · rw [SAT.toDirHamPath_mem_iff, mem_SAT]
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    refine ⟨fun h' => (h h'.1).elim, fun ⟨σ, hσ⟩ => ?_⟩
    simp at hσ

/-- `DirHamPath` is `NP`-hard. -/
theorem DirHamPath_npHard : NPHard (encPair encGraph (encPair encNat encNat)) DirHamPath :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_DirHamPath

/-- `SAT` reduces to `DirHamCycle` in polynomial time via `SAT.toDirHamCycle`. -/
theorem polyTimeReducible_SAT_DirHamCycle : PolyTimeReducible encCNF encGraph SAT DirHamCycle :=
  ⟨SAT.toDirHamCycle, SAT.computableInPolyTime_toDirHamCycle,
    fun φ => (SAT.toDirHamCycle_mem_iff φ).symm⟩

/-- `DirHamCycle` is `NP`-hard. -/
theorem DirHamCycle_npHard : NPHard encGraph DirHamCycle :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_DirHamCycle

/-- **`DirHamPath` is NP-complete.** -/
theorem DirHamPath_npComplete :
    NPComplete (encPair encGraph (encPair encNat encNat)) DirHamPath :=
  ⟨DirHamPath.mem_NP, DirHamPath_npHard⟩

/-- **`DirHamCycle` is NP-complete.** -/
theorem DirHamCycle_npComplete : NPComplete encGraph DirHamCycle :=
  ⟨DirHamCycle.mem_NP, DirHamCycle_npHard⟩

end Cslib.Complexity
