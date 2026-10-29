/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Hamiltonian.Diamond.Defs
public import Complexity.Computability.Complexity.Problems.Hamiltonian.Diamond.Soundness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Diamond graphs

The diamond construction of [Sipser, Theorem 7.46][Sipser2013] reduces satisfiability to directed
Hamiltonian paths. This file treats it for an arbitrary layout of the rows, so that reductions can
choose how many nodes each row has. A diamond graph (`Cslib.Complexity.Diamond.graph`) has

* `N` diamonds, diamond `i` with a top node, a bottom node (the top of diamond `i + 1`), and a row
  of `3 * slots i + 3` nodes joined both ways in a line; the top has arcs to both ends of the row,
  and both ends have arcs to the bottom. Slot `s < slots i` of row `i` is the pair of row nodes
  `3 * s + 2` and `3 * s + 3`, and the nodes `3 * s + 1` separate the pairs;
* `M` clause nodes;
* a list of detours `(j, i, s, b)`, each through the node of clause `j` across slot `s` of row `i`:
  left to right when `b` is true, right to left when it is false.

When the detours across each slot all belong to one clause (`Cslib.Complexity.Diamond.WellFormed`),
the graph has a Hamiltonian path from the first top to the last bottom exactly when the rows can be
given directions so that every clause has a detour in the direction of its row
(`Cslib.Complexity.Diamond.mem_DirHamPath_iff`). In a Hamiltonian path every separator has its two
row neighbours as predecessor and successor, a detour must return to the slot it left, so all
separators of a row point the same way, and the node of a clause is entered from a slot whose row
points the way of the detour. Conversely, rows traversed in the given directions, each clause
visited by one detour in the direction of its row, form a Hamiltonian path.

Sipser's construction is the layout with one slot for each clause in every row; giving each row
only the slots of the detours through it makes the graph linear in the size of the formula.

Node labels, detours, graphs, and the `WellFormed` and `Satisfiable` predicates are defined in
`Complexity.Computability.Complexity.Problems.Hamiltonian.Diamond.Defs`, and Hamiltonian-path
soundness (`satisfiable_of_mem_DirHamPath`) is proved in
`Complexity.Computability.Complexity.Problems.Hamiltonian.Diamond.Soundness`; both are re-exported
here alongside completeness, the equivalences `mem_DirHamPath_iff` and `mem_DirHamCycle_iff`, and
polynomial-time computability.

## Main definitions

* `Cslib.Complexity.Diamond.encDetour`: the encoding of detours used for polynomial-time
  computability.

## Main results

* `Cslib.Complexity.Diamond.mem_DirHamPath_iff`: Hamiltonian paths of a diamond graph are
  directions of its rows satisfying every clause.
* `Cslib.Complexity.Diamond.mem_DirHamCycle_iff`: Hamiltonian cycles of a closed diamond graph
  likewise.
* `Cslib.Complexity.Diamond.computableInPolyTime_graph`,
  `Cslib.Complexity.Diamond.computableInPolyTime_cycleGraph`: diamond graphs are computable
  in polynomial time from layouts computable in polynomial time.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

namespace Diamond

variable {N : ℕ} {slots : ℕ → ℕ} {M : ℕ} {D : List Detour}

/-! ### Directions satisfying every clause give Hamiltonian paths -/

section Blocks

variable {α : Type*} {R : α → α → Prop} {f : ℕ → List α} {n : ℕ}

/-- Nonempty chains indexed by `0, …, n - 1`, each linked to the next, form a chain. -/
private theorem isChain_flatMap_range (hne : ∀ a < n, f a ≠ [])
    (hblock : ∀ a < n, (f a).IsChain R)
    (hlink : ∀ a, a + 1 < n → ∀ x ∈ (f a).getLast?, ∀ y ∈ (f (a + 1)).head?, R x y) :
    ((List.range n).flatMap f).IsChain R := by
  rw [List.flatMap_def, List.isChain_flatten (by simpa using hne)]
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hl
    exact hblock a (List.mem_range.1 ha)
  · rw [List.isChain_map, List.isChain_range]
    exact fun a ha => hlink a (by omega)

/-- Nonempty chains indexed by `n - 1, …, 0`, each linked to the previous, form a chain. -/
private theorem isChain_flatMap_range_reverse (hne : ∀ a < n, f a ≠ [])
    (hblock : ∀ a < n, (f a).IsChain R)
    (hlink : ∀ a, a + 1 < n → ∀ x ∈ (f (a + 1)).getLast?, ∀ y ∈ (f a).head?, R x y) :
    ((List.range n).reverse.flatMap f).IsChain R := by
  rw [List.flatMap_def, List.isChain_flatten (by simpa using hne)]
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hl
    exact hblock a (List.mem_range.1 (List.mem_reverse.1 ha))
  · rw [List.isChain_map, List.isChain_reverse, List.isChain_range]
    exact fun a ha => hlink a (by omega)

private theorem head?_flatMap_range (hn : 0 < n) (h : f 0 ≠ []) :
    ((List.range n).flatMap f).head? = (f 0).head? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [Nat.zero_add, List.range_succ_eq_map, List.flatMap_cons, List.head?_append_of_ne_nil _ h]

private theorem getLast?_flatMap_range (hn : 0 < n) (h : f (n - 1) ≠ []) :
    ((List.range n).flatMap f).getLast? = (f (n - 1)).getLast? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [Nat.zero_add, Nat.add_sub_cancel] at h ⊢
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
    List.getLast?_append_of_ne_nil _ h]

private theorem head?_flatMap_range_reverse (hn : 0 < n) (h : f (n - 1) ≠ []) :
    ((List.range n).reverse.flatMap f).head? = (f (n - 1)).head? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [Nat.zero_add, Nat.add_sub_cancel] at h ⊢
  rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.flatMap_cons, List.head?_append_of_ne_nil _ h]

private theorem getLast?_flatMap_range_reverse (hn : 0 < n) (h : f 0 ≠ []) :
    ((List.range n).reverse.flatMap f).getLast? = (f 0).getLast? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [Nat.zero_add, List.range_succ_eq_map, List.reverse_cons, List.flatMap_append,
    List.flatMap_singleton, List.getLast?_append_of_ne_nil _ h]

end Blocks

section DirectionsToPath

variable (N slots M) (dir : ℕ → Bool) (pick : ℕ → Detour)

/-- The clause visited across slot `s` of row `i`: one whose picked detour crosses the slot. -/
private def visit (i s : ℕ) : Option ℕ :=
  (List.range M).find? fun j => decide ((pick j).2.1 = i ∧ (pick j).2.2.1 = s)

/-- Row node `a` of row `i` in a rightward traversal, followed by the node of the clause visited
across the slot starting at `a`. -/
private def rightStep (i a : ℕ) : List ℕ :=
  rowNode i a :: if a % 3 = 2 then ((visit M pick i (a / 3)).map clauseNode).toList else []

/-- Row node `a` of row `i` in a leftward traversal, followed by the node of the clause visited
across the slot ending at `a`. -/
private def leftStep (i a : ℕ) : List ℕ :=
  rowNode i a ::
    if a % 3 = 0 ∧ 0 < a then ((visit M pick i (a / 3 - 1)).map clauseNode).toList else []

/-- The traversal of row `i` in its direction, with the visited clauses. -/
private def rowPath (i : ℕ) : List ℕ :=
  if dir i then (List.range (rowLength slots i)).flatMap (rightStep M pick i)
  else (List.range (rowLength slots i)).reverse.flatMap (leftStep M pick i)

/-- The Hamiltonian path of the diamond graph read off directions of the rows. -/
private def hamPath : List ℕ :=
  (List.range N).flatMap (fun i => topNode i :: rowPath slots M dir pick i) ++ [topNode N]

variable {N slots M dir pick}

private theorem mem_rightStep {i a x : ℕ} : x ∈ rightStep M pick i a ↔ x = rowNode i a ∨
    (a % 3 = 2 ∧ ∃ j, visit M pick i (a / 3) = some j ∧ x = clauseNode j) := by
  unfold rightStep
  split_ifs with h
  · cases hv : visit M pick i (a / 3) <;> simp [h]
  · simp [h]

private theorem mem_leftStep {i a x : ℕ} : x ∈ leftStep M pick i a ↔ x = rowNode i a ∨
    ((a % 3 = 0 ∧ 0 < a) ∧ ∃ j, visit M pick i (a / 3 - 1) = some j ∧ x = clauseNode j) := by
  unfold leftStep
  split_ifs with h
  · cases hv : visit M pick i (a / 3 - 1) <;> simp [h]
  · simp [h]

private theorem rightStep_ne_nil (i a : ℕ) : rightStep M pick i a ≠ [] := List.cons_ne_nil _ _

private theorem leftStep_ne_nil (i a : ℕ) : leftStep M pick i a ≠ [] := List.cons_ne_nil _ _

private theorem rowLength_pos (i : ℕ) : 0 < rowLength slots i := by
  simp only [rowLength]
  omega

private theorem arc_of_mem_diamondArcs {i : ℕ} (hi : i < N) {e : ℕ × ℕ}
    (he : e ∈ diamondArcs slots i) : e ∈ arcs N slots D :=
  List.mem_append_left _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, he⟩)

private theorem arc_row_succ {i a : ℕ} (hi : i < N) (ha : a + 1 < rowLength slots i) :
    (rowNode i a, rowNode i (a + 1)) ∈ arcs N slots D :=
  arc_of_mem_diamondArcs hi (List.mem_append_right _
    (List.mem_flatMap.2 ⟨a, List.mem_range.2 (by omega), by simp⟩))

private theorem arc_row_pred {i a : ℕ} (hi : i < N) (ha : a + 1 < rowLength slots i) :
    (rowNode i (a + 1), rowNode i a) ∈ arcs N slots D :=
  arc_of_mem_diamondArcs hi (List.mem_append_right _
    (List.mem_flatMap.2 ⟨a, List.mem_range.2 (by omega), by simp⟩))

variable (hD : WellFormed N slots M D)
  (hpick : ∀ j < M, pick j ∈ D ∧ (pick j).1 = j ∧ dir (pick j).2.1 = (pick j).2.2.2)
include hD hpick

private theorem visit_eq_some_iff {i s j : ℕ} :
    visit M pick i s = some j ↔ j < M ∧ (pick j).2.1 = i ∧ (pick j).2.2.1 = s := by
  constructor
  · intro h
    have hmem := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [decide_eq_true_eq] at hp
    exact ⟨List.mem_range.1 hmem, hp⟩
  · rintro ⟨hj, hi, hs⟩
    cases hv : visit M pick i s with
    | none =>
      rw [visit, List.find?_eq_none] at hv
      exact absurd (by simp [hi, hs]) (hv j (List.mem_range.2 hj))
    | some j' =>
      have hmem := List.mem_range.1 (List.mem_of_find?_eq_some hv)
      have hp := List.find?_some hv
      simp only [decide_eq_true_eq] at hp
      have h₁ := (hpick j hj).2.1
      have h₂ := (hpick j' hmem).2.1
      have := hD.clause_eq _ (hpick j hj).1 _ (hpick j' hmem).1 (hi.trans hp.1.symm)
        (hs.trans hp.2.symm)
      rw [h₁, h₂] at this
      rw [this]

omit hD in
/-- The arcs of the picked detour of a clause, in the direction of its row. -/
private theorem arc_detour {j : ℕ} (hj : j < M) :
    (dir (pick j).2.1 = true →
      (rowNode (pick j).2.1 (3 * (pick j).2.2.1 + 2), clauseNode j) ∈ arcs N slots D ∧
      (clauseNode j, rowNode (pick j).2.1 (3 * (pick j).2.2.1 + 3)) ∈ arcs N slots D) ∧
    (dir (pick j).2.1 = false →
      (rowNode (pick j).2.1 (3 * (pick j).2.2.1 + 3), clauseNode j) ∈ arcs N slots D ∧
      (clauseNode j, rowNode (pick j).2.1 (3 * (pick j).2.2.1 + 2)) ∈ arcs N slots D) := by
  obtain ⟨hmem, hcl, hdir⟩ := hpick j hj
  have harc : ∀ e ∈ detourArcs (pick j), e ∈ arcs N slots D := fun e he =>
    List.mem_append_right _ (List.mem_flatMap.2 ⟨pick j, hmem, he⟩)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hb : (pick j).2.2.2 = true := hdir ▸ h
    exact ⟨harc _ (by simp [detourArcs, hb, hcl]), harc _ (by simp [detourArcs, hb, hcl])⟩
  · have hb : (pick j).2.2.2 = false := hdir ▸ h
    exact ⟨harc _ (by simp [detourArcs, hb, hcl]), harc _ (by simp [detourArcs, hb, hcl])⟩

/-- No clause is visited across the right end of a row. -/
private theorem visit_last (i : ℕ) : visit M pick i (slots i) = none := by
  cases hv : visit M pick i (slots i) with
  | none => rfl
  | some j =>
    obtain ⟨hj, hi, hs⟩ := (visit_eq_some_iff hD hpick).1 hv
    have := hD.slot_lt _ (hpick j hj).1
    rw [hi, hs] at this
    exact absurd this (lt_irrefl _)

/-- The traversal of a row, its first and last node, and its arcs. -/
private theorem rowPath_spec {i : ℕ} (hi : i < N) :
    (rowPath slots M dir pick i).IsChain (fun u v => (u, v) ∈ arcs N slots D) ∧
    (∀ x ∈ (rowPath slots M dir pick i).head?, (topNode i, x) ∈ arcs N slots D) ∧
    (∀ x ∈ (rowPath slots M dir pick i).getLast?, (x, topNode (i + 1)) ∈ arcs N slots D) ∧
    rowPath slots M dir pick i ≠ [] := by
  have hm := rowLength_sub_one slots i
  have hpos := rowLength_pos (slots := slots) i
  have hdiam : ∀ e ∈ diamondArcs slots i, e ∈ arcs N slots D := fun e he =>
    arc_of_mem_diamondArcs hi he
  unfold rowPath
  split_ifs with hd
  · refine ⟨isChain_flatMap_range (fun a _ => rightStep_ne_nil i a) (fun a ha => ?_)
      (fun a ha => ?_), ?_, ?_, ?_⟩
    · unfold rightStep
      split_ifs with h
      · cases hv : visit M pick i (a / 3) with
        | none => exact List.IsChain.singleton _
        | some j =>
          obtain ⟨hj, hji, hjs⟩ := (visit_eq_some_iff hD hpick).1 hv
          have := ((arc_detour (N := N) (slots := slots) hpick hj).1 (hji ▸ hd)).1
          rw [hji, hjs, show 3 * (a / 3) + 2 = a by omega] at this
          exact List.IsChain.cons_cons this (List.IsChain.singleton _)
      · exact List.IsChain.singleton _
    · intro x hx y hy
      simp only [rightStep, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      unfold rightStep at hx
      split_ifs at hx with h
      · cases hv : visit M pick i (a / 3) with
        | none =>
          simp only [hv, Option.map_none, Option.toList_none, List.getLast?_singleton,
            Option.mem_def, Option.some.injEq] at hx
          subst hx
          exact arc_row_succ hi ha
        | some j =>
          simp only [hv, Option.map_some, Option.toList_some, List.getLast?_cons_cons,
            List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
          subst hx
          obtain ⟨hj, hji, hjs⟩ := (visit_eq_some_iff hD hpick).1 hv
          have := ((arc_detour (N := N) (slots := slots) hpick hj).1 (hji ▸ hd)).2
          rwa [hji, hjs, show 3 * (a / 3) + 3 = a + 1 by omega] at this
      · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
        subst hx
        exact arc_row_succ hi ha
    · intro x hx
      rw [head?_flatMap_range hpos (rightStep_ne_nil i 0)] at hx
      simp only [rightStep, List.head?_cons, Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact hdiam _ (by simp [diamondArcs])
    · intro x hx
      rw [getLast?_flatMap_range hpos (rightStep_ne_nil i _)] at hx
      unfold rightStep at hx
      rw [show (rowLength slots i - 1) / 3 = slots i by omega, visit_last hD hpick] at hx
      simp only [Option.map_none, Option.toList_none, ite_self, List.getLast?_singleton,
        Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact hdiam _ (by simp [diamondArcs])
    · simpa using ⟨0, hpos, rightStep_ne_nil i 0⟩
  · have hd' : dir i = false := by simpa using hd
    refine ⟨isChain_flatMap_range_reverse (fun a _ => leftStep_ne_nil i a)
      (fun a ha => ?_) (fun a ha => ?_), ?_, ?_, ?_⟩
    · unfold leftStep
      split_ifs with h
      · cases hv : visit M pick i (a / 3 - 1) with
        | none => exact List.IsChain.singleton _
        | some j =>
          obtain ⟨hj, hji, hjs⟩ := (visit_eq_some_iff hD hpick).1 hv
          have := ((arc_detour (N := N) (slots := slots) hpick hj).2 (hji ▸ hd')).1
          rw [hji, hjs, show 3 * (a / 3 - 1) + 3 = a by omega] at this
          exact List.IsChain.cons_cons this (List.IsChain.singleton _)
      · exact List.IsChain.singleton _
    · intro x hx y hy
      simp only [leftStep, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      unfold leftStep at hx
      split_ifs at hx with h
      · cases hv : visit M pick i ((a + 1) / 3 - 1) with
        | none =>
          simp only [hv, Option.map_none, Option.toList_none, List.getLast?_singleton,
            Option.mem_def, Option.some.injEq] at hx
          subst hx
          exact arc_row_pred hi ha
        | some j =>
          simp only [hv, Option.map_some, Option.toList_some, List.getLast?_cons_cons,
            List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
          subst hx
          obtain ⟨hj, hji, hjs⟩ := (visit_eq_some_iff hD hpick).1 hv
          have := ((arc_detour (N := N) (slots := slots) hpick hj).2 (hji ▸ hd')).2
          rwa [hji, hjs, show 3 * ((a + 1) / 3 - 1) + 2 = a by omega] at this
      · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
        subst hx
        exact arc_row_pred hi ha
    · intro x hx
      rw [head?_flatMap_range_reverse hpos (leftStep_ne_nil i _)] at hx
      simp only [leftStep, List.head?_cons, Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact hdiam _ (by simp [diamondArcs])
    · intro x hx
      rw [getLast?_flatMap_range_reverse hpos (leftStep_ne_nil i 0)] at hx
      simp only [leftStep, lt_irrefl, and_false, ite_false, List.getLast?_singleton,
        Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact hdiam _ (by simp [diamondArcs])
    · simpa using ⟨0, hpos, leftStep_ne_nil i 0⟩

/-- The traversal of row `i` visits its row nodes and the nodes of the clauses picked across it.
-/
private theorem mem_rowPath {i v : ℕ} :
    v ∈ rowPath slots M dir pick i ↔ (∃ a < rowLength slots i, v = rowNode i a) ∨
      (∃ j < M, (pick j).2.1 = i ∧ v = clauseNode j) := by
  have hm := rowLength_sub_one slots i
  unfold rowPath
  split_ifs
  · simp only [List.mem_flatMap, List.mem_range, mem_rightStep]
    constructor
    · rintro ⟨a, ha, rfl | ⟨-, j, hv, rfl⟩⟩
      · exact Or.inl ⟨a, ha, rfl⟩
      · obtain ⟨hj, hji, -⟩ := (visit_eq_some_iff hD hpick).1 hv
        exact Or.inr ⟨j, hj, hji, rfl⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨j, hj, hji, rfl⟩)
      · exact ⟨a, ha, Or.inl rfl⟩
      · have hs := hD.slot_lt _ (hpick j hj).1
        rw [hji] at hs
        have hs' : (3 * (pick j).2.2.1 + 2) / 3 = (pick j).2.2.1 := by omega
        refine ⟨3 * (pick j).2.2.1 + 2, by simp only [rowLength]; omega,
          Or.inr ⟨by omega, j, ?_, rfl⟩⟩
        rw [hs']
        exact (visit_eq_some_iff hD hpick).2 ⟨hj, hji, rfl⟩
  · simp only [List.mem_flatMap, List.mem_reverse, List.mem_range, mem_leftStep]
    constructor
    · rintro ⟨a, ha, rfl | ⟨-, j, hv, rfl⟩⟩
      · exact Or.inl ⟨a, ha, rfl⟩
      · obtain ⟨hj, hji, -⟩ := (visit_eq_some_iff hD hpick).1 hv
        exact Or.inr ⟨j, hj, hji, rfl⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨j, hj, hji, rfl⟩)
      · exact ⟨a, ha, Or.inl rfl⟩
      · have hs := hD.slot_lt _ (hpick j hj).1
        rw [hji] at hs
        have hs' : (3 * (pick j).2.2.1 + 3) / 3 - 1 = (pick j).2.2.1 := by omega
        refine ⟨3 * (pick j).2.2.1 + 3, by simp only [rowLength]; omega,
          Or.inr ⟨⟨by omega, by omega⟩, j, ?_, rfl⟩⟩
        rw [hs']
        exact (visit_eq_some_iff hD hpick).2 ⟨hj, hji, rfl⟩

private theorem nodup_rowPath (i : ℕ) : (rowPath slots M dir pick i).Nodup := by
  unfold rowPath
  split_ifs
  · rw [List.nodup_flatMap]
    refine ⟨fun a _ => ?_, List.nodup_range.pairwise_of_forall_ne fun a _ b _ hab => ?_⟩
    · unfold rightStep
      split_ifs
      · cases visit M pick i (a / 3) <;> simp
      · simp
    · intro x hx hx'
      rw [mem_rightStep] at hx hx'
      rcases hx with rfl | ⟨h, j, hv, rfl⟩ <;> rcases hx' with h' | ⟨h', j', hv', h''⟩
      · simp only [rowNode_inj] at h'
        omega
      · simp at h''
      · simp at h'
      · simp only [clauseNode_inj] at h''
        subst h''
        obtain ⟨-, -, hs⟩ := (visit_eq_some_iff hD hpick).1 hv
        obtain ⟨-, -, hs'⟩ := (visit_eq_some_iff hD hpick).1 hv'
        omega
  · rw [List.nodup_flatMap]
    refine ⟨fun a _ => ?_,
      (List.nodup_reverse.2 List.nodup_range).pairwise_of_forall_ne fun a _ b _ hab => ?_⟩
    · unfold leftStep
      split_ifs
      · cases visit M pick i (a / 3 - 1) <;> simp
      · simp
    · intro x hx hx'
      rw [mem_leftStep] at hx hx'
      rcases hx with rfl | ⟨h, j, hv, rfl⟩ <;> rcases hx' with h' | ⟨h', j', hv', h''⟩
      · simp only [rowNode_inj] at h'
        omega
      · simp at h''
      · simp at h'
      · simp only [clauseNode_inj] at h''
        subst h''
        obtain ⟨-, -, hs⟩ := (visit_eq_some_iff hD hpick).1 hv
        obtain ⟨-, -, hs'⟩ := (visit_eq_some_iff hD hpick).1 hv'
        omega

/-- The Hamiltonian path read off directions of the rows satisfying every clause. -/
private theorem isDirHamPath_hamPath :
    (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) (hamPath N slots M dir pick) := by
  have hblock_ne : ∀ i, topNode i :: rowPath slots M dir pick i ≠ [] :=
    fun _ => List.cons_ne_nil _ _
  have hmem_block : ∀ {i v}, v ∈ topNode i :: rowPath slots M dir pick i ↔ v = topNode i ∨
      (∃ a < rowLength slots i, v = rowNode i a) ∨
      (∃ j < M, (pick j).2.1 = i ∧ v = clauseNode j) := by
    intro i v
    rw [List.mem_cons, mem_rowPath hD hpick]
  refine ⟨?_, fun v => ?_, ?_, ?_, ?_⟩
  · -- No repetitions.
    rw [hamPath, List.nodup_append, List.nodup_flatMap]
    refine ⟨⟨fun i _ => List.nodup_cons.2 ⟨fun h => ?_, nodup_rowPath hD hpick i⟩,
      List.nodup_range.pairwise_of_forall_ne fun i _ i' _ hii' => ?_⟩,
      List.nodup_singleton _, fun v hv w hw => ?_⟩
    · rcases (mem_rowPath hD hpick).1 h with ⟨a, -, h⟩ | ⟨j, -, -, h⟩ <;> simp at h
    · intro x hx hx'
      rw [hmem_block] at hx hx'
      rcases hx with rfl | ⟨a, -, rfl⟩ | ⟨j, -, hj, rfl⟩ <;>
        rcases hx' with h | ⟨a', -, h⟩ | ⟨j', -, hj', h⟩ <;>
        simp only [topNode_inj, rowNode_inj, clauseNode_inj, topNode_ne_rowNode,
          rowNode_ne_topNode, topNode_ne_clauseNode, clauseNode_ne_topNode,
          rowNode_ne_clauseNode, clauseNode_ne_rowNode] at h <;> grind
    · rw [List.mem_singleton] at hw
      subst hw
      obtain ⟨i, hi, hv⟩ := List.mem_flatMap.1 hv
      rw [List.mem_range] at hi
      rcases hmem_block.1 hv with rfl | ⟨a, -, rfl⟩ | ⟨j, -, -, rfl⟩
      · simp only [ne_eq, topNode_inj]
        omega
      · simp
      · simp
  · -- Every vertex is visited.
    change v ∈ hamPath N slots M dir pick ↔ v ∈ vertices N slots M
    rw [mem_vertices, hamPath, List.mem_append, List.mem_flatMap, List.mem_singleton]
    constructor
    · rintro (⟨i, hi, hv⟩ | rfl)
      · rw [List.mem_range] at hi
        rcases hmem_block.1 hv with rfl | ⟨a, ha, rfl⟩ | ⟨j, hj, -, rfl⟩
        · exact Or.inl ⟨i, hi.le, rfl⟩
        · exact Or.inr (Or.inl ⟨i, hi, a, ha, rfl⟩)
        · exact Or.inr (Or.inr ⟨j, hj, rfl⟩)
      · exact Or.inl ⟨_, le_rfl, rfl⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, a, ha, rfl⟩ | ⟨j, hj, rfl⟩)
      · rcases hi.lt_or_eq with hi | rfl
        · exact Or.inl ⟨i, List.mem_range.2 hi, hmem_block.2 (Or.inl rfl)⟩
        · exact Or.inr rfl
      · exact Or.inl ⟨i, List.mem_range.2 hi, hmem_block.2 (Or.inr (Or.inl ⟨a, ha, rfl⟩))⟩
      · exact Or.inl ⟨_, List.mem_range.2 (hD.row_lt _ (hpick j hj).1),
          hmem_block.2 (Or.inr (Or.inr ⟨j, hj, rfl, rfl⟩))⟩
  · -- It starts at the top of the first diamond.
    rw [hamPath]
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · rw [List.head?_append_of_ne_nil _ (by simpa using ⟨0, h⟩),
        head?_flatMap_range h (hblock_ne 0)]
      rfl
  · -- It ends at the bottom of the last diamond.
    rw [hamPath, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
    rfl
  · -- Consecutive vertices are joined by arcs.
    rw [hamPath, List.isChain_append]
    refine ⟨isChain_flatMap_range (fun i _ => hblock_ne i) (fun i hi => ?_) (fun i hi => ?_),
      List.IsChain.singleton _, ?_⟩
    · obtain ⟨hch, hhead, -, -⟩ := rowPath_spec hD hpick hi
      exact List.isChain_cons.2 ⟨hhead, hch⟩
    · intro x hx y hy
      obtain ⟨-, -, hlast, hne⟩ := rowPath_spec hD hpick (i := i) (by omega)
      rw [← List.singleton_append, List.getLast?_append_of_ne_nil _ hne] at hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact hlast x hx
    · intro x hx y hy
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      rcases Nat.eq_zero_or_pos N with h | h
      · simp [h] at hx
      · obtain ⟨-, -, hlast, hne⟩ := rowPath_spec hD hpick (i := N - 1) (by omega)
        rw [getLast?_flatMap_range h (hblock_ne _), ← List.singleton_append,
          List.getLast?_append_of_ne_nil _ hne] at hx
        have := hlast x hx
        rwa [Nat.sub_add_cancel h] at this

end DirectionsToPath

/-- **Hamiltonian paths of diamond graphs.** A well-formed diamond graph has a Hamiltonian path
from the top of the first diamond to the bottom of the last exactly when its rows can be given
directions so that every clause has a detour in the direction of its row. -/
theorem mem_DirHamPath_iff (hD : WellFormed N slots M D) :
    (graph N slots M D, topNode 0, topNode N) ∈ DirHamPath ↔ Satisfiable M D := by
  refine ⟨satisfiable_of_mem_DirHamPath hD, fun ⟨dir, hdir⟩ => ?_⟩
  choose! pick hpick using hdir
  exact ⟨_, isDirHamPath_hamPath (dir := dir) hD fun j hj =>
    ⟨(hpick j hj).1, (hpick j hj).2.1, (hpick j hj).2.2⟩⟩

/-- **Hamiltonian cycles of closed diamond graphs.** A well-formed closed diamond graph has a
Hamiltonian cycle exactly when its rows can be given directions so that every clause has a detour
in the direction of its row. -/
theorem mem_DirHamCycle_iff {N M : ℕ} {slots : ℕ → ℕ} {D : List Detour}
    (hD : WellFormed N slots M D) :
    cycleGraph N slots M D ∈ DirHamCycle ↔ Satisfiable M D :=
  (Graph.mem_DirHamCycle_cons_iff (G := graph N slots M D)
    (mem_vertices.2 (Or.inl ⟨0, Nat.zero_le _, rfl⟩)) notMem_arcs_topNode_zero).trans
    (mem_DirHamPath_iff hD)

/-! ### Polynomial time -/

section PolyTime

open Turing.MultiTapeTM ComputableInPolyTime

/-- Detours encoded with unary clause, row and slot indices. -/
abbrev encDetour : Detour ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary encBool))

/-- The top nodes are computable in polynomial time from unary indices. -/
@[fun_prop]
theorem computableInPolyTime_topNode :
    ComputableInPolyTime (fun i => topNode i) encUnary encNat :=
  unary_to_binary.comp
    (show ComputableInPolyTime (fun i => Nat.pair 0 i) _ _ by fun_prop)

/-- The row nodes are computable in polynomial time from unary indices. -/
@[fun_prop]
theorem computableInPolyTime_rowNode :
    ComputableInPolyTime (fun p : ℕ × ℕ => rowNode p.1 p.2) (encPair encUnary encUnary)
      encNat :=
  unary_to_binary.comp (show ComputableInPolyTime
    (fun p : ℕ × ℕ => Nat.pair 1 (Nat.pair p.1 p.2)) _ _ by fun_prop)

/-- The clause nodes are computable in polynomial time from unary indices. -/
@[fun_prop]
theorem computableInPolyTime_clauseNode :
    ComputableInPolyTime (fun j => clauseNode j) encUnary encNat :=
  unary_to_binary.comp
    (show ComputableInPolyTime (fun j => Nat.pair 2 j) _ _ by fun_prop)

/-- A diamond graph is computable in polynomial time from a layout computable in polynomial time,
with the numbers of diamonds, slots and clauses in unary. -/
theorem computableInPolyTime_graph {α : Type} {encIn : α ↪ List Bool} {N M : α → ℕ}
    {slots : α → ℕ → ℕ} {D : α → List Detour} (hN : ComputableInPolyTime N encIn encUnary)
    (hslots : ComputableInPolyTime (fun p : α × ℕ => slots p.1 p.2)
      (encPair encIn encUnary) encUnary)
    (hM : ComputableInPolyTime M encIn encUnary)
    (hD : ComputableInPolyTime D encIn (encList encDetour)) :
    ComputableInPolyTime (fun a => graph (N a) (slots a) (M a) (D a)) encIn encGraph := by
  have hvert : ComputableInPolyTime (fun a => vertices (N a) (slots a) (M a)) encIn
      (encList encNat) := by
    unfold vertices rowLength
    fun_prop
  have hdiam : ComputableInPolyTime (fun p : α × ℕ => diamondArcs (slots p.1) p.2)
      (encPair encIn encUnary) (encList (encPair encNat encNat)) := by
    unfold diamondArcs rowLength
    fun_prop
  have hdet : ComputableInPolyTime detourArcs encDetour (encList (encPair encNat encNat)) := by
    unfold detourArcs encDetour
    fun_prop
  have harcs : ComputableInPolyTime (fun a => arcs (N a) (slots a) (D a)) encIn
      (encList (encPair encNat encNat)) := by
    unfold arcs
    fun_prop
  exact hvert.prod harcs

/-- A closed diamond graph is computable in polynomial time from a layout computable in polynomial
time, with the numbers of diamonds, slots and clauses in unary. -/
theorem computableInPolyTime_cycleGraph {α : Type} {encIn : α ↪ List Bool} {N M : α → ℕ}
    {slots : α → ℕ → ℕ} {D : α → List Detour} (hN : ComputableInPolyTime N encIn encUnary)
    (hslots : ComputableInPolyTime (fun p : α × ℕ => slots p.1 p.2)
      (encPair encIn encUnary) encUnary)
    (hM : ComputableInPolyTime M encIn encUnary)
    (hD : ComputableInPolyTime D encIn (encList encDetour)) :
    ComputableInPolyTime (fun a => cycleGraph (N a) (slots a) (M a) (D a)) encIn
      encGraph := by
  have hg := computableInPolyTime_graph hN hslots hM hD
  unfold encGraph at hg ⊢
  exact hg.fst'.prod (cons' ((computableInPolyTime_topNode.comp hN).prod (const (topNode 0)))
    hg.snd')

end PolyTime

end Diamond

end Cslib.Complexity
