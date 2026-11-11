/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Hamiltonian.Diamond.Defs

/-!
# Soundness of diamond graphs: Hamiltonian paths give satisfying directions

In a well-formed diamond graph (`Cslib.Complexity.Diamond.WellFormed`), any directed Hamiltonian
path from `topNode 0` to `topNode N` traverses every separator of row `i` in a consistent direction
and enters every clause node via a detour in the direction of its row, establishing
`Cslib.Complexity.Diamond.Satisfiable`.

## Main results

* `Cslib.Complexity.Diamond.satisfiable_of_mem_DirHamPath`: a Hamiltonian path of the diamond graph
  gives directions of the rows satisfying every clause.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity.Diamond

variable {N : ℕ} {slots : ℕ → ℕ} {M : ℕ} {D : List Detour}

/-- Split an arc of the diamond graph into its kinds, simplify the label equations, and close
position constraints by `omega`. -/
local macro "diamond_arc_omega " h:ident : tactic => `(tactic|
  (rcases mem_arcs.1 $h with
      ⟨i', hi', ⟨h₁, h₂ | h₂⟩ | ⟨h₁ | h₁, h₂⟩ | ⟨a', ha', ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ |
      ⟨⟨j', i', s', b'⟩, hd, ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ | ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ <;>
    (try simp only [rowLength_sub_one] at *) <;>
    simp only [rowNode_inj, topNode_inj, clauseNode_inj, rowNode_ne_topNode,
      topNode_ne_rowNode, rowNode_ne_clauseNode, clauseNode_ne_rowNode] at h₁ h₂ <;>
    (try casesm* _ ∧ _) <;>
    subst_vars <;>
    simp only [rowNode_inj, topNode_inj, clauseNode_inj, rowNode_ne_topNode,
      topNode_ne_rowNode, rowNode_ne_clauseNode, clauseNode_ne_rowNode, true_and, and_true,
      false_or, or_false, or_true, true_or] <;>
    omega))

/-- Split an arc at a node of a slot into its kinds: the conclusion is an adjacent row node, a
clause node of a detour across the slot, or a contradiction in the positions. -/
local macro "diamond_slot_arc " h:ident : tactic => `(tactic|
  (rcases $h:ident with h | h <;>
  rcases mem_arcs.1 h with
      ⟨i', hi', ⟨h₁, h₂ | h₂⟩ | ⟨h₁ | h₁, h₂⟩ | ⟨a', ha', ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ |
      ⟨⟨j', i', s', b'⟩, hd, ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ | ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ <;>
    (try simp only [rowLength_sub_one] at *) <;>
    simp only [rowNode_inj, topNode_inj, clauseNode_inj, rowNode_ne_topNode,
      topNode_ne_rowNode, rowNode_ne_clauseNode, clauseNode_ne_rowNode] at h₁ h₂ <;>
    (try casesm* _ ∧ _) <;>
    subst_vars <;>
    first
    | (left; simp only [rowNode_inj, true_and] <;> omega)
    | (right; left; simp only [rowNode_inj, true_and] <;> omega)
    | (right; right; refine ⟨_, hd, rfl, ?_, rfl⟩; dsimp only; omega)
    | omega))

/-- The neighbours of a separator are the adjacent row nodes. -/
private theorem separator_nbrs {i s u : ℕ}
    (h : (u, rowNode i (3 * s + 1)) ∈ arcs N slots D ∨
      (rowNode i (3 * s + 1), u) ∈ arcs N slots D) :
    u = rowNode i (3 * s) ∨ u = rowNode i (3 * s + 2) := by
  rcases h with h | h
  · diamond_arc_omega h
  · diamond_arc_omega h

/-- The neighbours of the left node of slot `s` are the adjacent row nodes and the nodes of the
clauses of the detours across the slot. -/
private theorem pairLeft_nbrs {i s u : ℕ} (hs : s < slots i)
    (h : (u, rowNode i (3 * s + 2)) ∈ arcs N slots D ∨
      (rowNode i (3 * s + 2), u) ∈ arcs N slots D) :
    u = rowNode i (3 * s + 1) ∨ u = rowNode i (3 * s + 3) ∨
      ∃ d ∈ D, d.row = i ∧ d.slot = s ∧ u = clauseNode d.clause := by
  diamond_slot_arc h

/-- The neighbours of the right node of slot `s` are the adjacent row nodes and the nodes of the
clauses of the detours across the slot. -/
private theorem pairRight_nbrs {i s u : ℕ}
    (h : (u, rowNode i (3 * s + 3)) ∈ arcs N slots D ∨
      (rowNode i (3 * s + 3), u) ∈ arcs N slots D) :
    u = rowNode i (3 * s + 2) ∨ u = rowNode i (3 * s + 4) ∨
      ∃ d ∈ D, d.row = i ∧ d.slot = s ∧ u = clauseNode d.clause := by
  diamond_slot_arc h

/-- Arcs into the left end of a row come from the top of its diamond or the next row node. -/
private theorem leftEnd_nbrs {i u : ℕ} (h : (u, rowNode i 0) ∈ arcs N slots D) :
    u = topNode i ∨ u = rowNode i 1 := by
  diamond_arc_omega h

/-- Arcs into the node of clause `j` come from the slots of its detours: from the left node for a
detour from left to right, from the right node otherwise. -/
private theorem clauseNode_nbrs {j u : ℕ} (h : (u, clauseNode j) ∈ arcs N slots D) :
    ∃ d ∈ D, d.clause = j ∧
      u = rowNode d.row (if d.leftToRight then 3 * d.slot + 2 else 3 * d.slot + 3) := by
  rcases mem_arcs.1 h with
      ⟨i', hi', ⟨h₁, h₂ | h₂⟩ | ⟨h₁ | h₁, h₂⟩ | ⟨a', ha', ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ |
      ⟨d, hd, ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ | ⟨hb, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩⟩ <;>
    simp only [clauseNode_inj, clauseNode_ne_topNode, clauseNode_ne_rowNode] at h₂
  · exact ⟨d, hd, h₂.symm, by simp [h₁, hb]⟩
  · exact ⟨d, hd, h₂.symm, by simp [h₁, hb]⟩

/-! ### Successors in a list -/

/-- `v` immediately follows `u` in the list `p`. -/
private def Follows (p : List ℕ) (u v : ℕ) : Prop := ∃ i, p[i]? = some u ∧ p[i + 1]? = some v

private theorem Follows.rel {R : ℕ → ℕ → Prop} {p : List ℕ} (hp : p.IsChain R) {u v : ℕ}
    (h : Follows p u v) : R u v := by
  obtain ⟨i, hu, hv⟩ := h
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hu
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.1 hv
  exact List.isChain_iff_getElem.1 hp i hi'

private theorem Follows.right_unique {p : List ℕ} (hnd : p.Nodup) {u v v' : ℕ}
    (h : Follows p u v) (h' : Follows p u v') : v = v' := by
  obtain ⟨i, hu, hv⟩ := h
  obtain ⟨j, hu', hv'⟩ := h'
  obtain rfl : i = j :=
    (hnd.getElem?_inj (List.getElem?_eq_some_iff.1 hu).1).1 (hu.trans hu'.symm)
  exact Option.some_injective _ (hv.symm.trans hv')

private theorem Follows.left_unique {p : List ℕ} (hnd : p.Nodup) {u u' v : ℕ}
    (h : Follows p u v) (h' : Follows p u' v) : u = u' := by
  obtain ⟨i, hu, hv⟩ := h
  obtain ⟨j, hu', hv'⟩ := h'
  obtain rfl : i = j := by
    have := (hnd.getElem?_inj (List.getElem?_eq_some_iff.1 hv).1).1 (hv.trans hv'.symm)
    omega
  exact Option.some_injective _ (hu.symm.trans hu')

private theorem Follows.asymm {p : List ℕ} (hnd : p.Nodup) {u v : ℕ} (h : Follows p u v) :
    ¬Follows p v u := by
  rintro ⟨j, hv', hu'⟩
  obtain ⟨i, hu, hv⟩ := h
  have h₁ := (hnd.getElem?_inj (List.getElem?_eq_some_iff.1 hu).1).1 (hu.trans hu'.symm)
  have h₂ := (hnd.getElem?_inj (List.getElem?_eq_some_iff.1 hv).1).1 (hv.trans hv'.symm)
  omega

private theorem exists_follows_of_ne_getLast {p : List ℕ} {v : ℕ} (hv : v ∈ p)
    (hlast : p.getLast? ≠ some v) : ∃ w, Follows p v w := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hv
  have hilt := (List.getElem?_eq_some_iff.1 hi).1
  have : i + 1 < p.length := by
    by_contra h
    apply hlast
    rw [List.getLast?_eq_getElem?, show p.length - 1 = i by omega, hi]
  exact ⟨p[i + 1], i, hi, List.getElem?_eq_getElem this⟩

private theorem exists_follows_of_ne_head {p : List ℕ} {v : ℕ} (hv : v ∈ p)
    (hhead : p.head? ≠ some v) : ∃ u, Follows p u v := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hv
  cases i with
  | zero => exact (hhead (by rw [List.head?_eq_getElem?, hi])).elim
  | succ i =>
    have := (List.getElem?_eq_some_iff.1 hi).1
    exact ⟨p[i], i, List.getElem?_eq_getElem (by omega), hi⟩

/-! ### Hamiltonian paths give directions satisfying every clause -/

section PathToDirections

variable {p : List ℕ}

private theorem rowNode_mem_vertices {i a : ℕ} (hi : i < N) (ha : a < rowLength slots i) :
    rowNode i a ∈ vertices N slots M :=
  mem_vertices.2 (Or.inr (Or.inl ⟨i, hi, a, ha, rfl⟩))

private theorem clauseNode_mem_vertices {j : ℕ} (hj : j < M) :
    clauseNode j ∈ vertices N slots M :=
  mem_vertices.2 (Or.inr (Or.inr ⟨j, hj, rfl⟩))

/-- In a Hamiltonian path, every node other than the start has a predecessor. -/
private theorem exists_pred
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {v : ℕ}
    (hv : v ∈ vertices N slots M) (hne : v ≠ topNode 0) : ∃ u, Follows p u v :=
  exists_follows_of_ne_head ((hp.2.1 v).2 hv) (by
    rw [hp.2.2.1]
    exact fun h => hne (Option.some_injective _ h).symm)

/-- In a Hamiltonian path, every node other than the end has a successor. -/
private theorem exists_succ
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {v : ℕ}
    (hv : v ∈ vertices N slots M) (hne : v ≠ topNode N) : ∃ w, Follows p v w :=
  exists_follows_of_ne_getLast ((hp.2.1 v).2 hv) (by
    rw [hp.2.2.2.1]
    exact fun h => hne (Option.some_injective _ h).symm)

/-- A separator is traversed either rightwards or leftwards. -/
private theorem separator_dir
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {i s : ℕ}
    (hi : i < N) (hs : s ≤ slots i) :
    (Follows p (rowNode i (3 * s)) (rowNode i (3 * s + 1)) ∧
        Follows p (rowNode i (3 * s + 1)) (rowNode i (3 * s + 2))) ∨
      (Follows p (rowNode i (3 * s + 2)) (rowNode i (3 * s + 1)) ∧
        Follows p (rowNode i (3 * s + 1)) (rowNode i (3 * s))) := by
  have hmem := rowNode_mem_vertices (slots := slots) (M := M) (a := 3 * s + 1) hi
    (by simp only [rowLength]; omega)
  obtain ⟨u, hu⟩ := exists_pred hp hmem (rowNode_ne_topNode _ _ _)
  obtain ⟨w, hw⟩ := exists_succ hp hmem (rowNode_ne_topNode _ _ _)
  rcases separator_nbrs (Or.inl (hu.rel hp.2.2.2.2)) with rfl | rfl <;>
    rcases separator_nbrs (Or.inr (hw.rel hp.2.2.2.2)) with rfl | rfl
  · exact absurd hw (hu.asymm hp.1)
  · exact Or.inl ⟨hu, hw⟩
  · exact Or.inr ⟨hu, hw⟩
  · exact absurd hw (hu.asymm hp.1)

/-- Separator `s + 1` written with the positions of slot `s`. -/
private theorem separator_dir_succ
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {i s : ℕ}
    (hi : i < N) (hs : s < slots i) :
    (Follows p (rowNode i (3 * s + 3)) (rowNode i (3 * s + 4)) ∧
        Follows p (rowNode i (3 * s + 4)) (rowNode i (3 * s + 5))) ∨
      (Follows p (rowNode i (3 * s + 5)) (rowNode i (3 * s + 4)) ∧
        Follows p (rowNode i (3 * s + 4)) (rowNode i (3 * s + 3))) := by
  have h := separator_dir hp hi (s := s + 1) (by omega)
  rwa [show 3 * (s + 1) = 3 * s + 3 by ring, show 3 * s + 3 + 1 = 3 * s + 4 by ring,
    show 3 * s + 3 + 2 = 3 * s + 5 by ring] at h

/-- The clause nodes adjacent to the two nodes of a slot are the same. -/
private theorem clauseNode_eq_of_slot (hD : WellFormed N slots M D) {i s : ℕ} {d d' : Detour}
    (hd : d ∈ D) (hd' : d' ∈ D) (hi : d.row = i) (hs : d.slot = s) (hi' : d'.row = i)
    (hs' : d'.slot = s) : clauseNode d.clause = clauseNode d'.clause := by
  rw [hD.clause_eq d hd d' hd' (hi.trans hi'.symm) (hs.trans hs'.symm)]

/-- If the separator before slot `s` is traversed rightwards, so is the separator after it. -/
private theorem pair_rightwards (hD : WellFormed N slots M D)
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {i s : ℕ}
    (hi : i < N) (hs : s < slots i)
    (h : Follows p (rowNode i (3 * s + 1)) (rowNode i (3 * s + 2))) :
    Follows p (rowNode i (3 * s + 4)) (rowNode i (3 * s + 5)) := by
  have hnd := hp.1
  have hch := hp.2.2.2.2
  have hq := rowNode_mem_vertices (slots := slots) (M := M) (a := 3 * s + 3) hi
    (by simp only [rowLength]; omega)
  have hpp := rowNode_mem_vertices (slots := slots) (M := M) (a := 3 * s + 2) hi
    (by simp only [rowLength]; omega)
  -- Leaving the right pair node towards the right separator makes it rightward.
  have hright : Follows p (rowNode i (3 * s + 3)) (rowNode i (3 * s + 4)) →
      Follows p (rowNode i (3 * s + 4)) (rowNode i (3 * s + 5)) := fun hq' => by
    rcases separator_dir_succ hp hi hs with ⟨-, h'⟩ | ⟨-, h'⟩
    · exact h'
    · exact absurd h' (hq'.asymm hnd)
  -- The successor of the right pair node lies to its right.
  have hsucc_q : ∀ w, Follows p (rowNode i (3 * s + 3)) w →
      w ≠ rowNode i (3 * s + 2) →
      (∀ d ∈ D, d.row = i → d.slot = s → w ≠ clauseNode d.clause) →
      Follows p (rowNode i (3 * s + 4)) (rowNode i (3 * s + 5)) := fun w hw h₁ h₂ => by
    rcases pairRight_nbrs (Or.inr (hw.rel hch)) with rfl | rfl | ⟨d, hd, hdi, hds, rfl⟩
    · exact (h₁ rfl).elim
    · exact hright hw
    · exact (h₂ d hd hdi hds rfl).elim
  obtain ⟨w, hw⟩ := exists_succ hp hpp (rowNode_ne_topNode _ _ _)
  rcases pairLeft_nbrs hs (Or.inr (hw.rel hch)) with rfl | rfl | ⟨d, hd, hdi, hds, rfl⟩
  · exact absurd hw (h.asymm hnd)
  · -- `p → q`: the successor of `q` is neither `p` nor a clause node of the slot.
    obtain ⟨w', hw'⟩ := exists_succ hp hq (rowNode_ne_topNode _ _ _)
    refine hsucc_q w' hw' (fun he => ?_) (fun d hd hdi hds he => ?_)
    · subst he
      exact hw'.asymm hnd hw
    · subst he
      rcases separator_dir_succ hp hi hs with ⟨h₁, -⟩ | ⟨-, h₁⟩
      · exact clauseNode_ne_rowNode _ _ _ (hw'.right_unique hnd h₁)
      · simpa using hw.left_unique hnd h₁
  · -- `p → c`: the successor of `q` is neither `p` nor a clause node of the slot.
    obtain ⟨w', hw'⟩ := exists_succ hp hq (rowNode_ne_topNode _ _ _)
    have hw'p : w' ≠ rowNode i (3 * s + 2) := fun he => by
      subst he
      simpa using hw'.left_unique hnd h
    have hw'c : ∀ d' ∈ D, d'.row = i → d'.slot = s → w' ≠ clauseNode d'.clause :=
      fun d' hd' hdi' hds' he => by
      rw [he, ← clauseNode_eq_of_slot hD hd hd' hdi hds hdi' hds'] at hw'
      simpa using hw'.left_unique hnd hw
    exact hsucc_q w' hw' hw'p hw'c

/-- The separator before slot `s` cannot be traversed leftwards while the separator after it is
traversed rightwards. -/
private theorem not_pair_left_right (hD : WellFormed N slots M D)
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {i s : ℕ}
    (hi : i < N) (hs : s < slots i) :
    ¬(Follows p (rowNode i (3 * s + 2)) (rowNode i (3 * s + 1)) ∧
      Follows p (rowNode i (3 * s + 3)) (rowNode i (3 * s + 4))) := by
  rintro ⟨hl, hr⟩
  have hnd := hp.1
  have hch := hp.2.2.2.2
  obtain ⟨u, hu⟩ := exists_pred hp
    (rowNode_mem_vertices (slots := slots) (M := M) (a := 3 * s + 2) hi
      (by simp only [rowLength]; omega)) (rowNode_ne_topNode _ _ _)
  rcases pairLeft_nbrs hs (Or.inl (hu.rel hch)) with rfl | rfl | ⟨d, hd, hdi, hds, rfl⟩
  · exact hu.asymm hnd hl
  · simpa using hu.right_unique hnd hr
  · obtain ⟨u', hu'⟩ := exists_pred hp
      (rowNode_mem_vertices (slots := slots) (M := M) (a := 3 * s + 3) hi
        (by simp only [rowLength]; omega)) (rowNode_ne_topNode _ _ _)
    rcases pairRight_nbrs (Or.inl (hu'.rel hch)) with rfl | rfl | ⟨d', hd', hdi', hds', rfl⟩
    · simpa using hu'.right_unique hnd hl
    · exact hu'.asymm hnd hr
    · rw [← clauseNode_eq_of_slot hD hd hd' hdi hds hdi' hds'] at hu'
      simpa using hu'.right_unique hnd hu

/-- All separators of a row are traversed in the same direction. -/
private theorem rightwards_iff (hD : WellFormed N slots M D)
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {i : ℕ} (hi : i < N) :
    ∀ s ≤ slots i, (Follows p (rowNode i (3 * s + 1)) (rowNode i (3 * s + 2)) ↔
      Follows p (rowNode i 1) (rowNode i 2))
  | 0, _ => Iff.rfl
  | s + 1, hs => by
    have ih := rightwards_iff hD hp hi s (by omega)
    rw [show 3 * (s + 1) + 1 = 3 * s + 4 by ring, show 3 * (s + 1) + 2 = 3 * s + 5 by ring,
      ← ih]
    refine ⟨fun h => ?_, pair_rightwards hD hp hi (by omega)⟩
    by_contra hs'
    rcases separator_dir hp hi (s := s) (by omega) with ⟨-, h'⟩ | ⟨h', -⟩
    · exact hs' h'
    · rcases separator_dir_succ hp hi (s := s) (by omega) with ⟨h'', -⟩ | ⟨-, h''⟩
      · exact not_pair_left_right hD hp hi (by omega) ⟨h', h''⟩
      · simpa using h''.right_unique hp.1 h

/-- A row is traversed rightwards exactly when its diamond is entered at the left end. -/
private theorem rightwards_iff_top
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {i : ℕ} (hi : i < N) :
    Follows p (rowNode i 1) (rowNode i 2) ↔ Follows p (topNode i) (rowNode i 0) := by
  have hnd := hp.1
  have h0 := separator_dir hp hi (s := 0) (Nat.zero_le _)
  simp only [mul_zero, zero_add] at h0
  constructor
  · intro h
    rcases h0 with ⟨h₁, -⟩ | ⟨-, h₁⟩
    · obtain ⟨u, hu⟩ := exists_pred hp
        (rowNode_mem_vertices (slots := slots) (M := M) (a := 0) hi
          (by simp only [rowLength]; omega)) (rowNode_ne_topNode _ _ _)
      rcases leftEnd_nbrs (hu.rel hp.2.2.2.2) with rfl | rfl
      · exact hu
      · exact (hu.asymm hnd h₁).elim
    · simpa using h.right_unique hnd h₁
  · intro h
    rcases h0 with ⟨-, h₁⟩ | ⟨-, h₁⟩
    · exact h₁
    · simpa using h.left_unique hnd h₁

/-- The node of clause `j` is entered by a detour in the direction of its row. -/
private theorem exists_detour (hD : WellFormed N slots M D)
    (hp : (graph N slots M D).IsDirHamPath (topNode 0) (topNode N) p) {j : ℕ} (hj : j < M) :
    ∃ d ∈ D, d.clause = j ∧
      (Follows p (topNode d.row) (rowNode d.row 0) ↔ d.leftToRight = true) := by
  have hnd := hp.1
  obtain ⟨u, hu⟩ := exists_pred hp (clauseNode_mem_vertices (N := N) (slots := slots) hj)
    (clauseNode_ne_topNode _ _)
  obtain ⟨d, hd, hdj, rfl⟩ := clauseNode_nbrs (hu.rel hp.2.2.2.2)
  have hi := hD.row_lt d hd
  have hs := hD.slot_lt d hd
  refine ⟨d, hd, hdj, ?_⟩
  rw [← rightwards_iff_top hp hi]
  cases hb : d.leftToRight
  · simp only [hb, Bool.false_eq_true, ite_false] at hu
    rw [← rightwards_iff hD hp hi (d.slot + 1) (by omega),
      show 3 * (d.slot + 1) + 1 = 3 * d.slot + 4 by ring,
      show 3 * (d.slot + 1) + 2 = 3 * d.slot + 5 by ring]
    simp only [Bool.false_eq_true, iff_false]
    intro h
    rcases separator_dir_succ hp hi hs with ⟨h₁, -⟩ | ⟨-, h₁⟩
    · simpa using hu.right_unique hnd h₁
    · simpa using h₁.right_unique hnd h
  · simp only [hb, ite_true] at hu
    simp only [iff_true]
    rw [← rightwards_iff hD hp hi d.slot hs.le]
    rcases separator_dir hp hi (s := d.slot) hs.le with ⟨-, h₁⟩ | ⟨h₁, -⟩
    · exact h₁
    · simpa using hu.right_unique hnd h₁

/-- A Hamiltonian path of the diamond graph gives directions of the rows satisfying every
clause. -/
theorem satisfiable_of_mem_DirHamPath (hD : WellFormed N slots M D)
    (h : (graph N slots M D, topNode 0, topNode N) ∈ DirHamPath) : Satisfiable M D := by
  classical
  obtain ⟨p, hp⟩ := h
  refine ⟨fun i => decide (Follows p (topNode i) (rowNode i 0)), fun j hj => ?_⟩
  obtain ⟨d, hd, hdj, hiff⟩ := exists_detour hD hp hj
  refine ⟨d, hd, hdj, ?_⟩
  cases hb : d.leftToRight <;> simp_all

end PathToDirections

end Cslib.Complexity.Diamond
