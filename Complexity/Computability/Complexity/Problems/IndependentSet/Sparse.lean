/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.IndependentSet
public import Complexity.Logics.Propositional.CNF.ModelCount
import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Foundations.Data.List.Counting
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# A reduction of linear size to independent sets

Karp's reduction `Cslib.Complexity.SAT.toIndependentSet` joins all complementary occurrences of a
variable, so its graph can have quadratically many edges in the number of clauses even for formulas
with three literals per clause. `SAT.toSparseIndependentSet` is the reduction with variable edges
[Garey and Johnson, Theorem 3.3][GareyJohnson1979], stated for independent sets. It has

* two literal vertices for each of the `n` distinct variables of the formula, joined by an edge;
* a vertex for each position of each clause, the positions of a clause forming a clique;
* an edge from each position to the literal vertex of the complement of its literal,

and asks for an independent set of `n + m` vertices, for `m` clauses. An independent set has at
most one vertex in each variable edge and in each clause clique, so one of `n + m` vertices has
exactly one in each: the literal vertices chosen give an assignment, and the position chosen in a
clause is not joined to its literal, which therefore holds. Conversely, a satisfying assignment
chooses the true literal of each variable and a true position of each clause.

On formulas whose clauses have at most `k` literals the graph has at most `(k ^ 2 + 5 k) m`
vertices and edges in total (`Cslib.Complexity.SAT.length_toSparseIndependentSet_le`), which is
linear in `m` for fixed `k`.

## Main definitions

* `Cslib.Complexity.SAT.toSparseIndependentSet`, with the vertex labels
  `Cslib.Complexity.SAT.SparseIndependentSet.literalVertex` and
  `Cslib.Complexity.SAT.SparseIndependentSet.occurrenceVertex`.

## Main results

* `Cslib.Complexity.SAT.toSparseIndependentSet_mem_iff`:
  `toSparseIndependentSet φ ∈ IndependentSet ↔ φ ∈ SAT`.
* `Cslib.Complexity.SAT.computableInPolyTime_toSparseIndependentSet`: the reduction is
  polynomial-time.
* `Cslib.Complexity.SAT.length_toSparseIndependentSet_le`: the graph has linearly many vertices
  and edges for clauses of bounded width.

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

namespace SAT

namespace SparseIndependentSet

/-! ### The graph -/

/-- The vertex of the literal `l` of `φ`, its variable numbered by its position in
`φ.distinctVars`. -/
def literalVertex (φ : CNF ℕ) (l : Literal ℕ) : ℕ :=
  Nat.pair 0 (Nat.pair (φ.distinctVars.idxOf l.1) l.2.toNat)

/-- The vertex of position `j` of clause `i`. -/
def occurrenceVertex (i j : ℕ) : ℕ := Nat.pair 1 (Nat.pair i j)

/-- The vertices: the two literals of every variable of `φ`, and every position of every clause. -/
def vertices (φ : CNF ℕ) : List ℕ :=
  φ.distinctVars.flatMap
      (fun x => [literalVertex φ (x, true), literalVertex φ (x, false)]) ++
    φ.zipIdx.flatMap fun c => (List.range c.1.length).map (occurrenceVertex c.2)

/-- The edges between the two literals of each variable. -/
def literalEdges (φ : CNF ℕ) : List (ℕ × ℕ) :=
  φ.distinctVars.map fun x => (literalVertex φ (x, true), literalVertex φ (x, false))

/-- The edges between any two positions of a clause. -/
def cliqueEdges (φ : CNF ℕ) : List (ℕ × ℕ) :=
  φ.zipIdx.flatMap fun c => (List.range c.1.length).flatMap fun j =>
    (List.range c.1.length).map fun j' => (occurrenceVertex c.2 j, occurrenceVertex c.2 j')

/-- The edges from each position of a clause to the complement of its literal. -/
def conflictEdges (φ : CNF ℕ) : List (ℕ × ℕ) :=
  φ.zipIdx.flatMap fun c =>
    c.1.zipIdx.map fun l => (occurrenceVertex c.2 l.2, literalVertex φ (l.1.1, !l.1.2))

/-- The edges of the graph. -/
def edges (φ : CNF ℕ) : List (ℕ × ℕ) := literalEdges φ ++ cliqueEdges φ ++ conflictEdges φ

end SparseIndependentSet

open SparseIndependentSet in
/-- The reduction from `SAT` to `IndependentSet` with variable edges [Garey and Johnson,
Theorem 3.3][GareyJohnson1979]: the graph of `φ` with the target `n + m`, for `n` distinct
variables and `m` clauses. -/
def toSparseIndependentSet (φ : CNF ℕ) : Graph × ℕ :=
  ((vertices φ, edges φ), φ.distinctVars.length + φ.length)

namespace SparseIndependentSet

/-! ### Vertices and edges -/

variable {φ : CNF ℕ}

private theorem mem_zipIdx_iff {α : Type*} {l : List α} {a : α} {i : ℕ} :
    (a, i) ∈ l.zipIdx ↔ ∃ h : i < l.length, l[i] = a := by
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]

private theorem mem_vars {i j : ℕ} (hi : i < φ.length) (hj : j < φ[i].length) :
    φ[i][j].1 ∈ φ.vars :=
  List.mem_map.2 ⟨φ[i][j], List.mem_flatten.2 ⟨φ[i], List.getElem_mem hi, List.getElem_mem hj⟩,
    rfl⟩

theorem literalVertex_inj {x x' : ℕ} (hx : x ∈ φ.vars) {b b' : Bool} :
    literalVertex φ (x, b) = literalVertex φ (x', b') ↔ x = x' ∧ b = b' := by
  simp only [literalVertex, Nat.pair_eq_pair, true_and]
  rw [List.idxOf_inj (CNF.mem_distinctVars.2 hx)]
  cases b <;> cases b' <;> simp

theorem literalVertex_ne_occurrenceVertex (l : Literal ℕ) (i j : ℕ) :
    literalVertex φ l ≠ occurrenceVertex i j := by
  simp [literalVertex, occurrenceVertex, Nat.pair_eq_pair]

theorem occurrenceVertex_inj {i j i' j' : ℕ} :
    occurrenceVertex i j = occurrenceVertex i' j' ↔ i = i' ∧ j = j' := by
  simp [occurrenceVertex, Nat.pair_eq_pair]

theorem mem_vertices {v : ℕ} : v ∈ vertices φ ↔ (∃ x ∈ φ.vars, ∃ b, v = literalVertex φ (x, b)) ∨
    ∃ (i : ℕ) (hi : i < φ.length), ∃ j < φ[i].length, v = occurrenceVertex i j := by
  simp only [vertices, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_range, CNF.mem_distinctVars, Prod.exists]
  refine or_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rintro ⟨x, hx, rfl | rfl⟩
    · exact ⟨x, hx, true, rfl⟩
    · exact ⟨x, hx, false, rfl⟩
  · rintro ⟨x, hx, b, rfl⟩
    cases b
    · exact ⟨x, hx, Or.inr rfl⟩
    · exact ⟨x, hx, Or.inl rfl⟩
  · rintro ⟨c, i, hc, j, hj, rfl⟩
    obtain ⟨hi, rfl⟩ := mem_zipIdx_iff.1 hc
    exact ⟨i, hi, j, hj, rfl⟩
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨φ[i], i, mem_zipIdx_iff.2 ⟨hi, rfl⟩, j, hj, rfl⟩

theorem mem_literalEdges {e : ℕ × ℕ} : e ∈ literalEdges φ ↔
    ∃ x ∈ φ.vars, e = (literalVertex φ (x, true), literalVertex φ (x, false)) := by
  simp only [literalEdges, List.mem_map, CNF.mem_distinctVars]
  exact ⟨fun ⟨x, hx, he⟩ => ⟨x, hx, he.symm⟩, fun ⟨x, hx, he⟩ => ⟨x, hx, he.symm⟩⟩

theorem mem_cliqueEdges {e : ℕ × ℕ} : e ∈ cliqueEdges φ ↔ ∃ (i : ℕ) (hi : i < φ.length),
    ∃ j < φ[i].length, ∃ j' < φ[i].length, e = (occurrenceVertex i j, occurrenceVertex i j') := by
  simp only [cliqueEdges, List.mem_flatMap, List.mem_map, List.mem_range, Prod.exists]
  constructor
  · rintro ⟨c, i, hc, j, hj, j', hj', rfl⟩
    obtain ⟨hi, rfl⟩ := mem_zipIdx_iff.1 hc
    exact ⟨i, hi, j, hj, j', hj', rfl⟩
  · rintro ⟨i, hi, j, hj, j', hj', rfl⟩
    exact ⟨φ[i], i, mem_zipIdx_iff.2 ⟨hi, rfl⟩, j, hj, j', hj', rfl⟩

theorem mem_conflictEdges {e : ℕ × ℕ} : e ∈ conflictEdges φ ↔ ∃ (i : ℕ) (hi : i < φ.length),
    ∃ (j : ℕ) (hj : j < φ[i].length),
      e = (occurrenceVertex i j, literalVertex φ (φ[i][j].1, !φ[i][j].2)) := by
  simp only [conflictEdges, List.mem_flatMap, List.mem_map, Prod.exists]
  constructor
  · rintro ⟨c, i, hc, x, b, j, hl, rfl⟩
    obtain ⟨hi, rfl⟩ := mem_zipIdx_iff.1 hc
    obtain ⟨hj, hcj⟩ := mem_zipIdx_iff.1 hl
    exact ⟨i, hi, j, hj, by rw [hcj]⟩
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨φ[i], i, mem_zipIdx_iff.2 ⟨hi, rfl⟩, φ[i][j].1, φ[i][j].2, j,
      mem_zipIdx_iff.2 ⟨hj, rfl⟩, rfl⟩

private theorem adj_of_mem {u v : ℕ} (huv : u ≠ v) (h : (u, v) ∈ edges φ) :
    (toSparseIndependentSet φ).1.toSimpleGraph.Adj u v := by
  simp only [toSparseIndependentSet, Graph.toSimpleGraph_adj]
  exact ⟨huv, Or.inl h⟩

private theorem mem_edges_of_adj {u v : ℕ}
    (h : (toSparseIndependentSet φ).1.toSimpleGraph.Adj u v) :
    (u, v) ∈ edges φ ∨ (v, u) ∈ edges φ := by
  simp only [toSparseIndependentSet, Graph.toSimpleGraph_adj] at h
  exact h.2

/-! ### Correctness -/

/-- The block of a vertex: its variable for a literal vertex, and its clause for a position. -/
private def block (v : ℕ) : ℕ ⊕ ℕ :=
  if v.unpair.1 = 0 then .inl v.unpair.2.unpair.1 else .inr v.unpair.2.unpair.1

private theorem block_literalVertex (l : Literal ℕ) :
    block (literalVertex φ l) = .inl (φ.distinctVars.idxOf l.1) := by
  simp [block, literalVertex]

private theorem block_occurrenceVertex (i j : ℕ) : block (occurrenceVertex i j) = .inr i := by
  simp [block, occurrenceVertex]

/-- An independent set of `n + m` vertices gives a satisfying assignment. -/
private theorem satisfiable_of_mem (h : toSparseIndependentSet φ ∈ IndependentSet) :
    φ.Satisfiable := by
  classical
  obtain ⟨S, hSV, hS⟩ := mem_IndependentSet_iff.1 h
  set n := φ.distinctVars.length
  have hSV' : ∀ v ∈ S, v ∈ vertices φ := hSV
  have hind : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (u, v) ∉ edges φ := fun u hu v hv huv he =>
    hS.isIndepSet hu hv huv (adj_of_mem huv he)
  -- the blocks: variables, then clauses
  set B : Finset (ℕ ⊕ ℕ) := (Finset.range n).disjSum (Finset.range φ.length)
  have hblock : ∀ v ∈ S, block v ∈ B := fun v hv => by
    rcases mem_vertices.1 (hSV' v hv) with ⟨x, hx, b, rfl⟩ | ⟨i, hi, j, -, rfl⟩
    · rw [block_literalVertex]
      exact Finset.inl_mem_disjSum.2 (Finset.mem_range.2
        (List.idxOf_lt_length_iff.2 (CNF.mem_distinctVars.2 hx)))
    · rw [block_occurrenceVertex]
      exact Finset.inr_mem_disjSum.2 (Finset.mem_range.2 hi)
  -- each block holds at most one vertex of `S`
  have hinj : Set.InjOn block S := by
    intro u hu v hv huv
    by_contra hne
    rcases mem_vertices.1 (hSV' u hu) with ⟨x, hx, b, rfl⟩ | ⟨i, hi, j, hj, rfl⟩ <;>
      rcases mem_vertices.1 (hSV' v hv) with ⟨x', hx', b', rfl⟩ | ⟨i', hi', j', hj', rfl⟩ <;>
      simp only [block_literalVertex, block_occurrenceVertex, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq] at huv
    · rw [List.idxOf_inj (CNF.mem_distinctVars.2 hx)] at huv
      subst huv
      have hbb : b ≠ b' := fun h => hne (by rw [h])
      have he : (literalVertex φ (x, true), literalVertex φ (x, false)) ∈ edges φ :=
        List.mem_append_left _ (List.mem_append_left _ (mem_literalEdges.2 ⟨x, hx, rfl⟩))
      cases b <;> cases b'
      · exact hbb rfl
      · exact hind _ hv _ hu (Ne.symm hne) he
      · exact hind _ hu _ hv hne he
      · exact hbb rfl
    · subst huv
      have he : (occurrenceVertex i j, occurrenceVertex i j') ∈ edges φ :=
        List.mem_append_left _ (List.mem_append_right _
          (mem_cliqueEdges.2 ⟨i, hi, j, hj, j', hj', rfl⟩))
      exact hind _ hu _ hv hne he
  -- so every block holds exactly one
  have himage : S.image block = B := by
    refine Finset.eq_of_subset_of_card_le (fun b hb => ?_) ?_
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hb
      exact hblock v hv
    · rw [Finset.card_image_of_injOn hinj, hS.card_eq, Finset.card_disjSum, Finset.card_range,
        Finset.card_range]
  have hhit : ∀ b ∈ B, ∃ v ∈ S, block v = b := fun b hb => by
    rw [← himage] at hb
    exact Finset.mem_image.1 hb
  -- every variable has one of its literal vertices in `S`
  have hvar : ∀ x ∈ φ.vars, ∃ b, literalVertex φ (x, b) ∈ S := fun x hx => by
    have hxd := CNF.mem_distinctVars.2 hx
    obtain ⟨v, hv, hvb⟩ := hhit (.inl (φ.distinctVars.idxOf x))
      (Finset.inl_mem_disjSum.2 (Finset.mem_range.2 (List.idxOf_lt_length_iff.2 hxd)))
    rcases mem_vertices.1 (hSV' v hv) with ⟨x', hx', b, rfl⟩ | ⟨i, hi, j, -, rfl⟩
    · rw [block_literalVertex, Sum.inl.injEq,
        List.idxOf_inj (CNF.mem_distinctVars.2 hx')] at hvb
      exact ⟨b, hvb ▸ hv⟩
    · simp [block_occurrenceVertex] at hvb
  -- the two literal vertices of a variable are not both in `S`
  have hboth : ∀ x ∈ φ.vars, literalVertex φ (x, true) ∈ S → literalVertex φ (x, false) ∉ S :=
    fun x hx h₁ h₂ => hind _ h₁ _ h₂ (by simp [literalVertex_inj hx])
      (List.mem_append_left _ (List.mem_append_left _ (mem_literalEdges.2 ⟨x, hx, rfl⟩)))
  refine ⟨fun x => decide (literalVertex φ (x, true) ∈ S),
    (CNF.eval_eq_true_iff _ _).2 fun cl hcl => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcl
  obtain ⟨v, hv, hvb⟩ := hhit (.inr i) (Finset.inr_mem_disjSum.2 (Finset.mem_range.2 hi))
  rcases mem_vertices.1 (hSV' v hv) with ⟨x', -, b, rfl⟩ | ⟨i', hi', j, hj, rfl⟩
  · simp [block_literalVertex] at hvb
  rw [block_occurrenceVertex, Sum.inr.injEq] at hvb
  subst hvb
  rcases hlit : φ[i'][j] with ⟨x, b⟩
  have hx : x ∈ φ.vars := by simpa [hlit] using mem_vars hi' hj
  -- the complement of the chosen literal is not in `S`
  have hcompl : literalVertex φ (x, !b) ∉ S := fun hc => by
    refine hind _ hv _ hc (literalVertex_ne_occurrenceVertex _ _ _).symm ?_
    have := mem_conflictEdges.2 ⟨i', hi', j, hj, rfl⟩
    rw [hlit] at this
    exact List.mem_append_right _ this
  rw [Clause.eval_eq_true_iff]
  refine ⟨(x, b), hlit ▸ List.getElem_mem hj, ?_⟩
  obtain ⟨b', hb'⟩ := hvar x hx
  cases b <;> cases b' <;> simp only [Bool.not_true, Bool.not_false] at hcompl
  · exact decide_eq_false fun h => hboth x hx h hb'
  · exact (hcompl hb').elim
  · exact (hcompl hb').elim
  · exact decide_eq_true hb'

/-- A satisfying assignment gives an independent set of `n + m` vertices. -/
private theorem mem_of_satisfiable (h : φ.Satisfiable) :
    toSparseIndependentSet φ ∈ IndependentSet := by
  classical
  obtain ⟨σ, hσ⟩ := h
  have hcl : ∀ i : Fin φ.length, ∃ j : Fin φ[i].length, σ φ[i][j].1 = φ[i][j].2 := by
    intro i
    obtain ⟨l, hl, hσl⟩ := (Clause.eval_eq_true_iff _ _).1
      ((CNF.eval_eq_true_iff _ _).1 hσ φ[i] (List.getElem_mem i.2))
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    exact ⟨⟨j, hj⟩, hσl⟩
  choose J hJ using hcl
  set L : Finset ℕ := (φ.distinctVars.map fun x => literalVertex φ (x, σ x)).toFinset
  set O : Finset ℕ := Finset.univ.image fun i : Fin φ.length => occurrenceVertex i (J i)
  have hL : ∀ {v}, v ∈ L ↔ ∃ x ∈ φ.vars, v = literalVertex φ (x, σ x) := by
    intro v
    simp only [L, List.mem_toFinset, List.mem_map, CNF.mem_distinctVars]
    exact ⟨fun ⟨x, hx, he⟩ => ⟨x, hx, he.symm⟩, fun ⟨x, hx, he⟩ => ⟨x, hx, he.symm⟩⟩
  have hO : ∀ {v}, v ∈ O ↔ ∃ i : Fin φ.length, v = occurrenceVertex i (J i) := by
    intro v
    simp only [O, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, he⟩ => ⟨i, he.symm⟩, fun ⟨i, he⟩ => ⟨i, he.symm⟩⟩
  rw [mem_IndependentSet_iff]
  refine ⟨L ∪ O, fun v hv => ?_, ⟨fun u hu v hv huv hadj => ?_, ?_⟩⟩
  · change v ∈ vertices φ
    rcases Finset.mem_union.1 hv with hv | hv
    · obtain ⟨x, hx, rfl⟩ := hL.1 hv
      exact mem_vertices.2 (Or.inl ⟨x, hx, σ x, rfl⟩)
    · obtain ⟨i, rfl⟩ := hO.1 hv
      exact mem_vertices.2 (Or.inr ⟨i, i.2, J i, (J i).2, rfl⟩)
  · -- no edge joins two vertices of the set
    have key : ∀ u ∈ L ∪ O, ∀ v ∈ L ∪ O, u ≠ v → (u, v) ∉ edges φ := by
      intro u hu v hv huv he
      simp only [edges, List.mem_append] at he
      rcases he with (he | he) | he
      · obtain ⟨x, hx, he⟩ := mem_literalEdges.1 he
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rcases Finset.mem_union.1 hu with hu | hu
        · rcases Finset.mem_union.1 hv with hv | hv
          · obtain ⟨y, hy, hyu⟩ := hL.1 hu
            obtain ⟨z, hz, hzv⟩ := hL.1 hv
            rw [literalVertex_inj hx] at hyu hzv
            obtain ⟨rfl, h₁⟩ := hyu
            obtain ⟨rfl, h₂⟩ := hzv
            exact Bool.noConfusion (h₁.trans h₂.symm)
          · obtain ⟨i, hi⟩ := hO.1 hv
            exact literalVertex_ne_occurrenceVertex _ _ _ hi
        · obtain ⟨i, hi⟩ := hO.1 hu
          exact literalVertex_ne_occurrenceVertex _ _ _ hi
      · obtain ⟨i, hi, j, hj, j', hj', he⟩ := mem_cliqueEdges.1 he
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hocc : ∀ {k}, occurrenceVertex i k ∈ L ∪ O → k = J ⟨i, hi⟩ := fun hk => by
          rcases Finset.mem_union.1 hk with hk | hk
          · obtain ⟨x, -, hx⟩ := hL.1 hk
            exact (literalVertex_ne_occurrenceVertex _ _ _ hx.symm).elim
          · obtain ⟨i', hi'⟩ := hO.1 hk
            obtain ⟨rfl, rfl⟩ := occurrenceVertex_inj.1 hi'
            rfl
        exact huv (by rw [hocc hu, hocc hv])
      · obtain ⟨i, hi, j, hj, he⟩ := mem_conflictEdges.1 he
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hx := mem_vars hi hj
        have hj₀ : j = J ⟨i, hi⟩ := by
          rcases Finset.mem_union.1 hu with hu | hu
          · obtain ⟨x, -, hx⟩ := hL.1 hu
            exact (literalVertex_ne_occurrenceVertex _ _ _ hx.symm).elim
          · obtain ⟨i', hi'⟩ := hO.1 hu
            obtain ⟨rfl, rfl⟩ := occurrenceVertex_inj.1 hi'
            rfl
        have hσj : σ φ[i][j].1 = φ[i][j].2 := by
          subst hj₀
          exact hJ ⟨i, hi⟩
        rcases Finset.mem_union.1 hv with hv | hv
        · obtain ⟨y, -, hy⟩ := hL.1 hv
          rw [literalVertex_inj hx] at hy
          obtain ⟨rfl, hb⟩ := hy
          rw [hσj] at hb
          exact (Bool.not_ne_self _) hb
        · obtain ⟨i', hi'⟩ := hO.1 hv
          exact literalVertex_ne_occurrenceVertex _ _ _ hi'
    rcases mem_edges_of_adj hadj with he | he
    · exact key u hu v hv huv he
    · exact key v hv u hu (Ne.symm huv) he
  · -- the set has `n + m` vertices
    have hdisj : Disjoint L O := Finset.disjoint_left.2 fun v hvL hvO => by
      obtain ⟨x, -, rfl⟩ := hL.1 hvL
      obtain ⟨i, hi⟩ := hO.1 hvO
      exact literalVertex_ne_occurrenceVertex _ _ _ hi
    rw [Finset.card_union_of_disjoint hdisj]
    congr 1
    · rw [List.toFinset_card_of_nodup, List.length_map]
      refine φ.nodup_distinctVars.map_on fun x hx y hy hxy => ?_
      exact ((literalVertex_inj (CNF.mem_distinctVars.1 hx)).1 hxy).1
    · rw [Finset.card_image_of_injective _ fun i i' h => Fin.ext (occurrenceVertex_inj.1 h).1,
        Finset.card_univ, Fintype.card_fin]

end SparseIndependentSet

/-- **Correctness of the reduction with variable edges.** A formula is satisfiable exactly when its
graph has an independent set of `n + m` vertices, for `n` distinct variables and `m` clauses. -/
theorem toSparseIndependentSet_mem_iff (φ : CNF ℕ) :
    toSparseIndependentSet φ ∈ IndependentSet ↔ φ ∈ SAT :=
  ⟨SparseIndependentSet.satisfiable_of_mem, SparseIndependentSet.mem_of_satisfiable⟩

/-! ### Size -/

open SparseIndependentSet in
/-- **The graph has linear size.** On formulas with `m` clauses of at most `k` literals, the graph
of `toSparseIndependentSet` has at most `(k ^ 2 + 5 k) m` vertices and edges in total, counted as
listed. -/
theorem length_toSparseIndependentSet_le {k : ℕ} {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ k) :
    (toSparseIndependentSet φ).1.1.length + (toSparseIndependentSet φ).1.2.length ≤
      (k * k + 5 * k) * φ.length := by
  have hzip : ∀ c ∈ φ.zipIdx, c.1.length ≤ k := fun c hc => by
    obtain ⟨cl, i⟩ := c
    obtain ⟨hi, rfl⟩ := mem_zipIdx_iff.1 hc
    exact hφ _ (List.getElem_mem hi)
  have hn : φ.distinctVars.length ≤ k * φ.length :=
    (CNF.length_distinctVars φ).trans_le (CNF.numVars_le_mul_length hφ)
  have hV₁ : (φ.distinctVars.flatMap
      fun x => [literalVertex φ (x, true), literalVertex φ (x, false)]).length ≤
      φ.distinctVars.length * 2 :=
    List.length_flatMap_le fun _ _ => by simp
  have hV₂ : (φ.zipIdx.flatMap fun c => (List.range c.1.length).map (occurrenceVertex c.2)).length
      ≤ φ.length * k := by
    simpa using List.length_flatMap_le (l := φ.zipIdx) fun c hc => by simpa using hzip c hc
  have hE₁ : (literalEdges φ).length ≤ φ.distinctVars.length := by
    simp [literalEdges]
  have hE₂ : (cliqueEdges φ).length ≤ φ.length * (k * k) := by
    refine (List.length_flatMap_le (l := φ.zipIdx) (k := k * k) fun c hc => ?_).trans_eq
      (by rw [List.length_zipIdx])
    have := hzip c hc
    simp only [List.length_flatMap, List.length_map, List.length_range, List.map_const',
      List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul this this
  have hE₃ : (conflictEdges φ).length ≤ φ.length * k :=
    (List.length_flatMap_le (l := φ.zipIdx) (k := k) fun c hc => by simpa using hzip c hc).trans_eq
      (by rw [List.length_zipIdx])
  simp only [toSparseIndependentSet, vertices, edges, List.length_append]
  nlinarith

/-! ### Polynomial-time reduction -/

open SparseIndependentSet in
/-- The reduction `toSparseIndependentSet` is computable in polynomial time: vertex labels are
computed in unary from clause, position and variable indices, then converted to binary. -/
@[fun_prop]
theorem computableInPolyTime_toSparseIndependentSet :
    ComputableInPolyTime toSparseIndependentSet encCNF (encPair encGraph encNat) := by
  have hdv : ComputableInPolyTime CNF.distinctVars
      (encList (encList (encPair encNat encBool))) (encList encNat) :=
    CNF.computableInPolyTime_distinctVars encNat
  have hlit : ComputableInPolyTime (fun p : CNF ℕ × Literal ℕ => literalVertex p.1 p.2)
      (encPair (encList (encList (encPair encNat encBool))) (encPair encNat encBool)) encNat := by
    unfold literalVertex
    exact unary_to_binary.comp (by fun_prop)
  have hocc : ComputableInPolyTime (fun p : ℕ × ℕ => occurrenceVertex p.1 p.2)
      (encPair encUnary encUnary) encNat := by
    unfold occurrenceVertex
    exact unary_to_binary.comp (by fun_prop)
  have hk : ComputableInPolyTime
      (fun φ : CNF ℕ => φ.distinctVars.length + φ.length)
      (encList (encList (encPair encNat encBool))) encNat :=
    unary_to_binary.comp (unary_add.comp (((length_list encNat).comp hdv).prod (length_list _)))
  have hV : ComputableInPolyTime vertices (encList (encList (encPair encNat encBool)))
      (encList encNat) := by
    unfold vertices
    fun_prop
  have hE₁ : ComputableInPolyTime literalEdges (encList (encList (encPair encNat encBool)))
      (encList (encPair encNat encNat)) := by
    unfold literalEdges
    fun_prop
  have hE₂ : ComputableInPolyTime cliqueEdges (encList (encList (encPair encNat encBool)))
      (encList (encPair encNat encNat)) := by
    unfold cliqueEdges
    fun_prop
  have hE₃ : ComputableInPolyTime conflictEdges (encList (encList (encPair encNat encBool)))
      (encList (encPair encNat encNat)) := by
    unfold conflictEdges
    fun_prop
  have hE : ComputableInPolyTime edges (encList (encList (encPair encNat encBool)))
      (encList (encPair encNat encNat)) := by
    unfold edges
    fun_prop
  exact (hV.prod hE).prod hk

end SAT

end Cslib.Complexity
