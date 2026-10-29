/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.GeneralizedGeography
public import Complexity.Computability.Complexity.Classes.Space.TQBF.Prenex
import Complexity.Computability.Complexity.Classes.Space.TQBF.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.List.Counting

/-!
# Generalized Geography is `PSPACE`-hard

The reduction of [Sipser, Theorem 8.14][Sipser2013] for the vertex version of Generalized
Geography [Lichtenstein and Sipser][LichtensteinSipser1980], which adapts Schaefer's reduction from
quantified formulas to geography games [Schaefer1978], starts from true quantified Boolean formulas
in alternating prenex conjunctive normal form (`Cslib.Complexity.TQBFCNF`)
`∃ x₀, ∀ x₁, ⋯, ∃ x_{n-2}, ∀ x_{n-1}, ψ`. The graph of such a formula
(`Cslib.Complexity.GeneralizedGeography.formulaGraph`) has a diamond for each quantifier `j`: an
arc from its top to each of two value nodes, the nodes of `false` and of `true`, an arc from each
value node to its bottom, and an arc from the bottom to the top of the next diamond. Three moves
cross a diamond, so the first player chooses the value at the tops of the diamonds of the
existential quantifiers and the second player at those of the universal quantifiers. After the
last diamond the first player moves to a chooser node, from which the second player picks a
clause, and from the node of a clause the first player may move to the value node of `¬b` in the
diamond of the last quantifier over `x`, for each literal `(x, b)` of the clause. That node is
unvisited exactly when the literal is true, and from it the second player can only move to the
bottom of the diamond, already visited, and loses. The first player starts on the top of the first
diamond.

So the first player wins exactly when the existential player wins the game in which the moves
choose the values of the quantified variables and the formula `ψ` must hold
(`Cslib.Complexity.GeneralizedGeography.geographyWins_formulaGraph`), which is the value of the
formula (`Cslib.Logic.PL.QBF.eval_rounds_eq_true_iff`). An instance whose formula is not closed is
mapped to a graph without arcs, where the first player loses
(`Cslib.Complexity.GeneralizedGeography.reduce`).

## Main definitions

* `Cslib.Complexity.GeneralizedGeography.formulaGraph`: the graph of a formula.
* `Cslib.Complexity.GeneralizedGeography.visOf`: the vertices visited after some diamonds.
* `Cslib.Complexity.GeneralizedGeography.reduce`: the reduction from `TQBFCNF`.

## Main results

* `Cslib.Complexity.GeneralizedGeography.mem_formulaArcs`: the arcs of the graph of a formula, and
  the arcs from each kind of vertex
  (`Cslib.Complexity.GeneralizedGeography.mk_topNode_mem_formulaArcs_iff`, …).
* `Cslib.Complexity.GeneralizedGeography.geographyWins_topNode_lt`,
  `Cslib.Complexity.GeneralizedGeography.geographyWins_topNode_length`: crossing a diamond, and the
  end of a play.
* `Cslib.Complexity.GeneralizedGeography.geographyWins_formulaGraph`: the first player wins on the
  graph of a formula exactly when the existential player wins the game of the formula.
* `Cslib.Complexity.GeneralizedGeography.updates_eq_getD_lastIdx`: a variable takes the value of
  its last quantifier.
* `Cslib.Complexity.GeneralizedGeography.reduce_mem_iff`,
  `Cslib.Complexity.GeneralizedGeography.computableInPolyTime_reduce`: the reduction is
  correct and polynomial-time.
* `Cslib.Complexity.polyTimeReducible_TQBFCNF_GeneralizedGeography`,
  `Cslib.Complexity.GeneralizedGeography_pspaceHard`: Generalized Geography is `PSPACE`-hard.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.14][Sipser2013]
* [D. Lichtenstein, M. Sipser, *GO is polynomial-space hard*][LichtensteinSipser1980]
* [T. J. Schaefer, *On the complexity of some two-person perfect-information games*][Schaefer1978]
-/

@[expose] public section

namespace Cslib.Complexity

namespace GeneralizedGeography

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### The graph of a formula -/

/-- The top of diamond `j`. -/
def topNode (j : ℕ) : ℕ := Nat.pair 0 j

/-- The node of the value `b` in diamond `j`. -/
def valueNode (j : ℕ) (b : Bool) : ℕ := Nat.pair 1 (Nat.pair j b.toNat)

/-- The bottom of diamond `j`. -/
def bottomNode (j : ℕ) : ℕ := Nat.pair 2 j

/-- The node from which the second player picks a clause. -/
def chooserNode : ℕ := Nat.pair 3 0

/-- The node of clause `i`. -/
def clauseNode (i : ℕ) : ℕ := Nat.pair 4 i

/-- The arcs of diamond `j`. -/
def diamondArcs (j : ℕ) : List (ℕ × ℕ) :=
  [(topNode j, valueNode j false), (topNode j, valueNode j true),
    (valueNode j false, bottomNode j), (valueNode j true, bottomNode j),
    (bottomNode j, topNode (j + 1))]

/-- The position of the last quantifier over `x` in the list `xs` of quantified variables. -/
def lastIdx (xs : List ℕ) (x : ℕ) : ℕ := xs.length - 1 - xs.reverse.idxOf x

/-- The arcs from the node of clause `i`: to the value node of `¬b` in the diamond of the last
quantifier over `x`, for each literal `(x, b)` of the clause with a quantified variable. -/
def literalArcs (xs : List ℕ) (i : ℕ) (c : Clause ℕ) : List (ℕ × ℕ) :=
  (c.filter fun l => decide (l.1 ∈ xs)).map fun l =>
    (clauseNode i, valueNode (lastIdx xs l.1) (!l.2))

/-- The arcs of the graph of a formula `ψ` with quantified variables `xs`. -/
def formulaArcs (xs : List ℕ) (ψ : CNF ℕ) : List (ℕ × ℕ) :=
  (List.range xs.length).flatMap diamondArcs ++ (topNode xs.length, chooserNode) ::
    ((List.range ψ.length).map fun i => (chooserNode, clauseNode i)) ++
      ψ.zipIdx.flatMap fun c => literalArcs xs c.2 c.1

/-- **The graph of a formula**: its arcs, and as vertices the top of the first diamond and the
targets of the arcs. -/
def formulaGraph (xs : List ℕ) (ψ : CNF ℕ) : Graph :=
  (topNode 0 :: (formulaArcs xs ψ).map Prod.snd, formulaArcs xs ψ)

/-- **The reduction from `TQBFCNF`**: the graph of the formula, from the top of the first diamond,
when the formula is closed, and a graph without arcs otherwise. -/
def reduce (x : List (ℕ × ℕ) × CNF ℕ) : Graph × ℕ :=
  if x.2.all (fun c => c.all fun l => decide (l.1 ∈ QBF.roundVars x.1)) then
    (formulaGraph (QBF.roundVars x.1) x.2, topNode 0)
  else (([0], []), 0)

/-! ### The arcs -/

section Arcs

variable {xs : List ℕ} {ψ : CNF ℕ} {u w : ℕ}

/-- **The arcs of the graph of a formula**: those of the diamonds `j < xs.length`, the arc from the
top of diamond `xs.length` to the chooser node, the arcs from the chooser node to the clause nodes,
and the arcs from the node of clause `i` to the value node of `!b` in the diamond of the last
quantifier over `x`, for each literal `(x, b)` of clause `i` with `x ∈ xs`. -/
theorem mem_formulaArcs :
    (u, w) ∈ formulaArcs xs ψ ↔
      (∃ j < xs.length, (u = topNode j ∧ ∃ b, w = valueNode j b) ∨
        (∃ b, u = valueNode j b ∧ w = bottomNode j) ∨ (u = bottomNode j ∧ w = topNode (j + 1))) ∨
      (u = topNode xs.length ∧ w = chooserNode) ∨
      (∃ i < ψ.length, u = chooserNode ∧ w = clauseNode i) ∨
      (∃ i, ∃ h : i < ψ.length, ∃ l ∈ ψ[i], l.1 ∈ xs ∧ u = clauseNode i ∧
        w = valueNode (lastIdx xs l.1) (!l.2)) := by
  have hd (j : ℕ) : (u, w) ∈ diamondArcs j ↔ (u = topNode j ∧ ∃ b, w = valueNode j b) ∨
      (∃ b, u = valueNode j b ∧ w = bottomNode j) ∨ (u = bottomNode j ∧ w = topNode (j + 1)) := by
    simp only [diamondArcs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      exacts [Or.inl ⟨rfl, _, rfl⟩, Or.inl ⟨rfl, _, rfl⟩, Or.inr (Or.inl ⟨_, rfl, rfl⟩),
        Or.inr (Or.inl ⟨_, rfl, rfl⟩), Or.inr (Or.inr ⟨rfl, rfl⟩)]
    · rintro (⟨rfl, b, rfl⟩ | ⟨b, rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · cases b <;> simp
      · cases b <;> simp
      · simp
  have hc : (∃ i < ψ.length, (chooserNode, clauseNode i) = (u, w)) ↔
      ∃ i < ψ.length, u = chooserNode ∧ w = clauseNode i := by
    simp only [Prod.mk.injEq]
    exact exists_congr fun i => and_congr_right fun _ => ⟨fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩,
      fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩⟩
  have hl : (∃ c ∈ ψ.zipIdx, (u, w) ∈ literalArcs xs c.2 c.1) ↔ ∃ i, ∃ h : i < ψ.length,
      ∃ l ∈ ψ[i], l.1 ∈ xs ∧ u = clauseNode i ∧ w = valueNode (lastIdx xs l.1) (!l.2) := by
    constructor
    · rintro ⟨⟨c, i⟩, hci, hlit⟩
      obtain ⟨hi, rfl⟩ : ∃ h : i < ψ.length, ψ[i] = c := by
        rw [List.mem_zipIdx_iff_getElem?] at hci
        simpa using List.getElem?_eq_some_iff.1 hci
      simp only [literalArcs, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.mk.injEq]
        at hlit
      obtain ⟨l, ⟨hl, hlx⟩, rfl, rfl⟩ := hlit
      exact ⟨i, hi, l, hl, hlx, rfl, rfl⟩
    · rintro ⟨i, hi, l, hl, hlx, rfl, rfl⟩
      refine ⟨(ψ[i], i), List.mem_zipIdx_iff_getElem?.2 (by simp [hi]), ?_⟩
      simp only [literalArcs, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨l, ⟨hl, hlx⟩, rfl⟩
  simp only [formulaArcs, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.mem_map, hd, Prod.mk.injEq, or_assoc]
  rw [← hc, ← hl]
  simp only [Prod.mk.injEq]

theorem mk_topNode_mem_formulaArcs_iff {j : ℕ} :
    (topNode j, w) ∈ formulaArcs xs ψ ↔
      (j < xs.length ∧ ∃ b, w = valueNode j b) ∨ (j = xs.length ∧ w = chooserNode) := by
  rw [mem_formulaArcs]
  simp [topNode, valueNode, bottomNode, chooserNode, clauseNode, Nat.pair_eq_pair]

theorem mk_valueNode_mem_formulaArcs_iff {j : ℕ} {b : Bool} (hj : j < xs.length) :
    (valueNode j b, w) ∈ formulaArcs xs ψ ↔ w = bottomNode j := by
  rw [mem_formulaArcs]
  simp [topNode, valueNode, bottomNode, chooserNode, clauseNode, Nat.pair_eq_pair, hj]

theorem mk_bottomNode_mem_formulaArcs_iff {j : ℕ} (hj : j < xs.length) :
    (bottomNode j, w) ∈ formulaArcs xs ψ ↔ w = topNode (j + 1) := by
  rw [mem_formulaArcs]
  simp [topNode, valueNode, bottomNode, chooserNode, clauseNode, Nat.pair_eq_pair, hj]

theorem mk_chooserNode_mem_formulaArcs_iff :
    (chooserNode, w) ∈ formulaArcs xs ψ ↔ ∃ i < ψ.length, w = clauseNode i := by
  rw [mem_formulaArcs]
  simp [topNode, valueNode, bottomNode, chooserNode, clauseNode, Nat.pair_eq_pair]

theorem mk_clauseNode_mem_formulaArcs_iff {i : ℕ} :
    (clauseNode i, w) ∈ formulaArcs xs ψ ↔
      ∃ h : i < ψ.length, ∃ l ∈ ψ[i], l.1 ∈ xs ∧ w = valueNode (lastIdx xs l.1) (!l.2) := by
  rw [mem_formulaArcs]
  constructor
  · rintro (⟨j, -, ⟨h, -⟩ | ⟨b, h, -⟩ | ⟨h, -⟩⟩ | ⟨h, -⟩ | ⟨i', -, h, -⟩ |
        ⟨i', hi', l, hl, hlx, h, rfl⟩)
    · simp [clauseNode, topNode, Nat.pair_eq_pair] at h
    · simp [clauseNode, valueNode, Nat.pair_eq_pair] at h
    · simp [clauseNode, bottomNode, Nat.pair_eq_pair] at h
    · simp [clauseNode, topNode, Nat.pair_eq_pair] at h
    · simp [clauseNode, chooserNode, Nat.pair_eq_pair] at h
    · obtain rfl : i = i' := (Nat.pair_eq_pair.1 h).2
      exact ⟨hi', l, hl, hlx, rfl⟩
  · rintro ⟨hi, l, hl, hlx, rfl⟩
    exact Or.inr (Or.inr (Or.inr ⟨i, hi, l, hl, hlx, rfl, rfl⟩))

end Arcs

/-! ### Visited vertices -/

section Visited

variable {z : List Bool} {j : ℕ}

/-- The vertices visited once the values `z` have been chosen in the first `z.length` diamonds,
with the token on the top of the next one. -/
def visOf (z : List Bool) : List ℕ :=
  (List.range (z.length + 1)).map topNode ++ (List.range z.length).map bottomNode ++
    (List.range z.length).map fun j => valueNode j (z.getD j false)

private theorem topNode_mem_visOf : topNode j ∈ visOf z ↔ j ≤ z.length := by
  simp only [visOf, List.mem_append, List.mem_map, List.mem_range]
  simp [topNode, bottomNode, valueNode, Nat.pair_eq_pair]

private theorem bottomNode_mem_visOf : bottomNode j ∈ visOf z ↔ j < z.length := by
  simp only [visOf, List.mem_append, List.mem_map, List.mem_range]
  simp [topNode, bottomNode, valueNode, Nat.pair_eq_pair]

private theorem chooserNode_notMem_visOf : chooserNode ∉ visOf z := by
  simp only [visOf, List.mem_append, List.mem_map, List.mem_range]
  simp [topNode, bottomNode, valueNode, chooserNode, Nat.pair_eq_pair]

private theorem clauseNode_notMem_visOf {i : ℕ} : clauseNode i ∉ visOf z := by
  simp only [visOf, List.mem_append, List.mem_map, List.mem_range]
  simp [topNode, bottomNode, valueNode, clauseNode, Nat.pair_eq_pair]

/-- Every vertex of `visOf z` is a top, a bottom or a value node. -/
private theorem mem_visOf {u : ℕ} : u ∈ visOf z ↔
    (∃ j ≤ z.length, u = topNode j) ∨ (∃ j < z.length, u = bottomNode j) ∨
      ∃ j < z.length, u = valueNode j (z.getD j false) := by
  simp only [visOf, List.mem_append, List.mem_map, List.mem_range, Nat.lt_succ_iff, or_assoc]
  exact or_congr (exists_congr fun j => and_congr_right fun _ => eq_comm)
    (or_congr (exists_congr fun j => and_congr_right fun _ => eq_comm)
      (exists_congr fun j => and_congr_right fun _ => eq_comm))

theorem valueNode_inj {i : ℕ} {b c : Bool} : valueNode j b = valueNode i c ↔ j = i ∧ b = c := by
  simp only [valueNode, Nat.pair_eq_pair, true_and]
  cases b <;> cases c <;> simp

private theorem valueNode_mem_visOf {b : Bool} :
    valueNode j b ∈ visOf z ↔ j < z.length ∧ b = z.getD j false := by
  rw [mem_visOf]
  constructor
  · rintro (⟨i, -, h⟩ | ⟨i, -, h⟩ | ⟨i, hi, h⟩)
    · simp [valueNode, topNode, Nat.pair_eq_pair] at h
    · simp [valueNode, bottomNode, Nat.pair_eq_pair] at h
    · obtain ⟨rfl, rfl⟩ := valueNode_inj.1 h
      exact ⟨hi, rfl⟩
  · rintro ⟨hj, rfl⟩
    exact Or.inr (Or.inr ⟨j, hj, rfl⟩)

/-- Crossing a diamond visits its value node, its bottom and the next top. -/
private theorem mem_visOf_append {b : Bool} {u : ℕ} :
    u ∈ visOf (z ++ [b]) ↔
      u ∈ topNode (z.length + 1) :: bottomNode z.length :: valueNode z.length b :: visOf z := by
  have hget (j : ℕ) (hj : j < z.length + 1) :
      (z ++ [b]).getD j false = if j < z.length then z.getD j false else b := by
    split_ifs with h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_append_right _ _ _ _ (by omega), show j - z.length = 0 by omega]
      rfl
  simp only [mem_visOf, List.mem_cons, List.length_append, List.length_singleton]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · rcases Nat.lt_or_ge i (z.length + 1) with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, by omega, rfl⟩)))
      · exact Or.inl (by rw [show i = z.length + 1 by omega])
    · rcases Nat.lt_or_ge i z.length with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, h, rfl⟩))))
      · exact Or.inr (Or.inl (by rw [show i = z.length by omega]))
    · rw [hget i hi]
      split_ifs with h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, h, rfl⟩))))
      · exact Or.inr (Or.inr (Or.inl (by rw [show i = z.length by omega])))
  · rintro (rfl | rfl | rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact Or.inl ⟨_, le_rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨_, by omega, rfl⟩)
    · exact Or.inr (Or.inr ⟨z.length, by omega, by
        rw [hget z.length (by omega), ite_eq_right (lt_irrefl _)]⟩)
    · exact Or.inl ⟨i, by omega, rfl⟩
    · exact Or.inr (Or.inl ⟨i, by omega, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, by omega, by rw [hget i (by omega), ite_eq_left hi]⟩)

end Visited

/-! ### The game on the graph of a formula -/

section Game

variable {xs : List ℕ} {ψ : CNF ℕ}

/-- On the graph of a formula every arc leads to a vertex. -/
theorem geographyWins_formulaGraph_iff {vis : List ℕ} {v : ℕ} :
    (formulaGraph xs ψ).GeographyWins vis v ↔ ∃ w, (v, w) ∈ formulaArcs xs ψ ∧ w ∉ vis ∧
      ¬(formulaGraph xs ψ).GeographyWins (w :: vis) w := by
  rw [Graph.geographyWins_iff]
  refine exists_congr fun w => ⟨fun ⟨h, _, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨h, ?_, h'⟩⟩
  exact List.mem_cons_of_mem _ (List.mem_map_of_mem (f := Prod.snd) h)

private theorem lastIdx_lt {x : ℕ} (hx : x ∈ xs) : lastIdx xs x < xs.length := by
  have := List.length_pos_of_mem hx
  unfold lastIdx
  omega

/-- From a value node whose bottom is visited, the player to move loses. -/
private theorem not_geographyWins_valueNode {vis : List ℕ} {j : ℕ} {c : Bool} (hj : j < xs.length)
    (hvis : bottomNode j ∈ vis) : ¬(formulaGraph xs ψ).GeographyWins vis (valueNode j c) := by
  rw [geographyWins_formulaGraph_iff]
  rintro ⟨w, hw, hwvis, -⟩
  rw [mk_valueNode_mem_formulaArcs_iff hj] at hw
  exact hwvis (hw ▸ hvis)

/-- From the node of a clause, with every bottom visited, the first player wins exactly when the
value node of the negation of some literal of the clause is unvisited. -/
private theorem geographyWins_clauseNode {vis : List ℕ} {i : ℕ} (hi : i < ψ.length)
    (hvis : ∀ j < xs.length, bottomNode j ∈ vis) :
    (formulaGraph xs ψ).GeographyWins vis (clauseNode i) ↔
      ∃ l ∈ ψ[i], l.1 ∈ xs ∧ valueNode (lastIdx xs l.1) (!l.2) ∉ vis := by
  rw [geographyWins_formulaGraph_iff]
  constructor
  · rintro ⟨w, hw, hwvis, -⟩
    obtain ⟨hi', l, hl, hlx, rfl⟩ := mk_clauseNode_mem_formulaArcs_iff.1 hw
    exact ⟨l, hl, hlx, hwvis⟩
  · rintro ⟨l, hl, hlx, hvis'⟩
    exact ⟨_, mk_clauseNode_mem_formulaArcs_iff.2 ⟨hi, l, hl, hlx, rfl⟩, hvis',
      not_geographyWins_valueNode (lastIdx_lt hlx)
        (List.mem_cons_of_mem _ (hvis _ (lastIdx_lt hlx)))⟩

/-- **The end of a play**: after the last diamond, the first player wins exactly when the chosen
values satisfy the formula. -/
theorem geographyWins_topNode_length {z : List Bool} (hz : z.length = xs.length)
    (hvars : ∀ c ∈ ψ, ∀ l ∈ c, l.1 ∈ xs) :
    (formulaGraph xs ψ).GeographyWins (visOf z) (topNode xs.length) ↔
      ψ.eval (fun x => z.getD (lastIdx xs x) false) = true := by
  have hclause (i : ℕ) (hi : i < ψ.length) :
      (formulaGraph xs ψ).GeographyWins (clauseNode i :: chooserNode :: visOf z) (clauseNode i) ↔
        Clause.eval (fun x => z.getD (lastIdx xs x) false) ψ[i] = true := by
    rw [geographyWins_clauseNode hi fun j hj => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (bottomNode_mem_visOf.2 (hz ▸ hj))), Clause.eval_eq_true_iff]
    refine exists_congr fun l => and_congr_right fun hl => ?_
    have hlx := hvars _ (List.getElem_mem hi) l hl
    simp only [List.mem_cons, valueNode_mem_visOf, not_or]
    have hne₁ : valueNode (lastIdx xs l.1) (!l.2) ≠ clauseNode i := by
      simp [valueNode, clauseNode, Nat.pair_eq_pair]
    have hne₂ : valueNode (lastIdx xs l.1) (!l.2) ≠ chooserNode := by
      simp [valueNode, chooserNode, Nat.pair_eq_pair]
    have hlt := hz ▸ lastIdx_lt hlx
    constructor
    · rintro ⟨-, -, -, h⟩
      cases h' : z.getD (lastIdx xs l.1) false <;> cases hb : l.2 <;> simp_all
    · intro h
      refine ⟨hlx, hne₁, hne₂, fun ⟨_, h'⟩ => ?_⟩
      rw [h] at h'
      cases l.2 <;> simp at h'
  rw [geographyWins_formulaGraph_iff]
  constructor
  · rintro ⟨w, hw, -, hlose⟩
    rcases mk_topNode_mem_formulaArcs_iff.1 hw with ⟨h, -⟩ | ⟨-, rfl⟩
    · exact absurd h (lt_irrefl _)
    rw [geographyWins_formulaGraph_iff] at hlose
    simp only [mk_chooserNode_mem_formulaArcs_iff, not_exists, not_and, not_not] at hlose
    refine (CNF.eval_eq_true_iff _ _).2 fun c hc => ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    refine (hclause i hi).1 (hlose _ ⟨i, hi, rfl⟩ ?_)
    simp only [List.mem_cons, not_or]
    exact ⟨by simp [clauseNode, chooserNode, Nat.pair_eq_pair], clauseNode_notMem_visOf⟩
  · intro h
    refine ⟨chooserNode, mk_topNode_mem_formulaArcs_iff.2 (Or.inr ⟨rfl, rfl⟩),
      chooserNode_notMem_visOf, ?_⟩
    rw [geographyWins_formulaGraph_iff]
    rintro ⟨w, hw, -, hlose⟩
    obtain ⟨i, hi, rfl⟩ := mk_chooserNode_mem_formulaArcs_iff.1 hw
    exact hlose ((hclause i hi).2 ((CNF.eval_eq_true_iff _ _).1 h _ (List.getElem_mem hi)))

/-- **Crossing a diamond**: from its top, the player to move wins exactly when some value leaves
the other player to move on the top of the next diamond in a losing position. -/
theorem geographyWins_topNode_lt {z : List Bool} (hj : z.length < xs.length) :
    (formulaGraph xs ψ).GeographyWins (visOf z) (topNode z.length) ↔
      ∃ b, ¬(formulaGraph xs ψ).GeographyWins (visOf (z ++ [b])) (topNode (z.length + 1)) := by
  rw [geographyWins_formulaGraph_iff]
  have hstep (b : Bool) :
      ¬(formulaGraph xs ψ).GeographyWins (valueNode z.length b :: visOf z)
          (valueNode z.length b) ↔
        ¬(formulaGraph xs ψ).GeographyWins (visOf (z ++ [b])) (topNode (z.length + 1)) := by
    rw [geographyWins_formulaGraph_iff]
    simp only [mk_valueNode_mem_formulaArcs_iff hj, exists_eq_left, not_and, not_not]
    rw [geographyWins_formulaGraph_iff]
    simp only [mk_bottomNode_mem_formulaArcs_iff hj, exists_eq_left]
    have hb : bottomNode z.length ∉ valueNode z.length b :: visOf z := by
      simp only [List.mem_cons, not_or]
      exact ⟨by simp [bottomNode, valueNode, Nat.pair_eq_pair],
        fun h => lt_irrefl _ (bottomNode_mem_visOf.1 h)⟩
    have ht : topNode (z.length + 1) ∉ bottomNode z.length :: valueNode z.length b :: visOf z := by
      simp only [List.mem_cons, not_or]
      exact ⟨by simp [bottomNode, topNode, Nat.pair_eq_pair],
        by simp [valueNode, topNode, Nat.pair_eq_pair],
        fun h => by have := topNode_mem_visOf.1 h; omega⟩
    rw [Graph.geographyWins_congr (fun u => mem_visOf_append.symm)]
    tauto
  constructor
  · rintro ⟨w, hw, -, hlose⟩
    rcases mk_topNode_mem_formulaArcs_iff.1 hw with ⟨-, b, rfl⟩ | ⟨h, -⟩
    · exact ⟨b, (hstep b).1 hlose⟩
    · exact absurd h (Nat.ne_of_lt hj)
  · rintro ⟨b, h⟩
    exact ⟨valueNode z.length b, mk_topNode_mem_formulaArcs_iff.2 (Or.inl ⟨hj, b, rfl⟩),
      fun h' => by simpa using (valueNode_mem_visOf.1 h').1, (hstep b).2 h⟩

/-- **The game on the graph of a formula**, from the top of diamond `j` after the values `z` have
been chosen: the player to move, the first player when `j` is even, wins exactly when the
quantifiers over the remaining `k` variables, starting with `∃` when `j` is even, hold. -/
private theorem geographyWins_topNode (heven : Even xs.length)
    (hvars : ∀ c ∈ ψ, ∀ l ∈ c, l.1 ∈ xs) :
    ∀ (k : ℕ) (z : List Bool), z.length + k = xs.length →
      ((formulaGraph xs ψ).GeographyWins (visOf z) (topNode z.length) ↔
        ((z.length % 2 == 0) = true ↔ Alternation (z.length % 2 == 0) (List.replicate k 1)
          fun z' => ψ.eval (fun x => (z ++ z').getD (lastIdx xs x) false) = true))
  | 0, z, hz => by
    have hz' : z.length = xs.length := by omega
    have hpar : (z.length % 2 == 0) = true := by
      rw [hz', beq_iff_eq, ← Nat.even_iff]
      exact heven
    rw [hpar, iff_true_left rfl, List.replicate_zero, alternation_nil, List.append_nil, hz']
    exact geographyWins_topNode_length hz' hvars
  | k + 1, z, hz => by
    have ih (b : Bool) := geographyWins_topNode heven hvars k (z ++ [b])
      (by simp only [List.length_append, List.length_singleton]; omega)
    simp only [List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append] at ih
    rw [geographyWins_topNode_lt (by omega), List.replicate_succ]
    rcases Nat.mod_two_eq_zero_or_one z.length with h | h
    · have h' : (z.length + 1) % 2 = 1 := by omega
      simp only [h, h'] at ih ⊢
      simp only [beq_self_eq_true, true_iff, alternation_true_one_cons]
      refine exists_congr fun b => ?_
      rw [ih b]
      simp
    · have h' : (z.length + 1) % 2 = 0 := by omega
      simp only [h, h'] at ih ⊢
      rw [show (1 == 0) = false from rfl, iff_false_left Bool.false_ne_true,
        alternation_false_one_cons, not_forall]
      refine exists_congr fun b => ?_
      rw [ih b]
      simp

/-- **The first player wins on the graph of a formula** exactly when the existential player wins
the game of single-bit moves in which the moves choose the values of the quantified variables,
alternately existentially and universally, and the formula must hold, each variable taking the
value of its last quantifier. -/
theorem geographyWins_formulaGraph (heven : Even xs.length)
    (hvars : ∀ c ∈ ψ, ∀ l ∈ c, l.1 ∈ xs) :
    (formulaGraph xs ψ).GeographyWins [topNode 0] (topNode 0) ↔
      Alternation true (List.replicate xs.length 1)
        fun z => ψ.eval (fun x => z.getD (lastIdx xs x) false) = true := by
  have h := geographyWins_topNode heven hvars xs.length [] (by simp)
  simpa [visOf] using h

end Game

/-! ### The reduction -/

/-- A variable takes the value of its last update. -/
theorem updates_eq_getD_lastIdx (σ : ℕ → Bool) :
    ∀ (xs : List ℕ) (z : List Bool), z.length = xs.length → ∀ x ∈ xs,
      QBF.updates σ xs z x = z.getD (lastIdx xs x) false
  | [], _, _, _, hx => absurd hx List.not_mem_nil
  | _ :: _, [], hz, _, _ => absurd hz (by simp)
  | v :: vs, b :: bs, hz, x, hx => by
    rw [QBF.updates]
    have hz' : bs.length = vs.length := by simpa using hz
    by_cases hxs : x ∈ vs
    · rw [updates_eq_getD_lastIdx _ vs bs hz' x hxs]
      have hlt := List.idxOf_lt_length_of_mem (List.mem_reverse.2 hxs)
      rw [List.length_reverse] at hlt
      have hidx : (v :: vs).reverse.idxOf x = vs.reverse.idxOf x := by
        rw [List.reverse_cons, List.idxOf_append_of_mem (List.mem_reverse.2 hxs)]
      rw [lastIdx, lastIdx, hidx, List.length_cons,
        show vs.length + 1 - 1 - vs.reverse.idxOf x = (vs.length - 1 - vs.reverse.idxOf x) + 1 by
          omega, List.getD_cons_succ]
    · obtain rfl : x = v := by simpa [hxs] using hx
      rw [QBF.updates_of_notMem hxs, Function.update_self]
      have hidx : (x :: vs).reverse.idxOf x = vs.length := by
        rw [List.reverse_cons, List.idxOf_append_of_notMem (by simpa using hxs),
          List.length_reverse, List.idxOf_cons_self, Nat.add_zero]
      rw [lastIdx, hidx, List.length_cons, show vs.length + 1 - 1 - vs.length = 0 by omega]
      rfl

/-- **The reduction is correct**: the first player wins on the graph of an instance exactly when
its formula is a true closed formula. -/
theorem reduce_mem_iff (x : List (ℕ × ℕ) × CNF ℕ) :
    reduce x ∈ GeneralizedGeography ↔ x ∈ TQBFCNF := by
  obtain ⟨ps, ψ⟩ := x
  unfold reduce
  split_ifs with hall
  · have hvars : ∀ c ∈ ψ, ∀ l ∈ c, l.1 ∈ QBF.roundVars ps := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using hall
    have hclosed := (QBF.closed_rounds_ofCNF_iff ps ψ).2 hvars
    have heven : Even (QBF.roundVars ps).length := ⟨ps.length, by rw [QBF.length_roundVars]; ring⟩
    rw [mem_GeneralizedGeography, geographyWins_formulaGraph heven hvars, TQBFCNF,
      Set.mem_ofPred_eq, mem_TQBF_iff_of_closed hclosed (fun _ => false),
      QBF.eval_rounds_eq_true_iff, ← QBF.length_roundVars]
    refine alternation_congr_of_length fun z hz => ?_
    rw [sum_replicate_one] at hz
    rw [QBF.eval_ofCNF]
    refine Eq.congr_left (CNF.eval_congr fun v hv => ?_)
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hv
    obtain ⟨c, hc, hlc⟩ := List.mem_flatten.1 hl
    exact (updates_eq_getD_lastIdx _ _ z hz l.1 (hvars c hc l hlc)).symm
  · refine iff_of_false notMem_GeneralizedGeography_of_nil fun h => hall ?_
    simpa only [List.all_eq_true, decide_eq_true_eq] using
      (QBF.closed_rounds_ofCNF_iff ps ψ).1 h.1

/-! ### Polynomial time -/

section PolyTime

open ComputableInPolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

@[fun_prop]
theorem computableInPolyTime_topNode {j : γ → ℕ}
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => topNode (j x)) encIn encNat :=
  unary_to_binary.comp (show ComputableInPolyTime (fun x => Nat.pair 0 (j x)) _ _ by fun_prop)

@[fun_prop]
theorem computableInPolyTime_valueNode {j : γ → ℕ} {b : γ → Bool}
    (hj : ComputableInPolyTime j encIn encUnary)
    (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun x => valueNode (j x) (b x)) encIn encNat :=
  unary_to_binary.comp (show ComputableInPolyTime
    (fun x => Nat.pair 1 (Nat.pair (j x) (b x).toNat)) _ _ by fun_prop)

@[fun_prop]
theorem computableInPolyTime_bottomNode {j : γ → ℕ}
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => bottomNode (j x)) encIn encNat :=
  unary_to_binary.comp (show ComputableInPolyTime (fun x => Nat.pair 2 (j x)) _ _ by fun_prop)

@[fun_prop]
theorem computableInPolyTime_clauseNode {i : γ → ℕ}
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => clauseNode (i x)) encIn encNat :=
  unary_to_binary.comp (show ComputableInPolyTime (fun x => Nat.pair 4 (i x)) _ _ by fun_prop)

@[fun_prop]
theorem computableInPolyTime_diamondArcs {j : γ → ℕ}
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => diamondArcs (j x)) encIn
      (encList (encPair encNat encNat)) := by
  unfold diamondArcs
  fun_prop

@[fun_prop]
theorem computableInPolyTime_lastIdx {xs : γ → List ℕ} {v : γ → ℕ}
    (hxs : ComputableInPolyTime xs encIn (encList encNat))
    (hv : ComputableInPolyTime v encIn encNat) :
    ComputableInPolyTime (fun x => lastIdx (xs x) (v x)) encIn encUnary := by
  unfold lastIdx
  fun_prop

@[fun_prop]
theorem computableInPolyTime_literalArcs {xs : γ → List ℕ} {i : γ → ℕ}
    {c : γ → Clause ℕ} (hxs : ComputableInPolyTime xs encIn (encList encNat))
    (hi : ComputableInPolyTime i encIn encUnary)
    (hc : ComputableInPolyTime c encIn (encList (encPair encNat encBool))) :
    ComputableInPolyTime (fun x => literalArcs (xs x) (i x) (c x)) encIn
      (encList (encPair encNat encNat)) := by
  unfold literalArcs
  simp only [List.decide_mem_eq_any]
  fun_prop

/-- The graph of a formula is polynomial-time in its quantified variables and its clauses. -/
@[fun_prop]
theorem computableInPolyTime_formulaGraph {xs : γ → List ℕ} {ψ : γ → CNF ℕ}
    (hxs : ComputableInPolyTime xs encIn (encList encNat))
    (hψ : ComputableInPolyTime ψ encIn encCNF) :
    ComputableInPolyTime (fun x => formulaGraph (xs x) (ψ x)) encIn encGraph := by
  unfold formulaGraph formulaArcs encGraph
  unfold encCNF at hψ
  fun_prop

/-- **The reduction is polynomial-time.** -/
theorem computableInPolyTime_reduce :
    ComputableInPolyTime reduce encPrenexCNF (encPair encGraph encNat) := by
  unfold reduce QBF.roundVars encPrenexCNF
  simp only [List.decide_mem_eq_any]
  unfold encCNF
  fun_prop

end PolyTime

end GeneralizedGeography

open GeneralizedGeography Turing.MultiTapeTM

/-- **`TQBFCNF` reduces to Generalized Geography** [Sipser, Theorem 8.14][Sipser2013]
[LichtensteinSipser1980]. -/
theorem polyTimeReducible_TQBFCNF_GeneralizedGeography :
    PolyTimeReducible encPrenexCNF (encPair encGraph encNat) TQBFCNF GeneralizedGeography :=
  ⟨reduce, computableInPolyTime_reduce, fun x => (reduce_mem_iff x).symm⟩

/-- **Generalized Geography is `PSPACE`-hard** [Sipser, Theorem 8.14][Sipser2013]
[LichtensteinSipser1980]. -/
theorem GeneralizedGeography_pspaceHard :
    PSPACEHard (encPair encGraph encNat) GeneralizedGeography :=
  TQBFCNF_pspaceHard.trans polyTimeReducible_TQBFCNF_GeneralizedGeography

end Cslib.Complexity
