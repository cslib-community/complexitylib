/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Basic
public import Complexity.Logics.Propositional.DNF

/-!
# Decision trees in normal form

The paths of a decision tree to leaves labelled `true` are the terms of a formula in disjunctive
normal form computing the same function (`DecisionTree.toDNF`), and the paths to leaves labelled
`false`, negated, are the clauses of a formula in conjunctive normal form (`DecisionTree.toCNF`).
A path reads each variable at most once, a variable read again following the branch of its first
reading, so the terms and clauses have distinct variables and at most `depth` literals
[Jukna, Section 14.1][Jukna2012]. So a function of decision tree depth `t` is a disjunction of
terms and a conjunction of clauses of width at most `t`.

## Main definitions

* `Cslib.DecisionTree.toDNF`, `Cslib.DecisionTree.toCNF`: the normal forms of a decision tree.

## Main results

* `Cslib.DecisionTree.eval_toDNF`, `Cslib.DecisionTree.eval_toCNF`: they compute the tree.
* `Cslib.DecisionTree.length_le_depth_of_mem_toDNF`,
  `Cslib.DecisionTree.length_le_depth_of_mem_toCNF`: their width is at most the depth.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.DecisionTree

open Cslib.Logic.PL

variable {ι : Type*} [DecidableEq ι]

/-- The terms of the paths of a decision tree to leaves labelled `true`, each extending the term
`p` of the path so far; a variable already in `p` is not read again. -/
def toDNFAux : DecisionTree ι Bool → Term ι → DNF ι
  | leaf b, p => if b then [p] else []
  | node i t₀ t₁, p =>
    match p.lookup i with
    | some true => toDNFAux t₁ p
    | some false => toDNFAux t₀ p
    | none => toDNFAux t₀ ((i, false) :: p) ++ toDNFAux t₁ ((i, true) :: p)

/-- The formula in disjunctive normal form of the paths of a decision tree to leaves labelled
`true`. -/
def toDNF (t : DecisionTree ι Bool) : DNF ι :=
  toDNFAux t []

/-- The formula in conjunctive normal form of the negated paths of a decision tree to leaves
labelled `false`. -/
def toCNF (t : DecisionTree ι Bool) : CNF ι :=
  (toDNF (t.map not)).negate

private theorem eval_lookup {p : Term ι} {i : ι} {b : Bool} (h : p.lookup i = some b)
    {x : ι → Bool} (hx : p.eval x = true) : x i = b := by
  induction p with
  | nil => simp at h
  | cons l p ih =>
    obtain ⟨j, c⟩ := l
    rw [Term.eval_cons, Bool.and_eq_true] at hx
    rw [List.lookup_cons] at h
    by_cases hji : i = j
    · subst hji
      simp only [BEq.rfl, Option.some.injEq] at h
      simpa [h] using hx.1
    · have hne : (i == j) = false := by simpa using hji
      rw [hne] at h
      exact ih h hx.2

private theorem eval_toDNFAux (t : DecisionTree ι Bool) (p : Term ι) (x : ι → Bool) :
    DNF.eval x (toDNFAux t p) = (p.eval x && t.eval x) := by
  induction t generalizing p with
  | leaf b => cases b <;> simp [toDNFAux, DNF.eval]
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [toDNFAux, eval_node]
    cases h : p.lookup i with
    | some b =>
      cases b <;> simp only [ih₀, ih₁] <;> cases hp : p.eval x <;>
        first | (simp; done) | simp [eval_lookup h hp]
    | none =>
      simp only [DNF.eval_append, ih₀, ih₁, Term.eval_cons, Literal.eval]
      cases x i <;> simp

/-- The paths to leaves labelled `true` compute the tree. -/
@[simp] theorem eval_toDNF (t : DecisionTree ι Bool) (x : ι → Bool) :
    DNF.eval x t.toDNF = t.eval x := by
  simp [toDNF, eval_toDNFAux]

/-- The negated paths to leaves labelled `false` compute the tree. -/
@[simp] theorem eval_toCNF (t : DecisionTree ι Bool) (x : ι → Bool) :
    CNF.eval x t.toCNF = t.eval x := by
  simp [toCNF]

private theorem mem_toDNFAux {t : DecisionTree ι Bool} {p q : Term ι} (hq : q ∈ toDNFAux t p) :
    q.length ≤ p.length + t.depth ∧ ((p.map Prod.fst).Nodup → (q.map Prod.fst).Nodup) := by
  induction t generalizing p with
  | leaf b => cases b <;> simp_all [toDNFAux]
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [toDNFAux] at hq
    split at hq
    · obtain ⟨h₁, h₂⟩ := ih₁ hq
      exact ⟨h₁.trans (by simp only [depth_node]; omega), h₂⟩
    · obtain ⟨h₁, h₂⟩ := ih₀ hq
      exact ⟨h₁.trans (by simp only [depth_node]; omega), h₂⟩
    · rename_i hnone
      have hi : i ∉ p.map Prod.fst := fun hi => by
        obtain ⟨⟨j, c⟩, hj, rfl⟩ := List.mem_map.1 hi
        rw [List.lookup_eq_none_iff] at hnone
        simpa using hnone _ hj
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨h₁, h₂⟩ := ih₀ hq
        refine ⟨h₁.trans (by simp only [List.length_cons, depth_node]; omega), fun hp => h₂ ?_⟩
        exact List.nodup_cons.2 ⟨hi, hp⟩
      · obtain ⟨h₁, h₂⟩ := ih₁ hq
        refine ⟨h₁.trans (by simp only [List.length_cons, depth_node]; omega), fun hp => h₂ ?_⟩
        exact List.nodup_cons.2 ⟨hi, hp⟩

/-- The terms of the normal form of a tree have at most `depth` literals. -/
theorem length_le_depth_of_mem_toDNF {t : DecisionTree ι Bool} {q : Term ι} (hq : q ∈ t.toDNF) :
    q.length ≤ t.depth := by
  simpa using (mem_toDNFAux hq).1

/-- The terms of the normal form of a tree read each variable once. -/
theorem nodup_of_mem_toDNF {t : DecisionTree ι Bool} {q : Term ι} (hq : q ∈ t.toDNF) :
    (q.map Prod.fst).Nodup :=
  (mem_toDNFAux hq).2 List.nodup_nil

/-- The clauses of the conjunctive normal form of a tree have at most `depth` literals. -/
theorem length_le_depth_of_mem_toCNF {t : DecisionTree ι Bool} {c : Clause ι} (hc : c ∈ t.toCNF) :
    c.length ≤ t.depth := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc
  simpa [Term.negate] using length_le_depth_of_mem_toDNF hq

end Cslib.DecisionTree
