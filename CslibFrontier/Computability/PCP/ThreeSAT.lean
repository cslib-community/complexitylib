/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.ConstraintGraph
public import CslibFrontier.Logics.Propositional.CNF
public import Mathlib.Data.Fintype.Prod
import CslibFrontier.Logics.Propositional.CNF.UnsatVal

/-!
# From 3-SAT to constraint graphs

The standard reduction from 3-SAT to the satisfiability of constraint graphs over a constant
alphabet, with binary constraints [Arora and Barak, Chapter 22][AroraBarak09]. It can serve as the
starting point of Dinur's proof of the PCP theorem, which starts instead from graph 3-colouring
[Dinur, Proposition 2.1 and Corollary 4.2][Dinur2005]: it produces a constraint graph whose value is
at least a constant fraction of the proportion of clauses that every assignment falsifies, and the
rest of the proof amplifies that value.

The constraint graph `ConstraintGraph.ofCNF φ` of a formula `φ` with `m` clauses has

* a **variable vertex** `inl x` for each variable `x`, meant to carry the value of `x` as the first
  bit of its label, and
* a **clause vertex** `inr j` for each clause, meant to carry the values of the variables at the
  first three positions of clause `j`, one bit per position;
* three edges `(j, q)` per clause, so `3 m` in all. The edge `(j, q)` goes from clause vertex `j` to
  the variable vertex of the literal at position `q` of clause `j`, or back to clause vertex `j`
  when the clause has no such position. Its constraint asks that the label of the clause vertex
  satisfy clause `j`, and that its bit `q` agree with the first bit of the label of the variable
  vertex.

The alphabet is `Fin 3 → Bool`, with eight symbols. If an assignment of the variables falsifies `k`
clauses, labelling the vertices by it violates at most `3 k` edges
(`card_unsatEdges_cnfLabelling_le`); conversely, from a labelling violating `k'` edges, reading
off the variables from the variable vertices gives an assignment falsifying at most `k'` clauses
(`countUnsat_cnfAssignment_le_card_unsatEdges`), since a clause is falsified only if one of its
three edges is violated. The second direction holds for every formula; the first needs the clauses
to have at most three literals.

## Main definitions

* `Cslib.PCP.ConstraintGraph.ofCNF`: the constraint graph of a formula.
* `Cslib.PCP.ConstraintGraph.cnfLabelling`, `Cslib.PCP.ConstraintGraph.cnfAssignment`: the
  translations between assignments of the variables and labellings of the vertices.

## Main results

* `Cslib.PCP.ConstraintGraph.satisfiable_ofCNF_iff`: the constraint graph of a formula whose clauses
  have at most three literals is satisfiable exactly when the formula is.
* `Cslib.PCP.ConstraintGraph.le_unsatVal_ofCNF`: if every assignment falsifies a proportion at
  least `ε` of the clauses, the value of the constraint graph is at least `ε / 3`.
* `Cslib.PCP.ConstraintGraph.unsatVal_ofCNF_le`: conversely, its value is at most the proportion of
  clauses that any assignment falsifies.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
-/

@[expose] public section

open Finset

namespace Cslib.PCP

open Cslib.Logic.PL

namespace ConstraintGraph

variable {V : Type*}

/-- The values `a q` of the variables at the first three positions `q` of the clause `κ` satisfy
`κ`: some position `q` of `κ` holds a literal `(x, b)` with `a q = b`. -/
def ClauseHolds (κ : Clause V) (a : Fin 3 → Bool) : Prop :=
  ∃ q : Fin 3, ∃ l, κ[q.val]? = some l ∧ a q = l.2

/-- The **constraint graph of a formula** `φ` [Arora and Barak, Chapter 22][AroraBarak09], over the
alphabet `Fin 3 → Bool`. Its vertices are the variables (`inl x`) and the clauses (`inr j`); the
edge `(j, q)` goes from clause `j` to the variable of the literal at position `q` of clause `j`,
or back to clause `j` when there is no such literal. Its constraint asks that the label of clause
`j`, read as the values of the variables at its first three positions, satisfy it, and that its
bit `q` agree with the first bit of the label of the variable. -/
def ofCNF (φ : CNF V) :
    ConstraintGraph (V ⊕ Fin φ.length) (Fin φ.length × Fin 3) (Fin 3 → Bool) where
  src e := .inr e.1
  dst e := φ[e.1][e.2.val]?.elim (.inr e.1) fun l ↦ .inl l.1
  rel e a b := ClauseHolds φ[e.1] a ∧ ∀ l, φ[e.1][e.2.val]? = some l → a e.2 = b 0

variable (φ : CNF V)

/-- The labelling of the vertices of `ofCNF φ` by an assignment `τ` of the variables: a variable
is labelled by its value, a clause by the values of the variables at its first three positions. -/
def cnfLabelling (τ : V → Bool) : V ⊕ Fin φ.length → Fin 3 → Bool
  | .inl x => fun _ ↦ τ x
  | .inr j => fun q ↦ φ[j][q.val]?.elim false fun l ↦ τ l.1

variable {φ}

/-- The assignment of the variables read off from a labelling of the vertices of `ofCNF φ`: the
value of a variable is the first bit of its label. -/
def cnfAssignment (A : V ⊕ Fin φ.length → Fin 3 → Bool) (x : V) : Bool :=
  A (.inl x) 0

/-- A labelling satisfies the three edges of a clause only if the assignment it induces satisfies
the clause. -/
private theorem eval_cnfAssignment_of_forall_satisfies {A : V ⊕ Fin φ.length → Fin 3 → Bool}
    {j : Fin φ.length} (h : ∀ q, (ofCNF φ).Satisfies A (j, q)) :
    φ[j].eval (cnfAssignment A) = true := by
  obtain ⟨q, l, hl, hq⟩ := (h 0).1
  have hlq := (h q).2 l hl
  simp only [ofCNF, hl, Option.elim_some] at hlq
  rw [Clause.eval_eq_true_iff]
  exact ⟨l, List.mem_of_getElem? hl, hlq.symm.trans hq⟩

/-- **Soundness, counted**: the assignment read off from a labelling falsifies at most as many
clauses as the labelling violates edges. -/
theorem countUnsat_cnfAssignment_le_card_unsatEdges (A : V ⊕ Fin φ.length → Fin 3 → Bool) :
    φ.countUnsat (cnfAssignment A) ≤ #((ofCNF φ).unsatEdges A) := by
  classical
  rw [CNF.countUnsat_eq_card]
  refine (card_le_card fun j hj ↦ ?_).trans (card_image_le (f := Prod.fst))
  rw [mem_filter] at hj
  rw [mem_image]
  by_contra! h
  refine Bool.false_ne_true (hj.2.symm.trans (eval_cnfAssignment_of_forall_satisfies fun q ↦ ?_))
  by_contra hq
  exact h (j, q) (mem_unsatEdges.2 hq) rfl

variable (φ)

/-- The labelling by an assignment satisfies the consistency part of every constraint. -/
private theorem cnfLabelling_consistent (τ : V → Bool) (e : Fin φ.length × Fin 3) :
    ∀ l, φ[e.1][e.2.val]? = some l → cnfLabelling φ τ (.inr e.1) e.2 =
      cnfLabelling φ τ ((ofCNF φ).dst e) 0 := by
  intro l hl
  simp only [Fin.getElem_fin] at hl
  simp [cnfLabelling, ofCNF, hl]

/-- If the clauses of `φ` have at most three literals, the labelling by an assignment satisfies
every edge of a clause that the assignment satisfies. -/
private theorem satisfies_cnfLabelling (h3 : ∀ c ∈ φ, c.length ≤ 3) {τ : V → Bool}
    {e : Fin φ.length × Fin 3} (he : φ[e.1].eval τ = true) :
    (ofCNF φ).Satisfies (cnfLabelling φ τ) e := by
  refine ⟨?_, cnfLabelling_consistent φ τ e⟩
  obtain ⟨l, hl, hτ⟩ := (Clause.eval_eq_true_iff _ _).1 he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
  have hi3 : i < 3 := hi.trans_le (h3 _ (List.getElem_mem _))
  refine ⟨⟨i, hi3⟩, φ[e.1][i], List.getElem?_eq_getElem hi, ?_⟩
  change φ[e.1][i]?.elim false (fun l ↦ τ l.1) = φ[e.1][i].2
  rw [List.getElem?_eq_getElem hi]
  exact hτ

/-- **Completeness, counted**: if the clauses of `φ` have at most three literals, the labelling by
an assignment violates at most three edges per clause the assignment falsifies. -/
theorem card_unsatEdges_cnfLabelling_le (h3 : ∀ c ∈ φ, c.length ≤ 3) (τ : V → Bool) :
    #((ofCNF φ).unsatEdges (cnfLabelling φ τ)) ≤ 3 * φ.countUnsat τ := by
  classical
  rw [CNF.countUnsat_eq_card]
  calc #((ofCNF φ).unsatEdges (cnfLabelling φ τ))
      ≤ #(({j : Fin φ.length | φ[j].eval τ = false} : Finset _) ×ˢ (univ : Finset (Fin 3))) := by
        refine card_le_card fun e he ↦ ?_
        rw [mem_unsatEdges] at he
        rw [mem_product, mem_filter]
        refine ⟨⟨mem_univ _, ?_⟩, mem_univ _⟩
        by_contra h
        exact he (satisfies_cnfLabelling φ h3 (Bool.not_eq_false _ ▸ h))
    _ = 3 * #{j : Fin φ.length | φ[j].eval τ = false} := by simp [card_product, mul_comm]

/-- **The reduction preserves satisfiability**: the constraint graph of a formula whose clauses
have at most three literals is satisfiable exactly when the formula is. -/
theorem satisfiable_ofCNF_iff (h3 : ∀ c ∈ φ, c.length ≤ 3) :
    (ofCNF φ).Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨cnfAssignment A, CNF.countUnsat_eq_zero_iff.1 (Nat.le_zero.1 ?_)⟩
    refine (countUnsat_cnfAssignment_le_card_unsatEdges A).trans_eq ?_
    rw [card_eq_zero, unsatEdges_eq_empty_iff]
    exact hA
  · rintro ⟨τ, hτ⟩
    refine ⟨cnfLabelling φ τ, fun e ↦ satisfies_cnfLabelling φ h3 ?_⟩
    exact (CNF.eval_eq_true_iff _ _).1 hτ _ (List.getElem_mem _)

/-- The constraint graph of a formula with `m` clauses has `3 m` edges. -/
private theorem card_edges_ofCNF : Fintype.card (Fin φ.length × Fin 3) = 3 * φ.length := by
  simp [mul_comm]

/-- **Soundness**: a labelling violates at least a third of the proportion of clauses that the
assignment read off from it falsifies. -/
theorem countUnsat_div_le_unsatFrac (A : V ⊕ Fin φ.length → Fin 3 → Bool) :
    (φ.countUnsat (cnfAssignment A) : ℝ) / φ.length / 3 ≤ (ofCNF φ).unsatFrac A := by
  rw [unsatFrac, card_edges_ofCNF, Nat.cast_mul, div_div, mul_comm (φ.length : ℝ), Nat.cast_ofNat]
  gcongr
  exact_mod_cast countUnsat_cnfAssignment_le_card_unsatEdges A

/-- **The gap is preserved**: if every assignment falsifies a proportion at least `ε` of the
clauses of `φ`, the value of its constraint graph is at least `ε / 3`. -/
theorem le_unsatVal_ofCNF {ε : ℝ} (h : ∀ τ : V → Bool, ε ≤ φ.countUnsat τ / φ.length) :
    ε / 3 ≤ (ofCNF φ).unsatVal :=
  (le_unsatVal_iff _).2 fun A ↦ (div_le_div_of_nonneg_right (h _) (by norm_num)).trans
    (countUnsat_div_le_unsatFrac φ A)

/-- Conversely, if the clauses of `φ` have at most three literals, the value of its constraint
graph is at most the proportion of clauses that any assignment falsifies. -/
theorem unsatVal_ofCNF_le (h3 : ∀ c ∈ φ, c.length ≤ 3) (τ : V → Bool) :
    (ofCNF φ).unsatVal ≤ φ.countUnsat τ / φ.length := by
  refine ((ofCNF φ).unsatVal_le (cnfLabelling φ τ)).trans ?_
  rw [unsatFrac, card_edges_ofCNF, Nat.cast_mul]
  rcases (φ.length).eq_zero_or_pos with h0 | h0
  · simp [h0]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (#((ofCNF φ).unsatEdges (cnfLabelling φ τ)) : ℝ) ≤ 3 * φ.countUnsat τ := by
    exact_mod_cast card_unsatEdges_cnfLabelling_le φ h3 τ
  have := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) φ.length)
  push_cast
  linarith

end ConstraintGraph

end Cslib.PCP
