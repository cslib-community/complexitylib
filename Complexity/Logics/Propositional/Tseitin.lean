/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Multigraph
public import Complexity.Logics.Propositional.CNF.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.BooleanRing

/-!
# Tseitin formulas

A finite multigraph on the vertices `V` with edges `E`, parallel edges and self-loops allowed, is
given by the map `ends : E → Sym2 V` sending each edge to its ends (`Cslib.Multigraph`). Given a
*charge* `χ v` for every vertex `v`, the **Tseitin formula** `CNF.tseitinFormula ends χ`
[Tseitin][Tseitin1983] [Urquhart][Urquhart1987] has a variable for each edge and says, for every
vertex `v`, that the parity of the edges at `v` is the charge of `v`. A self-loop at `v` would
count twice towards the parity of `v`, so it does not count at all; the parity of `v` is that of
the edges at `v` that are not self-loops (`Multigraph.incidence`), and the constraint is
expressed by the formula `CNF.parityOnEq` with a clause per assignment to those edges of the wrong
parity. A vertex with `d` edges other than self-loops thus contributes at most `2 ^ d` clauses of
`d` literals each.

Every edge other than a self-loop is at exactly two vertices, so summing the constraints of all
vertices gives `0 = ∑ χ`: if the total charge is odd, the Tseitin formula is unsatisfiable
(`CNF.not_satisfiable_tseitinFormula`). On a connected multigraph the converse holds, and more:
the constraints of all vertices but one are satisfiable, whatever the charges
(`Tseitin.exists_forall_mem_parityOn_incidence_eq`). Flipping the value of an edge flips the
parities of its two ends, so flipping the edges of a path flips the parities of its two ends only;
combining such flips moves the parities to any target, up to the vertex left out.

These facts underlie the resolution lower bounds for Tseitin formulas
(`Cslib.Logic.PL.Tseitin.minBalancedCut_le_of_refutableInWidth`,
`Cslib.Logic.PL.Tseitin.exp_le_of_refutableInSize`).

## Main definitions

* `Cslib.Logic.PL.CNF.tseitinFormula`: the Tseitin formula of a multigraph with charges.

## Main results

* `Cslib.Logic.PL.CNF.eval_tseitinFormula_eq_true_iff`: the semantics of Tseitin formulas.
* `Cslib.Logic.PL.CNF.not_satisfiable_tseitinFormula`: Tseitin formulas with odd total charge are
  unsatisfiable.
* `Cslib.Logic.PL.CNF.satisfiable_tseitinFormula_iff`: on a connected multigraph, the Tseitin
  formula is satisfiable exactly when the total charge is even.
* `Cslib.Logic.PL.Tseitin.exists_forall_mem_parityOn_incidence_eq`: on a connected multigraph, the
  constraints of the vertices of any set other than the set of all vertices are satisfiable.
* `Cslib.Logic.PL.CNF.length_le_of_mem_tseitinFormula`,
  `Cslib.Logic.PL.CNF.length_tseitinFormula_le`: the clauses of a Tseitin formula have at most as
  many literals as a vertex has edges, and there are at most `|V| 2 ^ k` of them when every vertex
  has at most `k` edges.

## References

* [G. S. Tseitin, *On the complexity of derivation in propositional calculus*][Tseitin1983]
* [A. Urquhart, *Hard examples for resolution*][Urquhart1987]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 18][Jukna2012]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset Function

variable {V E : Type*}

namespace Tseitin

/-! ### Parities at the vertices -/

section Parity

variable {ends : E → Sym2 V} [Fintype E] [DecidableEq V]

/-- Flipping the value of an edge flips the parities at its ends, and only there. -/
theorem parityOn_incidence_update_not [DecidableEq E] (σ : E → Bool) (e : E) (v : V) :
    parityOn (Multigraph.incidence ends v) (update σ e !σ e) =
      (decide (e ∈ Multigraph.incidence ends v) ^^ parityOn (Multigraph.incidence ends v) σ) := by
  by_cases he : e ∈ Multigraph.incidence ends v
  · rw [parityOn_update_not he, decide_eq_true he, Bool.true_xor]
  · rw [parityOn_update_of_notMem he, decide_eq_false he, Bool.false_xor]

/-- On a connected multigraph, the parities at any two vertices `u` and `w`, and nowhere else, can
be flipped: some assignment has parity `1` exactly at `u` and `w` (and nowhere if `u = w`). -/
private theorem exists_forall_parityOn_incidence_eq_xor [Finite V]
    (hG : (Multigraph.toSimpleGraph ends).Connected) (u w : V) :
    ∃ τ : E → Bool, ∀ v,
      parityOn (Multigraph.incidence ends v) τ = (decide (v = u) ^^ decide (v = w)) := by
  classical
  have := Fintype.ofFinite V
  let R : Finset V :=
    {w | ∃ τ : E → Bool, ∀ v,
      parityOn (Multigraph.incidence ends v) τ = (decide (v = u) ^^ decide (v = w))}
  suffices hR : R = univ by
    have hw : w ∈ R := by rw [hR]; exact mem_univ w
    simpa [R] using hw
  by_contra hR
  have hu : u ∈ R := by
    simp only [R, mem_filter, mem_univ, true_and, Bool.xor_self]
    exact ⟨fun _ => false, fun v => by simp [parityOn]⟩
  obtain ⟨e, he⟩ := ((Multigraph.connected_toSimpleGraph_iff ends).1 hG).2 R ⟨u, hu⟩ hR
  obtain ⟨a, ha, b, hb, hab⟩ := Multigraph.mem_edgeCut.1 he
  obtain ⟨τ, hτ⟩ := by simpa [R] using ha
  have hne : a ≠ b := fun h => mem_compl.1 hb (h ▸ ha)
  -- flipping `e` moves the parity `1` from `a` to `b`
  have hb' : b ∈ R := by
    simp only [R, mem_filter, mem_univ, true_and]
    refine ⟨update τ e !τ e, fun v => ?_⟩
    rw [parityOn_incidence_update_not, hτ]
    simp only [Multigraph.mem_incidence_of_ends_eq hab]
    by_cases hva : v = a
    · subst hva
      simp [hne]
    · by_cases hvb : v = b
      · subst hvb
        simp [hva, hne]
      · simp [hva, hvb]
  exact mem_compl.1 hb hb'

variable [Fintype V]

/-- **The handshake argument**: the parities at all vertices of an assignment to the edges add up
to `0`, since every edge other than a self-loop is at exactly two vertices. -/
theorem parityOn_univ_parityOn_incidence_eq_false (σ : E → Bool) :
    parityOn univ (fun v => parityOn (Multigraph.incidence ends v) σ) = false := by
  simp only [parityOn_eq_sum]
  rw [sum_comm' (t' := univ) (s' := fun e => {v | v ∈ ends e ∧ ¬(ends e).IsDiag}) (by simp)]
  refine sum_eq_zero fun e _ => ?_
  obtain ⟨a, b, hab⟩ : ∃ a b, ends e = s(a, b) := Sym2.ind (f := fun z => ∃ a b, z = s(a, b))
    (fun a b => ⟨a, b, rfl⟩) (ends e)
  by_cases h : a = b
  · rw [filter_false_of_mem fun v _ => by simp [hab, h], sum_empty]
  · rw [show ({v | v ∈ ends e ∧ ¬(ends e).IsDiag} : Finset V) = {a, b} by
      ext v
      simp [hab, h], sum_pair h, BooleanRing.add_self]

/-- An assignment satisfying the constraints of all vertices has even total charge. -/
private theorem parityOn_univ_eq_false_of_forall {σ : E → Bool} {χ : V → Bool}
    (h : ∀ v, parityOn (Multigraph.incidence ends v) σ = χ v) : parityOn univ χ = false := by
  rw [← parityOn_univ_parityOn_incidence_eq_false (ends := ends) σ]
  exact parityOn_congr fun v _ => (h v).symm

/-- On a connected multigraph, for every vertex `u` some assignment satisfies the constraints of
all vertices except possibly `u`: its parity at `v` is `χ v`, flipped at `u` when the total charge
is odd. -/
private theorem exists_forall_parityOn_incidence_eq (hG : (Multigraph.toSimpleGraph ends).Connected)
    (χ : V → Bool) (u : V) :
    ∃ σ : E → Bool, ∀ v,
      parityOn (Multigraph.incidence ends v) σ = ((parityOn univ χ && decide (v = u)) ^^ χ v) := by
  choose τ hτ using exists_forall_parityOn_incidence_eq_xor hG u
  refine ⟨∑ w, if χ w then τ w else 0, fun v => ?_⟩
  have hite (b x : Bool) : (if b then x else 0) = b * x := by cases b <;> rfl
  have key : parityOn (Multigraph.incidence ends v) (∑ w, if χ w then τ w else 0) =
      ∑ w, χ w * (decide (v = u) + decide (v = w)) := by
    rw [← parityOnAddMonoidHom_apply, map_sum]
    refine sum_congr rfl fun w _ => ?_
    rw [apply_ite (parityOnAddMonoidHom _), map_zero, parityOnAddMonoidHom_apply, hτ, hite]
    rfl
  have hv : ∑ w, χ w * decide (v = w) = χ v := by
    rw [sum_eq_single v (fun w _ hw => by rw [decide_eq_false (Ne.symm hw)]; exact mul_zero _)
      (by simp), decide_eq_true rfl]
    exact mul_one _
  rw [key, parityOn_eq_sum]
  simp only [mul_add, sum_add_distrib, ← sum_mul, hv]
  rfl

/-- **Satisfiable subsystems**: on a connected multigraph, the constraints of the vertices of any
set other than the set of all vertices are satisfiable, whatever the charges. -/
theorem exists_forall_mem_parityOn_incidence_eq (hG : (Multigraph.toSimpleGraph ends).Connected)
    (χ : V → Bool) {S : Finset V} (hS : S ≠ univ) :
    ∃ σ : E → Bool, ∀ v ∈ S, parityOn (Multigraph.incidence ends v) σ = χ v := by
  obtain ⟨u, hu⟩ : ∃ u, u ∉ S := by
    by_contra! h'
    exact hS (eq_univ_of_forall h')
  obtain ⟨σ, hσ⟩ := exists_forall_parityOn_incidence_eq hG χ u
  refine ⟨σ, fun v hv => ?_⟩
  rw [hσ, decide_eq_false (ne_of_mem_of_not_mem hv hu), Bool.and_false, Bool.false_xor]

end Parity

end Tseitin

/-! ### Tseitin formulas -/

section Formula

variable [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The **Tseitin formula** of the multigraph `ends` with charges `χ`
[Tseitin][Tseitin1983] [Urquhart][Urquhart1987]: a variable for each edge, and for each vertex `v`
the clauses of `CNF.parityOnEq` saying that the parity of the edges at `v` other than self-loops is
`χ v`. -/
noncomputable def CNF.tseitinFormula (ends : E → Sym2 V) (χ : V → Bool) : CNF E :=
  (univ : Finset V).toList.flatMap fun v => CNF.parityOnEq (Multigraph.incidence ends v) (χ v)

variable {ends : E → Sym2 V} {χ : V → Bool}

namespace CNF

/-- A clause belongs to `tseitinFormula ends χ` iff it belongs to the parity constraint
`parityOnEq (Multigraph.incidence ends v) (χ v)` of some vertex `v`. -/
theorem mem_tseitinFormula {c : Clause E} :
    c ∈ tseitinFormula ends χ ↔ ∃ v, c ∈ parityOnEq (Multigraph.incidence ends v) (χ v) := by
  simp [tseitinFormula]

/-- An assignment satisfies the Tseitin formula when its parity at every vertex is the charge. -/
theorem eval_tseitinFormula_eq_true_iff (σ : E → Bool) :
    (tseitinFormula ends χ).eval σ = true ↔
      ∀ v, parityOn (Multigraph.incidence ends v) σ = χ v := by
  simp [tseitinFormula, eval_flatMap_eq_true_iff, eval_parityOnEq_eq_true_iff]

/-- **Tseitin formulas with odd total charge are unsatisfiable**
[Urquhart][Urquhart1987]. -/
theorem not_satisfiable_tseitinFormula (h : parityOn univ χ = true) :
    ¬ (tseitinFormula ends χ).Satisfiable :=
  fun ⟨σ, hσ⟩ => by
    rw [Tseitin.parityOn_univ_eq_false_of_forall ((eval_tseitinFormula_eq_true_iff σ).1 hσ)] at h
    exact Bool.false_ne_true h

/-- On a connected multigraph, **the Tseitin formula is satisfiable exactly when the total charge
is even** [Urquhart][Urquhart1987]. -/
theorem satisfiable_tseitinFormula_iff (hG : (Multigraph.toSimpleGraph ends).Connected) :
    (tseitinFormula ends χ).Satisfiable ↔ parityOn univ χ = false := by
  refine ⟨fun ⟨σ, hσ⟩ => Tseitin.parityOn_univ_eq_false_of_forall
    ((eval_tseitinFormula_eq_true_iff σ).1 hσ), fun h => ?_⟩
  obtain ⟨u⟩ := hG.nonempty
  obtain ⟨σ, hσ⟩ := Tseitin.exists_forall_parityOn_incidence_eq hG χ u
  exact ⟨σ, (eval_tseitinFormula_eq_true_iff σ).2 fun v => by
    rw [hσ, h, Bool.false_and, Bool.false_xor]⟩

/-- A clause of a Tseitin formula has as many literals as some vertex has edges other than
self-loops. -/
private theorem exists_length_eq_of_mem_tseitinFormula {c : Clause E}
    (hc : c ∈ tseitinFormula ends χ) :
    ∃ v, c.length = #(Multigraph.incidence ends v) := by
  obtain ⟨v, hv⟩ := mem_tseitinFormula.1 hc
  exact ⟨v, length_of_mem_parityOnEq hv⟩

/-- If every vertex has at most `k` edges other than self-loops, the clauses of the Tseitin
formula have at most `k` literals. -/
theorem length_le_of_mem_tseitinFormula {k : ℕ} (hk : ∀ v, #(Multigraph.incidence ends v) ≤ k)
    {c : Clause E} (hc : c ∈ tseitinFormula ends χ) : c.length ≤ k := by
  obtain ⟨v, hv⟩ := exists_length_eq_of_mem_tseitinFormula hc
  exact hv ▸ hk v

/-- If every vertex has at most `k` edges other than self-loops, the Tseitin formula has at most
`|V| 2 ^ k` clauses. -/
theorem length_tseitinFormula_le {k : ℕ} (hk : ∀ v, #(Multigraph.incidence ends v) ≤ k) :
    (tseitinFormula ends χ).length ≤ Fintype.card V * 2 ^ k := by
  rw [tseitinFormula, List.length_flatMap, ← card_univ, ← length_toList]
  rw [← List.length_map (f := fun v => (parityOnEq (Multigraph.incidence ends v) (χ v)).length),
    ← smul_eq_mul]
  refine List.sum_le_length_nsmul _ _ fun n hn => ?_
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hn
  exact (length_parityOnEq_le _ _).trans (Nat.pow_le_pow_right two_pos (hk v))

/-- The variables of a Tseitin formula are edges. -/
theorem card_toFinset_vars_tseitinFormula_le :
    (tseitinFormula ends χ).vars.toFinset.card ≤ Fintype.card E :=
  card_le_univ _

end CNF

end Formula

end Cslib.Logic.PL
