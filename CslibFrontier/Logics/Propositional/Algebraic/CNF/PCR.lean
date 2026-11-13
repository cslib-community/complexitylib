/-
Copyright (c) 2026 Vincent Palma, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.Propositional.Algebraic.CNF
public import CslibFrontier.Logics.Propositional.Algebraic.Boolean
public import CslibFrontier.Logics.Propositional.Resolution.Proof
import CslibFrontier.Foundations.Data.MvPolynomial.CoefficientDegree

/-!
# The squarefree CNF encoding for polynomial calculus resolution

`Clause.toPCRPoly` multiplies the complementary variables of the distinct literals of a
clause. It is the squarefree version of `Clause.toPoly`: repeating a literal leaves it unchanged,
and its degree is at most the clause's distinct-literal width. The coordinates continue to mean
literal truth values, as in `Literal.toPolyAssignment`.

`CNF.toPCRPolys` adds the Boolean equations `X l ^ 2 - X l` for both polarities and the
complementarity equations `X (v, true) + X (v, false) - 1`. Thus polynomial calculus on these
inputs is the usual twin-variable polynomial calculus resolution (PCR) of
[AlekhnovichBenSassonRazborovWigderson2002, §4.1]. The original list-based
`Clause.toPoly`, which retains repeated factors, is unchanged.

Every satisfying Boolean assignment gives a common zero of the complete encoding. Conversely,
over a field every common zero has Boolean, complementary coordinates and is a satisfying
assignment. Polynomial-calculus refutations are therefore sound over any nontrivial commutative
ring. Proof sizes and degrees use the existing `PC.IsProof`, `PC.size` and `PC.degree`.

## Main definitions

* `Cslib.Logic.PL.Clause.toPCRPoly`: the squarefree twin-variable clause polynomial.
* `Cslib.Logic.PL.PCR.complementAxiom`, `Cslib.Logic.PL.PCR.axioms`: complementarity and Boolean
  axioms.
* `Cslib.Logic.PL.CNF.toPCRPolys`: the complete polynomial input system of a CNF.

## Main results

* `Cslib.Logic.PL.Clause.card_support_toPCRPoly_le`: a clause polynomial has at most one monomial.
* `Cslib.Logic.PL.Clause.totalDegree_toPCRPoly_le`: its degree is bounded by clause width.
* `Cslib.Logic.PL.Clause.eval_toPCRPoly`: its value is zero for a satisfied clause and one
  otherwise.
* `Cslib.Logic.PL.CNF.eval_eq_true_iff_forall_eval_toPCRPolys_eq_zero`: exact assignment semantics.
* `Cslib.Logic.PL.CNF.exists_commonZero_toPCRPolys_iff`: common zeros over a field correspond to
  satisfying assignments.
* `Cslib.Logic.PL.CNF.not_satisfiable_of_pcr`: soundness of PCR refutations.

## References

* [M. Alekhnovich, E. Ben-Sasson, A. A. Razborov, A. Wigderson,
  *Space Complexity in Propositional Calculus*, §4.1][AlekhnovichBenSassonRazborovWigderson2002]
-/

public section

namespace Cslib.Logic.PL

open MvPolynomial

variable {V : Type*} [DecidableEq V]

/-- The squarefree polynomial of a clause: one complementary variable for each distinct literal.
In particular, repeated literals do not increase its degree. -/
@[expose] noncomputable def Clause.toPCRPoly (c : Clause V) (R : Type*) [CommSemiring R] :
    MvPolynomial (Literal V) R := ∏ l ∈ c.toFinset, X l.negate

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The defining product of the squarefree clause encoding. -/
theorem Clause.toPCRPoly_eq_prod (c : Clause V) :
    c.toPCRPoly R = ∏ l ∈ c.toFinset, X l.negate := rfl

/-- The empty clause has polynomial `1`. -/
@[simp] theorem Clause.toPCRPoly_nil : Clause.toPCRPoly ([] : Clause V) R = 1 := by
  simp [Clause.toPCRPoly]

/-- Clauses with the same distinct literals have the same squarefree polynomial. -/
theorem Clause.toPCRPoly_congr {c d : Clause V} (h : c.toFinset = d.toFinset) :
    c.toPCRPoly R = d.toPCRPoly R := by
  simp only [Clause.toPCRPoly, h]

/-- Adding a literal already present does not change the squarefree polynomial. -/
theorem Clause.toPCRPoly_cons_of_mem {l : Literal V} {c : Clause V} (hl : l ∈ c) :
    Clause.toPCRPoly (l :: c) R = c.toPCRPoly R := by
  simp [Clause.toPCRPoly, List.mem_toFinset.2 hl]

/-- Adding a new literal multiplies by its complementary variable. -/
theorem Clause.toPCRPoly_cons_of_not_mem {l : Literal V} {c : Clause V} (hl : l ∉ c) :
    Clause.toPCRPoly (l :: c) R = X l.negate * c.toPCRPoly R := by
  simp [Clause.toPCRPoly, hl]

/-- A squarefree clause polynomial has at most one supported monomial, over any coefficient
semiring, including the trivial one. -/
theorem Clause.card_support_toPCRPoly_le (c : Clause V) : (c.toPCRPoly R).support.card ≤ 1 := by
  classical
  have h : c.toPCRPoly R = monomial (∑ l ∈ c.toFinset, Finsupp.single l.negate 1) 1 := by
    rw [monomial_sum_one]
    rfl
  rw [h]
  exact (Finset.card_le_card support_monomial_subset).trans_eq (Finset.card_singleton _)

/-- The degree of the squarefree polynomial is at most the number of distinct literals. -/
theorem Clause.totalDegree_toPCRPoly_le (c : Clause V) : (c.toPCRPoly R).totalDegree ≤ c.width := by
  classical
  unfold Clause.toPCRPoly Clause.width
  calc
    _ ≤ ∑ l ∈ c.toFinset, (X l.negate : MvPolynomial (Literal V) R).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ ∑ _ ∈ c.toFinset, 1 := Finset.sum_le_sum fun l _ => totalDegree_X_le l.negate
    _ = _ := by simp

/-- A squarefree clause polynomial is zero at a satisfying Boolean assignment and one at a
falsifying assignment. -/
theorem Clause.eval_toPCRPoly (c : Clause V) (σ : V → Bool) :
    (c.toPCRPoly R).eval (Literal.toPolyAssignment R σ) = if c.eval σ then 0 else 1 := by
  classical
  rw [Clause.toPCRPoly, map_prod]
  by_cases hc : c.eval σ = true
  · obtain ⟨l, hl, he⟩ := (Clause.eval_eq_true_iff σ c).1 hc
    rw [hc]
    exact Finset.prod_eq_zero (List.mem_toFinset.2 hl) (by
      simp [Literal.toPolyAssignment, (Literal.eval_eq_true_iff σ l).2 he])
  · have hc' : c.eval σ = false := Bool.eq_false_iff.2 hc
    rw [hc']
    apply Finset.prod_eq_one
    intro l hl
    have h : Literal.eval σ l = false := by
      apply Bool.eq_false_iff.2
      intro h
      exact hc ((Clause.eval_eq_true_iff σ c).2
        ⟨l, List.mem_toFinset.1 hl, (Literal.eval_eq_true_iff σ l).1 h⟩)
    simp [Literal.toPolyAssignment, h]

/-- Satisfaction of a clause is equivalent to vanishing of its squarefree polynomial at the
same Boolean assignment. -/
theorem Clause.eval_eq_true_iff_eval_toPCRPoly_eq_zero [Nontrivial R] (c : Clause V)
    (σ : V → Bool) :
    c.eval σ = true ↔ (c.toPCRPoly R).eval (Literal.toPolyAssignment R σ) = 0 := by
  rw [Clause.eval_toPCRPoly]
  cases c.eval σ <;> simp

end CommSemiring

namespace PCR

omit [DecidableEq V]

variable {R : Type*} [CommRing R]

/-- The complementarity equation for the two literal coordinates of a variable. -/
@[expose] noncomputable def complementAxiom (v : V) : MvPolynomial (Literal V) R :=
  X (v, true) + X (v, false) - 1

/-- A complementarity equation has at most three supported monomials. -/
theorem card_support_complementAxiom_le (v : V) :
    (complementAxiom v : MvPolynomial (Literal V) R).support.card ≤ 3 := by
  classical
  have hmono (m : Literal V →₀ ℕ) (a : R) : (monomial m a).support.card ≤ 1 :=
    (Finset.card_le_card support_monomial_subset).trans_eq (Finset.card_singleton m)
  have hadd (p q : MvPolynomial (Literal V) R) :
      (p + q).support.card ≤ p.support.card + q.support.card :=
    (Finset.card_le_card support_add).trans (Finset.card_union_le _ _)
  unfold complementAxiom
  rw [sub_eq_add_neg]
  have h₁ := hadd (X (v, true)) (X (v, false))
  have h₂ := hadd (X (v, true) + X (v, false)) (-1)
  have h₃ : (X (v, true) : MvPolynomial (Literal V) R).support.card ≤ 1 := hmono _ _
  have h₄ : (X (v, false) : MvPolynomial (Literal V) R).support.card ≤ 1 := hmono _ _
  have h₅ : (-1 : MvPolynomial (Literal V) R).support.card ≤ 1 := by
    simpa only [support_neg, ← one_def] using hmono 0 1
  omega

/-- A complementarity equation has degree at most one. -/
theorem totalDegree_complementAxiom_le (v : V) :
    (complementAxiom v : MvPolynomial (Literal V) R).totalDegree ≤ 1 := by
  exact (totalDegree_sub _ _).trans
    (max_le ((totalDegree_add _ _).trans
      (max_le (totalDegree_X_le _) (totalDegree_X_le _))) (by simp))

variable (V R) in
/-- The PCR axioms: a complementarity equation for each original variable, followed by the
Boolean axioms for both literal coordinates. -/
@[expose] noncomputable def axioms [Fintype V] : List (MvPolynomial (Literal V) R) :=
  Finset.univ.toList.map complementAxiom ++ Algebraic.boolAxioms (Literal V) R

/-- Every complementarity equation occurs among the PCR axioms. -/
theorem complementAxiom_mem_axioms [Fintype V] (v : V) :
    (complementAxiom v : MvPolynomial (Literal V) R) ∈ axioms V R := by
  simp [axioms]

/-- Every Boolean equation for a literal coordinate occurs among the PCR axioms. -/
theorem boolAxiom_mem_axioms [Fintype V] (l : Literal V) :
    (Algebraic.boolAxiom l : MvPolynomial (Literal V) R) ∈ axioms V R :=
  List.mem_append_right _ (Algebraic.boolAxiom_mem_boolAxioms l)

/-- Complementarity equations vanish at the literal truth values of a Boolean assignment. -/
@[simp] theorem eval_complementAxiom (σ : V → Bool) (v : V) :
    eval (Literal.toPolyAssignment R σ) (complementAxiom v) = 0 := by
  cases h : σ v <;> simp [complementAxiom, h]

/-- Every PCR axiom vanishes at every Boolean assignment with complementary literal values. -/
theorem eval_eq_zero_of_mem_axioms [Fintype V] (σ : V → Bool)
    {p : MvPolynomial (Literal V) R} (hp : p ∈ axioms V R) :
    eval (Literal.toPolyAssignment R σ) p = 0 := by
  rcases List.mem_append.1 hp with hp | hp
  · obtain ⟨v, _, rfl⟩ := List.mem_map.1 hp
    exact eval_complementAxiom σ v
  · obtain ⟨l, rfl⟩ := Algebraic.mem_boolAxioms.1 hp
    obtain ⟨v, b⟩ := l
    cases b <;> cases h : σ v <;> simp [Algebraic.boolAxiom, h]

end PCR

section CommRing

variable {R : Type*} [CommRing R] [Fintype V]

/-- The squarefree clause polynomials followed by all complementarity and Boolean axioms. -/
@[expose] noncomputable def CNF.toPCRPolys (φ : CNF V) (R : Type*) [CommRing R] :
    List (MvPolynomial (Literal V) R) := φ.map (fun c => c.toPCRPoly R) ++ PCR.axioms V R

/-- The polynomial of every input clause occurs in the encoded PCR input system. -/
theorem CNF.toPCRPoly_mem_toPCRPolys {φ : CNF V} {c : Clause V} (hc : c ∈ φ) :
    c.toPCRPoly R ∈ φ.toPCRPolys R :=
  List.mem_append_left _ (List.mem_map.2 ⟨c, hc, rfl⟩)

/-- Every PCR axiom occurs in the encoded input system of every CNF. -/
theorem CNF.axioms_subset_toPCRPolys (φ : CNF V) : PCR.axioms V R ⊆ φ.toPCRPolys R :=
  fun _ hp => List.mem_append_right _ hp

/-- Boolean satisfaction of the CNF is equivalent to the vanishing of every encoded polynomial
at the corresponding literal truth values. -/
theorem CNF.eval_eq_true_iff_forall_eval_toPCRPolys_eq_zero [Nontrivial R] (φ : CNF V)
    (σ : V → Bool) :
    φ.eval σ = true ↔
      ∀ p ∈ φ.toPCRPolys R, MvPolynomial.eval (Literal.toPolyAssignment R σ) p = 0 := by
  constructor
  · intro hφ p hp
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
      exact (Clause.eval_eq_true_iff_eval_toPCRPoly_eq_zero c σ).1
        ((CNF.eval_eq_true_iff σ φ).1 hφ c hc)
    · exact PCR.eval_eq_zero_of_mem_axioms σ hp
  · intro h
    apply (CNF.eval_eq_true_iff σ φ).2
    intro c hc
    exact (Clause.eval_eq_true_iff_eval_toPCRPoly_eq_zero c σ).2
      (h _ (CNF.toPCRPoly_mem_toPCRPolys hc))

/-- A PCR refutation of the complete squarefree encoding rules out every satisfying assignment.
This soundness statement needs only a nontrivial commutative coefficient ring. -/
theorem CNF.not_satisfiable_of_pcr [Nontrivial R] {φ : CNF V}
    {ls : List (MvPolynomial (Literal V) R)} (h : PC.IsProof (φ.toPCRPolys R) ls)
    (h1 : 1 ∈ ls) : ¬ φ.Satisfiable := by
  rintro ⟨σ, hσ⟩
  obtain ⟨p, hp, hne⟩ := h.exists_eval_ne_zero h1 (Literal.toPolyAssignment R σ)
  exact hne ((CNF.eval_eq_true_iff_forall_eval_toPCRPolys_eq_zero φ σ).1 hσ p hp)

end CommRing

section Field

variable {K : Type*} [Field K] [Fintype V]

omit [DecidableEq V] in
/-- Over a field, a common zero of the PCR axioms is the literal truth-value assignment of a
Boolean assignment. -/
theorem PCR.exists_toPolyAssignment_eq_of_eval_axioms_eq_zero (z : Literal V → K)
    (hz : ∀ p ∈ PCR.axioms V K, eval z p = 0) :
    ∃ σ : V → Bool, Literal.toPolyAssignment K σ = z := by
  classical
  let σ : V → Bool := fun v => decide (z (v, true) = 1)
  have hbool (v : V) : z (v, true) = 0 ∨ z (v, true) = 1 := by
    have hb := hz _ (PCR.boolAxiom_mem_axioms (v, true))
    have hh : z (v, true) * (z (v, true) - 1) = 0 := by
      simpa [Algebraic.boolAxiom, pow_two, mul_sub] using hb
    rcases mul_eq_zero.1 hh with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have hpos (v : V) : Literal.toPolyAssignment K σ (v, true) = z (v, true) := by
    rcases hbool v with h | h <;> simp [Literal.toPolyAssignment_pos, σ, h]
  refine ⟨σ, funext ?_⟩
  rintro ⟨v, b⟩
  cases b
  · have hc : z (v, true) + z (v, false) = 1 := by
      exact sub_eq_zero.1 (by simpa [PCR.complementAxiom] using
        (hz _ (PCR.complementAxiom_mem_axioms v)))
    have hn : z (v, false) = 1 - z (v, true) :=
      eq_sub_iff_add_eq.2 (by simpa [add_comm] using hc)
    rw [Literal.toPolyAssignment_neg_eq_one_sub, hn, ← hpos]
    simp
  · exact hpos v

/-- Over a field, the complete squarefree PCR system has a common zero exactly when the CNF is
satisfiable. -/
theorem CNF.exists_commonZero_toPCRPolys_iff (φ : CNF V) :
    (∃ z : Literal V → K, ∀ p ∈ φ.toPCRPolys K, MvPolynomial.eval z p = 0) ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨σ, rfl⟩ := PCR.exists_toPolyAssignment_eq_of_eval_axioms_eq_zero z
      (fun p hp => hz p (φ.axioms_subset_toPCRPolys hp))
    exact ⟨σ, (CNF.eval_eq_true_iff_forall_eval_toPCRPolys_eq_zero φ σ).2 hz⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨Literal.toPolyAssignment K σ,
      (CNF.eval_eq_true_iff_forall_eval_toPCRPolys_eq_zero φ σ).1 hσ⟩

end Field

end Cslib.Logic.PL
