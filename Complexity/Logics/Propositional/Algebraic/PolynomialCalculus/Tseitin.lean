/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Multigraph.CutSpace
public import Complexity.Logics.Propositional.Algebraic.CNF.Boolean
public import Complexity.Logics.Propositional.Algebraic.PolynomialCalculus.Invariant
public import Complexity.Logics.Propositional.Algebraic.PolynomialCalculus.Nullstellensatz
public import Complexity.Logics.Propositional.Tseitin
import Complexity.Foundations.Data.Finset.SymmDiff
import Complexity.Foundations.Data.MvPolynomial.Substitution
import Complexity.Logics.Propositional.Algebraic.CNF.Parity
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Polynomial calculus degree lower bound for Tseitin formulas

Let `ends : E → Sym2 V` be a connected multigraph and `χ : V → Bool` a charge with odd total. Over a
field `K` with `2 ≠ 0`, every polynomial calculus refutation of the Tseitin formula
`CNF.tseitinFormula ends χ`, given as its clause polynomials together with the Boolean axioms, has
degree at least `e(G) / 2`. Here `e(G)` (`Cslib.Multigraph.minBalancedCut`) is the expansion of
[Ben-Sasson and Wigderson][BenSassonWigderson2001], the least number of edges leaving a set of
between a third and two thirds of the vertices
(`Cslib.Logic.PL.Tseitin.minBalancedCut_le_two_mul_of_pc_refutableInDegree`). Since a
Nullstellensatz refutation of degree `d` gives a polynomial calculus refutation of degree `d`, the
same bound holds for the Nullstellensatz
(`Cslib.Logic.PL.Tseitin.minBalancedCut_le_two_mul_of_ns_refutableInDegree`). On expanders the
bound is linear in the number of vertices
(`Complexity.Logics.Propositional.Algebraic.PolynomialCalculus.TseitinExpander`).

**Sources.** That Tseitin formulas are hard for polynomial calculus over fields of characteristic
other than `2` is due to
[Buss, Grigoriev, Impagliazzo and Pitassi][BussGrigorievImpagliazzoPitassi2001], and, for the
Nullstellensatz, to [Grigoriev][Grigoriev1998]. [Buss and Nordström, §7.5.4][BussNordstrom2021]
record this hardness qualitatively, citing the former, and describe the `R`-operator method for
degree lower bounds. The quantitative form `e(G) ≤ 2 d`, with the expansion of Ben-Sasson and
Wigderson, is the form proved here; it is not taken from a checked source statement. The theorem
numbers and constants of the two original papers have not been checked against a copy.

Both hypotheses are needed. In characteristic `2` the clause polynomials add up to `1`, which is a
refutation of degree the largest number of edges at a vertex
(`Cslib.Logic.PL.CNF.ns_refutableInDegree_tseitinFormula_of_charP_two`). On a disconnected
multigraph, an isolated vertex with charge `1` contributes the empty clause, a refutation of degree
`0`, while `e(G)` can be positive.

## Proof

The proof is by the invariant method (`Cslib.Logic.PL.PC.IsProof.mem_of_degree_le`). The change of
variables `x ↦ (1 - y) / 2` takes `{0, 1}` to `{1, -1}`. Call a set of edges `D` a *small cut* if
it is the edge cut of a set `U` of fewer than a third of the vertices; on a connected multigraph
`U` is then unique, and the *sign* of `D` is `(-1) ^ χ(U)`, where `χ(U)` is the total charge of
`U`. Other sets of edges have sign `0`. For a set of edges `T`, the *sign functional* at `T` sends
a monomial to the sign of the symmetric difference of `T` and its variables of odd degree. The
polynomials `p` such that, after the change of variables, the sign functionals at all sets of at
most `d` edges vanish on `p` form a subspace. If `2 d < e(G)`, it contains the inputs of degree at
most `d`: the Boolean axioms, and the clause polynomials, whose terms cancel in pairs (this is
where `2 ≠ 0` is used). It is closed under multiplication by a variable within degree `d`, by a
re-basing argument: signs of small cuts are multiplicative while the cuts stay below `e(G)`. It
does not contain `1`, on which the sign functional at `∅` is `1`. So there is no refutation of
degree `d`.

## Main results

* `Cslib.Logic.PL.Tseitin.minBalancedCut_le_two_mul_of_pc_refutableInDegree`: over a field with
  `2 ≠ 0`, on a connected multigraph, polynomial calculus refutations of a Tseitin formula have
  degree at least `e(G) / 2`.
* `Cslib.Logic.PL.Tseitin.minBalancedCut_le_two_mul_of_ns_refutableInDegree`: the same bound for
  Nullstellensatz refutations.

## References

* [S. Buss, D. Grigoriev, R. Impagliazzo, T. Pitassi, *Linear gaps between degrees for the
  polynomial calculus modulo distinct primes*][BussGrigorievImpagliazzoPitassi2001]
* [S. Buss, J. Nordström, *Proof complexity and SAT solving*, §7.5.4][BussNordstrom2021]
* [D. Grigoriev, *Tseitin's tautologies and lower bounds for Nullstellensatz
  proofs*][Grigoriev1998]
* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow — resolution made
  simple*][BenSassonWigderson2001]
-/

public section

namespace Cslib.Logic.PL.Tseitin

open Finset MvPolynomial Cslib.Logic.PL.Algebraic
open scoped symmDiff

variable {V E K : Type*} [Field K]

/-! ### Signs -/

/-- The sign `(-1) ^ b` of a bit. -/
private def boolSign (b : Bool) : K := cond b (-1) 1

private theorem boolSign_xor (a b : Bool) :
    (boolSign (a ^^ b) : K) = boolSign a * boolSign b := by
  cases a <;> cases b <;> simp [boolSign]

private theorem boolSign_mul_self (b : Bool) : (boolSign b : K) * boolSign b = 1 := by
  cases b <;> simp [boolSign]

/-- The product of the signs of the bits of `y` in `B` is the sign of their parity. -/
private theorem prod_boolSign (B : Finset E) (y : E → Bool) :
    ∏ i ∈ B, (boolSign (y i) : K) = boolSign (parityOn B y) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp [boolSign]
  | insert i B hi ih => rw [prod_insert hi, ih, parityOn_insert hi, boolSign_xor]

/-! ### Signs of small cuts -/

section Cut

variable [Fintype V] [DecidableEq V] [Fintype E] {ends : E → Sym2 V} {χ : V → Bool}

/-- `D` is the edge cut of `U`, a set of fewer than a third of the vertices. -/
private def IsSmallCut (ends : E → Sym2 V) (D : Finset E) (U : Finset V) : Prop :=
  3 * #U < Fintype.card V ∧ Multigraph.edgeCut ends U = D

open scoped Classical in
/-- The sign of a set of edges `D`: if `D` is the edge cut of a set `U` of fewer than a third of
the vertices, the sign `(-1) ^ χ(U)` of the total charge of `U`; otherwise `0`. On a connected
multigraph such a `U` is unique (`Cslib.Logic.PL.Tseitin.eq_of_isSmallCut`). -/
private noncomputable def cutSign (ends : E → Sym2 V) (χ : V → Bool) (D : Finset E) : K :=
  if h : ∃ U, IsSmallCut ends D U then boolSign (parityOn h.choose χ) else 0

private theorem cutSign_of_not {D : Finset E} (h : ¬ ∃ U, IsSmallCut ends D U) :
    (cutSign ends χ D : K) = 0 := by
  simp only [cutSign, h, dite_false]

private theorem exists_of_cutSign_ne_zero {D : Finset E} (h : (cutSign ends χ D : K) ≠ 0) :
    ∃ U, IsSmallCut ends D U := by
  by_contra h'
  exact h (cutSign_of_not h')

/-- On a connected multigraph, two sets of fewer than a third of the vertices with the same edge
cut are equal. -/
private theorem eq_of_isSmallCut (hG : (Multigraph.toSimpleGraph ends).Connected) {D : Finset E}
    {U₁ U₂ : Finset V} (h₁ : IsSmallCut ends D U₁) (h₂ : IsSmallCut ends D U₂) : U₁ = U₂ := by
  classical
  have hU : Multigraph.edgeCut ends (U₁ ∆ U₂) = ∅ := by
    rw [Multigraph.edgeCut_symmDiff, h₁.2, h₂.2, symmDiff_self, bot_eq_empty]
  rcases Multigraph.eq_empty_or_eq_univ_of_edgeCut_eq_empty hG hU with h | h
  · exact symmDiff_eq_empty.1 h
  · have hcard : Fintype.card V ≤ #U₁ + #U₂ := by
      rw [← card_univ, ← h]
      exact card_symmDiff_le U₁ U₂
    have := h₁.1
    have := h₂.1
    omega

private theorem cutSign_of_isSmallCut (hG : (Multigraph.toSimpleGraph ends).Connected)
    {D : Finset E} {U : Finset V} (hU : IsSmallCut ends D U) :
    (cutSign ends χ D : K) = boolSign (parityOn U χ) := by
  have h : ∃ U, IsSmallCut ends D U := ⟨U, hU⟩
  simp only [cutSign, h, dite_true]
  rw [eq_of_isSmallCut hG h.choose_spec hU]

variable [DecidableEq E]

/-- **Signs of small cuts are multiplicative.** If `D₂` is a small cut and fewer than `e(G)` edges
lie in `D₁` and in `D₁ ∆ D₂`, the sign of `D₁ ∆ D₂` is the product of the signs. Both sides vanish
when `D₁` is not a small cut. -/
private theorem cutSign_symmDiff (hG : (Multigraph.toSimpleGraph ends).Connected)
    {D₁ D₂ : Finset E} {U₂ : Finset V} (h₂ : IsSmallCut ends D₂ U₂)
    (hD₁ : #D₁ < Multigraph.minBalancedCut ends)
    (hD : #(D₁ ∆ D₂) < Multigraph.minBalancedCut ends) :
    (cutSign ends χ (D₁ ∆ D₂) : K) = cutSign ends χ D₁ * cutSign ends χ D₂ := by
  rw [cutSign_of_isSmallCut hG h₂]
  by_cases h₁ : ∃ U₁, IsSmallCut ends D₁ U₁
  · obtain ⟨U₁, h₁⟩ := h₁
    have hcut : Multigraph.edgeCut ends (U₁ ∆ U₂) = D₁ ∆ D₂ := by
      rw [Multigraph.edgeCut_symmDiff, h₁.2, h₂.2]
    have hsmall : 3 * #(U₁ ∆ U₂) < Fintype.card V := by
      refine Multigraph.three_mul_card_lt_of_card_edgeCut_lt (hcut ▸ hD) ?_
      have := card_symmDiff_le U₁ U₂
      have := h₁.1
      have := h₂.1
      omega
    rw [cutSign_of_isSmallCut hG ⟨hsmall, hcut⟩, cutSign_of_isSmallCut hG h₁, parityOn_symmDiff,
      boolSign_xor]
  · rw [cutSign_of_not h₁, zero_mul]
    refine cutSign_of_not fun ⟨U, hU⟩ => h₁ ⟨U ∆ U₂, ?_, ?_⟩
    · refine Multigraph.three_mul_card_lt_of_card_edgeCut_lt (ends := ends) ?_ ?_
      · rwa [Multigraph.edgeCut_symmDiff, hU.2, h₂.2, symmDiff_symmDiff_cancel_right]
      · have := card_symmDiff_le U U₂
        have := hU.1
        have := h₂.1
        omega
    · rw [Multigraph.edgeCut_symmDiff, hU.2, h₂.2, symmDiff_symmDiff_cancel_right]

end Cut

/-! ### Variables of odd degree -/

/-- The variables of odd degree in a monomial. -/
private def oddSupp (m : E →₀ ℕ) : Finset E := {i ∈ m.support | m i % 2 = 1}

private theorem mem_oddSupp {m : E →₀ ℕ} {i : E} : i ∈ oddSupp m ↔ m i % 2 = 1 := by
  rw [oddSupp, mem_filter, Finsupp.mem_support_iff, and_iff_right_iff_imp]
  intro h h0
  rw [h0] at h
  exact absurd h (by decide)

@[simp] private theorem oddSupp_zero : oddSupp (0 : E →₀ ℕ) = ∅ := by
  ext i
  simp [mem_oddSupp]

/-- A monomial has at most as many variables of odd degree as its degree. -/
private theorem card_oddSupp_le {p : MvPolynomial E K} {m : E →₀ ℕ} (hm : m ∈ p.support) :
    #(oddSupp m) ≤ p.totalDegree := by
  refine le_trans ?_ (le_totalDegree hm)
  rw [card_eq_sum_ones, Finsupp.sum]
  refine (sum_le_sum fun i hi => ?_).trans (sum_le_sum_of_subset (filter_subset _ _))
  have := mem_oddSupp.1 hi
  omega

private theorem oddSupp_single_add [DecidableEq E] (e : E) (m : E →₀ ℕ) :
    oddSupp (Finsupp.single e 1 + m) = oddSupp m ∆ {e} := by
  ext i
  rw [mem_oddSupp, Finset.mem_symmDiff, mem_oddSupp, mem_singleton, Finsupp.add_apply]
  by_cases hi : i = e
  · subst hi
    simp only [Finsupp.single_eq_same, not_true_eq_false, and_false, false_or, true_and]
    omega
  · simp only [Finsupp.single_eq_of_ne hi, hi, zero_add, not_false_eq_true, and_true, false_and,
      or_false]

/-! ### The change of variables `x ↦ (1 - y) / 2` -/

/-- The change of variables `x ↦ (1 - y) / 2` from `{0, 1}` to `{1, -1}`. -/
private noncomputable def toSign : MvPolynomial E K →ₐ[K] MvPolynomial E K :=
  aeval fun i => C 2⁻¹ * (1 - X i)

private theorem toSign_X (i : E) : (toSign (X i) : MvPolynomial E K) = C 2⁻¹ * (1 - X i) :=
  aeval_X _ i

private theorem totalDegree_toSign_le (p : MvPolynomial E K) :
    (toSign p).totalDegree ≤ p.totalDegree := by
  refine totalDegree_aeval_le (fun i => ?_) p
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_sub _ _).trans ?_
  rw [totalDegree_one, totalDegree_X]
  exact max_le (Nat.zero_le 1) le_rfl

private theorem C_inv_two_mul_two (h2 : (2 : K) ≠ 0) :
    (C 2⁻¹ : MvPolynomial E K) * 2 = 1 := by
  rw [show (2 : MvPolynomial E K) = C 2 from (map_ofNat C 2).symm, ← C_mul, inv_mul_cancel₀ h2,
    C_1]

/-! ### The sign functionals -/

section Functional

variable [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {ends : E → Sym2 V}
  {χ : V → Bool}

/-- The sign functional at `T`: the linear functional sending each monomial `m` to the sign of
`oddSupp m ∆ T`. -/
private noncomputable def signFunctional (ends : E → Sym2 V) (χ : V → Bool) (T : Finset E) :
    MvPolynomial E K →ₗ[K] K :=
  (basisMonomials E K).constr K fun m => cutSign ends χ (oddSupp m ∆ T)

private theorem signFunctional_monomial (T : Finset E) (m : E →₀ ℕ) (c : K) :
    signFunctional ends χ T (monomial m c) = c * cutSign ends χ (oddSupp m ∆ T) := by
  have h : monomial m c = c • basisMonomials E K m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, signFunctional, Module.Basis.constr_basis, smul_eq_mul]

/-- Multiplying by a variable shifts the sign functional. -/
private theorem signFunctional_X_mul (T : Finset E) (e : E) (q : MvPolynomial E K) :
    signFunctional ends χ T (X e * q) = signFunctional ends χ (T ∆ {e}) q := by
  induction q using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [X, monomial_mul_monomial, one_mul, signFunctional_monomial, signFunctional_monomial,
      oddSupp_single_add, symmDiff_assoc, symmDiff_comm {e} T, ← symmDiff_assoc]
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq]

private theorem signFunctional_one (T : Finset E) :
    signFunctional ends χ T (1 : MvPolynomial E K) = cutSign ends χ T := by
  rw [← C_1, C_apply, signFunctional_monomial, one_mul, oddSupp_zero, ← bot_eq_empty,
    bot_symmDiff]

/-- The sign functional at `T` sends a multilinear monomial `∏_{i ∈ t} X i` to the sign of
`t ∆ T`. -/
private theorem signFunctional_prod_X (T t : Finset E) :
    signFunctional ends χ T (∏ i ∈ t, X i : MvPolynomial E K) = cutSign ends χ (t ∆ T) := by
  induction t using Finset.induction_on generalizing T with
  | empty => rw [prod_empty, signFunctional_one, ← bot_eq_empty, bot_symmDiff]
  | insert i t hi ih =>
    have hins : insert i t = {i} ∆ t := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp [Finset.mem_symmDiff, hi]
      · simp [Finset.mem_symmDiff, hj]
    rw [prod_insert hi, signFunctional_X_mul, ih, hins]
    congr 1
    rw [symmDiff_comm T {i}, symmDiff_left_comm, ← symmDiff_assoc]

/-- **Re-basing.** Let every monomial of `q` have at most `k` variables of odd degree, where
`k + 1 ≤ d` and `2 d < e(G)`. If the sign functionals at all sets of at most `d` edges vanish on
`q`, then so do those at sets of `d + 1` edges. -/
private theorem signFunctional_eq_zero (hG : (Multigraph.toSimpleGraph ends).Connected)
    {d k : ℕ} (hd : 2 * d < Multigraph.minBalancedCut ends) (hk : k + 1 ≤ d)
    {q : MvPolynomial E K} (hq : ∀ m ∈ q.support, #(oddSupp m) ≤ k)
    (h0 : ∀ A : Finset E, #A ≤ d → signFunctional ends χ A q = 0) {T : Finset E}
    (hT : #T ≤ d + 1) : signFunctional ends χ T q = 0 := by
  by_cases hex : ∃ m₀ ∈ q.support, (cutSign ends χ (oddSupp m₀ ∆ T) : K) ≠ 0
  · obtain ⟨m₀, hm₀, hne⟩ := hex
    obtain ⟨U₀, hU₀⟩ := exists_of_cutSign_ne_zero hne
    have key : ∀ m ∈ q.support, (cutSign ends χ (oddSupp m ∆ T) : K) =
        cutSign ends χ (oddSupp m ∆ oddSupp m₀) * cutSign ends χ (oddSupp m₀ ∆ T) := by
      intro m hm
      have h₁ := card_symmDiff_le (oddSupp m) (oddSupp m₀)
      have h₂ := card_symmDiff_le (oddSupp m) T
      have hm' := hq m hm
      have hm₀' := hq m₀ hm₀
      have hsplit : oddSupp m ∆ T = oddSupp m ∆ oddSupp m₀ ∆ (oddSupp m₀ ∆ T) := by
        rw [symmDiff_assoc, symmDiff_symmDiff_cancel_left]
      rw [hsplit]
      refine cutSign_symmDiff hG hU₀ (by omega) ?_
      rw [← hsplit]
      omega
    have hsum : signFunctional ends χ T q =
        signFunctional ends χ (oddSupp m₀) q * cutSign ends χ (oddSupp m₀ ∆ T) := by
      conv_lhs => rw [q.as_sum]
      conv_rhs => rw [q.as_sum]
      rw [map_sum, map_sum, sum_mul]
      refine sum_congr rfl fun m hm => ?_
      rw [signFunctional_monomial, signFunctional_monomial, key m hm, mul_assoc]
    rw [hsum, h0 _ ((hq m₀ hm₀).trans (by omega)), zero_mul]
  · simp only [not_exists, not_and, ne_eq, not_not] at hex
    conv_lhs => rw [q.as_sum]
    rw [map_sum]
    refine sum_eq_zero fun m hm => ?_
    rw [signFunctional_monomial, hex m hm, mul_zero]

private theorem signFunctional_toSign_X_mul (T : Finset E) (e : E) (p : MvPolynomial E K) :
    signFunctional ends χ T (toSign (X e * p)) =
      2⁻¹ * (signFunctional ends χ T (toSign p) -
        signFunctional ends χ (T ∆ {e}) (toSign p)) := by
  rw [map_mul, toSign_X, mul_assoc, sub_mul, one_mul, ← smul_eq_C_mul, map_smul, map_sub,
    signFunctional_X_mul, smul_eq_mul]

/-- The sign functionals vanish on the Boolean axioms after the change of variables. -/
private theorem signFunctional_toSign_boolAxiom (h2 : (2 : K) ≠ 0) (T : Finset E) (e : E) :
    signFunctional ends χ T (toSign (boolAxiom e : MvPolynomial E K)) = 0 := by
  have hC := C_inv_two_mul_two (E := E) h2
  have h : (toSign (boolAxiom e : MvPolynomial E K)) =
      C (2⁻¹ * 2⁻¹) * (X e * (X e * 1) - 1) := by
    rw [boolAxiom, map_sub, map_pow, toSign_X, C_mul]
    linear_combination (1 - X e) * C 2⁻¹ * hC
  rw [h, ← smul_eq_C_mul, map_smul, map_sub, signFunctional_X_mul, signFunctional_X_mul,
    symmDiff_symmDiff_cancel_right, sub_self, smul_zero]

/-- The sign functionals at sets of at most `d` edges vanish on the clauses of the parity
constraint at a vertex `v` after the change of variables, when `v` has at most `d` edges and
`2 d < e(G)`. This is where the characteristic matters: the terms cancel in pairs, and `2 ≠ 0`
turns `2 S = 0` into `S = 0`. -/
private theorem signFunctional_toSign_exclude (h2 : (2 : K) ≠ 0)
    (hG : (Multigraph.toSimpleGraph ends).Connected) {d : ℕ}
    (hd : 2 * d < Multigraph.minBalancedCut ends) {v : V} {B : Finset E}
    (hBv : Multigraph.incidence ends v = B) {y : E → Bool} (hy : parityOn B y ≠ χ v)
    (hB : #B ≤ d) {T : Finset E} (hT : #T ≤ d) :
    signFunctional ends χ T (toSign ((Clause.exclude B y).toBoolPoly K)) = 0 := by
  have hC := C_inv_two_mul_two (E := E) h2
  have hlit (i : E) : toSign (if y i then X i else 1 - X i : MvPolynomial E K) =
      C 2⁻¹ * (1 + C (boolSign (y i)) * X i) := by
    cases y i
    · simp only [Bool.false_eq_true, ite_false, map_sub, map_one, toSign_X, boolSign,
        Bool.cond_false]
      linear_combination -hC
    · simp only [ite_true, toSign_X, boolSign, Bool.cond_true, map_neg, map_one]
      ring
  have hpoly : toSign ((Clause.exclude B y).toBoolPoly K) =
      C (2⁻¹ ^ #B) * ∑ t ∈ B.powerset, ∏ i ∈ t, C (boolSign (y i)) * X i := by
    rw [Clause.toBoolPoly_exclude, map_prod, prod_congr rfl fun i _ => hlit i, prod_mul_distrib,
      prod_const, prod_one_add, C_pow]
  -- the terms of the expansion
  have hterm (t : Finset E) : signFunctional ends χ T (∏ i ∈ t, C (boolSign (y i)) * X i) =
      (∏ i ∈ t, (boolSign (y i) : K)) * cutSign ends χ (t ∆ T) := by
    rw [prod_mul_distrib, ← map_prod, ← smul_eq_C_mul, map_smul, signFunctional_prod_X,
      smul_eq_mul]
  rw [hpoly, ← smul_eq_C_mul, map_smul, map_sum, sum_congr rfl fun t _ => hterm t, smul_eq_mul]
  refine mul_eq_zero_of_right _ ?_
  -- the vertex `v` has a small cut
  have he : 0 < Multigraph.minBalancedCut ends := by omega
  have hn : 2 ≤ Fintype.card V := by
    by_contra hn
    have : Subsingleton V := Fintype.card_le_one_iff_subsingleton.1 (by omega)
    rw [Multigraph.minBalancedCut_eq_zero_of_subsingleton] at he
    exact lt_irrefl 0 he
  have hv : IsSmallCut ends B {v} := by
    refine ⟨Multigraph.three_mul_card_lt_of_card_edgeCut_lt (ends := ends) ?_ ?_, ?_⟩
    · rw [Multigraph.edgeCut_singleton, hBv]
      omega
    · rw [card_singleton]
      omega
    · rw [Multigraph.edgeCut_singleton, hBv]
  -- pairing `t` with `B \ t` flips the sign of the term
  have hflip : ∀ t ∈ B.powerset,
      (∏ i ∈ B \ t, (boolSign (y i) : K)) * cutSign ends χ ((B \ t) ∆ T) =
        -((∏ i ∈ t, (boolSign (y i) : K)) * cutSign ends χ (t ∆ T)) := by
    intro t ht
    rw [mem_powerset] at ht
    have hprod : ∏ i ∈ B \ t, (boolSign (y i) : K) =
        (∏ i ∈ B, (boolSign (y i) : K)) * ∏ i ∈ t, (boolSign (y i) : K) := by
      have h := prod_sdiff (f := fun i => (boolSign (y i) : K)) ht
      have ht2 : (∏ i ∈ t, (boolSign (y i) : K)) * ∏ i ∈ t, (boolSign (y i) : K) = 1 := by
        rw [prod_boolSign]
        exact boolSign_mul_self _
      linear_combination (∏ i ∈ t, (boolSign (y i) : K)) * h -
        (∏ i ∈ B \ t, (boolSign (y i) : K)) * ht2
    have hcut : (B \ t) ∆ T = (t ∆ T) ∆ B := by
      rw [← symmDiff_of_le ht, symmDiff_right_comm]
    have h₁ := card_symmDiff_le t T
    have h₂ := card_symmDiff_le (B \ t) T
    have h₃ : #(B \ t) ≤ #B := card_le_card Finset.sdiff_subset
    have h₄ : #t ≤ #B := card_le_card ht
    have hsign : (cutSign ends χ ((B \ t) ∆ T) : K) =
        cutSign ends χ (t ∆ T) * boolSign (χ v) := by
      rw [hcut, cutSign_symmDiff hG hv (by omega) (by rw [← hcut]; omega),
        cutSign_of_isSmallCut hG hv, parityOn_singleton]
    have hpar : (∏ i ∈ B, (boolSign (y i) : K)) * boolSign (χ v) = -1 := by
      rw [prod_boolSign, ← boolSign_xor]
      have : (parityOn B y ^^ χ v) = true := by
        revert hy
        cases parityOn B y <;> cases χ v <;> simp
      rw [this]
      rfl
    rw [hprod, hsign]
    linear_combination (∏ i ∈ t, (boolSign (y i) : K)) * cutSign ends χ (t ∆ T) * hpar
  set S := ∑ t ∈ B.powerset, (∏ i ∈ t, (boolSign (y i) : K)) * cutSign ends χ (t ∆ T) with hSdef
  have hS : S = -S := by
    rw [hSdef, ← sum_neg_distrib]
    refine sum_nbij' (B \ ·) (B \ ·) (fun t _ => mem_powerset.2 Finset.sdiff_subset)
      (fun t _ => mem_powerset.2 Finset.sdiff_subset)
      (fun t ht => Finset.sdiff_sdiff_eq_self (mem_powerset.1 ht))
      (fun t ht => Finset.sdiff_sdiff_eq_self (mem_powerset.1 ht)) ?_
    intro t ht
    rw [hflip t ht, neg_neg]
  have h2S : (2 : K) * S = 0 := by linear_combination hS
  exact (mul_eq_zero.1 h2S).resolve_left h2

/-- The polynomials on which, after the change of variables, the sign functionals at all sets of at
most `d` edges vanish. -/
private noncomputable def invariant (K : Type*) [Field K] (ends : E → Sym2 V) (χ : V → Bool)
    (d : ℕ) : Submodule K (MvPolynomial E K) where
  carrier := {p | ∀ T : Finset E, #T ≤ d → signFunctional ends χ T (toSign p) = 0}
  add_mem' {p q} hp hq T hT := by rw [map_add, map_add, hp T hT, hq T hT, add_zero]
  zero_mem' T _ := by rw [map_zero, map_zero]
  smul_mem' c p hp T hT := by rw [map_smul, map_smul, hp T hT, smul_zero]

private theorem mem_invariant {d : ℕ} {p : MvPolynomial E K} :
    p ∈ invariant K ends χ d ↔ ∀ T : Finset E, #T ≤ d → signFunctional ends χ T (toSign p) = 0 :=
  Iff.rfl

end Functional

variable [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {ends : E → Sym2 V}
  {χ : V → Bool}

/-- **The polynomial calculus degree lower bound for Tseitin formulas.** Over a field of
characteristic other than `2`, on a connected multigraph, every polynomial calculus refutation of a
Tseitin formula has degree at least half the expansion `e(G)`. That such formulas are hard over
these fields is due to
[Buss, Grigoriev, Impagliazzo and Pitassi][BussGrigorievImpagliazzoPitassi2001], and is recorded
qualitatively in [Buss and Nordström, §7.5.4][BussNordstrom2021]; the quantitative form
`e(G) ≤ 2 d` is the one proved here, not a checked source statement. -/
theorem minBalancedCut_le_two_mul_of_pc_refutableInDegree (h2 : (2 : K) ≠ 0)
    (hG : (Multigraph.toSimpleGraph ends).Connected) {d : ℕ}
    (h : PC.RefutableInDegree ((CNF.tseitinFormula ends χ).toBoolPolys K ++ boolAxioms E K) d) :
    Multigraph.minBalancedCut ends ≤ 2 * d := by
  by_contra! hd
  obtain ⟨ls, hls, h1, hdeg⟩ := h
  have hF : ∀ f ∈ (CNF.tseitinFormula ends χ).toBoolPolys K ++ boolAxioms E K,
      f.totalDegree ≤ d → f ∈ invariant K ends χ d := by
    intro f hf hfd
    rw [mem_invariant]
    intro T hT
    rcases List.mem_append.1 hf with hf | hf
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hf
      obtain ⟨v, hv⟩ := CNF.mem_tseitinFormula.1 hc
      obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hv
      rw [mem_toList, mem_filter] at hA
      rw [Clause.totalDegree_toBoolPoly_exclude] at hfd
      exact signFunctional_toSign_exclude h2 hG hd rfl hA.2 hfd hT
    · obtain ⟨e, rfl⟩ := mem_boolAxioms.1 hf
      exact signFunctional_toSign_boolAxiom h2 T e
  have hX : ∀ e, ∀ p ∈ invariant K ends χ d, (X e * p).totalDegree ≤ d →
      X e * p ∈ invariant K ends χ d := by
    intro e p hp hpd
    rw [mem_invariant] at hp ⊢
    intro T hT
    by_cases hp0 : p = 0
    · rw [hp0, mul_zero, map_zero, map_zero]
    have hdeg' : p.totalDegree + 1 ≤ d := by
      rwa [totalDegree_mul_of_isDomain (X_ne_zero e) hp0, totalDegree_X, add_comm] at hpd
    have hzero (A : Finset E) (hA : #A ≤ d + 1) : signFunctional ends χ A (toSign p) = 0 :=
      signFunctional_eq_zero hG hd hdeg'
        (fun m hm => (card_oddSupp_le hm).trans (totalDegree_toSign_le p)) hp hA
    rw [signFunctional_toSign_X_mul, hzero T (by omega),
      hzero _ ((card_symmDiff_le T {e}).trans (by rw [card_singleton]; omega)), sub_self,
      mul_zero]
  have hmem := hls.mem_of_degree_le hdeg _ hF hX 1 h1
  rw [mem_invariant] at hmem
  have hne : Nonempty V := hG.nonempty
  have hsmall : IsSmallCut ends ∅ (∅ : Finset V) :=
    ⟨by rw [card_empty, mul_zero]; exact Fintype.card_pos, Multigraph.edgeCut_empty ends⟩
  have h0 := hmem ∅ (by rw [card_empty]; exact Nat.zero_le d)
  rw [map_one, signFunctional_one, cutSign_of_isSmallCut hG hsmall, parityOn_empty] at h0
  exact one_ne_zero h0

/-- **The Nullstellensatz degree lower bound for Tseitin formulas.** Over a field of characteristic
other than `2`, on a connected multigraph, every Nullstellensatz refutation of a Tseitin formula
has degree at least half the expansion `e(G)`. Linear Nullstellensatz degree lower bounds for
Tseitin formulas are due to [Grigoriev][Grigoriev1998]; only the title and venue of that paper
have been checked, not its constant, and the quantitative form `e(G) ≤ 2 d` is the one proved
here. -/
theorem minBalancedCut_le_two_mul_of_ns_refutableInDegree (h2 : (2 : K) ≠ 0)
    (hG : (Multigraph.toSimpleGraph ends).Connected) {d : ℕ}
    (h : NS.RefutableInDegree ((CNF.tseitinFormula ends χ).toBoolPolys K ++ boolAxioms E K) d) :
    Multigraph.minBalancedCut ends ≤ 2 * d :=
  minBalancedCut_le_two_mul_of_pc_refutableInDegree h2 hG (PC.RefutableInDegree.of_ns h)

end Cslib.Logic.PL.Tseitin
