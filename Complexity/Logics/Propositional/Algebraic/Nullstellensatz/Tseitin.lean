/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Algebraic.CNF.Boolean
public import Complexity.Logics.Propositional.Algebraic.Nullstellensatz.Combination
public import Complexity.Logics.Propositional.Tseitin
import Complexity.Logics.Propositional.Algebraic.CNF.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.CharP.Two
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Tseitin formulas are easy for the Nullstellensatz in characteristic `2`

Over a ring of characteristic `2`, the clause polynomials of the Tseitin formula of a multigraph
with odd total charge add up to `1` (`Cslib.Logic.PL.CNF.sum_toBoolPolys_parityOnEq` at each
vertex, then the handshake argument). So if every vertex has at most `k` edges other than
self-loops, the formula has a Nullstellensatz refutation of degree `k`, with every multiplier `1`
and without the Boolean axioms
(`Cslib.Logic.PL.CNF.ns_refutableInDegree_tseitinFormula_of_charP_two`). No connectivity is
needed.

This is the easy side of the gap between characteristics of
[Buss, Grigoriev, Impagliazzo and Pitassi][BussGrigorievImpagliazzoPitassi2001]. In characteristic
other than `2`, Tseitin formulas on a connected multigraph need refutations of degree at least
`e(G) / 2` (`Cslib.Logic.PL.Tseitin.minBalancedCut_le_two_mul_of_pc_refutableInDegree`), which is
linear in the number of vertices on expanders of constant degree. So the hypothesis `2 ≠ 0` of the
lower bound cannot be dropped.

## Main results

* `Cslib.Logic.PL.CNF.ns_refutableInDegree_tseitinFormula_of_charP_two`: in characteristic `2`, a
  Tseitin formula with odd total charge whose vertices have at most `k` edges has a
  Nullstellensatz refutation of degree `k`.

## References

* [S. Buss, D. Grigoriev, R. Impagliazzo, T. Pitassi, *Linear gaps between degrees for the
  polynomial calculus modulo distinct primes*][BussGrigorievImpagliazzoPitassi2001]
-/

public section

namespace Cslib.Logic.PL.CNF

open Finset MvPolynomial

variable {V E R : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {ends : E → Sym2 V} {χ : V → Bool} [CommRing R] [CharP R 2]

/-- In characteristic `2`, **a Tseitin formula with odd total charge whose vertices have at most
`k` edges other than self-loops has a Nullstellensatz refutation of degree `k`**: its clause
polynomials add up to `1`. The Boolean axioms are not needed, and neither is connectivity. -/
theorem ns_refutableInDegree_tseitinFormula_of_charP_two {k : ℕ}
    (hk : ∀ v, #(Multigraph.incidence ends v) ≤ k) (h : parityOn univ χ = true) :
    NS.RefutableInDegree ((tseitinFormula ends χ).toBoolPolys R) k := by
  have h2 : (2 : MvPolynomial E R) = 0 := CharTwo.two_eq_zero
  -- the clauses, indexed by a vertex and an assignment of the wrong parity to its edges
  let f : (Σ _ : V, Finset E) → MvPolynomial E R := fun p =>
    (Clause.exclude (Multigraph.incidence ends p.1) fun i => decide (i ∈ p.2)).toBoolPoly R
  let s : Finset (Σ _ : V, Finset E) := univ.sigma fun v =>
    {A ∈ (Multigraph.incidence ends v).powerset |
      parityOn (Multigraph.incidence ends v) (fun i => decide (i ∈ A)) ≠ χ v}
  have hf : ∀ p ∈ s, f p ∈ (tseitinFormula ends χ).toBoolPolys R := by
    intro p hp
    rw [mem_sigma] at hp
    refine List.mem_map.2 ⟨_, mem_tseitinFormula.2 ⟨p.1, List.mem_map.2 ⟨p.2, ?_, rfl⟩⟩, rfl⟩
    rw [mem_toList]
    exact hp.2
  have hd : ∀ p ∈ s, (fun _ => (1 : MvPolynomial E R)) p ≠ 0 →
      (f p).totalDegree + ((fun _ => (1 : MvPolynomial E R)) p).totalDegree ≤ k := by
    intro p _ _
    rw [totalDegree_one, add_zero]
    exact (Clause.totalDegree_toBoolPoly_le _).trans
      ((Clause.length_exclude _ _).trans_le (hk p.1))
  obtain ⟨P, hP, hPd⟩ := NS.exists_isProof_of_sum s f (fun _ => 1) hf hd
  -- the total charge is odd
  have hcharge : ∑ v, (if χ v then (1 : MvPolynomial E R) else 0) = 1 := by
    have hodd : #{v | χ v = true} % 2 = 1 := by simpa [parityOn] using h
    obtain ⟨m, hm⟩ : ∃ m, #{v | χ v = true} = 2 * m + 1 :=
      ⟨_, (Nat.div_add_mod _ 2).symm.trans (by rw [hodd])⟩
    rw [sum_boole, hm]
    push_cast
    rw [h2, zero_mul, zero_add]
  -- the handshake argument: every edge other than a self-loop is at exactly two vertices
  have hhand : ∑ v, ∑ i ∈ Multigraph.incidence ends v, (X i : MvPolynomial E R) = 0 := by
    rw [sum_comm' (t' := univ) (s' := fun e => {v | v ∈ ends e ∧ ¬(ends e).IsDiag}) (by simp)]
    refine sum_eq_zero fun e _ => ?_
    obtain ⟨a, b, hab⟩ : ∃ a b, ends e = s(a, b) := Sym2.ind (f := fun z => ∃ a b, z = s(a, b))
      (fun a b => ⟨a, b, rfl⟩) (ends e)
    by_cases hab' : a = b
    · rw [filter_false_of_mem fun v _ => by simp [hab, hab'], sum_empty]
    · rw [show ({v | v ∈ ends e ∧ ¬(ends e).IsDiag} : Finset V) = {a, b} by
        ext v
        simp [hab, hab'], sum_pair hab']
      linear_combination X e * h2
  have h1 : ∑ p ∈ s, f p * 1 = 1 := by
    simp only [mul_one, s, f]
    rw [sum_sigma, sum_congr rfl fun v _ => sum_toBoolPoly_exclude_parityOn_ne (R := R)
      (Multigraph.incidence ends v) (χ v), sum_add_distrib, hcharge, hhand, add_zero]
  exact ⟨P, Eq.trans hP h1, hPd⟩

end Cslib.Logic.PL.CNF
