/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Moser
public import Complexity.Probability.LocalLemma
import Complexity.Logics.Propositional.CNF.Eval

/-!
# The Lovász Local Lemma for `k`-SAT

A uniformly random assignment falsifies a clause on `k` distinct variables with probability
`2 ^ (-k)` (`Cslib.Logic.PL.Clause.toOuterMeasure_pi_setOf_eval_eq_false`), and the event that it
does depends only on the variables of the clause. Two such events share a variable exactly when the
clauses do (`Cslib.Logic.PL.Moser.Shares`). The symmetric Local Lemma
[Alon and Spencer, Corollary 5.1.2][AlonSpencer2016], in its form for events determined by
independent coordinates [MoserTardos2010] (`Cslib.Probability.PMF.pi_iInter_compl_pos`), then shows
that an exact `k`-CNF in which every clause shares a variable with at most `d` other clauses is
satisfiable as soon as `e (d + 1) ≤ 2 ^ k`
(`Cslib.Logic.PL.CNF.IsExactDistinct.satisfiable_of_exp_mul_le`). This is the standard application
of the Local Lemma to `k`-SAT.

This existential bound is weaker in kind but stronger in its constant than the constructive bound
`d < 2 ^ (k - 3)` of `Cslib.Logic.PL.Moser.satisfiable_of_degree_lt`, which comes from Moser's
algorithm and its entropy-compression analysis: for `k ≥ 3`, `d < 2 ^ (k - 3)` implies
`e (d + 1) ≤ 2 ^ k`, since `e < 8`.

## Main results

* `Cslib.Logic.PL.Clause.toOuterMeasure_pi_setOf_eval_eq_false`: the probability that a clause on
  distinct variables is falsified.
* `Cslib.Logic.PL.CNF.IsExactDistinct.satisfiable_of_exp_mul_le`: the Local Lemma for `k`-SAT.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Chapter 5][AlonSpencer2016]
* [R. A. Moser, G. Tardos, *A constructive proof of the general Lovász Local Lemma*]
  [MoserTardos2010]
-/

public section

namespace Cslib.Logic.PL

open Finset Cslib.Probability

/-- A uniformly random assignment falsifies a clause whose literals are on distinct variables with
probability `2 ^ (-|c|)`. -/
theorem Clause.toOuterMeasure_pi_setOf_eval_eq_false {V : Type*} [Fintype V] {c : Clause V}
    (hc : (c.map Prod.fst).Nodup) :
    (PMF.pi fun _ : V => PMF.uniformOfFintype Bool).toOuterMeasure {σ | Clause.eval σ c = false} =
      2⁻¹ ^ c.length := by
  induction c with
  | nil =>
    simp only [Clause.eval_nil, Set.ofPred_true, List.length_nil, pow_zero]
    rw [PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe]
  | cons l c ih =>
    rw [List.map_cons, List.nodup_cons] at hc
    have hset : {σ : V → Bool | Clause.eval σ (l :: c) = false} =
        {σ | σ l.1 = !l.2} ∩ {σ | Clause.eval σ c = false} := by
      ext σ
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Clause.eval_cons, Bool.or_eq_false_iff,
        Literal.eval, beq_eq_false_iff_ne]
      cases σ l.1 <;> cases l.2 <;> simp
    have hdisj : Disjoint ({l.1} : Set V) {v | v ∈ c.map Prod.fst} :=
      Set.disjoint_singleton_left.2 hc.1
    rw [hset, PMF.toOuterMeasure_pi_inter_eq_mul _ hdisj
      (fun σ τ h => by simp only [Set.mem_ofPred_eq, h l.1 rfl])
      (fun σ τ h => by
        simp only [Set.mem_ofPred_eq,
          Clause.eval_congr fun l hl => h l.1 (List.mem_map_of_mem hl)]),
      ih hc.2, List.length_cons, pow_succ, mul_comm]
    congr 1
    have h := PMF.toOuterMeasure_map_apply (fun σ : V → Bool => σ l.1)
      (PMF.pi fun _ : V => PMF.uniformOfFintype Bool) {!l.2}
    rw [PMF.pi_map_eval] at h
    rw [show {σ : V → Bool | σ l.1 = !l.2} = (fun σ => σ l.1) ⁻¹' {!l.2} from rfl, ← h,
      PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
    simp

/-- **The Lovász Local Lemma for `k`-SAT**, by the symmetric Local Lemma
[Alon and Spencer, Corollary 5.1.2][AlonSpencer2016]: if every clause of an exact `k`-CNF shares a
variable with at most `d` other clauses and `e (d + 1) ≤ 2 ^ k`, the formula is satisfiable. -/
theorem CNF.IsExactDistinct.satisfiable_of_exp_mul_le {n k d : ℕ} {φ : CNF (Fin n)}
    (hφ : φ.IsExactDistinct k) (hdeg : ∀ i : Fin φ.length, Moser.degree φ i ≤ d)
    (hlll : Real.exp 1 * (d + 1) ≤ 2 ^ k) : φ.Satisfiable := by
  classical
  let A (i : Fin φ.length) : Set (Fin n → Bool) := {σ | φ[i].eval σ = false}
  let vbl (i : Fin φ.length) : Finset (Fin n) := (φ[i].map Prod.fst).toFinset
  have hpos := PMF.pi_iInter_compl_pos (fun _ : Fin n => PMF.uniformOfFintype Bool) A vbl
    (fun i σ τ h => by
      simp only [A, Set.mem_ofPred_eq]
      rw [Clause.eval_congr fun l hl => h l.1
        (Finset.mem_coe.2 (List.mem_toFinset.2 (List.mem_map_of_mem hl)))])
    (d := d) (fun i => by
      refine le_of_eq_of_le (congrArg card (filter_congr fun j _ => ?_)) (hdeg i)
      simp only [vbl, Moser.Shares, Finset.not_disjoint_iff, List.mem_toFinset])
    (q := 2⁻¹ ^ k) (fun i => by
      have hi := hφ _ (Moser.getElem_mem_fin i)
      rw [show A i = {σ | φ[i].eval σ = false} from rfl,
        Clause.toOuterMeasure_pi_setOf_eval_eq_false hi.2, hi.1]
      simp)
    (by
      rw [inv_pow, mul_comm (Real.exp 1), mul_assoc, inv_mul_le_iff₀ (by positivity), mul_one]
      exact hlll)
  obtain ⟨σ, hσ⟩ : (⋂ i, (A i)ᶜ).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    simp [h] at hpos
  refine ⟨σ, (CNF.eval_eq_true_iff σ φ).2 fun c hc => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have h := Set.mem_iInter.1 hσ ⟨i, hi⟩
  simpa [A] using h

end Cslib.Logic.PL
