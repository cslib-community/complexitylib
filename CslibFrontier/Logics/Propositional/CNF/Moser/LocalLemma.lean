/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.Moser
public import CslibFrontier.Probability.MoserTardos.Lopsided
public import CslibFrontier.Probability.MoserTardos.Parallel
import CslibFrontier.Logics.Propositional.CNF.Eval
import CslibFrontier.Logics.Propositional.CNF.LocalLemma

/-!
# Constructive Lovász Local Lemma for `k`-SAT via Moser–Tardos

This module instantiates the constructive Moser–Tardos theorems (`Cslib.Probability.MoserTardos`)
for exact `k`-CNF formulas (`CNF.IsExactDistinct`), using independent fair coin flips per variable
(`MoserTardos.table fairCoin`).

* Under the symmetric local lemma bound `e (d + 1) ≤ 2 ^ k` (using `Moser.degree`), any valid
  clause-resampling rule resamples each clause at most `1 / d` times in expectation (`1 ≤ d`) and
  at most `φ.length / d` times in total, and stops almost surely (for all `d : ℕ`, including for
  `firstViolatedRule`, matching `CNF.IsExactDistinct.satisfiable_of_exp_mul_le`). Compare with
  `Cslib.Logic.PL.Moser.lintegral_resamplings_le` under the entropy-compression condition
  `r < 2 ^ (k - 3)`.
* Under the slack symmetric bound `e (d + 1) ≤ (1 - ε) * 2 ^ k`, the parallel Moser–Tardos
  algorithm (`MoserTardos.Parallel`) terminates in `O(log (φ.length / d) / ε)` expected parallel
  rounds for every valid parallel selection rule, including the computable greedy MIS rule
  `Moser.greedyParallelCNF`.
* Using **lopsided Moser–Tardos** (`MoserTardos.Lopsided`, [MoserTardos2010, Section 6]), we show
  that two violated clause events can only be lopsidependent when they *conflict*
  (`Moser.Conflicts`: one contains a literal and the other its negation). Thus `e (d' + 1) ≤ 2 ^ k`
  in terms of `Moser.conflictDegree` suffices constructively with the same resampling bounds and
  `φ.Satisfiable`.

## Main definitions

* `Cslib.Logic.PL.Moser.fairCoin`, `Cslib.Logic.PL.Moser.clauseVbl`,
  `Cslib.Logic.PL.Moser.violated`: the uniform product measure and violated-clause events.
* `Cslib.Logic.PL.Moser.firstViolatedRule`: deterministic sequential selection rule picking the
  first violated clause.
* `Cslib.Logic.PL.Moser.greedyParallelCNF`: computable greedy maximal independent set parallel
  selection rule for CNF clauses.
* `Cslib.Logic.PL.Moser.Conflicts`, `Cslib.Logic.PL.Moser.conflictDegree`: clause conflicts and
  conflict-graph degree.

## Main results

* `Cslib.Logic.PL.Moser.lintegral_resamplings_le_of_exp_mul_le`,
  `Cslib.Logic.PL.Moser.lintegral_sum_resamplings_le_of_exp_mul_le`: expected resampling bounds
  (`1 / d` per clause, `φ.length / d` total) under `e (d + 1) ≤ 2 ^ k` (`1 ≤ d`).
* `Cslib.Logic.PL.Moser.ae_exists_eval_run_firstViolated_of_exp_mul_le`: almost sure termination of
  `firstViolatedRule` at a satisfying assignment.
* `Cslib.Logic.PL.Moser.isValidParallelRule_greedyParallelCNF`,
  `Cslib.Logic.PL.Moser.lintegral_parallelRounds_le_of_exp_mul_le_of_pos`,
  `Cslib.Logic.PL.Moser.lintegral_parallelRounds_le_of_exp_mul_le`,
  `Cslib.Logic.PL.Moser.ae_exists_eval_parallelRun_of_exp_mul_le`,
  `Cslib.Logic.PL.Moser.ae_exists_eval_parallelRun_greedy_of_exp_mul_le`: constructive parallel
  `k`-SAT expected-round bounds and almost sure termination under `e (d + 1) ≤ (1 - ε) * 2 ^ k`.
* `Cslib.Logic.PL.Moser.not_lopsidependent_of_not_conflicts`: non-conflicting clauses are not
  lopsidependent.
* `Cslib.Logic.PL.Moser.lintegral_resamplings_le_of_conflict_exp_mul_le`,
  `Cslib.Logic.PL.Moser.lintegral_sum_resamplings_le_of_conflict_exp_mul_le`,
  `Cslib.Logic.PL.Moser.ae_exists_eval_run_firstViolated_of_conflict_exp_mul_le`,
  `Cslib.Logic.PL.CNF.IsExactDistinct.satisfiable_of_conflict_exp_mul_le`: constructive lopsided
  `k`-SAT bounds and satisfiability under `e (d' + 1) ≤ 2 ^ k` on `conflictDegree`.

## References

* [R. A. Moser, G. Tardos, *A constructive proof of the general Lovász Local Lemma*]
  [MoserTardos2010, Sections 1, 4, 6]
-/

public section

namespace Cslib.Logic.PL

open Finset MeasureTheory ProbabilityTheory Cslib.Probability
open scoped ENNReal

namespace Moser

section Setup

variable {n : ℕ}

/-- Fair coin probability measure on a single Boolean variable. -/
noncomputable def fairCoin : Fin n → Measure Bool :=
  fun _ => (Cslib.Probability.PMF.uniformOfFintype Bool).toMeasure

instance (v : Fin n) : IsProbabilityMeasure (fairCoin (n := n) v) := by
  unfold fairCoin
  infer_instance

/-- Variables occurring in clause `i` of `φ`. -/
@[expose] def clauseVbl (φ : CNF (Fin n)) (i : Fin φ.length) : Finset (Fin n) :=
  (vbl φ[i]).toFinset

/-- The event that clause `i` of `φ` evaluates to `false`. -/
def violated (φ : CNF (Fin n)) (i : Fin φ.length) : Set (Fin n → Bool) :=
  {σ | φ[i].eval σ = false}

theorem violated_dependsOn (φ : CNF (Fin n)) (i : Fin φ.length) :
    DependsOn (· ∈ violated φ i) (clauseVbl φ i : Set (Fin n)) := by
  intro σ τ h
  simp only [violated, Set.mem_ofPred_eq]
  rw [Clause.eval_congr fun l hl =>
    h l.1 (Finset.mem_coe.2 (List.mem_toFinset.2 (List.mem_map_of_mem hl)))]

theorem measurableSet_violated (φ : CNF (Fin n)) (i : Fin φ.length) :
    MeasurableSet (violated φ i) :=
  measurableSet_preimage (measurable_of_finite _) (measurableSet_singleton false)

theorem measureReal_violated {k : ℕ} {φ : CNF (Fin n)} (hφ : φ.IsExactDistinct k)
    (i : Fin φ.length) :
    (Measure.pi (fairCoin (n := n))).real (violated φ i) = 2⁻¹ ^ k := by
  have hi := hφ _ (getElem_mem_fin i)
  have hfc : fairCoin (n := n) =
      fun _ => (Cslib.Probability.PMF.uniformOfFintype Bool).toMeasure := rfl
  rw [hfc, ← MoserTardos.toReal_toOuterMeasure_pi_eq_measureReal _
      (measurableSet_violated φ i),
    violated, Clause.toOuterMeasure_pi_setOf_eval_eq_false hi.2, hi.1]
  simp

/-- Deterministic selection rule picking the first clause violated in the current assignment. -/
@[expose] def firstViolatedRule (φ : CNF (Fin n)) :
    (∀ p : Fin n × ℕ, (fun _ : Fin n => Bool) p.1) → List (Fin φ.length) →
      Option (Fin φ.length) :=
  fun T w => (List.finRange φ.length).find? fun i =>
    !φ[i].eval (MoserTardos.current (clauseVbl φ) T w)

theorem firstViolatedRule_eq_some {φ : CNF (Fin n)}
    {T : ∀ p : Fin n × ℕ, (fun _ : Fin n => Bool) p.1} {w : List (Fin φ.length)}
    {i : Fin φ.length} (h : firstViolatedRule φ T w = some i) :
    MoserTardos.current (clauseVbl φ) T w ∈ violated φ i := by
  simpa [firstViolatedRule, violated] using List.find?_some h

theorem firstViolatedRule_eq_none {φ : CNF (Fin n)}
    {T : ∀ p : Fin n × ℕ, (fun _ : Fin n => Bool) p.1} {w : List (Fin φ.length)}
    (h : firstViolatedRule φ T w = none) :
    φ.eval (MoserTardos.current (clauseVbl φ) T w) = true := by
  rw [CNF.eval_eq_true_iff]
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hfi := List.find?_eq_none.1 h ⟨i, hi⟩ (List.mem_finRange _)
  simpa using hfi

theorem firstViolatedRule_notMem_violated {φ : CNF (Fin n)}
    {T : ∀ p : Fin n × ℕ, (fun _ : Fin n => Bool) p.1} {w : List (Fin φ.length)}
    (h : firstViolatedRule φ T w = none) (i : Fin φ.length) :
    MoserTardos.current (clauseVbl φ) T w ∉ violated φ i := by
  have hev := (CNF.eval_eq_true_iff _ φ).1 (firstViolatedRule_eq_none h) φ[i] (getElem_mem_fin i)
  simpa [violated] using hev

private theorem exp_mul_inv_pow_le {k d : ℕ} {r : ℝ}
    (hlll : Real.exp 1 * (d + 1) ≤ r * 2 ^ k) :
    Real.exp 1 * (2⁻¹ ^ k : ℝ) * (d + 1) ≤ r := by
  rw [inv_pow, mul_comm (Real.exp 1), mul_assoc, inv_mul_le_iff₀ (by positivity)]
  simpa [mul_comm r] using hlll

private theorem card_fin_mul_inv_le_ofReal {m d : ℕ} {x : ℝ≥0∞}
    (hx : x ≤ Fintype.card (Fin m) * ENNReal.ofReal (1 / (d : ℝ))) :
    x ≤ ENNReal.ofReal ((m : ℝ) / (d : ℝ)) := by
  refine hx.trans_eq ?_
  rw [Fintype.card_fin, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_one_div]

private theorem ae_eval_of_ae_notMem_violated (φ : CNF (Fin n))
    (trace : (∀ p : Fin n × ℕ, (fun _ : Fin n => Bool) p.1) → ℕ → List (Fin φ.length))
    (hae : ∀ᵐ T ∂MoserTardos.table (fairCoin (n := n)),
      ∃ N, ∀ i, MoserTardos.current (clauseVbl φ) T (trace T N) ∉ violated φ i) :
    ∀ᵐ T ∂MoserTardos.table (fairCoin (n := n)),
      ∃ N, φ.eval (MoserTardos.current (clauseVbl φ) T (trace T N)) = true := by
  filter_upwards [hae] with T ⟨N, hN⟩
  refine ⟨N, (CNF.eval_eq_true_iff _ φ).2 fun c hc => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hvi := hN ⟨i, hi⟩
  simp only [violated, Set.mem_ofPred_eq, Bool.not_eq_false] at hvi
  exact hvi

end Setup

section StandardMT

variable {n : ℕ}

private theorem shares_iff_not_disjoint (φ : CNF (Fin n)) (i j : Fin φ.length) :
    Shares φ[i] φ[j] ↔ ¬Disjoint (clauseVbl φ i) (clauseVbl φ j) := by
  simp only [Shares, clauseVbl, Finset.not_disjoint_iff, List.mem_toFinset]

private theorem degree_card_le {d : ℕ} {φ : CNF (Fin n)}
    (hdeg : ∀ i : Fin φ.length, degree φ i ≤ d) (i : Fin φ.length) :
    #{j : Fin φ.length | j ≠ i ∧ ¬Disjoint (clauseVbl φ i) (clauseVbl φ j)} ≤ d := by
  refine le_of_eq_of_le (congrArg card (filter_congr fun j _ => ?_)) (hdeg i)
  exact (and_congr_right fun _ => (shares_iff_not_disjoint φ i j).symm)

/-- Under `e (d + 1) ≤ 2 ^ k` with `1 ≤ d`, any valid clause-resampling rule resamples clause `i`
at most `1 / d` times in expectation. -/
theorem lintegral_resamplings_le_of_exp_mul_le {k d : ℕ} {φ : CNF (Fin n)}
    (hφ : φ.IsExactDistinct k) (hdpos : 1 ≤ d) (hdeg : ∀ i : Fin φ.length, degree φ i ≤ d)
    (hlll : Real.exp 1 * (d + 1) ≤ 2 ^ k)
    {sel : (∀ p : Fin n × ℕ, (fun _ : Fin n => Bool) p.1) → List (Fin φ.length) →
      Option (Fin φ.length)}
    (hsel : ∀ T w i, sel T w = some i → MoserTardos.current (clauseVbl φ) T w ∈ violated φ i)
    (i : Fin φ.length) :
    ∫⁻ T, MoserTardos.resamplings (α := fun _ : Fin n => Bool) sel i T
      ∂MoserTardos.table (fairCoin (n := n)) ≤ ENNReal.ofReal (1 / (d : ℝ)) :=
  MoserTardos.lintegral_resamplings_le_symmetric (fairCoin (n := n)) (clauseVbl φ) (violated φ)
    (measurableSet_violated φ) (violated_dependsOn φ) hdpos (degree_card_le hdeg)
    (fun j => (measureReal_violated hφ j).le) (exp_mul_inv_pow_le (by simpa using hlll)) hsel i

/-- Under `e (d + 1) ≤ 2 ^ k` with `1 ≤ d`, the expected total number of resamplings of any valid
clause-resampling rule is at most `φ.length / d`. -/
theorem lintegral_sum_resamplings_le_of_exp_mul_le {k d : ℕ} {φ : CNF (Fin n)}
    (hφ : φ.IsExactDistinct k) (hdpos : 1 ≤ d) (hdeg : ∀ i : Fin φ.length, degree φ i ≤ d)
    (hlll : Real.exp 1 * (d + 1) ≤ 2 ^ k)
    {sel : (∀ p : Fin n × ℕ, (fun _ : Fin n => Bool) p.1) → List (Fin φ.length) →
      Option (Fin φ.length)}
    (hsel : ∀ T w i, sel T w = some i → MoserTardos.current (clauseVbl φ) T w ∈ violated φ i) :
    ∫⁻ T, ∑ i, MoserTardos.resamplings (α := fun _ : Fin n => Bool) sel i T
      ∂MoserTardos.table (fairCoin (n := n)) ≤ ENNReal.ofReal ((φ.length : ℝ) / (d : ℝ)) :=
  card_fin_mul_inv_le_ofReal (MoserTardos.lintegral_sum_resamplings_le_symmetric
    (fairCoin (n := n)) (clauseVbl φ) (violated φ) (measurableSet_violated φ)
    (violated_dependsOn φ) hdpos (degree_card_le hdeg)
    (fun j => (measureReal_violated hφ j).le) (exp_mul_inv_pow_le (by simpa using hlll)) hsel)

/-- Under `e (d + 1) ≤ 2 ^ k`, almost surely any valid complete rule stops after finitely many
steps at a satisfying assignment of `φ`. -/
theorem ae_exists_eval_run_of_exp_mul_le {k d : ℕ} {φ : CNF (Fin n)}
    (hφ : φ.IsExactDistinct k) (hdeg : ∀ i : Fin φ.length, degree φ i ≤ d)
    (hlll : Real.exp 1 * (d + 1) ≤ 2 ^ k)
    {sel : (∀ p : Fin n × ℕ, (fun _ : Fin n => Bool) p.1) → List (Fin φ.length) →
      Option (Fin φ.length)}
    (hsel : ∀ T w i, sel T w = some i → MoserTardos.current (clauseVbl φ) T w ∈ violated φ i)
    (hstop : ∀ T w, sel T w = none → ∀ i, MoserTardos.current (clauseVbl φ) T w ∉ violated φ i) :
    ∀ᵐ T ∂MoserTardos.table (fairCoin (n := n)),
      ∃ N, φ.eval (MoserTardos.current (clauseVbl φ) T
        (MoserTardos.run (α := fun _ : Fin n => Bool) sel T N)) = true :=
  ae_eval_of_ae_notMem_violated φ _ (MoserTardos.ae_exists_forall_notMem_run_symmetric
    (fairCoin (n := n)) (clauseVbl φ) (violated φ) (measurableSet_violated φ)
    (violated_dependsOn φ) (degree_card_le hdeg) (fun j => (measureReal_violated hφ j).le)
    (exp_mul_inv_pow_le (by simpa using hlll)) hsel hstop)

/-- Under `e (d + 1) ≤ 2 ^ k`, almost surely the deterministic `firstViolatedRule` stops after
finitely many resamplings with a satisfying assignment of `φ`. -/
theorem ae_exists_eval_run_firstViolated_of_exp_mul_le {k d : ℕ} {φ : CNF (Fin n)}
    (hφ : φ.IsExactDistinct k) (hdeg : ∀ i : Fin φ.length, degree φ i ≤ d)
    (hlll : Real.exp 1 * (d + 1) ≤ 2 ^ k) :
    ∀ᵐ T ∂MoserTardos.table (fairCoin (n := n)),
      ∃ N, φ.eval (MoserTardos.current (clauseVbl φ) T
        (MoserTardos.run (α := fun _ : Fin n => Bool) (firstViolatedRule φ) T N)) = true :=
  ae_exists_eval_run_of_exp_mul_le hφ hdeg hlll
    (fun _ _ _ h => firstViolatedRule_eq_some h)
    (fun _ _ h i => firstViolatedRule_notMem_violated h i)

end StandardMT

section ConflictLopsided

variable {n : ℕ}

/-- Two clauses *conflict* [MoserTardos2010, Section 6] if one contains a literal and the other
contains its negation. -/
@[expose] def Conflicts (c d : Clause (Fin n)) : Prop :=
  ∃ l ∈ c, (l.1, !l.2) ∈ d

instance (c d : Clause (Fin n)) : Decidable (Conflicts c d) :=
  inferInstanceAs (Decidable (∃ l ∈ c, (l.1, !l.2) ∈ d))

theorem conflicts_comm (c d : Clause (Fin n)) : Conflicts c d ↔ Conflicts d c := by
  constructor <;>
  · rintro ⟨l, hl, hnl⟩
    refine ⟨(l.1, !l.2), hnl, ?_⟩
    simpa using hl

/-- The number of other clauses in `φ` conflicting with clause `i`. -/
@[expose] def conflictDegree (φ : CNF (Fin n)) (i : Fin φ.length) : ℕ :=
  #{j : Fin φ.length | j ≠ i ∧ Conflicts φ[i] φ[j]}

/-- Two violated clause events can be lopsidependent only when the clauses conflict
[MoserTardos2010, Section 6]. -/
theorem not_lopsidependent_of_not_conflicts (φ : CNF (Fin n)) {i j : Fin φ.length}
    (hc : ¬Conflicts φ[i] φ[j]) :
    ¬MoserTardos.Lopsidependent (clauseVbl φ) (violated φ) i j := by
  rw [MoserTardos.lopsidependent_iff]
  rintro ⟨f, g, hfg, hfi, hgj, hhor⟩
  have haux : ∀ {a b : Fin φ.length} {fa ga : Fin n → Bool},
      (∀ v, v ∉ clauseVbl φ a ∩ clauseVbl φ b → fa v = ga v) →
      ¬Conflicts φ[a] φ[b] →
      fa ∈ violated φ a → ga ∈ violated φ b → ga ∈ violated φ a := by
    intro a b fa ga hfg' hab hfa hgb
    by_contra hga
    simp only [violated, Set.mem_ofPred_eq, Bool.not_eq_false] at hfa hgb hga
    rw [Clause.eval_eq_true_iff] at hga
    obtain ⟨l, hla, hlga⟩ := hga
    have hlfa : fa l.1 = !l.2 := (Clause.eval_eq_false_iff fa φ[a]).1 hfa l hla
    have hneq : fa l.1 ≠ ga l.1 := by
      rw [hlfa, hlga]
      cases l.2 <;> simp
    have hinter : l.1 ∈ clauseVbl φ a ∩ clauseVbl φ b := by
      by_contra hni
      exact hneq (hfg' l.1 hni)
    have hvb : l.1 ∈ clauseVbl φ b := (mem_inter.1 hinter).2
    simp only [clauseVbl, List.mem_toFinset, vbl, List.mem_map] at hvb
    obtain ⟨m, hmb, hml⟩ := hvb
    have hmg : ga m.1 = !m.2 := (Clause.eval_eq_false_iff ga φ[b]).1 hgb m hmb
    have hm_eq : m = (l.1, !l.2) := by
      refine Prod.ext hml ?_
      have : ga l.1 = l.2 := hlga
      rw [← hml] at this
      rw [this] at hmg
      cases hm2 : m.2 <;> cases hl2 : l.2 <;> simp [hm2, hl2] at hmg ⊢
    exact hab ⟨l, hla, hm_eq ▸ hmb⟩
  rcases hhor with hfj | hgi
  · refine hfj (haux (fun v hv => (hfg v ?_).symm)
      (fun h => hc ((conflicts_comm _ _).1 h)) hgj hfi)
    rwa [inter_comm]
  · exact hgi (haux hfg hc hfi hgj)

private def conflictNbhd (φ : CNF (Fin n)) (i : Fin φ.length) : Finset (Fin φ.length) :=
  univ.filter fun j => j ≠ i ∧ Conflicts φ[i] φ[j]

private theorem mem_conflictNbhd (φ : CNF (Fin n)) (i j : Fin φ.length) (hji : j ≠ i)
    (hlop : MoserTardos.Lopsidependent (clauseVbl φ) (violated φ) i j) :
    j ∈ conflictNbhd φ i := by
  refine mem_filter.2 ⟨mem_univ _, hji, ?_⟩
  by_contra hc
  exact not_lopsidependent_of_not_conflicts φ hc hlop

private theorem conflictNbhd_card_le {d : ℕ} {φ : CNF (Fin n)}
    (hdeg : ∀ i : Fin φ.length, conflictDegree φ i ≤ d) (i : Fin φ.length) :
    #(conflictNbhd φ i) ≤ d := by
  simpa [conflictNbhd, conflictDegree] using hdeg i

/-- Under the lopsided conflict-graph condition `e (d' + 1) ≤ 2 ^ k` with `1 ≤ d'`, any valid
clause-resampling rule resamples clause `i` at most `1 / d'` times in expectation. -/
theorem lintegral_resamplings_le_of_conflict_exp_mul_le {k d' : ℕ} {φ : CNF (Fin n)}
    (hφ : φ.IsExactDistinct k) (hdpos : 1 ≤ d')
    (hdeg : ∀ i : Fin φ.length, conflictDegree φ i ≤ d')
    (hlll : Real.exp 1 * (d' + 1) ≤ 2 ^ k)
    {sel : (∀ p : Fin n × ℕ, (fun _ : Fin n => Bool) p.1) → List (Fin φ.length) →
      Option (Fin φ.length)}
    (hsel : ∀ T w i, sel T w = some i → MoserTardos.current (clauseVbl φ) T w ∈ violated φ i)
    (i : Fin φ.length) :
    ∫⁻ T, MoserTardos.resamplings (α := fun _ : Fin n => Bool) sel i T
      ∂MoserTardos.table (fairCoin (n := n)) ≤ ENNReal.ofReal (1 / (d' : ℝ)) :=
  MoserTardos.Lopsided.lintegral_resamplings_le_symmetric (fairCoin (n := n)) (clauseVbl φ)
    (violated φ) (measurableSet_violated φ) (violated_dependsOn φ) (conflictNbhd φ)
    (mem_conflictNbhd φ) hdpos (conflictNbhd_card_le hdeg)
    (fun j => (measureReal_violated hφ j).le) (exp_mul_inv_pow_le (by simpa using hlll)) hsel i

/-- Under the lopsided conflict-graph condition `e (d' + 1) ≤ 2 ^ k` with `1 ≤ d'`, the expected
total number of resamplings of any valid rule is at most `φ.length / d'`. -/
theorem lintegral_sum_resamplings_le_of_conflict_exp_mul_le {k d' : ℕ} {φ : CNF (Fin n)}
    (hφ : φ.IsExactDistinct k) (hdpos : 1 ≤ d')
    (hdeg : ∀ i : Fin φ.length, conflictDegree φ i ≤ d')
    (hlll : Real.exp 1 * (d' + 1) ≤ 2 ^ k)
    {sel : (∀ p : Fin n × ℕ, (fun _ : Fin n => Bool) p.1) → List (Fin φ.length) →
      Option (Fin φ.length)}
    (hsel : ∀ T w i, sel T w = some i → MoserTardos.current (clauseVbl φ) T w ∈ violated φ i) :
    ∫⁻ T, ∑ i, MoserTardos.resamplings (α := fun _ : Fin n => Bool) sel i T
      ∂MoserTardos.table (fairCoin (n := n)) ≤ ENNReal.ofReal ((φ.length : ℝ) / (d' : ℝ)) :=
  card_fin_mul_inv_le_ofReal (MoserTardos.Lopsided.lintegral_sum_resamplings_le_symmetric
    (fairCoin (n := n)) (clauseVbl φ) (violated φ) (measurableSet_violated φ)
    (violated_dependsOn φ) (conflictNbhd φ) (mem_conflictNbhd φ) hdpos
    (conflictNbhd_card_le hdeg) (fun j => (measureReal_violated hφ j).le)
    (exp_mul_inv_pow_le (by simpa using hlll)) hsel)

/-- Under the lopsided conflict-graph condition `e (d' + 1) ≤ 2 ^ k` (for any `d' : ℕ`,
including `d' = 0`), almost surely any valid complete rule stops at a satisfying assignment. -/
theorem ae_exists_eval_run_of_conflict_exp_mul_le {k d' : ℕ} {φ : CNF (Fin n)}
    (hφ : φ.IsExactDistinct k) (hdeg : ∀ i : Fin φ.length, conflictDegree φ i ≤ d')
    (hlll : Real.exp 1 * (d' + 1) ≤ 2 ^ k)
    {sel : (∀ p : Fin n × ℕ, (fun _ : Fin n => Bool) p.1) → List (Fin φ.length) →
      Option (Fin φ.length)}
    (hsel : ∀ T w i, sel T w = some i → MoserTardos.current (clauseVbl φ) T w ∈ violated φ i)
    (hstop : ∀ T w, sel T w = none → ∀ i, MoserTardos.current (clauseVbl φ) T w ∉ violated φ i) :
    ∀ᵐ T ∂MoserTardos.table (fairCoin (n := n)),
      ∃ N, φ.eval (MoserTardos.current (clauseVbl φ) T
        (MoserTardos.run (α := fun _ : Fin n => Bool) sel T N)) = true :=
  ae_eval_of_ae_notMem_violated φ _ (MoserTardos.Lopsided.ae_exists_forall_notMem_run_symmetric
    (fairCoin (n := n)) (clauseVbl φ) (violated φ) (measurableSet_violated φ)
    (violated_dependsOn φ) (conflictNbhd φ) (mem_conflictNbhd φ) (conflictNbhd_card_le hdeg)
    (fun j => (measureReal_violated hφ j).le) (exp_mul_inv_pow_le (by simpa using hlll))
    hsel hstop)

/-- Under `e (d' + 1) ≤ 2 ^ k` on `conflictDegree`, almost surely `firstViolatedRule` stops after
finitely many resamplings with a satisfying assignment of `φ`. -/
theorem ae_exists_eval_run_firstViolated_of_conflict_exp_mul_le {k d' : ℕ} {φ : CNF (Fin n)}
    (hφ : φ.IsExactDistinct k) (hdeg : ∀ i : Fin φ.length, conflictDegree φ i ≤ d')
    (hlll : Real.exp 1 * (d' + 1) ≤ 2 ^ k) :
    ∀ᵐ T ∂MoserTardos.table (fairCoin (n := n)),
      ∃ N, φ.eval (MoserTardos.current (clauseVbl φ) T
        (MoserTardos.run (α := fun _ : Fin n => Bool) (firstViolatedRule φ) T N)) = true :=
  ae_exists_eval_run_of_conflict_exp_mul_le hφ hdeg hlll
    (fun _ _ _ h => firstViolatedRule_eq_some h)
    (fun _ _ h i => firstViolatedRule_notMem_violated h i)

end ConflictLopsided

section ParallelMT

variable {n : ℕ}

/-- Computable greedy maximal independent set parallel selection rule for CNF clauses. -/
@[expose] def greedyParallelCNF (φ : CNF (Fin n)) :
    (∀ p : Fin n × ℕ, (fun _ : Fin n => Bool) p.1) → List (Fin φ.length) →
      List (Fin φ.length) :=
  MoserTardos.greedyParallelList (clauseVbl φ) (List.finRange φ.length) fun σ i => !φ[i].eval σ

theorem isValidParallelRule_greedyParallelCNF (φ : CNF (Fin n)) :
    MoserTardos.IsValidParallelRule (clauseVbl φ) (violated φ) (greedyParallelCNF φ) :=
  MoserTardos.isValidParallelRule_greedyParallelList (clauseVbl φ) (violated φ)
    (List.finRange φ.length) List.mem_finRange _ fun σ i => by
      simp [violated]

/-- Parallel Moser–Tardos theorem for `k`-SAT (`1 ≤ d`): under `e (d + 1) ≤ (1 - ε) * 2 ^ k`
with `ε ∈ (0, 1]`, every admissible parallel clause-resampling rule terminates in at most
`(max 0 (Real.log (φ.length / d)) + 1) / ε` expected parallel rounds. -/
theorem lintegral_parallelRounds_le_of_exp_mul_le_of_pos {k d : ℕ} {ε : ℝ} {φ : CNF (Fin n)}
    (hφ : φ.IsExactDistinct k) (hdpos : 1 ≤ d) (hdeg : ∀ i : Fin φ.length, degree φ i ≤ d)
    (hε : ε ∈ Set.Ioc 0 1) (hlll : Real.exp 1 * (d + 1) ≤ (1 - ε) * 2 ^ k)
    {psel : (∀ p : Fin n × ℕ, (fun _ : Fin n => Bool) p.1) → List (Fin φ.length) →
      List (Fin φ.length)}
    (hrule : MoserTardos.IsValidParallelRule (clauseVbl φ) (violated φ) psel) :
    ∫⁻ T, MoserTardos.parallelRounds (α := fun _ : Fin n => Bool) psel T
        ∂MoserTardos.table (fairCoin (n := n)) ≤
      ENNReal.ofReal ((max 0 (Real.log ((φ.length : ℝ) / d)) + 1) / ε) := by
  simpa only [Fintype.card_fin] using
    MoserTardos.lintegral_parallelRounds_le_symmetric_of_pos (fairCoin (n := n)) (clauseVbl φ)
      (violated φ) (measurableSet_violated φ) (violated_dependsOn φ) hdpos
      (degree_card_le hdeg) (fun j => (measureReal_violated hφ j).le) hε
      (exp_mul_inv_pow_le hlll) hrule

/-- Parallel Moser–Tardos theorem for `k`-SAT (all `d : ℕ`): under `e (d + 1) ≤ (1 - ε) * 2 ^ k`
with `ε ∈ (0, 1]`, every admissible parallel clause-resampling rule terminates in at most
`(max 0 (Real.log φ.length) + 1) / ε` expected parallel rounds. -/
theorem lintegral_parallelRounds_le_of_exp_mul_le {k d : ℕ} {ε : ℝ} {φ : CNF (Fin n)}
    (hφ : φ.IsExactDistinct k) (hdeg : ∀ i : Fin φ.length, degree φ i ≤ d)
    (hε : ε ∈ Set.Ioc 0 1) (hlll : Real.exp 1 * (d + 1) ≤ (1 - ε) * 2 ^ k)
    {psel : (∀ p : Fin n × ℕ, (fun _ : Fin n => Bool) p.1) → List (Fin φ.length) →
      List (Fin φ.length)}
    (hrule : MoserTardos.IsValidParallelRule (clauseVbl φ) (violated φ) psel) :
    ∫⁻ T, MoserTardos.parallelRounds (α := fun _ : Fin n => Bool) psel T
        ∂MoserTardos.table (fairCoin (n := n)) ≤
      ENNReal.ofReal ((max 0 (Real.log (φ.length : ℝ)) + 1) / ε) := by
  simpa only [Fintype.card_fin] using
    MoserTardos.lintegral_parallelRounds_le_symmetric (fairCoin (n := n)) (clauseVbl φ)
      (violated φ) (measurableSet_violated φ) (violated_dependsOn φ)
      (degree_card_le hdeg) (fun j => (measureReal_violated hφ j).le) hε
      (exp_mul_inv_pow_le hlll) hrule

/-- Under `e (d + 1) ≤ (1 - ε) * 2 ^ k` with `ε ∈ (0, 1]`, almost surely every admissible parallel
clause-resampling rule reaches a satisfying assignment of `φ` in finitely many parallel rounds. -/
theorem ae_exists_eval_parallelRun_of_exp_mul_le {k d : ℕ} {ε : ℝ} {φ : CNF (Fin n)}
    (hφ : φ.IsExactDistinct k) (hdeg : ∀ i : Fin φ.length, degree φ i ≤ d)
    (hε : ε ∈ Set.Ioc 0 1) (hlll : Real.exp 1 * (d + 1) ≤ (1 - ε) * 2 ^ k)
    {psel : (∀ p : Fin n × ℕ, (fun _ : Fin n => Bool) p.1) → List (Fin φ.length) →
      List (Fin φ.length)}
    (hrule : MoserTardos.IsValidParallelRule (clauseVbl φ) (violated φ) psel) :
    ∀ᵐ T ∂MoserTardos.table (fairCoin (n := n)),
      ∃ N, φ.eval (MoserTardos.current (clauseVbl φ) T
        (MoserTardos.parallelRun (α := fun _ : Fin n => Bool) psel T N)) = true :=
  ae_eval_of_ae_notMem_violated φ _ (MoserTardos.ae_exists_forall_notMem_parallelRun_symmetric
    (fairCoin (n := n)) (clauseVbl φ) (violated φ) (measurableSet_violated φ)
    (violated_dependsOn φ) (degree_card_le hdeg) (fun j => (measureReal_violated hφ j).le) hε
    (exp_mul_inv_pow_le hlll) hrule)

/-- Under `e (d + 1) ≤ (1 - ε) * 2 ^ k` with `ε ∈ (0, 1]`, almost surely `greedyParallelCNF`
reaches a satisfying assignment of `φ` in finitely many parallel rounds. -/
theorem ae_exists_eval_parallelRun_greedy_of_exp_mul_le {k d : ℕ} {ε : ℝ} {φ : CNF (Fin n)}
    (hφ : φ.IsExactDistinct k) (hdeg : ∀ i : Fin φ.length, degree φ i ≤ d)
    (hε : ε ∈ Set.Ioc 0 1) (hlll : Real.exp 1 * (d + 1) ≤ (1 - ε) * 2 ^ k) :
    ∀ᵐ T ∂MoserTardos.table (fairCoin (n := n)),
      ∃ N, φ.eval (MoserTardos.current (clauseVbl φ) T
        (MoserTardos.parallelRun (α := fun _ : Fin n => Bool) (greedyParallelCNF φ) T N)) = true :=
  ae_exists_eval_parallelRun_of_exp_mul_le hφ hdeg hε hlll (isValidParallelRule_greedyParallelCNF φ)

end ParallelMT

end Moser

/-- **Constructive lopsided `k`-SAT local lemma** [MoserTardos2010, Section 6]: if every clause of
an exact `k`-CNF conflicts with at most `d'` other clauses and `e (d' + 1) ≤ 2 ^ k`, then `φ` is
satisfiable (proved via `Moser.ae_exists_eval_run_firstViolated_of_conflict_exp_mul_le`). -/
theorem CNF.IsExactDistinct.satisfiable_of_conflict_exp_mul_le {n k d' : ℕ} {φ : CNF (Fin n)}
    (hφ : φ.IsExactDistinct k) (hdeg : ∀ i : Fin φ.length, Moser.conflictDegree φ i ≤ d')
    (hlll : Real.exp 1 * (d' + 1) ≤ 2 ^ k) : φ.Satisfiable := by
  obtain ⟨T, N, hN⟩ :=
    (Moser.ae_exists_eval_run_firstViolated_of_conflict_exp_mul_le hφ hdeg hlll).exists
  exact ⟨_, hN⟩

end Cslib.Logic.PL
