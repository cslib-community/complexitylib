/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.PartialCover
public import CslibFrontier.Probability.FiniteTable
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Tactic

/-!
# History-dependent partial-cover response laws

[Wang2027], Theorem 4, first probability assertion, Section 5 (PDF pp. 10–11).
The response alphabet consists of all subfamilies of the original finite set
system. Arbitrary conditional kernels may depend on the complete preceding
response history; independence of calls or of element-coverage events is not
required. `Admissible` imposes the source's joint local-certification/coverage
probability only at histories reached with positive probability. Eligibility
sets are listed in the fixed processing order, with one entry per issued call.

`law` executes the local test and retains accepted responses. `completion_bound`
derives its success probability from the conditional response hypotheses,
including zero eligible calls and overlapping eligibility sets. It does not
supply the greedy selector, runtime or hardness assertions of Theorem 4.

## Main results

* `miss_bound`: an element is missed with probability at most `q` to its eligible-call count.
* `completion_bound`: the union-bound success guarantee for the actual processing law.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.PartialCover.Instance
open Finset Cslib.Optimization.OneConstraint
variable {E J : Type} [DecidableEq E] [DecidableEq J] [Fintype J]
variable (I : Instance E J) (ρ : ℝ)

open scoped Classical in
/-- The actual retained family after processing one response. -/
@[expose] def step (C P : Finset J) : Finset J :=
  if I.Certified ρ C P then C ∪ P else C

/-- A complete conditional response kernel, with histories stored most recent first. -/
abbrev ResponseKernel (J : Type) [Fintype J] :=
  List (Finset J) → Distribution (Finset J) ℝ

/-- Execute the fixed-order responses, retaining only locally certified subfamilies. -/
@[expose] def law (I : Instance E J) (ρ : ℝ) (K : ResponseKernel J) :
    List (Finset J) → Finset J → List (Finset E) → Distribution (Finset J) ℝ
  | _, C, [] => Distribution.pure C
  | h, C, _ :: vs => (K h).bind fun P => I.law ρ K (P :: h) (I.step ρ C P) vs

/-- Number of issued calls certified for an individual element. -/
@[expose] def chances (e : E) (vs : List (Finset E)) : ℕ :=
  (vs.filter (e ∈ ·)).length

open scoped Classical in
/-- Conditional probability of an event under a response table. -/
@[expose] def event (w : Distribution (Finset J) ℝ) (A : Finset J → Prop) : ℝ :=
  w.mean fun P => if A P then 1 else 0

/-- Source's joint conditional guarantee. Tail obligations apply only to positive-mass
responses, so arbitrary definitions of kernels at null histories are harmless. -/
@[expose] def Admissible (I : Instance E J) (ρ p : ℝ) (K : ResponseKernel J) :
    List (Finset J) → Finset J → List (Finset E) → Prop
  | _, _, [] => True
  | h, C, V :: vs =>
    (∀ e ∈ V, e ∉ I.covered C →
      p ≤ event (K h) (fun P => I.Certified ρ C P ∧ e ∈ I.covered P)) ∧
    ∀ P, 0 < (K h).weight P → I.Admissible ρ p K (P :: h) (I.step ρ C P) vs

omit [Fintype J] in
/-- Accepted responses preserve earlier coverage. -/
theorem covered_subset_step (C P : Finset J) : I.covered C ⊆ I.covered (I.step ρ C P) := by
  classical
  unfold step
  split_ifs
  · rw [I.covered_union]; exact subset_union_left
  · exact Subset.rfl

/-- A single eligible call misses an uncovered element with probability at most `1-p`. -/
theorem step_miss_le (K : ResponseKernel J) (h : List (Finset J)) (C : Finset J)
    (e : E) (he : e ∉ I.covered C) {p : ℝ}
    (hp : p ≤ event (K h) (fun P => I.Certified ρ C P ∧ e ∈ I.covered P)) :
    event (K h) (fun P => e ∉ I.covered (I.step ρ C P)) ≤ 1 - p := by
  classical
  have hid : event (K h) (fun P => e ∉ I.covered (I.step ρ C P)) +
      event (K h) (fun P => I.Certified ρ C P ∧ e ∈ I.covered P) = 1 := by
    rw [event, event, ← Distribution.mean_add]
    unfold Distribution.mean
    calc
      _ = ∑ P, (K h).weight P * 1 := by
        apply sum_congr rfl
        intro P _
        dsimp only
        by_cases hc : I.Certified ρ C P <;>
          by_cases heP : e ∈ I.covered P <;> simp [step, hc, I.covered_union, he, heP]
      _ = 1 := by simpa using (K h).total
  linarith

omit [DecidableEq J] in
private theorem event_nonneg (w : Distribution (Finset J) ℝ) (A : Finset J → Prop) :
    0 ≤ event w A := by
  classical
  unfold event Distribution.mean
  exact sum_nonneg fun P _ => mul_nonneg (w.nonneg P) (by dsimp only; split_ifs <;> norm_num)

omit [DecidableEq J] in
private theorem event_le_one (w : Distribution (Finset J) ℝ) (A : Finset J → Prop) :
    event w A ≤ 1 := by
  classical
  rw [← w.total]
  unfold event Distribution.mean
  apply sum_le_sum
  intro P _
  dsimp only
  split_ifs <;> nlinarith [w.nonneg P]

/-- The per-element failure recurrence, derived from actual conditional response kernels.
The bound is zero for an already covered element. -/
theorem miss_bound {p : ℝ} (_hp : 0 ≤ p) (hpone : p ≤ 1) (K : ResponseKernel J)
    (vs : List (Finset E)) (h : List (Finset J)) (C : Finset J)
    (had : I.Admissible ρ p K h C vs) (e : E) :
    event (I.law ρ K h C vs) (fun P => e ∉ I.covered P) ≤
      if e ∈ I.covered C then 0 else (1 - p) ^ chances e vs := by
  classical
  induction vs generalizing h C with
  | nil =>
    simp only [law, event, Distribution.mean_pure, chances, List.filter_nil, List.length_nil,
      pow_zero]
    by_cases he : e ∈ I.covered C <;> simp [he]
  | cons V vs ih =>
    rw [law, event, Distribution.mean_bind]
    have hb : (K h).mean (fun P =>
        event (I.law ρ K (P :: h) (I.step ρ C P) vs) (fun Q => e ∉ I.covered Q)) ≤
        (1 - p) ^ chances e vs *
          event (K h) (fun P => e ∉ I.covered (I.step ρ C P)) := by
      rw [event, ← Distribution.mean_mul]
      unfold Distribution.mean
      apply sum_le_sum
      intro P _
      by_cases hw : 0 < (K h).weight P
      · have hi := ih (P :: h) (I.step ρ C P) (had.2 P hw)
        have hi' : event (I.law ρ K (P :: h) (I.step ρ C P) vs)
            (fun Q => e ∉ I.covered Q) ≤
            (1 - p) ^ chances e vs * (if e ∉ I.covered (I.step ρ C P) then 1 else 0) := by
          by_cases he : e ∈ I.covered (I.step ρ C P) <;> simpa [he] using hi
        apply mul_le_mul_of_nonneg_left _ ((K h).nonneg P)
        by_cases heP : e ∈ I.covered (I.step ρ C P) <;> simpa [heP] using hi'
      · have hz : (K h).weight P = 0 := le_antisymm (le_of_not_gt hw) ((K h).nonneg P)
        simp [hz]
    change (K h).mean _ ≤ _
    apply hb.trans
    by_cases he : e ∈ I.covered C
    · have hz : event (K h) (fun P => e ∉ I.covered (I.step ρ C P)) = 0 := by
        unfold event Distribution.mean
        apply sum_eq_zero
        intro P _
        simp [I.covered_subset_step ρ C P he]
      simp [he, hz]
    · simp only [he, ↓reduceIte]
      by_cases hv : e ∈ V
      · have hs := I.step_miss_le ρ K h C e he (had.1 e hv he)
        have hn : chances e (V :: vs) = chances e vs + 1 := by simp [chances, hv]
        rw [hn, pow_succ]
        exact mul_le_mul_of_nonneg_left hs (pow_nonneg (by linarith) _)
      · have hn : chances e (V :: vs) = chances e vs := by simp [chances, hv]
        rw [hn]
        exact (mul_le_mul_of_nonneg_left (event_le_one (K h) _)
          (pow_nonneg (by linarith) _)).trans_eq (mul_one _)

/-- Every positive-probability output of the response law satisfies the accumulated
local dual-charge invariant. No admissibility/probability assumption is needed. -/
theorem law_support_bound (K : ResponseKernel J) (vs : List (Finset E))
    (h : List (Finset J)) (C : Finset J)
    (hC : I.cost C ≤ ρ * ∑ e ∈ I.covered C, I.dual e)
    (P : Finset J) (hP : 0 < (I.law ρ K h C vs).weight P) :
    I.cost P ≤ ρ * ∑ e ∈ I.covered P, I.dual e := by
  classical
  induction vs generalizing h C with
  | nil =>
    have heq : P = C := by
      by_contra hn
      simp [law, Distribution.pure, hn] at hP
    simpa [heq] using hC
  | cons V vs ih =>
    change 0 < ∑ Q, (K h).weight Q *
      (I.law ρ K (Q :: h) (I.step ρ C Q) vs).weight P at hP
    obtain ⟨Q, _, hQ⟩ := (sum_pos_iff_of_nonneg (fun Q _ =>
      mul_nonneg ((K h).nonneg Q)
        ((I.law ρ K (Q :: h) (I.step ρ C Q) vs).nonneg P))).mp hP
    have htail : 0 < (I.law ρ K (Q :: h) (I.step ρ C Q) vs).weight P :=
      pos_of_mul_pos_right hQ ((K h).nonneg Q)
    apply ih (Q :: h) (I.step ρ C Q) _ htail
    unfold step
    split_ifs with hc
    · exact I.certified_union_bound hC hc
    · exact hC

/-- Union-bound completion probability for the actual retained family. This includes
an empty universe and zero eligible calls. No element-event independence is assumed. -/
theorem completion_bound {p : ℝ} (hp : 0 ≤ p) (hpone : p ≤ 1) (K : ResponseKernel J)
    (vs : List (Finset E)) (had : I.Admissible ρ p K [] ∅ vs) :
    max 0 (1 - ∑ e ∈ I.ground, (1 - p) ^ chances e vs) ≤
      event (I.law ρ K [] ∅ vs) (fun P => I.covered P = I.ground) := by
  classical
  let w := I.law ρ K [] ∅ vs
  have hu : 1 - event w (fun P => I.covered P = I.ground) ≤
      ∑ e ∈ I.ground, event w (fun P => e ∉ I.covered P) := by
    have hpoint : ∀ P : Finset J,
        (1 : ℝ) ≤ (if I.covered P = I.ground then 1 else 0) +
          ∑ e ∈ I.ground, if e ∉ I.covered P then (1 : ℝ) else 0 := by
      intro P
      by_cases hc : I.covered P = I.ground
      · simp only [hc, ↓reduceIte, le_add_iff_nonneg_right]
        exact sum_nonneg fun e _ => by split_ifs; norm_num
      · obtain ⟨e, heU, heC⟩ : ∃ e ∈ I.ground, e ∉ I.covered P := by
          by_contra! h
          exact hc (Subset.antisymm (I.covered_subset P) h)
        have hh : (1 : ℝ) ≤ ∑ e ∈ I.ground, if e ∉ I.covered P then (1 : ℝ) else 0 := by
          have := single_le_sum (f := fun e => if e ∉ I.covered P then (1 : ℝ) else 0)
            (fun e _ => by split_ifs <;> norm_num) heU
          simpa [heC] using this
        simpa [hc] using hh
    have hsum := sum_le_sum (s := (univ : Finset (Finset J)))
      (fun P _ => mul_le_mul_of_nonneg_left (hpoint P) (w.nonneg P))
    simp only [mul_add, mul_sum, sum_add_distrib, mul_one, w.total] at hsum
    unfold event Distribution.mean
    rw [sum_comm (s := I.ground)]
    dsimp only
    simp only [mul_ite, mul_one, mul_zero] at hsum ⊢
    linarith
  have hb : (∑ e ∈ I.ground, event w (fun P => e ∉ I.covered P)) ≤
      ∑ e ∈ I.ground, (1 - p) ^ chances e vs := by
    apply sum_le_sum
    intro e _
    simpa [covered] using I.miss_bound ρ hp hpone K vs [] ∅ had e
  exact max_le (event_nonneg w _) (by linarith)

/-- Completed positive-probability outputs are certified against every integral cover. -/
theorem law_completed_cost {ρ : ℝ} (hρ : 0 ≤ ρ) (K : ResponseKernel J)
    (vs : List (Finset E)) (P : Finset J)
    (hP : 0 < (I.law ρ K [] ∅ vs).weight P) (hcover : I.covered P = I.ground)
    (C : Finset J) (hC : I.covered C = I.ground) :
    I.cost P ≤ ρ * (∑ e ∈ I.ground, I.dual e) ∧
      ρ * (∑ e ∈ I.ground, I.dual e) ≤ ρ * I.cost C := by
  have hb := I.law_support_bound ρ K vs [] ∅ (by simp [cost, covered]) P hP
  rw [hcover] at hb
  refine ⟨hb, mul_le_mul_of_nonneg_left ?_ hρ⟩
  rw [← hC]
  exact I.dual_le_cost C

/-- The probability bound concerns an actually certified completed cover, not merely
coverage by unchecked oracle responses. The dual objective also bounds every integral cover. -/
theorem certified_completion_bound {p : ℝ} (hp : 0 ≤ p) (hpone : p ≤ 1)
    (K : ResponseKernel J) (vs : List (Finset E))
    (had : I.Admissible ρ p K [] ∅ vs) :
    max 0 (1 - ∑ e ∈ I.ground, (1 - p) ^ chances e vs) ≤
      event (I.law ρ K [] ∅ vs) (fun P => I.covered P = I.ground ∧
        I.cost P ≤ ρ * ∑ e ∈ I.ground, I.dual e) := by
  classical
  apply (I.completion_bound ρ hp hpone K vs had).trans
  unfold event Distribution.mean
  apply sum_le_sum
  intro P _
  dsimp only
  by_cases hw : 0 < (I.law ρ K [] ∅ vs).weight P
  · by_cases hc : I.covered P = I.ground
    · have hb := I.law_support_bound ρ K vs [] ∅ (by simp [cost, covered]) P hw
      rw [hc] at hb
      simp [hc, hb]
    · simp [hc]
  · have hz : (I.law ρ K [] ∅ vs).weight P = 0 :=
      le_antisymm (le_of_not_gt hw) ((I.law ρ K [] ∅ vs).nonneg P)
    simp [hz]

/-- A certified failure-risk budget implies the requested completion probability. -/
theorem completion_of_risk_le {p η : ℝ} (hp : 0 ≤ p) (hpone : p ≤ 1)
    (K : ResponseKernel J) (vs : List (Finset E))
    (had : I.Admissible ρ p K [] ∅ vs)
    (hrisk : (∑ e ∈ I.ground, (1 - p) ^ chances e vs) ≤ 1 - η) :
    η ≤ event (I.law ρ K [] ∅ vs) (fun P => I.covered P = I.ground) := by
  have hb := I.completion_bound ρ hp hpone K vs had
  exact (show η ≤ 1 - ∑ e ∈ I.ground, (1 - p) ^ chances e vs by linarith).trans
    ((le_max_right _ _).trans hb)

omit [DecidableEq J] [Fintype J] in
/-- Repeating one oracle adds exactly the issued number of chances for its eligible elements. -/
theorem chances_replicate (e : E) (V : Finset E) (n : ℕ) :
    chances e (List.replicate n V) = if e ∈ V then n else 0 := by
  by_cases he : e ∈ V <;> simp [chances, he]

omit [DecidableEq J] [Fintype J] in
/-- Processing-order concatenation adds chances; it does not require independent laws. -/
theorem chances_append (e : E) (xs ys : List (Finset E)) :
    chances e (xs ++ ys) = chances e xs + chances e ys := by
  simp [chances]

omit [DecidableEq J] [Fintype J] in
/-- A call-count vector expanded into a parallel batch has precisely the source's
`d_e(ζ) = ∑_{i:e∈V_i} ζ_i` eligible calls. The list fixes only processing order. -/
theorem chances_batch {ι : Type*} (e : E) (oracles : List ι)
    (V : ι → Finset E) (ζ : ι → ℕ) :
    chances e (oracles.flatMap fun i => List.replicate (ζ i) (V i)) =
      (oracles.map fun i => if e ∈ V i then ζ i else 0).sum := by
  induction oracles with
  | nil => simp [chances]
  | cons i is ih => simp [chances_append, chances_replicate, ih]

omit [DecidableEq J] [Fintype J] in
/-- Every `r`-fold multicover meets the elementary uniform certified-risk bound. -/
theorem multicover_risk_le {q : ℝ} (hq : 0 ≤ q) (hqone : q ≤ 1)
    (vs : List (Finset E)) (r : ℕ) (hr : ∀ e ∈ I.ground, r ≤ chances e vs) :
    (∑ e ∈ I.ground, q ^ chances e vs) ≤ I.ground.card * q ^ r := by
  calc
    _ ≤ ∑ _e ∈ I.ground, q ^ r := sum_le_sum fun e he =>
      pow_le_pow_of_le_one hq hqone (hr e he)
    _ = _ := by simp

/-- The source's logarithmic repetition threshold at failure budget `δ`.
For `r₀`, use `δ = 1-η`; for `r₁`, use `δ = (1-η)/n`. -/
@[expose] def repetitions (q δ : ℝ) : ℕ :=
  ⌈Real.log (1 / δ) / Real.log (1 / q)⌉₊

/-- The logarithmic threshold is the least integer meeting the power-risk budget. -/
theorem pow_le_iff_repetitions_le {q δ : ℝ} (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) (d : ℕ) : q ^ d ≤ δ ↔ repetitions q δ ≤ d := by
  rw [repetitions, Nat.ceil_le, Real.pow_le_iff_le_log hq hδ]
  simp only [one_div, Real.log_inv, neg_div_neg_eq]
  exact (div_le_iff_of_neg (Real.log_neg hq hqone)).symm

omit [DecidableEq J] [Fintype J] in
/-- Every risk-feasible call-count vector supplies at least `r₀` chances to each element. -/
theorem risk_implies_multicover {q δ : ℝ} (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) (vs : List (Finset E))
    (hrisk : (∑ e ∈ I.ground, q ^ chances e vs) ≤ δ) :
    ∀ e ∈ I.ground, repetitions q δ ≤ chances e vs := by
  intro e he
  apply (pow_le_iff_repetitions_le hq hqone hδ _).mp
  exact (single_le_sum (f := fun e => q ^ chances e vs)
    (fun e _ => pow_nonneg hq.le _) he).trans hrisk

omit [DecidableEq J] [Fintype J] in
/-- `r₁` chances per element suffice for the prescribed failure budget. -/
theorem multicover_implies_risk {q δ : ℝ} (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) (hU : I.ground.Nonempty) (vs : List (Finset E))
    (hr : ∀ e ∈ I.ground,
      repetitions q (δ / I.ground.card) ≤ chances e vs) :
    (∑ e ∈ I.ground, q ^ chances e vs) ≤ δ := by
  have hn : (0 : ℝ) < I.ground.card := by exact_mod_cast hU.card_pos
  have hb := I.multicover_risk_le hq.le hqone.le vs _ hr
  have hp := (pow_le_iff_repetitions_le hq hqone (div_pos hδ hn)
    (repetitions q (δ / I.ground.card))).mpr le_rfl
  have hm := mul_le_mul_of_nonneg_left hp hn.le
  have heq : (I.ground.card : ℝ) * (δ / I.ground.card) = δ := by field_simp
  exact hb.trans (hm.trans_eq heq)

omit [DecidableEq J] [Fintype J] in
/-- In the source's nonempty-universe, positive-target regime, `1 ≤ r₀ ≤ r₁`. -/
theorem repetition_thresholds {q δ : ℝ} (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) (hδone : δ < 1) (hU : I.ground.Nonempty) :
    1 ≤ repetitions q δ ∧ repetitions q δ ≤ repetitions q (δ / I.ground.card) := by
  have hn : (1 : ℝ) ≤ I.ground.card := by exact_mod_cast hU.card_pos
  have hnpos : (0 : ℝ) < I.ground.card := lt_of_lt_of_le zero_lt_one hn
  constructor
  · by_contra h
    have hz : repetitions q δ = 0 := by omega
    have hp := (pow_le_iff_repetitions_le hq hqone hδ 0).mpr (by omega)
    simp only [pow_zero] at hp
    linarith
  · apply (pow_le_iff_repetitions_le hq hqone hδ _).mp
    have hp := (pow_le_iff_repetitions_le hq hqone (div_pos hδ hnpos)
      (repetitions q (δ / I.ground.card))).mpr le_rfl
    exact hp.trans ((div_le_iff₀ hnpos).mpr (by nlinarith))

end Cslib.Probability.StochasticOracle.PartialCover.Instance
