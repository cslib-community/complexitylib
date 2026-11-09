/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Multicover.Greedy
public import CslibFrontier.Probability.StochasticOracle.PartialCoverRisk
public import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# Greedy multicover and certified response risk

[Wang2027], Theorem 4, Section 5 (PDF pp. 10–11). The executable rational-cost
selector is compared with every risk-feasible batch, using the source's
necessary/sufficient repetition thresholds and harmonic charging. This avoids
assuming that a risk optimum exists or supplying greedy performance as an input.
The finite universe is the whole type; use a subtype for a restricted universe.

Only batch construction and its mathematical bill/risk guarantees are proved.
A native binary implementation/resource certificate, response token-bill and
latency execution, asymptotic approximation corollaries and encoded Set Cover
hardness remain separate obligations; this is not completion of Theorem 4.

## Main results

* `batch_scaled_log_bill_le`: logarithmic comparison after repeating a benchmark.
* `greedy_risk_bill`: source repetition thresholds and risk-benchmark comparison.
* `greedy_certified_completion`: probability for the actual selected response law.
-/

public section
namespace Cslib.Algorithms.Lean.Multicover
open Cslib.Probability.StochasticOracle
open Finset PartialCover.Instance
variable {E : Type} [DecidableEq E] [Fintype E]

omit [Fintype E] in
/-- The actual residual is initial demand minus the number of eligible calls. -/
theorem residual_eq (d : Demand E) (bs : List (Oracle E)) (e : E) :
    residual d bs e = d e - chances e (bs.map Oracle.eligible) := by
  induction bs generalizing d with
  | nil => simp [residual, chances]
  | cons b bs ih =>
    rw [residual, ih]
    by_cases he : e ∈ b.eligible
    · simp [reduce, he, chances, Nat.sub_sub, Nat.add_comm]
    · simp [reduce, he, chances]

/-- The actual emitted batch gives every element at least `r` eligible calls. -/
theorem batch_chances (as : List (Oracle E))
    (hcover : ∀ e : E, ∃ a ∈ as, e ∈ a.eligible) (r : ℕ) (e : E) :
    r ≤ chances e ((batch as r).map Oracle.eligible) := by
  have h := (batch_spec as hcover r).2 e
  rw [residual_eq] at h
  exact Nat.sub_eq_zero_iff_le.mp h

omit [Fintype E] in
/-- Repeating a benchmark batch multiplies each element's number of chances. -/
theorem chances_repeat (bs : List (Oracle E)) (m : ℕ) (e : E) :
    chances e (((List.replicate m bs).flatten).map Oracle.eligible) =
      m * chances e (bs.map Oracle.eligible) := by
  induction m with
  | zero => simp [chances]
  | succ m ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.map_append, chances_append, ih,
      Nat.succ_mul, Nat.add_comm]

omit [DecidableEq E] [Fintype E] in
/-- Repeating a benchmark batch multiplies its known cost bound. -/
theorem bill_repeat (bs : List (Oracle E)) (m : ℕ) :
    bill ((List.replicate m bs).flatten) = (m : ℚ) * bill bs := by
  induction m with
  | zero => simp [bill]
  | succ m ih =>
    simp only [List.replicate_succ, List.flatten_cons, bill, List.map_append,
      List.sum_append] at *
    rw [ih, Nat.cast_add, Nat.cast_one]
    ring

/-- Source scaling comparison: greedy for demand `r₁` is within
`H_(nr₁) * m` of every `r₀`-fold batch when `r₁ ≤ m*r₀`. -/
theorem batch_scaled_bill_le (as bs : List (Oracle E)) (r₀ r₁ m : ℕ)
    (hcost : ∀ b ∈ as, 0 ≤ b.cost) (hsub : ∀ b ∈ bs, b ∈ as)
    (hfull : ∀ e, r₀ ≤ chances e (bs.map Oracle.eligible)) (hm : r₁ ≤ m * r₀) :
    bill (batch as r₁) ≤ harmonic (Fintype.card E * r₁) * (m : ℚ) * bill bs := by
  have hsub' : ∀ b ∈ (List.replicate m bs).flatten, b ∈ as := by
    intro b hb
    obtain ⟨cs, hcs, hb⟩ := List.mem_flatten.mp hb
    have hcs' : cs = bs := List.mem_replicate.mp hcs |>.2
    subst cs
    exact hsub b hb
  have hfull' : ∀ e, residual (fun _ => r₁) (List.replicate m bs).flatten e = 0 := by
    intro e
    rw [residual_eq, chances_repeat, Nat.sub_eq_zero_iff_le]
    exact hm.trans (Nat.mul_le_mul_left m (hfull e))
  have h := batch_bill_le as (List.replicate m bs).flatten r₁ hcost hsub' hfull'
  rw [bill_repeat] at h
  simpa only [mul_assoc] using h

/-- The source's logarithmic cost factor, with no supplied greedy guarantee. -/
theorem batch_scaled_log_bill_le (as bs : List (Oracle E)) (r₀ r₁ m : ℕ)
    (hcost : ∀ b ∈ as, 0 ≤ b.cost) (hsub : ∀ b ∈ bs, b ∈ as)
    (hfull : ∀ e, r₀ ≤ chances e (bs.map Oracle.eligible)) (hm : r₁ ≤ m * r₀) :
    (bill (batch as r₁) : ℝ) ≤
      (1 + Real.log (Fintype.card E * r₁)) * m * (bill bs : ℝ) := by
  have h := batch_scaled_bill_le as bs r₀ r₁ m hcost hsub hfull hm
  have hc : (0 : ℝ) ≤ bill bs := by
    exact_mod_cast bill_nonneg bs (fun b hb => hcost b (hsub b hb))
  have hh := harmonic_le_one_add_log (Fintype.card E * r₁)
  have h' : (bill (batch as r₁) : ℝ) ≤
      (harmonic (Fintype.card E * r₁) : ℝ) * m * (bill bs : ℝ) := by exact_mod_cast h
  exact h'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by simpa only [Nat.cast_mul] using hh)
      (Nat.cast_nonneg m)) hc)

/-- Integral ceiling of the ratio of two positive repetition demands. -/
@[expose] def repeatFactor (r₀ r₁ : ℕ) : ℕ := (r₁ + r₀ - 1) / r₀

/-- The computed ceiling supplies enough repeated benchmark calls. -/
theorem repeatFactor_sufficient {r₀ : ℕ} (h₀ : 0 < r₀) (r₁ : ℕ) :
    r₁ ≤ repeatFactor r₀ r₁ * r₀ := by
  have hmod := Nat.mod_lt (r₁ + r₀ - 1) h₀
  have heq := Nat.mod_add_div (r₁ + r₀ - 1) r₀
  unfold repeatFactor
  rw [Nat.mul_comm r₀] at heq
  omega

variable {J : Type} [DecidableEq J] [Fintype J]

omit [DecidableEq J] [Fintype J] in
/-- Source's risk-benchmark guarantee for the actual rational-cost greedy batch.
`δ=1-η`; the comparison ranges over every risk-feasible benchmark. Its
eligibility sets must be among the input oracles, with repetitions allowed.
No existence, attainment or approximation premise is required of an optimizer. -/
theorem greedy_risk_bill (I : PartialCover.Instance E J) (hground : I.ground = univ)
    (hU : I.ground.Nonempty) (as bs : List (Oracle E))
    (hcover : ∀ e : E, ∃ a ∈ as, e ∈ a.eligible)
    (hcost : ∀ b ∈ as, 0 ≤ b.cost) (hsub : ∀ b ∈ bs, b ∈ as)
    {q δ : ℝ} (hq : 0 < q) (hqone : q < 1) (hδ : 0 < δ) (hδone : δ < 1)
    (hrisk : (∑ e ∈ I.ground, q ^ chances e (bs.map Oracle.eligible)) ≤ δ) :
    let r₀ := repetitions q δ
    let r₁ := repetitions q (δ / Fintype.card E)
    let calls := batch as r₁
    (∑ e ∈ I.ground, q ^ chances e (calls.map Oracle.eligible)) ≤ δ ∧
    (bill calls : ℝ) ≤ (1 + Real.log (Fintype.card E * r₁)) *
      repeatFactor r₀ r₁ * (bill bs : ℝ) := by
  dsimp only
  have hcard : I.ground.card = Fintype.card E := by simp [hground]
  constructor
  · apply I.multicover_implies_risk hq hqone hδ hU
    intro e _
    rw [hcard]
    exact batch_chances as hcover _ e
  · apply batch_scaled_log_bill_le as bs (repetitions q δ) _ _ hcost hsub
    · intro e
      exact I.risk_implies_multicover hq hqone hδ _ hrisk e (by simp [hground])
    · exact repeatFactor_sufficient
        (by have := (I.repetition_thresholds hq hqone hδ hδone hU).1; omega) _

/-- The chosen greedy batch really has certified-completion probability at least
`1-δ` under the history-conditional source response hypothesis. This is about
the observed-response law, without a native sampling or deadline certificate. -/
theorem greedy_certified_completion (I : PartialCover.Instance E J)
    (hground : I.ground = univ) (hU : I.ground.Nonempty) (as : List (Oracle E))
    (hcover : ∀ e : E, ∃ a ∈ as, e ∈ a.eligible)
    {ρ p δ : ℝ} (hp : 0 < p) (hpone : p < 1) (hδ : 0 < δ)
    (K : ResponseKernel J)
    (had : I.Admissible ρ p K [] ∅
      ((batch as (repetitions (1-p) (δ / Fintype.card E))).map Oracle.eligible)) :
    1 - δ ≤ event
      (I.law ρ K [] ∅
        ((batch as (repetitions (1-p) (δ / Fintype.card E))).map Oracle.eligible))
      (fun P => I.covered P = I.ground ∧ I.cost P ≤ ρ * ∑ e ∈ I.ground, I.dual e) := by
  have hrisk : (∑ e ∈ I.ground, (1-p) ^ chances e
      ((batch as (repetitions (1-p) (δ / Fintype.card E))).map Oracle.eligible)) ≤ δ := by
    apply I.multicover_implies_risk (by linarith) (by linarith) hδ hU
    intro e _
    have hcard : I.ground.card = Fintype.card E := by simp [hground]
    rw [hcard]
    exact batch_chances as hcover _ e
  have h := I.certified_completion_bound ρ hp.le hpone.le K _ had
  exact (show 1 - δ ≤ 1 - ∑ e ∈ I.ground, (1-p) ^ chances e
    ((batch as (repetitions (1-p) (δ / Fintype.card E))).map Oracle.eligible) by linarith).trans
      ((le_max_right _ _).trans h)

end Cslib.Algorithms.Lean.Multicover
