/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.SelectionLowerBound

/-!
# Necessary deadlines for arbitrary selection-only policies

Theorem 5(2) of [Wang2027], PDF p. 12, Appendix A.5, p. 16. Physical
latency per issued batch bounds the number of completed calls by the deadline.
The probability comparison uses actual revealed proposals and the arbitrary
randomized policy, without independence of actual responses.

## Main results

* `latency_ge_calls`, `count_eq_deadline_prefix`: derive the physical call limit.
* `deadline_probability_le`, `universal_lower_bounds`: necessary binomial deadline and token bounds.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.SelectionPolicy
open Cslib.Optimization.OneConstraint AdaptiveSelection PartialCover Finset MeasureTheory
variable {B R J E : Type} [Fintype B] [Fintype R] [Fintype J]
  [DecidableEq J] [DecidableEq E]

private theorem progressExpectation_le_supported {Ω : Type} [Fintype Ω]
    (law : List Ω → Distribution Ω ℝ) (b : List Ω → Ω → Bool)
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hprob : ∀ h, Reachable law h → (law h).mean (fun x => if b h x then 1 else 0) ≤ p)
    (f : ℕ → ℝ) (hf : Monotone f) (n : ℕ) (h : List Ω) (hh : Reachable law h) (k : ℕ) :
    progressExpectation law b f n h k ≤ bernoulliExpectation p f n k := by
  induction n generalizing h k with
  | zero => exact le_rfl
  | succ n ih =>
    have hm := bernoulliExpectation_mono p hp hp' f hf n
    have he : (fun x => bernoulliExpectation p f n (k + if b h x then 1 else 0)) =
        (fun x => bernoulliExpectation p f n k +
          (bernoulliExpectation p f n (k + 1) - bernoulliExpectation p f n k) *
            (if b h x then 1 else 0)) := by
      funext x
      split_ifs <;> simp
    calc
      _ ≤ (law h).mean (fun x => bernoulliExpectation p f n
          (k + if b h x then 1 else 0)) := by
        apply sum_le_sum
        intro x _
        by_cases hx : (law h).weight x = 0
        · simp [hx]
        · exact mul_le_mul_of_nonneg_left
            (ih _ (.cons hh (lt_of_le_of_ne ((law h).nonneg x) (Ne.symm hx))) _)
            ((law h).nonneg x)
      _ = bernoulliExpectation p f n k +
          (bernoulliExpectation p f n (k + 1) - bernoulliExpectation p f n k) *
            (law h).mean (fun x => if b h x then 1 else 0) := by
        rw [he, Distribution.mean_add, Distribution.mean_const, Distribution.mean_mul]
      _ ≤ bernoulliExpectation p f n k +
          (bernoulliExpectation p f n (k + 1) - bernoulliExpectation p f n k) * p :=
        add_le_add_right (mul_le_mul_of_nonneg_left (hprob h hh)
          (sub_nonneg.mpr (hm (Nat.le_succ k)))) _
      _ = _ := by simp only [bernoulliExpectation]; ring

/-- The actual revealed-progress tail for an arbitrary policy has the binomial
upper bound under the supported selected-batch upper envelope. -/
theorem revealed_tail_le (O : Oracle B R J) (π : Policy B R J) (I : Instance E J)
    (b r u : ℕ) (p : Set.Icc (0 : ℝ) 1) (c ℓ : ℝ) (H : LowerBounds O π I b p c ℓ) :
    historyExpectation (law O π)
      (fun h => if r ≤ count (reveals I (proposals O)) h then (1 : ℝ) else 0) u [] ≤
      ∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial u p := by
  have hp (h : List (Record B R)) (hh : Reachable (law O π) h) :
      (law O π h).mean (fun x => if reveals I (proposals O) h x then 1 else 0) ≤ p := by
    apply (conditional_means O π I b p c ℓ H h hh).1.trans
    have hi : (law O π h).mean (fun x => if issued h x then (1 : ℝ) else 0) ≤ 1 := by
      calc
        _ ≤ (law O π h).mean (fun _ => 1) := by
          apply sum_le_sum
          intro x _
          apply mul_le_mul_of_nonneg_left _ ((law O π h).nonneg x)
          dsimp only
          split_ifs <;> norm_num
        _ = 1 := Distribution.mean_const (law O π h) 1
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hi p.2.1
  rw [historyExpectation_count (law O π) (reveals I (proposals O))
    (fun k => if r ≤ k then 1 else 0) u []]
  have ht := progressExpectation_le_supported (law O π) (reveals I (proposals O))
    p p.2.1 p.2.2 hp (fun k => if r ≤ k then 1 else 0) (by
      intro i j hij
      dsimp only
      split_ifs <;> norm_num; omega) u [] .nil 0
  rw [bernoulliExpectation_eq_integral] at ht
  simpa only [count, Nat.zero_add] using ht

/-- Universal physical latency gives a pathwise lower bound on elapsed time by
number of actual issued calls, even when proposals are buffered without retention. -/
theorem latency_ge_calls (O : Oracle B R J) (π : Policy B R J) (I : Instance E J)
    (b : ℕ) (p c ℓ : ℝ) (H : LowerBounds O π I b p c ℓ)
    (h : List (Record B R)) (hh : Reachable (law O π) h) :
    ℓ * (count issued h : ℝ) ≤ accruedBill (latency O) h := by
  induction hh with
  | nil => simp [count, accruedBill]
  | @cons h x hh hx ih =>
    cases x with
    | none => simpa only [count, issued, Option.isSome_none, Bool.false_eq_true,
        ite_false, Nat.add_zero, accruedBill, latency, add_zero] using ih
    | some z =>
      rcases z with ⟨a, x⟩
      have hs := active_of_call O π h a x hx
      rw [law_weight_call O π h hs] at hx
      have hl := H.time h hh hs a (pos_of_mul_pos_left hx ((O.respond h a).nonneg x)) x
        (pos_of_mul_pos_right hx ((π.choose h).nonneg (some a)))
      simp only [count, issued, Option.isSome_some, ite_true, accruedBill, latency, Nat.cast_add,
        Nat.cast_one, mul_add, mul_one]
      linarith

omit [Fintype B] [Fintype R] in
private theorem calls_eq_length (h : List (Record B R)) (hh : none ∉ h) :
    count issued h = h.length := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    have hn : x ≠ none ∧ none ∉ h := by simpa [eq_comm] using hh
    cases x with
    | none => exact (hn.1 rfl).elim
    | some z => simp [count, issued, ih hn.2]

omit [Fintype B] [Fintype R] in
private theorem count_prefix_mono (f : List (Record B R) → Record B R → Bool)
    (ω : ℕ → Record B R) : Monotone (fun n => count f (responseHistory ω n)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [responseHistory_succ, count]
  omega

/-- Deadline-limited successful paths cannot gain any new revealed progress after
v=min(u,floor(D/ell)): calls are sequential and halt is absorbing. -/
theorem count_eq_deadline_prefix (O : Oracle B R J) (π : Policy B R J) (I : Instance E J)
    (b u : ℕ) (p c ℓ D : ℝ) (hℓ : 0 < ℓ) (H : LowerBounds O π I b p c ℓ)
    (ω : ℕ → Record B R) (hω : ∀ n, Reachable (law O π) (responseHistory ω n))
    (hD : accruedBill (latency O) (responseHistory ω u) ≤ D) :
    count (reveals I (proposals O)) (responseHistory ω u) =
      count (reveals I (proposals O)) (responseHistory ω (min u ⌊D / ℓ⌋₊)) := by
  let v := min u ⌊D / ℓ⌋₊
  have hk : count issued (responseHistory ω u) ≤ ⌊D / ℓ⌋₊ := by
    apply Nat.le_floor
    apply (le_div_iff₀ hℓ).mpr
    have hl := latency_ge_calls O π I b p c ℓ H _ (hω u)
    nlinarith
  have hn (t : ℕ) (hvt : v ≤ t) (htu : t < u) : ω t = none := by
    cases he : ω t with
    | none => rfl
    | some z =>
      rcases z with ⟨a, x⟩
      have hh := hω (t + 1)
      rw [responseHistory_succ, he] at hh
      cases hh with
      | cons hh hx =>
        have hs := active_of_call O π _ a x hx
        have hc := calls_eq_length (responseHistory ω t) hs
        have hlen : (responseHistory ω t).length = t := by simp [responseHistory]
        have hm := count_prefix_mono issued ω (show t + 1 ≤ u by omega)
        dsimp only at hm
        rw [responseHistory_succ, he, count] at hm
        simp only [issued, Option.isSome_some, ite_true] at hm
        rw [hc, hlen] at hm
        have hv : ⌊D / ℓ⌋₊ ≤ t := by dsimp [v] at hvt; omega
        omega
  have he : ∀ n, v ≤ n → n ≤ u →
      count (reveals I (proposals O)) (responseHistory ω n) =
        count (reveals I (proposals O)) (responseHistory ω v) := by
    intro n hvn
    induction n, hvn using Nat.le_induction with
    | base => intro _; rfl
    | succ n hvn ih =>
      intro hnu
      rw [responseHistory_succ, hn n hvn (by omega), count]
      simp only [reveals_none, Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih (by omega)
  exact he u (min_le_left _ _) le_rfl

/-- The source's necessary binomial deadline bound for arbitrary adaptive,
randomized admissible output: at most min(u,floor(D/ell)) calls can finish by D. -/
theorem deadline_probability_le (O : Oracle B R J) (π : Policy B R J) (I : Instance E J)
    (hA : Admissible O π) (b r u : ℕ) (hr : ∀ k < r, b * k < I.ground.card)
    (p : Set.Icc (0 : ℝ) 1) (c ℓ ρ D : ℝ) (hℓ : 0 < ℓ)
    (H : LowerBounds O π I b p c ℓ) :
    successProbability O π I ρ D u ≤
      ∫ i, (if r ≤ i then (1 : ℝ) else 0)
        ∂ProbabilityTheory.binomial (min u ⌊D / ℓ⌋₊) p := by
  classical
  let : MeasurableSpace (Record B R) := ⊤
  let : MeasurableSingletonClass (Record B R) := ⟨fun _ => trivial⟩
  let v := min u ⌊D / ℓ⌋₊
  have hi : Integrable (fun ω => success O π I ρ D (responseHistory ω u))
      (responseMeasure (law O π)) :=
    Integrable.of_bound (measurable_responseHistory u (success O π I ρ D)).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (success_bounds O π I ρ D _).1]
        exact (success_bounds O π I ρ D _).2)
  have hj : Integrable (fun ω => if r ≤ count (reveals I (proposals O)) (responseHistory ω v)
      then (1 : ℝ) else 0) (responseMeasure (law O π)) :=
    Integrable.of_bound (measurable_responseHistory v
      (fun h => if r ≤ count (reveals I (proposals O)) h then 1 else 0)).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun ω => by split_ifs <;> norm_num)
  have hle : (fun ω => success O π I ρ D (responseHistory ω u)) ≤ᵐ[responseMeasure (law O π)]
      (fun ω => if r ≤ count (reveals I (proposals O)) (responseHistory ω v) then 1 else 0) := by
    filter_upwards [ae_responseHistory_reachable (law O π)] with ω hω
    by_cases hd : accruedBill (latency O) (responseHistory ω u) ≤ D
    · have he := count_eq_deadline_prefix O π I b u p c ℓ D hℓ H ω hω hd
      have hs := success_le_count_tail O π I hA b r hr p c ℓ ρ D H _ (hω u)
      simpa only [he] using hs
    · rw [success_eq_zero_of_late O π I ρ D _ hd]
      split_ifs <;> norm_num
  rw [successProbability_eq_integral]
  apply (integral_mono_ae hi hj hle).trans
  rw [integral_responseHistory (law O π)
    (fun h => if r ≤ count (reveals I (proposals O)) h then 1 else 0) v]
  exact revealed_tail_le O π I b r v p c ℓ H

/-- Full finite-alphabet lower conclusion simultaneously for every admissible
randomized policy achieving eta: token lower bound and necessary deadline tail. -/
theorem universal_lower_bounds (O : Oracle B R J) (I : Instance E J)
    (b r u : ℕ) (hr : ∀ k < r, b * k < I.ground.card)
    (p : Set.Icc (0 : ℝ) 1) (hp : 0 < (p : ℝ)) (c ℓ ρ D η : ℝ)
    (hc : 0 ≤ c) (hℓ : 0 < ℓ) (hη0 : 0 ≤ η) (H : UniversalBounds O I b p c ℓ) :
    ∀ π : Policy B R J, Admissible O π → η ≤ successProbability O π I ρ D u →
      η * (r : ℝ) * c / p ≤ expectedCost O π u ∧
      η ≤ ∫ i, (if r ≤ i then (1 : ℝ) else 0)
        ∂ProbabilityTheory.binomial (min u ⌊D / ℓ⌋₊) p := by
  intro π hA hη
  exact ⟨lower_cost O π I hA b r u hr p c ℓ ρ D η hp hc hη0 (H π hA) hη,
    hη.trans (deadline_probability_le O π I hA b r u hr p c ℓ ρ D hℓ (H π hA))⟩

end Cslib.Probability.StochasticOracle.SelectionPolicy
