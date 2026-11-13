/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.DangerousProbability
public import CslibFrontier.Computability.Communication.Lifting.Dangerous
public import CslibFrontier.Computability.Communication.Lifting.DensitySimulation
public import CslibFrontier.Computability.Communication.Lifting.UnsafeWitness
public import CslibFrontier.Computability.Communication.Lifting.RatioWitness
public import CslibFrontier.Computability.Communication.Lifting.RatioProbability
public import CslibFrontier.Computability.Communication.Lifting.RatioCounting
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.Linarith

/-!
# Dangerous values and density-preserving steps

A finite family covering all unsafe inputs converts the conditional parity sampling estimates
into a bound on the number of unsafe inputs. The intermediate lemmas retain explicit family
budgets. The final theorem `card_le_two_mul_card_safe_of_discrepancy` discharges coverage,
integer-order selection, and witness counting: its hypotheses involve only source densities,
alphabet and coordinate sizes, the single-block gadget discrepancy, and scalar parameters
`r`, `u`, and `q`. It proves that at least half of the speaker's source is safe.

`exists_densityStep_of_discrepancy` feeds that estimate into the proved simulation step. Its
message and query set are chosen before the query answers, and both resulting sources remain
nonempty with the prescribed densities for every answer.

These are finite quantitative versions of the dangerous-value mechanism in CFKMP Lemma 3.9 and
Section 4.1, using a weaker fourth-power XOR estimate and correspondingly different constants.
No asymptotic choice of gadget size or complete protocol-to-decision-tree compiler is asserted.

## Main results

* `card_le_two_mul_card_safe_of_discrepancy`: safe inputs occupy at least half the source.
* `exists_densityStep_of_discrepancy`: a density-preserving step from numerical assumptions.
* `exists_pair_of_discrepancy`: terminal full range from the same numerical assumptions.

## References

* [Chattopadhyay, Filmus, Koroth, Meir and Pitassi, *Query-to-Communication Lifting Using
  Low-Discrepancy Gadgets*, arXiv:1904.13056v4][ChattopadhyayFilmusKorothMeirPitassi2021]
-/

public section

namespace Cslib.Communication.Lifting

open Finset Probability

variable {n m : ℕ}

open scoped Classical in
/-- A finite family of conditional parity witnesses bounds the number of unsafe inputs. -/
theorem card_unsafe_le_of_parityTest_cover {κ : Type*} [Fintype κ] [NeZero m]
    {F : Finset (Fin n)} {X Y : Finset (Fin n → Fin m)}
    (w : κ → ParityTest F Y) (g : Fin m → Fin m → Bool)
    {τX τY σ : ℝ} (hX : IsDense τX F X) (hY : IsDense τY F Y)
    (hτX : 0 < τX) (hτY : 0 < τY) (hXne : X.Nonempty)
    (t β : κ → ℝ) (ht : ∀ k, 0 < t k) (hβ : ∀ k, 0 < β k)
    (hbound : ∀ k, (w k).tailCost g τX τY ≤ t k * β k)
    (hcover : ∀ x ∈ X, ¬ IsSafe g σ F Y x → ∃ k, t k < (w k).bias g x) :
    (#(X.filter fun x => ¬ IsSafe g σ F Y x) : ℝ) ≤ (∑ k, β k) * #X := by
  classical
  have htail := probability_exists_parityTest_le w g hX hY hτX hτY hXne t β ht hβ hbound
  rw [PMF.toOuterMeasure_uniformOfFinset_toReal] at htail
  have hcard : (0 : ℝ) < #X := by exact_mod_cast hXne.card_pos
  have hbad := (div_le_iff₀ hcard).mp htail
  refine le_trans ?_ hbad
  exact_mod_cast card_le_card (show X.filter (fun x => ¬ IsSafe g σ F Y x) ⊆
      X.filter (fun x => ∃ k, t k < (w k).bias g x) from by
    intro x hx
    exact mem_filter.mpr ⟨(mem_filter.mp hx).1,
      hcover x (mem_filter.mp hx).1 (mem_filter.mp hx).2⟩)

open scoped Classical in
/-- A total conditional-parity tail budget of one half leaves at least half of the speaker's
source safe. This is the exact safety-size premise of `exists_densityStep`. -/
theorem card_le_two_mul_card_safe_of_parityTest_cover {κ : Type*} [Fintype κ] [NeZero m]
    {F : Finset (Fin n)} {X Y : Finset (Fin n → Fin m)}
    (w : κ → ParityTest F Y) (g : Fin m → Fin m → Bool)
    {τX τY σ : ℝ} (hX : IsDense τX F X) (hY : IsDense τY F Y)
    (hτX : 0 < τX) (hτY : 0 < τY) (hXne : X.Nonempty)
    (t β : κ → ℝ) (ht : ∀ k, 0 < t k) (hβ : ∀ k, 0 < β k)
    (hbound : ∀ k, (w k).tailCost g τX τY ≤ t k * β k)
    (hcover : ∀ x ∈ X, ¬ IsSafe g σ F Y x → ∃ k, t k < (w k).bias g x)
    (hbudget : ∑ k, β k ≤ 1 / 2) :
    (#X : ℝ) ≤ 2 * #(X.filter (IsSafe g σ F Y)) := by
  classical
  have hbad := card_unsafe_le_of_parityTest_cover w g hX hY hτX hτY hXne t β ht hβ hbound hcover
  have hsplit := card_filter_add_card_filter_not (s := X) (IsSafe g σ F Y)
  have hsplitR : (#(X.filter (IsSafe g σ F Y)) : ℝ) +
      #(X.filter fun x => ¬ IsSafe g σ F Y x) = #X := by exact_mod_cast hsplit
  have hmul := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg X.card : (0 : ℝ) ≤ #X)
  linarith

/-- Conditional parity-tail estimates supply a valid density-preserving step when their
witness family covers unsafe inputs and has total budget at most one half. The selected
message and queried coordinates are chosen before the answers, as recorded by `Valid`. -/
theorem exists_densityStep_of_parityTest_cover {κ : Type*} [Fintype κ] [NeZero m]
    {F : Finset (Fin n)} {X Y : Finset (Fin n → Fin m)}
    (w : κ → ParityTest F Y) (g : Fin m → Fin m → Bool)
    {τX τY τ σ : ℝ} (hX : IsDense τX F X) (hY : IsDense τY F Y)
    (hτX : 0 < τX) (hτY : 0 < τY) (hτ : 0 < τ)
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (t β : κ → ℝ) (ht : ∀ k, 0 < t k) (hβ : ∀ k, 0 < β k)
    (hbound : ∀ k, (w k).tailCost g τX τY ≤ t k * β k)
    (hcover : ∀ x ∈ X, ¬ IsSafe g σ F Y x → ∃ k, t k < (w k).bias g x)
    (hbudget : ∑ k, β k ≤ 1 / 2) (send : (Fin n → Fin m) → Bool) :
    ∃ st : DensityStep n m, st.Valid g τ σ F X Y send :=
  exists_densityStep g τ σ F X Y send hτ hXne hYne
    (card_le_two_mul_card_safe_of_parityTest_cover w g hX hY hτX hτY hXne
      t β ht hβ hbound hcover hbudget)

namespace ParityTest

/-- Eligible canonical parity tests. The larger output set is existentially quantified, so it
is not counted as extra data when the same parity witness can arise from several output sets. -/
structure IsEligible [NeZero m] {F : Finset (Fin n)} {Y : Finset (Fin n → Fin m)}
    (order : (I J : Finset (Fin n)) → (J → Fin m) → ℕ) (w : ParityTest F Y) : Prop where
  /-- Assignments outside the conditioning coordinates are zero. -/
  canonical : w.IsCanonical
  /-- Empty parities cannot witness bias. -/
  nonempty : w.parity.Nonempty
  /-- Some output set certifies eligibility of the conditional order. -/
  eligible : ∃ I ⊆ F, w.parity ⊆ I ∧
    (w.conditioned = ∅ ∨ (w.conditioned.Nonempty ∧ w.conditioned ⊆ F \ I ∧
      order I w.conditioned (w.conditioned.restrict w.assignment) ≤ w.parity.card))

end ParityTest

open scoped Classical in
/-- The concrete finite dangerous-values estimate. The canonical eligible family comes from
the proved unsafe-to-parity reduction, rather than an assumed covering family. Its integer
orders, per-witness discrepancy budgets and total finite budget are all explicit. -/
theorem card_le_two_mul_card_safe_of_eligible_budget [NeZero m]
    {F : Finset (Fin n)} {X Y : Finset (Fin n → Fin m)}
    (g : Fin m → Fin m → Bool) {τX τY σ : ℝ}
    (hX : IsDense τX F X) (hY : IsDense τY F Y)
    (hτX : 0 < τX) (hτY : 0 < τY) (hσ : 0 ≤ σ)
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (order : (I J : Finset (Fin n)) → (J → Fin m) → ℕ)
    (horder : ∀ I ⊆ F, ∀ J ⊆ F \ I, J.Nonempty → ∀ a : J → Fin m,
      ∀ _hA : (agreeOn Y J (ParityTest.extendAssignment J a)).Nonempty,
      1 ≤ order I J a ∧
        2 * (#{S : Finset I | S.card < order I J a} + 1 : ℝ) * σ ^ #J *
          #(agreeOn Y J (ParityTest.extendAssignment J a)) ≤ #Y)
    (β : {w : ParityTest F Y // w.IsEligible order} → ℝ)
    (hβ : ∀ w, 0 < β w)
    (hcost : ∀ w, w.val.tailCost g τX τY ≤
      ((1 / 2 : ℝ) * (1 / (2 * n) : ℝ) ^ w.val.parity.card) * β w)
    (hbudget : ∑ w, β w ≤ 1 / 2) :
    (#X : ℝ) ≤ 2 * #(X.filter (IsSafe g σ F Y)) := by
  classical
  apply card_le_two_mul_card_safe_of_parityTest_cover
    (fun w : {w : ParityTest F Y // w.IsEligible order} => w.val)
    g hX hY hτX hτY hXne
    (fun w => (1 / 2 : ℝ) * (1 / (2 * n) : ℝ) ^ w.val.parity.card)
    β ?_ hβ hcost ?_ hbudget
  · intro w
    obtain ⟨i, _⟩ := w.property.nonempty
    have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
    positivity
  · intro x _ hx
    obtain ⟨I, w, hI, hcan, hpI, hpne, hel, hb⟩ :=
      exists_parityTest_of_not_isSafe g σ F Y hYne hσ order horder x hx
    exact ⟨⟨w, hcan, hpne, I, hI, hpI, hel⟩, hb⟩

open scoped Classical in
/-- A concrete eligible-parity budget supplies the full pre-answer simulation-step certificate.
No separate safety or witness-coverage premise is assumed. -/
theorem exists_densityStep_of_eligible_budget [NeZero m]
    {F : Finset (Fin n)} {X Y : Finset (Fin n → Fin m)}
    (g : Fin m → Fin m → Bool) {τX τY τ σ : ℝ}
    (hX : IsDense τX F X) (hY : IsDense τY F Y)
    (hτX : 0 < τX) (hτY : 0 < τY) (hτ : 0 < τ) (hσ : 0 ≤ σ)
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (order : (I J : Finset (Fin n)) → (J → Fin m) → ℕ)
    (horder : ∀ I ⊆ F, ∀ J ⊆ F \ I, J.Nonempty → ∀ a : J → Fin m,
      ∀ _hA : (agreeOn Y J (ParityTest.extendAssignment J a)).Nonempty,
      1 ≤ order I J a ∧
        2 * (#{S : Finset I | S.card < order I J a} + 1 : ℝ) * σ ^ #J *
          #(agreeOn Y J (ParityTest.extendAssignment J a)) ≤ #Y)
    (β : {w : ParityTest F Y // w.IsEligible order} → ℝ)
    (hβ : ∀ w, 0 < β w)
    (hcost : ∀ w, w.val.tailCost g τX τY ≤
      ((1 / 2 : ℝ) * (1 / (2 * n) : ℝ) ^ w.val.parity.card) * β w)
    (hbudget : ∑ w, β w ≤ 1 / 2) (send : (Fin n → Fin m) → Bool) :
    ∃ st : DensityStep n m, st.Valid g τ σ F X Y send :=
  exists_densityStep g τ σ F X Y send hτ hXne hYne
    (card_le_two_mul_card_safe_of_eligible_budget g hX hY hτX hτY hσ hXne hYne
      order horder β hβ hcost hbudget)

namespace ParityTest

/-- Intrinsically eligible tests: canonical nonempty parities whose conditioning ratio can
be paid by the parity size. This definition contains no auxiliary output set or integer order. -/
structure IsRatioEligible [NeZero m] {F : Finset (Fin n)} {Y : Finset (Fin n → Fin m)}
    (σ : ℝ) (w : ParityTest F Y) : Prop where
  /-- No irrelevant assignment values are retained. -/
  canonical : w.IsCanonical
  /-- The parity support is nonempty. -/
  nonempty : w.parity.Nonempty
  /-- Unconditional tests or a supported ratio bound are allowed. -/
  ratio : w.conditioned = ∅ ∨ (#Y : ℝ) ≤ (n : ℝ) ^ (2 * w.parity.card) *
    σ ^ w.conditioned.card * #(agreeOn Y w.conditioned w.assignment)

end ParityTest

open scoped Classical in
/-- The concrete ratio witness family supplies safety from a finite sum of sampling budgets.
Density supplies the required orders and witness coverage, so neither is a separate premise. -/
theorem card_le_two_mul_card_safe_of_ratio_budget [NeZero m]
    {F : Finset (Fin n)} {X Y : Finset (Fin n → Fin m)}
    (g : Fin m → Fin m → Bool) {τX τY σ : ℝ}
    (hX : IsDense τX F X) (hY : IsDense τY F Y)
    (hτX : 0 < τX) (hτY : 0 < τY) (hσ : 0 < σ)
    (hXne : X.Nonempty) (hYne : Y.Nonempty) (hn : 2 ≤ n)
    (hgap : 16 * (n : ℝ) ^ 2 ≤ τY / σ)
    (β : {w : ParityTest F Y // w.IsRatioEligible σ} → ℝ)
    (hβ : ∀ w, 0 < β w)
    (hcost : ∀ w, w.val.tailCost g τX τY ≤
      ((1 / 2 : ℝ) * (1 / (2 * n) : ℝ) ^ w.val.parity.card) * β w)
    (hbudget : ∑ w, β w ≤ 1 / 2) :
    (#X : ℝ) ≤ 2 * #(X.filter (IsSafe g σ F Y)) := by
  classical
  apply card_le_two_mul_card_safe_of_parityTest_cover
    (fun w : {w : ParityTest F Y // w.IsRatioEligible σ} => w.val)
    g hX hY hτX hτY hXne
    (fun w => (1 / 2 : ℝ) * (1 / (2 * n) : ℝ) ^ w.val.parity.card)
    β ?_ hβ hcost ?_ hbudget
  · intro w
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    positivity
  · intro x _ hx
    obtain ⟨w, hcan, hne, hratio, hb⟩ :=
      exists_ratio_parityTest_of_isDense_not_isSafe g τY σ F Y hYne hn hσ hY hgap x hx
    exact ⟨⟨w, hcan, hne, hratio⟩, hb⟩

open scoped Classical in
/-- **A finite numerical dangerous-values theorem.** The hypotheses involve only densities,
alphabet and coordinate sizes, single-block discrepancy, and three scalar counting parameters.
There is no assumed safety bound, witness cover, integer-order choice, or finite witness sum.
The constants reflect the elementary fourth-power XOR bound used in this development. -/
theorem card_le_two_mul_card_safe_of_discrepancy [NeZero m]
    {F : Finset (Fin n)} {X Y : Finset (Fin n → Fin m)}
    (g : Fin m → Fin m → Bool) {τX τY σ u q : ℝ} {r : ℕ}
    (hX : IsDense τX F X) (hY : IsDense τY F Y)
    (hτX : 0 < τX) (hτY : 0 < τY) (hσ : 0 < σ)
    (hXne : X.Nonempty) (hYne : Y.Nonempty) (hn : 2 ≤ n) (hr : 0 < r)
    (hgap : 16 * (n : ℝ) ^ 2 ≤ τY / σ)
    (hratio : (n : ℝ) ^ (2 * r) ≤ τY / σ)
    (hu : 1 ≤ u) (hsize : ((n * m : ℕ) : ℝ) ≤ u ^ r) (hq : 0 < q)
    (hweight : n * (((n + 1 : ℕ) : ℝ) * u * q) ≤ 1 / 2)
    (hdisc : 16384 * ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 / (τX * τY)) ^ 4 *
      discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g ≤ (q / (2 * n)) ^ 4) :
    (#X : ℝ) ≤ 2 * #(X.filter (IsSafe g σ F Y)) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnR2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hστ : σ ≤ τY := by
    have hdiv : 1 ≤ τY / σ := by nlinarith [sq_nonneg (n : ℝ)]
    simpa only [one_mul] using (le_div_iff₀ hσ).mp hdiv
  let P := fun w : ParityTest F Y => w.IsRatioEligible σ
  have hratioW (w : ParityTest F Y) (hw : P w) :
      (#Y : ℝ) ≤ (n : ℝ) ^ (2 * w.parity.card) * σ ^ w.conditioned.card *
        #(agreeOn Y w.conditioned w.assignment) := by
    rcases hw.ratio with he | he
    · exact w.ratio_card_le_of_conditioned_eq_empty hn1 σ he
    · exact he
  have hcount (w : ParityTest F Y) (hw : P w) : w.conditioned.card ≤ w.parity.card / r :=
    conditioningSize_le_div_of_ratio hn hr hratio
      (w.density_ratio_pow_le hY hσ (hratioW w hw))
  have hNm : 1 ≤ n * m := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (NeZero.ne m))
  have hnonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) * u * q := by positivity
  have hwgt : ((n + 1 : ℕ) : ℝ) * u * q ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hnR hnonneg]
  have hsum := sum_parityTest_pow_le_one P (fun _ hw => hw.canonical)
    (fun _ hw => hw.nonempty) (fun S => S.card / r) hcount hNm
    (by linarith : 0 ≤ u) hq.le
    (fun S _ => pow_div_le_pow_of_le_pow (s := S.card) hu hsize) hwgt hweight
  apply card_le_two_mul_card_safe_of_ratio_budget g hX hY hτX hτY hσ hXne hYne hn hgap
    (fun w => (1 / 2 : ℝ) * q ^ w.val.parity.card) (fun _ => by positivity) ?_ ?_
  · intro w
    exact w.val.tailCost_le_geometric_budget_of_ratio g hτX hτY hσ.le hστ hq hn1
      w.property.nonempty (hratioW w.val w.property) hdisc
  · rw [← mul_sum]
    nlinarith [hsum]

/-- Single-block discrepancy and finite numerical density/counting conditions produce a valid
simulation step, with no assumed safety or witness estimates. The speaker is restored to the
listener's original density while the listener retains density `σ`, for every query answer. -/
theorem exists_densityStep_of_discrepancy [NeZero m]
    {F : Finset (Fin n)} {X Y : Finset (Fin n → Fin m)}
    (g : Fin m → Fin m → Bool) {τX τY σ u q : ℝ} {r : ℕ}
    (hX : IsDense τX F X) (hY : IsDense τY F Y)
    (hτX : 0 < τX) (hτY : 0 < τY) (hσ : 0 < σ)
    (hXne : X.Nonempty) (hYne : Y.Nonempty) (hn : 2 ≤ n) (hr : 0 < r)
    (hgap : 16 * (n : ℝ) ^ 2 ≤ τY / σ)
    (hratio : (n : ℝ) ^ (2 * r) ≤ τY / σ)
    (hu : 1 ≤ u) (hsize : ((n * m : ℕ) : ℝ) ≤ u ^ r) (hq : 0 < q)
    (hweight : n * (((n + 1 : ℕ) : ℝ) * u * q) ≤ 1 / 2)
    (hdisc : 16384 * ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 / (τX * τY)) ^ 4 *
      discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g ≤ (q / (2 * n)) ^ 4)
    (send : (Fin n → Fin m) → Bool) :
    ∃ st : DensityStep n m, st.Valid g τY σ F X Y send :=
  exists_densityStep g τY σ F X Y send hτY hXne hYne
    (card_le_two_mul_card_safe_of_discrepancy g hX hY hτX hτY hσ hXne hYne hn hr
      hgap hratio hu hsize hq hweight hdisc)

/-- Terminal full range under the same numerical conditions as the simulation. A safe speaker
value has a nonempty fiber for every assignment on all remaining free coordinates. Thus no
separate parity-bound or full-range hypothesis is required at a terminal protocol node. -/
theorem exists_pair_of_discrepancy [NeZero m]
    {F : Finset (Fin n)} {X Y : Finset (Fin n → Fin m)}
    (g : Fin m → Fin m → Bool) {τX τY σ u q : ℝ} {r : ℕ}
    (hX : IsDense τX F X) (hY : IsDense τY F Y)
    (hτX : 0 < τX) (hτY : 0 < τY) (hσ : 0 < σ)
    (hXne : X.Nonempty) (hYne : Y.Nonempty) (hn : 2 ≤ n) (hr : 0 < r)
    (hgap : 16 * (n : ℝ) ^ 2 ≤ τY / σ)
    (hratio : (n : ℝ) ^ (2 * r) ≤ τY / σ)
    (hu : 1 ≤ u) (hsize : ((n * m : ℕ) : ℝ) ≤ u ^ r) (hq : 0 < q)
    (hweight : n * (((n + 1 : ℕ) : ℝ) * u * q) ≤ 1 / 2)
    (hdisc : 16384 * ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 / (τX * τY)) ^ 4 *
      discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g ≤ (q / (2 * n)) ^ 4)
    (answer : Fin n → Bool) :
    ∃ x ∈ X, ∃ y ∈ Y, ∀ i ∈ F, g (x i) (y i) = answer i := by
  classical
  have hsafe := card_le_two_mul_card_safe_of_discrepancy g hX hY hτX hτY hσ
    hXne hYne hn hr hgap hratio hu hsize hq hweight hdisc
  have hXpos : (0 : ℝ) < #X := by exact_mod_cast hXne.card_pos
  have hsafePos : (0 : ℝ) < #(X.filter (IsSafe g σ F Y)) := by linarith
  have hsafeNe : (X.filter (IsSafe g σ F Y)).Nonempty :=
    card_pos.mp (by exact_mod_cast hsafePos)
  obtain ⟨x, hx⟩ := hsafeNe
  obtain ⟨y, hy⟩ := (mem_filter.mp hx).2.fiber_nonempty hYne (Subset.refl F) answer
  exact ⟨x, (mem_filter.mp hx).1, y, (mem_gadgetFiber.mp hy).1, (mem_gadgetFiber.mp hy).2⟩

end Cslib.Communication.Lifting
