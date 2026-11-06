/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyEvaluatorInitial
public import Complexity.Foundations.Probability.HierarchyCanonicalRange

/-!
# Executed initial RAW relative propagation

The actual initial input uses positive lower-budget dense leaves, whose own rooted
errors are zero (`evaluate_lower_dense_contract`), and the actual zero correction
(`positiveSample_initial`). Its product term is therefore zero; it has no negative
ray. This is an initial input edge, not residual accuracy substituted for input IH.

Keep the genuine denominator `f + C` through the literal dyadic completion. The
payment below consists of unconditional spectral noise and the exact finite-bin
mean deficit, including fine exhaustion and the coarse boundary. Bin importance,
actual rounded slice densities, source normalization and suffixes stay inside these
quantities. No ordinary allowance is converted freely to relative accuracy. The
payment still needs a scalar reserve comparison; it need not decay for an arbitrary
finite bin family. For example a half-bin has a persistent mean deficit.

Both initial actual and pilot inputs are covered. Later inputs with nonzero
correction products need new lower-child relative/root transfers, source-reset
costs and mean/omission payments. The next concrete edge is `pilotInput 1`:
its left child is `pilotNormalized 0` on the parent source and midpoint, and
its right dense child resets the source to the midpoint with empty suffix.
Their product carries the actual midpoint-density reciprocal; the direct child
keeps endpoint usage `min(a,b)`. Neither input route has a negative ray; the
residual's once-negative ray is a separate remaining task. No changing-request
joint availability, full recursive invariant, uniform precision allocation or native
endpoint follows.
These are original consequences of the existing initial execution/noise API.

## Main results

* `initialFinalInput`: literal telescoped positive samples at both endpoint budgets.
* `evaluate_initial_relative_payment`: executed RAW relative error from computed costs.
* `canonicalPreparationInput_initial`: the genuine initial reference is the base.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability Cslib.RowCompression NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- The actual fine and coarse boundaries after summing all dyadic groups.
`initialSample` retains each direct child's bin rate and own usage importance.
Positive endpoints use actual dense child contracts; exhausted endpoints call nobody. -/
@[expose] def initialFinalInput (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  fun σ x y => ∑ bin ∈ B.bins,
    ((if LogSpaceEstimation.lastBudget M
        (dyadicSlack (Nat.log2 M + 1) (Nat.log2 M)) B.slack
        (B.sampleScale r (some bin)) = 0 then 0 else B.initialSample r bin σ x y) -
      (if LogSpaceEstimation.lastBudget M
        (2 * dyadicSlack (Nat.log2 M + 1) 0) B.slack
        (B.sampleScale r (some bin)) = 0 then 0 else B.initialSample r bin σ x y))

/-- A computed payment, not a desired parent-error premise. Noise is unconditional;
the mean term keeps `f+C` inside its own joint source/usage norm. -/
@[expose] def initialRawRelativePayment (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P)) : ℝ :=
  let X := retainedMask s (side P ks) B.padding ss
  let U := retainedMask t (side P ka) B.padding st
  8 * (B.initialRelativeNoiseBudget M r s t hst ks ka ss st B.base (Nat.log2 M + 1) +
    rowNormPow 4 P r.source.rate X U (fun _ x y =>
      (rowSliceMean X U (B.initialFinalInput M {r with usage := r.terminal}) x y -
        B.base x y) / (rate ka + B.base x y)))

/-- The initial canonical input is the base for either route and every channel tuple.
This says nothing about a later correction input. -/
theorem canonicalPreparationInput_initial (pilot : Bool)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    B.canonicalPreparationInput pilot ⟨0, HP.k_pos⟩ r = B.base := by
  cases pilot
  · simp [canonicalPreparationInput, HierarchyParams.correctionInput,
      HierarchyParams.correctionIter, cutoffCorrectionIter]
  · simp [canonicalPreparationInput, PilotTask.value, pilotInput, pilotCorrection_zero]

/-- Positive lower-budget dense calls and zero correction calls construct the actual
RAW row. Stationarity and the existing relative spectral payment then propagate its
accuracy, with a literal finite mean cost. No supplied RAW error/history is used.
Rate alignment additionally derives the canonical range with fixed `d=k+1`.
The two conclusions can feed `evaluate_preparation_relative_root` after a scalar
comparison of `initialRawRelativePayment` with the chosen own relative allowance. -/
theorem evaluate_initial_relative_payment (M : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (pilot : Bool)
    (hr : r.task = .row 0 (if pilot then .pilotInput ⟨0, HP.k_pos⟩ else
      .input ⟨0, HP.k_pos⟩))
    (hu : r.usage = r.terminal) (hp : 0 < B.requestPrecision M r)
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, B.base x y ≤ r.terminal.rate) :
    (∀ x y, B.canonicalPreparationInput pilot ⟨0, HP.k_pos⟩ r x y ∈
      Set.Icc 0 (((HP.k : ℝ) + 1) * r.terminal.rate)) ∧
    ∃ A, B.evaluate M r = some (.row A) ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y)
        (fun σ x y => (A σ x y - B.base x y) / (r.terminal.rate + B.base x y)) ≤
          B.initialRawRelativePayment M r s t hst ks ka ss st := by
  refine ⟨B.canonicalPreparationInput_range pilot ⟨0, HP.k_pos⟩ r
    (by rw [ht]; exact rate_pos ka) hC hC1 hCf, ?_⟩
  obtain ⟨F, hex⟩ : ∃ F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ,
      B.initialPrefixes M r = some F :=
    ⟨_, (B.initialPrefixes_grid M hM hbins r s t hst ks ka ss st hs ht).1⟩
  let Xs := retainedMask s (side P ks) B.padding ss
  let U := retainedMask t (side P ka) B.padding st
  have hmean (x y : ZMod P) : rowSliceMean Xs U (F (Nat.log2 M + 1)) x y =
      rowSliceMean Xs U (B.initialFinalInput M {r with usage := r.terminal}) x y := by
    change rowSliceMean (X s (side P ks) (CopyPadding.identifier B.padding ss))
      (Y t (side P ka) (CopyPadding.identifier B.padding st)) _ _ _ = _
    rw [B.initialPrefix_mean M hM hbins r s t hst ks ka ss st hs ht F hex]
    simp only [min_self, rowSliceMean, ← expect_sum_comm]
    congr 1
    funext σ
    exact B.initialGroupInput_sum M (Nat.log2 M + 1) (Nat.log2 M)
      (by omega) {r with usage := r.terminal} σ x y
  have hn := B.initialPrefix_relative_noise M hM hbins r s t hst ks ka ss st
    hs ht F hex B.base (Nat.log2 M + 1)
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hsplit := rowNormPow_add_le (X := Xs) (Y := U) hNu
    (fun σ x y => (F (Nat.log2 M + 1) σ x y -
      rowSliceMean Xs U (F (Nat.log2 M + 1)) x y) / (rate ka + B.base x y))
    (fun _ x y => (rowSliceMean Xs U (F (Nat.log2 M + 1)) x y -
      B.base x y) / (rate ka + B.base x y))
  have hadd (a b c d : ℝ) : (a - b) / d + (b - c) / d = (a - c) / d := by ring
  simp only [hadd] at hsplit
  change rowNormPow 4 P r.source.rate Xs U (fun σ x y =>
    (F (Nat.log2 M + 1) σ x y - rowSliceMean Xs U (F (Nat.log2 M + 1)) x y) /
      (rate ka + B.base x y)) ≤ _ at hn
  simp_rw [hmean] at hsplit hn
  refine ⟨F (Nat.log2 M + 1), B.evaluate_initial_prefix M r pilot hr hu hp F hex, ?_⟩
  have hb := hsplit.trans (mul_le_mul_of_nonneg_left (add_le_add hn le_rfl) (by norm_num))
  simpa only [rowNormPow, initialRawRelativePayment, Xs, U, hs, hu, ht,
    gridChannel, CorrectionRowTask.Channel.retains, channels, semanticSide_grid,
    retainedMask] using hb

/-- One executed initial RAW → incoming PREP → fixed-numerator rooted consumer.
Only the computed finite payment is compared with the own relative allowance;
RAW accuracy and both executions are conclusions. The fixed `L` precedes fields,
requests and rates. Scalar salary into any further normalized budget is separate. -/
theorem evaluate_initial_preparation_relative_root :
    ∃ L : ℝ, 0 ≤ L ∧
    ∀ (P : ℕ) [Fact P.Prime] (B : BudgetData HP P) (M : ℕ) (pilot : Bool)
      (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
    r.task = .row 0 (if pilot then .pilotPreparation ⟨0, HP.k_pos⟩ else
      .preparation ⟨0, HP.k_pos⟩) →
    Admissible r → 0 < B.requestPrecision M r → 0 < B.childBudget M →
    B.childBudget M < M → r.usage = r.terminal →
    ∀ (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P)),
    r.source = gridChannel s ks ss → r.terminal = gridChannel t ka st →
    B.bins.Nonempty → (∀ x y, 0 ≤ B.base x y) → B.base *ᵥ 1 ≤ 1 →
    (∀ x y, B.base x y ≤ r.terminal.rate) →
    let q := {r with task := .row 0 (if pilot then .pilotInput ⟨0, HP.k_pos⟩ else
      .input ⟨0, HP.k_pos⟩)}
    0 < B.requestPrecision (B.childBudget M) q → ∀ ε : ℝ,
    B.initialRawRelativePayment (B.childBudget M) q s t hst ks ka ss st ≤ ε ^ 4 →
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    ∃ A W, B.evaluate (B.childBudget M) q = some (.row A) ∧
      B.evaluate M r = some (.row W) ∧
      rowNormPow 4 P r.source.rate X U (fun σ x y =>
        (A σ x y - B.base x y) / (r.terminal.rate + B.base x y)) ≤ ε ^ 4 ∧
      ∀ (raw : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
        (maximum : Environment P 3 → ZMod P → ℝ),
      let output := fun prep => correctionRequest B.padding id r
        (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
        HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ raw prep maximum
      rootDistPow 4 P r.source.rate X U (output W)
        (output (B.incomingPreparation r (fun _ => B.base))) ≤
        HP.Q HP.toHierarchyParams.atomCap / 8 *
          (L * (1 + ((HP.k : ℝ) + 1))) ^ 4 * ε ^ 4 := by
  obtain ⟨L, hL, htransfer⟩ := evaluate_preparation_relative_root (HP := HP)
  refine ⟨L, hL, ?_⟩
  intro P instP B M pilot r hr had hp hm0 hm hu s t hst ks ka ss st hs ht
    hbins hC hC1 hCf q hqp ε hpay Xs U
  obtain ⟨hG, A, hA, hrel⟩ := B.evaluate_initial_relative_payment
    (B.childBudget M) hm0 hbins q pilot rfl hu hqp s t hst ks ka ss st hs ht hC hC1 hCf
  have hpaid := hrel.trans hpay
  have hW := B.evaluate_preparation_grid M pilot ⟨0, HP.k_pos⟩ r hr hp hm A hA
    s t hst ks ka ss st hs (hu.trans ht)
  refine ⟨A, _, hA, hW, hpaid, ?_⟩
  intro raw maximum
  have hb := htransfer P B M pilot ⟨0, HP.k_pos⟩ r hr had hp hm hu
    (by rw [hs]; exact (rate_pos ks).le) (by rw [ht]; exact rate_pos ka)
    A _ hqp hA hW ((HP.k : ℝ) + 1) ε (by positivity)
  simp only [B.canonicalPreparationInput_initial] at hb hG
  exact (hb hG hpaid s t hst ks ka ss st hs (hu.trans ht) raw maximum).2

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
