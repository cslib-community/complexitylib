/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchySignedMean
public import Complexity.Foundations.Probability.HierarchyBudgetEvaluator
import all Complexity.Foundations.Probability.HierarchyCutoffs
import all Complexity.Foundations.Probability.PilotRowTasks
import all Complexity.Foundations.Probability.HierarchySampling

/-!
# Genuine requested-iterate pilot correction means

The pilot reference uses its own input, its own incoming preparation on the actual
sampling source, and the current maximum at `j + 1`. It is distinct from the actual
correction reference with its fixed final maximum. The source can be narrower than
the stage rate, and usage can have any grid rate. Copy suffixes and all spectator
coordinates are retained in the single-environment split.

This is a true-child mean bridge, not estimated-child accuracy or availability.
Later product transport, finite payments and recursive evaluator correctness remain
open. The specialization is Christian Reitwiessner's original work using Samuel
Schlesinger's hierarchy construction.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment
open Finset Cslib Cslib.Probability
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime] {V : Type} [Fintype V]
  (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
  {n : ℕ} (r : HierarchyTask.Request n (Fin J) (ZMod P)) (hr : Admissible r)

/-- Requested pilot raw input in matrix units, using the true stage channels. -/
@[expose] def pilotRaw (C : Matrix V V ℝ) (j : ℕ) : Matrix V V ℝ :=
  PilotTask.value HP.toHierarchyParams (stageSource D ident r hr)
    (splitTerminal D ident r) r.terminal.rate C (.input j)

/-- The pilot's own incoming preparation uses the inherited sampling source. -/
@[expose] def pilotPreparation (C : Matrix V V ℝ) (j : ℕ)
    (σ : Environment P J) : Matrix V V ℝ :=
  CorrectionRowRecipe.preparation (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
    (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ r.terminal.rate
    (splitSource D ident r hr) (splitTerminal D ident r)
    (pilotRaw HP D ident r hr C j) (terminalSplit r.terminal.role σ)

/-- The preparatory denominator is the joint mean on the actual source/usage event. -/
theorem pilotPreparation_normalizer (C : Matrix V V ℝ) (j : ℕ) (x y : V) :
    CorrectionRowRecipe.normalizer (splitSource D ident r hr) (splitUsage D ident r)
      (fun p => pilotPreparation HP D ident r hr C j
        ((terminalSplit r.terminal.role).symm p)) x y =
    rowSliceMean (fun σ v => r.source.retains (channels D) σ (ident v))
      (fun σ v => r.usage.retains (channels D) σ (ident v))
      (pilotPreparation HP D ident r hr C j) x y := by
  convert normalizer_full D ident r hr (pilotPreparation HP D ident r hr C j) x y using 1
  rfl

/-- A genuine pilot normalized request, with current maximum `j + 1`. No dispatcher fallback. -/
@[expose] def pilotChild (C : Matrix V V ℝ) (j : ℕ)
    (σ : Environment P J) : Matrix V V ℝ :=
  correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
    HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
    (fun _ => pilotRaw HP D ident r hr C j) (pilotPreparation HP D ident r hr C j)
    (fun _ => PilotTask.value HP.toHierarchyParams (stageSource D ident r hr)
      (splitTerminal D ident r) r.terminal.rate C (.maximum (j + 1))) σ

/-- Exact request-to-recipe identity, including the actual source and usage normalizer. -/
theorem pilotChild_eq (C : Matrix V V ℝ) (j : ℕ) (σ : Environment P J) (x y : V) :
    pilotChild HP D ident r hr C j σ x y =
    CorrectionRowRecipe.normalized (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ r.terminal.rate
      (splitSource D ident r hr) (splitTerminal D ident r) (splitUsage D ident r)
      (pilotRaw HP D ident r hr C j)
      (CorrectionRowRecipe.preparation (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
        (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ r.terminal.rate
        (splitSource D ident r hr) (splitTerminal D ident r) (pilotRaw HP D ident r hr C j))
      (PilotTask.value HP.toHierarchyParams (stageSource D ident r hr)
        (splitTerminal D ident r) r.terminal.rate C (.maximum (j + 1)))
      (terminalSplit r.terminal.role σ) x y :=
  correctionRequest_eq_split HP D ident r hr _ _ _ σ x y

/-- The single-environment source mean is the requested pilot correction, with measured
usage density and current maximum. This does not assert an estimated-child IH. -/
theorem pilotChild_mean (hD : D ≠ 0) (hid : Function.Injective ident)
    (H : Horizon P) {k s u : ℕ} (hsH : s ≤ H.maxExponent) (hks : k ≤ s)
    (hs : r.source.rate = rate s) (ht : r.terminal.rate = rate k)
    (hu : r.usage.rate = rate u)
    (C : Matrix V V ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ r.terminal.rate) {j : ℕ} (hj : j < HP.k) (x y : V) :
    (𝔼 σ ∈ ({σ | r.source.retains (channels D) σ (ident x)} : Finset _),
      (r.terminal.rate / (dens {σ : Environment P J |
        r.usage.retains (channels D) σ (ident y)} : ℝ)) *
        pilotChild HP D ident r hr C j σ x y) =
      PilotTask.value HP.toHierarchyParams (stageSource D ident r hr)
        (splitTerminal D ident r) r.terminal.rate C (.correction (j + 1)) x y := by
  have hk := hks.trans hsH
  have hh := stage_channels D ident r hr hD hid H hk ht
  rw [← ht] at hh
  have hf : 0 < r.terminal.rate := ht ▸ rate_pos k
  have hπ : 0 < (((side P k : ℝ) / P)^4) := by linarith [hh.1.lower]
  have huπ : 0 < (((side P u : ℝ) / P)^4) := by
    have : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
    have : (0 : ℝ) < side P u := by
      exact_mod_cast side_pos P u (Fact.out : P.Prime).pos
    positivity
  let A := HP.pilotSampling (stageSource D ident r hr) (splitTerminal D ident r)
    hh.1 hh.2 hf hπ hC hC1 hj
  have hp : A.p = 32 * r.terminal.rate := rfl
  have hc : A.c = 32 := rfl
  have hsp : ∀ x w, w ≠ x →
      (#{a | splitSource D ident r hr a x ∧ splitSource D ident r hr a w} : ℝ) ≤
        A.p * #{a | splitSource D ident r hr a x} := by
    rw [hp]
    intro x w hw
    exact (source_pair_count D ident r hr hD hid H hsH hs x w hw).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (ht ▸ rate_antitone hks) (by norm_num)) (by positivity))
  have htp : ∀ z w, w ≠ z →
      (#{t | splitUsage D ident r t z ∧ splitTerminal D ident r t w} : ℝ) ≤
        A.c * r.terminal.rate * #{t | splitUsage D ident r t z} := by
    rw [hc]
    exact split_usage_pair D ident r hr hD hid H hk ht hu
  let T : HP.toHierarchyParams.PilotSampling (stageSource D ident r hr)
      (splitTerminal D ident r) (splitSource D ident r hr) (splitTerminal D ident r)
      (splitUsage D ident r) r.terminal.rate C j :=
    { toCorrectionSamplingLaws := { A.toCorrectionSamplingLaws with
        source_pair := hsp, π := (((side P u : ℝ) / P)^4), π_pos := huπ,
        density := split_usage_density D ident r hu, terminal_pair := htp } }
  have hm := (T.value_correction_mean hf hC hC1 hCf hj.le
    (source_nonempty D ident r hr hD hid H hsH hs x) y).symm
  simp only [HierarchyParams.PilotSampling.value, PilotRowRecipe.value] at hm
  unfold HierarchyParams.PilotSampling.normalizedRecipe
    HierarchyParams.PilotSampling.preparationRecipe at hm
  rw [channel_density D r.usage u hu, source_expect_split D ident r hr]
  simp_rw [pilotChild_eq HP D ident r hr C j, Equiv.apply_symm_apply]
  dsimp only [T, A, FourthRootHierarchyParams.pilotSampling,
    HierarchyParams.PilotSampling.ofChannels, CorrectionSamplingLaws.ofHierarchyChannels] at hm
  simpa only [pilotRaw] using hm

/-- Spectator integration and affine padding transport preserve every pilot correction
iterate, not just the final maximum. -/
theorem stage_pilotCorrection_eq_canonical (hD : D ≠ 0) (C : Matrix V V ℝ) (j : ℕ) :
    PilotTask.value HP.toHierarchyParams (stageSource D ident r hr)
      (splitTerminal D ident r) r.terminal.rate C (.correction j) =
    PilotTask.value HP.toHierarchyParams (canonicalChannel ident r.terminal.rate)
      (canonicalChannel ident r.terminal.rate) r.terminal.rate C (.correction j) := by
  have hU := funext (fun G => stage_columnDetector_eq_canonical HP D ident r hr hD G)
  simp only [PilotTask.value, hU]

/-- Usage zero extension holds for the genuine pilot family itself. -/
theorem pilotChild_zero_off_usage (C : Matrix V V ℝ) (j : ℕ)
    (σ : Environment P J) (x y : V)
    (hy : ¬ splitUsage D ident r (σ r.terminal.role) y) :
    pilotChild HP D ident r hr C j σ x y = 0 := by
  simp only [pilotChild, correctionRequest, dite_eq_left hr, CorrectionRowRecipe.normalized,
    Equiv.piSplitAt_apply]
  change (if splitUsage D ident r (σ r.terminal.role) y then _ else 0) = 0
  simp only [hy, ↓reduceIte]

/-- Inherited terminal conditioning retains its exact measured importance factor.
This reference is the pilot correction family, independently of the actual dispatcher. -/
theorem pilotChild_mean_on_terminal_event (hD : D ≠ 0) (hid : Function.Injective ident)
    (H : Horizon P) {k s u : ℕ} (hsH : s ≤ H.maxExponent) (hks : k ≤ s)
    (hs : r.source.rate = rate s) (ht : r.terminal.rate = rate k)
    (hu : r.usage.rate = rate u)
    (C : Matrix V V ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ r.terminal.rate) {j : ℕ} (hj : j < HP.k)
    (q : FrameChannel P 4 1 → Prop) [DecidablePred q]
    (x y : V) (hsub : ∀ A, splitUsage D ident r A y → q A) :
    (𝔼 σ ∈ ({σ : Environment P J |
      r.source.retains (channels D) σ (ident x) ∧ q (σ r.terminal.role)} : Finset _),
      (r.terminal.rate * ((dens {σ : Environment P J | q (σ r.terminal.role)} : ℝ) /
        dens {σ : Environment P J | r.usage.retains (channels D) σ (ident y)})) *
        pilotChild HP D ident r hr C j σ x y) =
      PilotTask.value HP.toHierarchyParams (canonicalChannel ident r.terminal.rate)
        (canonicalChannel ident r.terminal.rate) r.terminal.rate C (.correction (j + 1)) x y := by
  have hm := pilotChild_mean HP D ident r hr hD hid H hsH hks hs ht hu C hC hC1 hCf hj x y
  rw [stage_pilotCorrection_eq_canonical HP D ident r hr hD C] at hm
  rw [dens_filter_pi_eval r.terminal.role q]
  have he := expect_pi_supported_terminal r.source.role r.terminal.role hr.1
    (fun A => coordinate D r.source A (ident x)) q
    (fun σ => (r.terminal.rate / (dens {τ : Environment P J |
      r.usage.retains (channels D) τ (ident y)} : ℝ)) *
      pilotChild HP D ident r hr C j σ x y) (fun σ hq => by
        rw [pilotChild_zero_off_usage HP D ident r hr C j σ x y
          (fun hy => hq (hsub _ hy)), mul_zero])
  calc
    _ = 𝔼 σ ∈ ({σ : Environment P J |
        r.source.retains (channels D) σ (ident x) ∧ q (σ r.terminal.role)} : Finset _),
        (dens {A | q A} : ℝ) * ((r.terminal.rate /
          (dens {τ : Environment P J | r.usage.retains (channels D) τ (ident y)} : ℝ)) *
          pilotChild HP D ident r hr C j σ x y) := by
      apply expect_congr rfl
      intro σ _
      ring
    _ = _ := he.trans hm

/-- On the literal source/usage event the unscaled normalized reference is `E_(j+1)/f`.
No accuracy or availability conclusion follows from this deterministic mean identity. -/
theorem pilotChild_usage_mean (hD : D ≠ 0) (hid : Function.Injective ident)
    (H : Horizon P) {k s u : ℕ} (hsH : s ≤ H.maxExponent) (hks : k ≤ s)
    (hs : r.source.rate = rate s) (ht : r.terminal.rate = rate k)
    (hu : r.usage.rate = rate u)
    (C : Matrix V V ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ r.terminal.rate) {j : ℕ} (hj : j < HP.k) (x y : V) :
    rowSliceMean (fun σ v => r.source.retains (channels D) σ (ident v))
      (fun σ v => r.usage.retains (channels D) σ (ident v))
      (pilotChild HP D ident r hr C j) x y =
      PilotTask.value HP.toHierarchyParams (canonicalChannel ident r.terminal.rate)
        (canonicalChannel ident r.terminal.rate) r.terminal.rate C (.correction (j + 1)) x y /
        r.terminal.rate := by
  have hm := pilotChild_mean_on_terminal_event HP D ident r hr hD hid H hsH hks hs ht hu
    C hC hC1 hCf hj (splitUsage D ident r · y) x y (fun _ h => h)
  have hden : (dens {σ : Environment P J |
      r.usage.retains (channels D) σ (ident y)} : ℝ) ≠ 0 := by
    rw [channel_density D r.usage u hu]
    have : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
    have : (0 : ℝ) < side P u := by
      exact_mod_cast side_pos P u (Fact.out : P.Prime).pos
    positivity
  have hpred (σ : Environment P J) :
      splitUsage D ident r (σ r.terminal.role) y =
        r.usage.retains (channels D) σ (ident y) := by
    simp only [splitUsage, CorrectionRowTask.Channel.retains, channels, coordinate, hr.2.1]
  simp only [hpred, div_self hden, mul_one] at hm
  rw [← mul_expect] at hm
  apply (eq_div_iff (ht ▸ (rate_pos k).ne')).mpr
  exact (mul_comm _ _).trans hm

namespace BudgetData
variable {HP : FourthRootHierarchyParams 16 1 16 32 8} (B : BudgetData HP P)

/-- The literal pilot evaluator edge keeps all three own-request lower calls at
`childBudget M`. The maximum is current, not final. Availability is explicit;
accuracy of these values is a separate lower-budget induction hypothesis. -/
theorem evaluate_pilotNormalized_of_children (M : ℕ) (hM : 0 < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (i : Fin HP.k)
    (hr : r.task = .row 0 (.pilotNormalized i))
    (hactive : 0 < B.requestPrecision M r)
    (raw prep : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : Environment P 3 → ZMod P → ℝ)
    (hraw : B.evaluate (B.childBudget M) { r with task := .row 0 (.pilotInput i) } =
      some (.row raw))
    (hprep : B.evaluate (B.childBudget M) { r with task := .row 0 (.pilotPreparation i) } =
      some (.row prep))
    (hmax : B.evaluate (B.childBudget M) { r with task := .row 0 (.maximum i.succ) } =
      some (.vector maximum)) :
    B.evaluate M r = some (.row
      (correctionRequest B.padding id r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        raw prep maximum)) := by
  rw [B.evaluate_eq, step, hr]
  simp only [hactive, ↓reduceIte, normalized,
    row, vector, B.childBudget_lt hM, hraw, hprep, hmax,
    Option.bind_some, BudgetValue.row?, BudgetValue.vector?]
  rfl

end BudgetData

end Matrix.HierarchyParams.H4RankEnvironment
