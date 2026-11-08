/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.InitialPilotCorrection
import Complexity.Foundations.Probability.HierarchyCorrectionMean

/-!
# Canonical mean of the first normalized pilot

This bounded specialization uses a common source, rank and usage grid rate. The
existing pilot sampling laws supply the incoming margin and joint normalizer law;
no desired-mean premise is supplied. The factor converting a normalized sample to
parent matrix units is the stage rate, including on the joint retained slice.
These are original specializations of the existing sampling API, not recursive closure.

## Main definitions

* `initialTrueNormalized`: original true request used only as a proof reference.

## Main results

* `initialTrueNormalized_mean`: joint conditional mean in parent matrix units.
-/
public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- Original true normalized request, with the same source/usage joint normalizer
as the computed child. This reference is used only in proofs. -/
@[expose] def initialTrueNormalized
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (ks kt : ℕ) (ss st : List (ZMod P)) (C : Matrix (ZMod P) (ZMod P) ℝ) :=
  let r : HierarchyTask.Request HP.k (Fin J) (ZMod P) :=
    ⟨.row 0 (.pilotNormalized ⟨0, HP.k_pos⟩), gridChannel R.source ks ss,
      gridChannel R.terminal kt st, gridChannel R.terminal kt st⟩
  let prep := fun σ => correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
    HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ (rate kt) C (polynomialPrepCutoff4 HP.θ) HP.ρ
    {x | X R.source (side P ks) (CopyPadding.identifier D ss) σ x}
    {y | Y R.terminal (side P kt) (CopyPadding.identifier D st) σ y}
  correctionRequest D id r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
    HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
    (fun _ => C) prep
    (fun _ => PilotRowRecipe.maximum 0 (initialTrueDetector HP D R ks kt ss st C))

set_option backward.isDefEq.respectTransparency false in
/-- The joint conditional mean in parent matrix units is the genuine first pilot
correction. All rates coincide here; the literal importance factor is therefore
`rate k`, not one and not the inverse frame density. Incoming margins are derived
by `pilotSampling` from its canonical detector and primitive frame channel laws. -/
theorem initialTrueNormalized_mean
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (hD : D ≠ 0)
    (R : RoleProfile J) (H : Horizon P) (k : ℕ) (hk : k ≤ H.maxExponent)
    (ss st : List (ZMod P)) (C : Matrix (ZMod P) (ZMod P) ℝ)
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ rate k) (x y : ZMod P) :
    rate k * rowSliceMean
      (X R.source (side P k) (CopyPadding.identifier D ss))
      (Y R.terminal (side P k) (CopyPadding.identifier D st))
      (initialTrueNormalized HP D R k k ss st C) x y =
    pilotCorrection (HP.toHierarchyParams.cutoff (rate k)) HP.γ
      (columnDetector (canonicalChannel id (rate k)) (canonicalChannel id (rate k))
        HP.ϕ HP.ρ HP.J HP.K (rate k)) C 1 x y := by
  let r : HierarchyTask.Request HP.k (Fin J) (ZMod P) :=
    ⟨.row 0 (.pilotNormalized ⟨0, HP.k_pos⟩), gridChannel R.source k ss,
      gridChannel R.terminal k st, gridChannel R.terminal k st⟩
  have hr : Admissible r := ⟨R.source_terminal, rfl, rfl⟩
  have hh := split_channels D id r hr hD Function.injective_id H hk rfl rfl
  have hπ : 0 < (((side P k : ℝ) / P)^4) := by linarith [hh.1.lower, rate_pos k]
  let A := HP.pilotSampling (splitSource D id r hr) (splitTerminal D id r)
    hh.1 hh.2 (rate_pos k) hπ hC hC1 (show 0 < HP.k from HP.k_pos)
  have hm := A.expect_normalizedRecipe (rate_pos k) hC hC1 hCf (Nat.zero_le _)
    (split_source_nonempty D id r hr hD Function.injective_id H hk rfl rfl x) y
  have hdet : columnDetector (splitSource D id r hr) (splitTerminal D id r)
      HP.ϕ HP.ρ HP.J HP.K (rate k) C = initialTrueDetector HP D R k k ss st C := by
    rw [initialTrueDetector_eq_canonical HP D hD R k k ss st C]
    exact stage_columnDetector_eq_canonical HP D id r hr hD C
  have hinput : PilotTask.value HP.toHierarchyParams (splitSource D id r hr)
      (splitTerminal D id r) (rate k) C (.input 0) = C := by
    simp [PilotTask.value, pilotInput, pilotCorrection_zero]
  have hmax : PilotTask.value HP.toHierarchyParams (splitSource D id r hr)
      (splitTerminal D id r) (rate k) C (.maximum 1) =
      PilotRowRecipe.maximum 0 (initialTrueDetector HP D R k k ss st C) := by
    rw [PilotTask.value, pilotMax_succ, pilotMax_zero]
    simp only [pilotInput, pilotCorrection_zero, zero_mul, add_zero]
    rw [hdet]
    funext z
    have h0 : 0 ≤ initialTrueDetector HP D R k k ss st C z := by
      change 0 ≤ min 1 (max 0 _); exact le_min zero_le_one (le_max_left _ _)
    have h1 : initialTrueDetector HP D R k k ss st C z ≤ 1 := min_le_left _ _
    simp only [Pi.sup_apply, Pi.zero_apply, PilotRowRecipe.maximum,
      max_eq_right h0, min_eq_right h1]
  have he (σ : Environment P J) :
      initialTrueNormalized HP D R k k ss st C σ x y =
        A.value (.normalized 0) (terminalSplit r.terminal.role σ) x y := by
    change _ = A.normalizedRecipe
      (PilotTask.value HP.toHierarchyParams (splitSource D id r hr)
        (splitTerminal D id r) (rate k) C (.input 0)) _ _ _ x y
    simp only [hinput, hmax]
    rw [show A.preparationRecipe C = CorrectionRowRecipe.preparation
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff (polynomialPrepCutoff4 HP.θ)
      HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ (rate k)
      (splitSource D id r hr) (splitTerminal D id r) C from
        HP.selectedPilot_preparation _ _ hh.1 hh.2 (rate_pos k) hπ hC hC1 HP.k_pos C]
    rw [show A.normalizedRecipe = _ from funext fun input => funext fun prep =>
      funext fun maximum => HP.selectedPilot_normalized _ _ hh.1 hh.2 (rate_pos k) hπ
        hC hC1 HP.k_pos input prep maximum]
    change _ = CorrectionRowRecipe.normalized _ _ _ _ _ _ _ _ _ _
      (splitUsage D id r) _ _ _ _ _ _
    have ht := correctionRequest_eq_split HP D id r hr C
      (CorrectionRowRecipe.preparation (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
        (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ (rate k)
        (splitSource D id r hr) (splitTerminal D id r) C)
      (PilotRowRecipe.maximum 0 (initialTrueDetector HP D R k k ss st C)) σ x y
    refine Eq.trans ?_ ht
    unfold initialTrueNormalized
    congr 1
    funext τ
    simp only [CorrectionRowRecipe.preparation, splitSource, splitTerminal,
      terminalSplit, Equiv.trans_apply, Equiv.prodComm_apply, Equiv.piSplitAt_apply,
      r, gridChannel, coordinate, semanticSide_grid, X, Y, id_eq, Prod.swap_prod_mk]
  have hmean : rowSliceMean (X R.source (side P k) (CopyPadding.identifier D ss))
      (Y R.terminal (side P k) (CopyPadding.identifier D st))
      (initialTrueNormalized HP D R k k ss st C) x y =
      𝔼 p ∈ ({s | splitSource D id r hr s x} : Finset _) ×ˢ
        ({t | splitTerminal D id r t y} : Finset _), A.value (.normalized 0) p x y := by
    unfold rowSliceMean
    apply expect_equiv (terminalSplit r.terminal.role)
    · intro σ
      simp [splitSource, splitTerminal, terminalSplit, Equiv.piSplitAt_apply, r, coordinate,
        gridChannel,
        semanticSide_grid, X, Y]
    · intro σ _; exact he σ
  rw [hmean, mul_expect]
  rw [hm]
  change pilotCorrection _ _ _ C 1 x y = _
  have hc : columnDetector (splitSource D id r hr) (splitTerminal D id r)
      HP.ϕ HP.ρ HP.J HP.K (rate k) =
      columnDetector (canonicalChannel id (rate k)) (canonicalChannel id (rate k))
        HP.ϕ HP.ρ HP.J HP.K (rate k) := by
    funext G; exact stage_columnDetector_eq_canonical HP D id r hr hD G
  rw [hc]

end Matrix.HierarchyParams.H4RankEnvironment
