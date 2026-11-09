/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Computability.LogSpaceDerandomization.HierarchyCutoffs
public import Complexity.Computability.LogSpaceDerandomization.HierarchyRankEnvironment

/-!
# Selected cutoffs on actual H4 rank environments

Actual H=4 finite-horizon frame channels supply the selected sampling constructors.
The reused environment/noise proof is credited to Christian Reitwiessner; the underlying
fourth-root hierarchy witness is Samuel Schlesinger's. No child input moment is bounded here. The
    two sampling constructors use independent full
environments for their source and terminal seeds; the request support and noise clients use
the actual terminal-coordinate split of one environment.
-/
public section
namespace Matrix.HierarchyParams.H4RankEnvironment
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open scoped BigOperators
noncomputable section
private instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {P J : ℕ} [Fact P.Prime]
  (HP : FourthRootHierarchyParams 16 1 16 32 8)
  {V : Type} [Fintype V]
  (s t : Fin J) (is it : V → ZMod P)
  (his : Function.Injective is) (hit : Function.Injective it)
  (H : Horizon P) {k : ℕ} (hk : k ≤ H.maxExponent)

/-- The actual full-environment channel law, with supplied finite-horizon admissibility,
constructs correction sampling data without a separate incoming-count certificate. -/
noncomputable def selectedCorrectionSampling {C : Matrix V V ℝ} {i : ℕ}
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1) (hi : i < HP.k) :=
  let hXY := retention_environment_ident s t is it his hit H hk
  let hYX := retention_environment_ident t s it is hit his H hk
  HP.correctionSampling
    (fun (σ : Environment P J) v => frameRetains P 4 (side P k) (σ s) (is v))
    (fun (σ : Environment P J) v => frameRetains P 4 (side P k) (σ t) (it v))
    hXY hYX (rate_pos k)
    (lt_of_lt_of_le (by simpa only [one_mul] using rate_pos k) hXY.lower)
    hC hC1 hi

/-- The pilot constructor is instantiated on the same actual frame channels. -/
noncomputable def selectedPilotSampling {C : Matrix V V ℝ} {i : ℕ}
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1) (hi : i < HP.k) :=
  let hXY := retention_environment_ident s t is it his hit H hk
  let hYX := retention_environment_ident t s it is hit his H hk
  HP.pilotSampling
    (fun (σ : Environment P J) v => frameRetains P 4 (side P k) (σ s) (is v))
    (fun (σ : Environment P J) v => frameRetains P 4 (side P k) (σ t) (it v))
    hXY hYX (rate_pos k)
    (lt_of_lt_of_le (by simpa only [one_mul] using rate_pos k) hXY.lower)
    hC hC1 hi

/-- The actual full-environment normalized request has the incoming column cap.
Source conditioning uses the very same terminal-coordinate split as correctionRequest;
the usage channel can be narrower than the rank channel. -/
theorem selectedRequest_col_support {k : ℕ}
    (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (hr : Admissible r)
    (Kc : ℕ) (hKc : 0 < Kc)
    (raw prep : Environment P J → Matrix V V ℝ)
    (maximum : Environment P J → V → ℝ) (σ : Environment P J) (y : V) :
    let split := Equiv.piSplitAt r.terminal.role (fun _ : Fin J => FrameChannel P 4 1)
    #{x ∈ ({w | coordinate D r.source ((split σ).2 ⟨r.source.role, hr.1⟩)
        (ident w)} : Finset V) |
      correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum σ x y ≠ 0} < Kc := by
  dsimp only
  simp only [correctionRequest, dite_eq_left hr]
  exact HP.normalized_col_support _ _ _ HP.K Kc hKc _ _ _ _ _ _

/-- Actual conditional-walk contraction with the selected incoming functions.
The input fourth moment is retained, and is not an assumed output certificate. -/
theorem selectedIncoming_noise {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (ident : V → ZMod P) (R : RoleProfile J)
    (l bin ks km kt kb : ℕ) (ss sm st : List (ZMod P))
    (Kc : ℕ) (binCutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request k (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    (maximum : HierarchyTask.Request k (Fin J) (ZMod P) → Environment P J → V → ℝ)
    {N u : ℝ} (hNu : 0 ≤ N * u) (steps : ℕ) :
    let a := fun v => CopyPadding.identifier D ss (ident v)
    let b := fun v => CopyPadding.identifier D st (ident v)
    let F := rawIncomingNormalized HP D ident R l bin ks km kt kb ss sm st
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff Kc binCutoff raw prep maximum
    let G := graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
      (side_le P ks) (side_le P kt) a b
    rowNormPow 4 N u (X R.source (side P ks) a) (Y R.terminal (side P kt) b)
      (fun σ x z => conditionalWalk (X R.source (side P ks) a)
        (Y R.terminal (side P kt) b) G (fun _ _ => steps) F σ x z -
        rowSliceMean (X R.source (side P ks) a) (Y R.terminal (side P kt) b) F x z) ≤
      32 * (1 - 1 / (155648 * (J+1) * (4:ℝ)^4))^(2*steps) *
        rowNormPow 4 N u (X R.source (side P ks) a) (Y R.terminal (side P kt) b) F := by
  exact rawIncomingNormalized_noise HP D ident R l bin ks km kt kb ss sm st
    (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff Kc binCutoff raw prep maximum hNu steps

end
end Matrix.HierarchyParams.H4RankEnvironment
