/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.HierarchyRankCutoffs
public import Complexity.Foundations.Probability.RawProductMoment

/-!
# Lower-child moments for actual hierarchy samples

Original moment bridges by Christian Reitwiessner, using Samuel Schlesinger's hierarchy
and source-release proof. The actual normalized correction is bounded and sparse for arbitrary
raw, preparatory and pilot children. All functions retain one full rank environment.
The positive-iteration residual input moment
is paid by its actual direct, source-released right and negative lower-child moments. These
quantitative child budgets still need recursive proofs; this is no native or class endpoint.

## Main results

* `rawIncomingNormalized_moment`: the actual signed input moment, from lower-child norms.
* `rawIncomingNormalized_noise_le_lower`: actual walk noise with the input premise discharged.
-/
public section
namespace Matrix.HierarchyParams.H4RankEnvironment
open Finset Cslib Cslib.Probability
open scoped BigOperators
noncomputable section
private instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {P J : ℕ} [Fact P.Prime] {V : Type} [Fintype V]

/-- Actual lower-child substitution used by the incoming-normalized residual, including
its literal zero correction base and dense base bins. -/
@[expose] noncomputable def incomingChildren {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
    (Kc : ℕ) (binCutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request k (Fin J) (ZMod P) → Environment P J → Matrix V V ℝ)
    (maximum : HierarchyTask.Request k (Fin J) (ZMod P) → Environment P J → V → ℝ)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (σ : Environment P J) : Matrix V V ℝ :=
  match r.task with
  | .row _ (.correction _) => 0
  | .row _ (.normalized _) => correctionRequest D ident r (polynomialAuxCutoff4 HP.θ)
      HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc
      (raw r) (prep r) (maximum r) σ
  | _ => normalizedRequest D ident r binCutoff HP.ρ HP.K (raw r) (prep r) σ

/-- The actual correction child has a uniform range even for arbitrary earlier estimates. -/
theorem selectedRequest_mem_Icc {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (Kc : ℕ)
    (raw prep : Environment P J → Matrix V V ℝ) (maximum : Environment P J → V → ℝ)
    (σ : Environment P J) (x y : V) :
    correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum σ x y ∈
        Set.Icc 0 (2 * HP.Q HP.toHierarchyParams.atomCap) := by
  unfold correctionRequest
  split_ifs
  · exact CorrectionRowRecipe.normalized_mem_Icc _ _ _ _ _ _ _ _ _ _ _
      (HP.Q_nonneg _) HP.toHierarchyParams.atomCutoff_nonneg
      HP.toHierarchyParams.atomCutoff_le HP.ρ_nonneg HP.ρ_le_one
      HP.incomingCutoff_nonneg HP.incomingCutoff_le_one HP.γ_nonneg HP.γ_le_one
      _ _ _ _ _ _
  · exact ⟨le_rfl, mul_nonneg (by norm_num) (HP.Q_nonneg _)⟩

/-- The actual correction's row support is bounded on its rank channel. -/
theorem selectedRequest_row_support {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (Kc : ℕ)
    (raw prep : Environment P J → Matrix V V ℝ) (maximum : Environment P J → V → ℝ)
    (σ : Environment P J) (x : V) :
    #{y ∈ ({y | r.terminal.retains (channels D) σ (ident y)} : Finset V) |
      correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep maximum σ x y ≠ 0} ≤ HP.K := by
  classical
  by_cases hr : Admissible r
  · simp only [correctionRequest, dite_eq_left hr]
    have h := CorrectionRowRecipe.card_filter_normalized_row_ne_zero_lt
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
      HP.γ HP.K Kc r.terminal.rate
      (fun rest x => coordinate D r.source (rest ⟨r.source.role, hr.1⟩) (ident x))
      (fun A v => coordinate D r.terminal A (ident v))
      (fun A v => coordinate D r.usage A (ident v)) (raw σ)
      (fun p => prep ((Equiv.piSplitAt r.terminal.role
        (fun _ : Fin J => FrameChannel P 4 1)).symm (p.2, p.1))) (maximum σ)
      (((Equiv.piSplitAt r.terminal.role (fun _ : Fin J => FrameChannel P 4 1)) σ).2,
        ((Equiv.piSplitAt r.terminal.role (fun _ : Fin J => FrameChannel P 4 1)) σ).1)
      x hK HP.θ_pos.le
      (fun d hd => HP.toHierarchyParams.atomCutoff_eq_zero_of_Q_eq_zero
        (le_antisymm (by simpa [max_eq_right (sub_nonpos.mpr hd)] using HP.Q_le d)
          (HP.Q_nonneg d)))
      (show HP.η₂ ≤ HP.θ by linarith [HP.η₂_lt, HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_pos])
      HP.ρ_zero
    simp only [Equiv.piSplitAt_apply, coordinate,
      CorrectionRowTask.Channel.retains, channels] at h ⊢
    convert h.le using 1
    congr 1
    ext y
    simp
  · simp [correctionRequest, hr]

/-- Zero extension on the actual usage channel, without a child-moment premise. -/
theorem correctionRequest_eq_zero_of_not_usage {k : ℕ}
    (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (I : ℝ → ℝ → ℝ) (τ ρ Q γ : ℝ → ℝ) (K Kc : ℕ)
    (raw prep : Environment P J → Matrix V V ℝ) (maximum : Environment P J → V → ℝ)
    (σ : Environment P J) (x y : V)
    (hy : ¬ r.usage.retains (channels D) σ (ident y)) :
    correctionRequest D ident r I τ ρ Q γ K Kc raw prep maximum σ x y = 0 := by
  unfold correctionRequest
  split_ifs with hr
  · have ht : ¬ coordinate D r.usage (σ r.terminal.role) (ident y) := by
      simpa only [coordinate, CorrectionRowTask.Channel.retains, channels, hr.2.1] using hy
    simp only [Equiv.piSplitAt_apply, CorrectionRowRecipe.normalized, ht, ↓reduceIte]
  · rfl

/-- Explicit lower-child moment payment. Importance factors and source normalization
are part of the expression; no width, prime or horizon is hidden in its constants. -/
@[expose] noncomputable def incomingMomentBudget {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (ident : V → ZMod P) (R : RoleProfile J)
    (l bin ks km kt kb : ℕ) (ss sm st : List (ZMod P))
    (Kc : ℕ) (binCutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request k (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    (maximum : HierarchyTask.Request k (Fin J) (ZMod P) → Environment P J → V → ℝ)
    (N u : ℝ) : ℝ :=
  let source := gridChannel R.source ks ss
  let mid := gridChannel R.midpoint km sm
  let terminal := gridChannel R.terminal kt st
  let requests := HierarchyTask.rawRequests (k := k) l bin .residual
    source mid terminal (rate kb)
  let child := incomingChildren HP D ident Kc binCutoff raw prep maximum
  let ratio := HierarchyTask.usageRatio (fun role b suffix σ v =>
    channels D role b suffix σ (ident v)) terminal
  let XD := fun σ x => source.retains (channels D) σ (ident x)
  let ZD := fun σ x => mid.retains (channels D) σ (ident x)
  let YD := fun σ x => terminal.retains (channels D) σ (ident x)
  let direct := fun σ x y => rate kb * ratio requests.direct y * child requests.direct σ x y
  let right := fun σ z y => rate kb * ratio requests.right y *
    (rate km / (dens {τ | mid.retains (channels D) τ (ident y)} : ℝ)) *
      child requests.right σ z y
  let negative := fun σ x y => rate km * ratio
    ⟨HierarchyTask.correctionAtomTask l false (Fin.last k), source,
      {terminal with rate := rate km}, {terminal with rate := min terminal.rate (rate km)}⟩
        y *
      child ⟨HierarchyTask.correctionAtomTask l false (Fin.last k), source,
        {terminal with rate := rate km}, {terminal with rate := min terminal.rate (rate km)}⟩
          σ x y
  64 * (rowNormPow 4 N u XD YD direct +
      (HP.K : ℝ) ^ 3 * (2 * HP.Q HP.toHierarchyParams.atomCap) ^ 4 * Kc *
        (rate km / u) * rowNormPow 4 N (rate km) ZD YD right +
      rowNormPow 4 N u XD YD negative)

/-- Actual signed residual input moment from three explicit lower-child moments.
The source-released right term includes its literal importance and midpoint-density factors.
There is no raw-sample moment premise and no independence premise. Positive correction
iterations are treated here; the zero-correction base is still literal in `incomingChildren`.
This is a bounded moment milestone, not recursive moment induction. -/
theorem rawIncomingNormalized_moment {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (ident : V → ZMod P) (R : RoleProfile J)
    (l bin ks km kt kb : ℕ) (ss sm st : List (ZMod P))
    (Kc : ℕ) (hKc : 0 < Kc) (binCutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request (k + 1) (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    (maximum : HierarchyTask.Request (k + 1) (Fin J) (ZMod P) → Environment P J → V → ℝ)
    {N u : ℝ} (hN : 0 < N) (hu : 0 < u) :
    rowNormPow 4 N u
      (fun σ x => (gridChannel R.source ks ss).retains (channels D) σ (ident x))
      (fun σ y => (gridChannel R.terminal kt st).retains (channels D) σ (ident y))
      (rawIncomingNormalized HP D ident R l bin ks km kt kb ss sm st
        (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff Kc binCutoff raw prep maximum) ≤
      incomingMomentBudget HP D ident R l bin ks km kt kb ss sm st Kc binCutoff
        raw prep maximum N u := by
  unfold incomingMomentBudget
  dsimp only
  let source := gridChannel R.source ks ss
  let mid := gridChannel R.midpoint km sm
  let terminal := gridChannel R.terminal kt st
  let requests := HierarchyTask.rawRequests (k := k + 1) l bin .residual
    source mid terminal (rate kb)
  let child := incomingChildren HP D ident Kc binCutoff raw prep maximum
  let XD := fun σ x => source.retains (channels D) σ (ident x)
  let ZD := fun σ x => mid.retains (channels D) σ (ident x)
  let YD := fun σ x => terminal.retains (channels D) σ (ident x)
  have hr : Admissible requests.left := ⟨R.source_midpoint, rfl, rfl⟩
  have hleft (σ : Environment P J) : child requests.left σ =
      correctionRequest D ident requests.left (polynomialAuxCutoff4 HP.θ)
        HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc
        (raw requests.left) (prep requests.left) (maximum requests.left) σ := by
    rfl
  have hrow : ∀ σ x, XD σ x →
      #{z ∈ ({z | ZD σ z} : Finset V) | child requests.left σ x z ≠ 0} ≤ HP.K := by
    intro σ x _
    rw [hleft]
    exact selectedRequest_row_support HP hK D ident requests.left Kc _ _ _ σ x
  have hcol : ∀ σ z, ZD σ z →
      #{x ∈ ({x | XD σ x} : Finset V) | child requests.left σ x z ≠ 0} ≤ Kc := by
    intro σ z _
    rw [hleft]
    have h := selectedRequest_col_support HP D ident requests.left hr Kc hKc
      (raw requests.left) (prep requests.left) (maximum requests.left) σ z
    convert h.le using 1
    congr 1
  have hbound : ∀ σ x z, |child requests.left σ x z| ≤
      2 * HP.Q HP.toHierarchyParams.atomCap := by
    intro σ x z
    rw [hleft]
    have h := selectedRequest_mem_Icc HP D ident requests.left Kc
      (raw requests.left) (prep requests.left) (maximum requests.left) σ x z
    rw [abs_of_nonneg h.1]
    exact h.2
  have hz : ∀ σ x z, ¬ ZD σ z → child requests.left σ x z = 0 := by
    intro σ x z h
    rw [hleft]
    exact correctionRequest_eq_zero_of_not_usage D ident requests.left _ _ _ _ _ _ _
      _ _ _ σ x z h
  have hprod := rowNormPow_product_le (X := XD) (Z := ZD) (Y := YD)
    hN hu (rate_pos km) hbound hrow hcol
    (B := fun σ z y => rate kb *
      HierarchyTask.usageRatio (fun role b suffix σ v =>
        channels D role b suffix σ (ident v)) terminal requests.right y *
      (rate km / (dens {τ | mid.retains (channels D) τ (ident y)} : ℝ)) *
        child requests.right σ z y)
  have heq : rawIncomingNormalized HP D ident R l bin ks km kt kb ss sm st
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff Kc binCutoff raw prep maximum =
      fun σ x y => rate kb *
        HierarchyTask.usageRatio (fun role b suffix σ v =>
          channels D role b suffix σ (ident v)) terminal requests.direct y *
        child requests.direct σ x y +
        (∑ z ∈ ({z | ZD σ z} : Finset V), child requests.left σ x z *
          (rate kb * HierarchyTask.usageRatio (fun role b suffix σ v =>
            channels D role b suffix σ (ident v)) terminal requests.right y *
            (rate km / (dens {τ | mid.retains (channels D) τ (ident y)} : ℝ)) *
              child requests.right σ z y)) -
        rate km * HierarchyTask.usageRatio (fun role b suffix σ v =>
          channels D role b suffix σ (ident v)) terminal
          ⟨HierarchyTask.correctionAtomTask l false (Fin.last (k + 1)), source,
            {terminal with rate := rate km}, {terminal with rate := min terminal.rate (rate km)}⟩
          y *
          child ⟨HierarchyTask.correctionAtomTask l false (Fin.last (k + 1)), source,
            {terminal with rate := rate km}, {terminal with rate := min terminal.rate (rate km)}⟩
            σ x y := by
    funext σ x y
    change HierarchyTask.rawSample (fun role b suffix σ v =>
      channels D role b suffix σ (ident v)) l bin .residual source mid terminal
        (rate kb) (fun r => child r σ) x y = _
    unfold HierarchyTask.rawSample HierarchyTask.rawPositiveSample
      HierarchyTask.rawNegativeSample
    dsimp only
    congr 1
    congr 1
    rw [mul_sum, sum_filter]
    apply sum_congr rfl
    intro z _
    by_cases h : ZD σ z
    · simp only [h, ↓reduceIte]
      change (rate kb * _ * (rate km / _)) *
        (child requests.left σ x z * child requests.right σ z y) = _
      ring
    · simp only [h, ↓reduceIte]
      change (rate kb * _ * (rate km / _)) *
        (child requests.left σ x z * child requests.right σ z y) = 0
      rw [hz σ x z h, zero_mul, mul_zero]
  rw [heq]
  exact (rowNormPow_add_sub_le (mul_pos hN hu).le _ _ _).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add le_rfl hprod) le_rfl) (by norm_num))

/-- The actual H4 walk noise paid entirely by explicit lower-child norms. The retained
raw input moment in `rawIncomingNormalized_noise` is discharged by the moment theorem. -/
theorem rawIncomingNormalized_noise_le_lower {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (ident : V → ZMod P) (R : RoleProfile J)
    (l bin ks km kt kb : ℕ) (ss sm st : List (ZMod P))
    (Kc : ℕ) (hKc : 0 < Kc) (binCutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request (k + 1) (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    (maximum : HierarchyTask.Request (k + 1) (Fin J) (ZMod P) → Environment P J → V → ℝ)
    {N u : ℝ} (hN : 0 < N) (hu : 0 < u) (steps : ℕ) :
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
      32 * (1 - 1 / (155648 * (J + 1) * (4 : ℝ)^4)) ^ (2 * steps) *
        incomingMomentBudget HP D ident R l bin ks km kt kb ss sm st Kc binCutoff
          raw prep maximum N u := by
  have hm := rawIncomingNormalized_moment HP hK D ident R l bin ks km kt kb ss sm st
    Kc hKc binCutoff raw prep maximum hN hu
  have hm' : rowNormPow 4 N u
      (X R.source (side P ks) (fun v => CopyPadding.identifier D ss (ident v)))
      (Y R.terminal (side P kt) (fun v => CopyPadding.identifier D st (ident v)))
      (rawIncomingNormalized HP D ident R l bin ks km kt kb ss sm st
        (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff Kc binCutoff raw prep maximum) ≤
      incomingMomentBudget HP D ident R l bin ks km kt kb ss sm st Kc binCutoff
        raw prep maximum N u := by
    simp only [rowNormPow, CorrectionRowTask.Channel.retains, gridChannel, channels,
      semanticSide_grid, X, Y] at hm ⊢
    convert hm using 1
    congr 1
    apply expect_congr rfl
    intro σ _
    apply sum_congr (by ext x; simp)
    intro x _
    apply sum_congr (by ext y; simp)
    intro y _
    rfl
  exact (rawIncomingNormalized_noise HP D ident R l bin ks km kt kb ss sm st
    (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff Kc binCutoff raw prep maximum
    (mul_pos hN hu).le steps).trans
      (mul_le_mul_of_nonneg_left hm' (mul_nonneg (by norm_num)
        (by rw [pow_mul]; positivity)))

end
end Matrix.HierarchyParams.H4RankEnvironment
