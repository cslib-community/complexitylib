/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyPreparationExecution
public import Complexity.Foundations.Probability.HierarchyCanonicalTargets
public import Complexity.Foundations.Probability.HierarchyCorrectionRawStability
public import Complexity.Foundations.Probability.HierarchyInitialFeasibility
public import Complexity.Foundations.Probability.RootMetric.FiniteError

/-!
# Incoming PREP normalizer bias from its actual input child

These original bounds consume the completed input/pilotInput at the literal `childBudget M`,
with its own positive precision and ordinary signed RAW error against the canonical stage
input. They retain the incoming gate, source and terminal rank sets and default completion
slack zero. They do not concern the dense selected-preparation dyadic list.

The own-mask consumer currently requires usage equal to terminal. For narrower usage the
incoming gate reads RAW errors outside that usage; an own-usage IH alone does not pay them.
No support property of the approximate RAW child is assumed. The retained coefficient is
`(L / f)^4 * P^2`, before any relative normalizer scale. The exact salary condition below
is an additional invariant, not a consequence of the existing joint depth/field guards.
Increasing the field can increase this cost without increasing the fixed rank salary.
No recursive availability, second-coordinate reserve or native complexity claim is made.

## Main results

* `BudgetData.evaluate_preparation_bias`: actual conditional normalizer bias from own RAW error.
* `BudgetData.correctionRequest_normalizer_root_moment_le`: integrated rooted sensitivity.
* `BudgetData.requestPrecision_preparation_input`: exact changed-task precision salary.
* `BudgetData.preparation_bias_salary_iff`: exact scalar invariant needed for payment.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- The deterministic input of the corresponding stage task. Pilot input uses its current
pilot correction; actual input uses its correction with the final pilot multiplier.
Neither is the final residual `C - E + E C`. -/
@[expose] def canonicalPreparationInput (B : BudgetData HP P) (pilot : Bool)
    (i : Fin HP.k) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Matrix (ZMod P) (ZMod P) ℝ :=
  if pilot then
    PilotTask.value HP.toHierarchyParams (canonicalChannel id r.terminal.rate)
      (canonicalChannel id r.terminal.rate) r.terminal.rate B.base (.input i.val)
  else HP.toHierarchyParams.correctionInput (canonicalChannel id r.terminal.rate)
    (canonicalChannel id r.terminal.rate) r.terminal.rate B.base i.val

/-- The regularity constant is fixed before the evaluator, field, request and geometry.
Only the literal successful RAW child is charged, at its own positive precision. This
full-terminal usage contract is deliberately explicit: it does not infer full-rank
accuracy from a narrower-usage child IH. The conclusion measures deterministic bias,
not the pointwise error of walked PREP. -/
theorem evaluate_preparation_bias :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (P : ℕ) [Fact P.Prime] (B : BudgetData HP P)
      (M : ℕ) (pilot : Bool) (i : Fin HP.k)
      (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
    r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i) →
    0 < B.requestPrecision M r → B.childBudget M < M →
    r.usage = r.terminal → 0 ≤ r.source.rate → 0 < r.terminal.rate →
    ∀ (A W : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ),
    let q := { r with task := .row 0 (if pilot then .pilotInput i else .input i) }
    0 < B.requestPrecision (B.childBudget M) q →
    B.evaluate (B.childBudget M) q = some (.row A) →
    B.evaluate M r = some (.row W) →
    rowNormPow 4 P q.source.rate
      (fun σ x => q.source.retains (channels B.padding) σ x)
      (fun σ y => q.usage.retains (channels B.padding) σ y)
      (fun σ x y => A σ x y - B.canonicalPreparationInput pilot i r x y) ≤
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 →
    ∀ (s u : Fin 3) (_hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P)),
    r.source = gridChannel s ks ss → r.usage = gridChannel u ku su →
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    rowNormPow 4 P r.source.rate X U (fun _ x y => rowSliceMean X U W x y -
      rowSliceMean X U (B.incomingPreparation r
        (fun _ => B.canonicalPreparationInput pilot i r)) x y) ≤
      (L / r.terminal.rate) ^ 4 * (P : ℝ) ^ 2 *
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 := by
  obtain ⟨L, hL, hreg⟩ := HP.correction_preparation_row_moment
  refine ⟨L, hL, ?_⟩
  intro P instP B M pilot i r hr hp hm hu hs hf A W q _hqp hA hW hih
    s u hsu ks ku ss su hsource husage
  dsimp only
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let U := fun σ y => r.usage.retains (channels B.padding) σ y
  let C := fun _ : Environment P 3 => B.canonicalPreparationInput pilot i r
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := mul_nonneg (Nat.cast_nonneg _) hs
  have hmean : (fun (_ : Environment P 3) x y => rowSliceMean X U W x y -
      rowSliceMean X U (B.incomingPreparation r C) x y) =
      (fun _ => rowSliceMean X U (fun σ x y =>
        B.incomingPreparation r A σ x y - B.incomingPreparation r C σ x y)) := by
    funext σ x y
    rw [B.evaluate_preparation_mean M pilot i r hr hp hm A W hA hW
      s u hsu ks ku ss su hsource husage]
    simp only [rowSliceMean, expect_sub_distrib, X, U]
  rw [hmean]
  apply (rowNormPow_sliceMean_fourth_le hNu X U _).trans
  have hKc : 0 < ⌈4 * (1 + 32 * HP.R)⌉₊ :=
    Nat.ceil_pos.mpr (by linarith [HP.R_var])
  have h := hreg (Environment P 3) (ZMod P) X U _ hKc r.terminal.rate hf A C
    P r.source.rate hNu
  have he : (fun σ x y => B.incomingPreparation r A σ x y -
      B.incomingPreparation r C σ x y) = (fun σ x y =>
      correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K
        ⌈4 * (1 + 32 * HP.R)⌉₊ r.terminal.rate (A σ) (polynomialPrepCutoff4 HP.θ)
        HP.ρ {z | X σ z} {w | U σ w} x y -
      correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K
        ⌈4 * (1 + 32 * HP.R)⌉₊ r.terminal.rate (C σ) (polynomialPrepCutoff4 HP.θ)
        HP.ρ {z | X σ z} {w | U σ w} x y) := by
    simp only [incomingPreparation, U, hu, X]
  rw [he]
  apply h.trans
  rw [ZMod.card]
  exact mul_le_mul_of_nonneg_left hih (by positivity)

set_option backward.isDefEq.respectTransparency false in
/-- The actual normalized correction can consume the signed conditional bias above.
RAW and maximum are held fixed here; their separately budgeted parent calls are not
identified with the PREP child's calls. No pointwise PREP approximation is required. -/
theorem correctionRequest_normalizer_root_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [Fact P.Prime] (B : BudgetData HP P)
      (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (_hr : Admissible r),
    0 < r.terminal.rate → ∀ (raw W V : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
      (maximum : Environment P 3 → ZMod P → ℝ) (σ : Environment P 3) (x y : ZMod P),
    |correctionRequest B.padding id r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
        HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        raw W maximum σ x y ^ (4⁻¹ : ℝ) -
      correctionRequest B.padding id r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
        HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        raw V maximum σ x y ^ (4⁻¹ : ℝ)| ≤
    C * |rowSliceMean (fun τ z => r.source.retains (channels B.padding) τ z)
        (fun τ z => r.usage.retains (channels B.padding) τ z) W x y -
      rowSliceMean (fun τ z => r.source.retains (channels B.padding) τ z)
        (fun τ z => r.usage.retains (channels B.padding) τ z) V x y| := by
  obtain ⟨C, LI, Lτ, hC, _hLI, _hLτ, h⟩ := HP.normalized_raw_normalizer_root_stability
  refine ⟨C, hC, ?_⟩
  intro P instP B r hr hf raw W V maximum σ x y
  let split := Equiv.piSplitAt r.terminal.role (fun _ : Fin 3 => FrameChannel P 4 1)
  have hd := h (ZMod P) _ _
    (fun rest z => coordinate B.padding r.source (rest ⟨r.source.role, hr.1⟩) z)
    (fun A z => coordinate B.padding r.terminal A z)
    (fun A z => coordinate B.padding r.usage A z)
    ⌈4 * (1 + 32 * HP.R)⌉₊ (Nat.ceil_pos.mpr (by linarith [HP.R_var]))
    r.terminal.rate hf (raw σ) (raw σ)
    (fun p => W (split.symm (p.2, p.1)))
    (fun p => V (split.symm (p.2, p.1)))
    (maximum σ) ((split σ).2, (split σ).1) x y 0 0 le_rfl le_rfl
    (by intro z _; simp)
    (by intro z _; exact kthLargest_le le_rfl (fun _ _ => by simp))
  have hw := normalizer_full B.padding id r hr W x y
  have hv := normalizer_full B.padding id r hr V x y
  dsimp only [CorrectionRowRecipe.normalizer, split] at hw hv hd
  simp only [id_eq] at hw hv
  rw [hw, hv] at hd
  have hz (S : Finset (ZMod P)) : kthLargest 1 S (fun _ => (0 : ℝ)) = 0 :=
    le_antisymm (kthLargest_le le_rfl (fun _ _ => le_rfl)) kthLargest_nonneg
  simpa only [correctionRequest, dite_eq_left hr, sub_self, abs_zero, hz, id_eq, zero_div,
    zero_add, add_zero, mul_zero, zero_mul] using hd

set_option backward.isDefEq.respectTransparency false in
/-- Integrated normalizer sensitivity on the request's own source/usage masks.
Together with `evaluate_preparation_bias` this pays the rooted normalized error by
`C^4 * (L / f)^4 * P^2` times the literal input-child allowance. RAW and maximum
are held fixed; successful separately budgeted parent calls remain a separate obligation. -/
theorem correctionRequest_normalizer_root_moment_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [Fact P.Prime] (B : BudgetData HP P)
      (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (_hr : Admissible r),
    0 ≤ r.source.rate → 0 < r.terminal.rate →
    ∀ (raw W V : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
      (maximum : Environment P 3 → ZMod P → ℝ),
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    let output := fun prep => correctionRequest B.padding id r
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ raw prep maximum
    rootDistPow 4 P r.source.rate X U (output W) (output V) ≤
      C ^ 4 * rowNormPow 4 P r.source.rate X U
        (fun _ x y => rowSliceMean X U W x y - rowSliceMean X U V x y) := by
  obtain ⟨C, hC, h⟩ := correctionRequest_normalizer_root_le (HP := HP)
  refine ⟨C, hC, ?_⟩
  intro P instP B r hr hs hf raw W V maximum X U output
  apply rowNormPow_le_mul (mul_nonneg (Nat.cast_nonneg P) hs)
  intro σ x y _hx _hy
  have hp := pow_le_pow_left₀ (abs_nonneg _)
    (h P B r hr hf raw W V maximum σ x y) 4
  simpa only [mul_pow, output, X, U, Nat.cast_ofNat] using hp

omit [Fact P.Prime] in
/-- Both task changes keep all channels. The pilot rank gap is forty; the actual gap
is four. The budget loss remains literal and cannot be dropped in a payment claim. -/
theorem requestPrecision_preparation_input (B : BudgetData HP P) (M m : ℕ)
    (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i)) :
    let q := { r with task := .row 0 (if pilot then .pilotInput i else .input i) }
    B.requestPrecision m q - B.requestPrecision M r =
      ((m : ℝ) - M) / (16 * B.slack) + B.rankCharge * (if pilot then 40 else 4) := by
  cases pilot <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
  all_goals
    simp only [requestPrecision, LogSpaceEstimation.precision, hr,
      HierarchyTask.rank, CorrectionRowTask.rank,
      PilotRowTask.rank, PilotTask.rank, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      mul_zero, zero_add]
    ring

omit [Fact P.Prime] in
/-- Exact sufficient-coefficient payment invariant, with the relative normalizer scale
included in `c`. For example `c = (L / (f * scale))^4 * P^2`. This is an equivalence
of scalar allowances, not a theorem that the joint guards provide this invariant. -/
theorem preparation_bias_salary_iff (B : BudgetData HP P) (M m : ℕ)
    (r q : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (c : ℝ) :
    c * ((2 : ℝ) ^ (-B.requestPrecision m q)) ^ 4 ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 ↔
    c ≤ (2 : ℝ) ^ (4 * (B.requestPrecision m q - B.requestPrecision M r)) := by
  have hpow (t : ℝ) : ((2 : ℝ) ^ t) ^ 4 = (2 : ℝ) ^ (4 * t) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hpow, hpow, ← le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _),
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  ring_nf

omit [Fact P.Prime] in
/-- At the production child budget the required scalar invariant has a fixed rank
salary and a nonpositive budget loss. Joint depth feasibility does not assert it. -/
theorem preparation_bias_production_salary_iff (B : BudgetData HP P) (M : ℕ)
    (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (c : ℝ) :
    let q := { r with task := .row 0 (if pilot then .pilotInput i else .input i) }
    c * ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 ↔
    c ≤ (2 : ℝ) ^ (4 * (((B.childBudget M : ℕ) : ℝ) - M) / (16 * B.slack) +
      4 * B.rankCharge * (if pilot then 40 else 4)) := by
  dsimp only
  rw [B.preparation_bias_salary_iff,
    B.requestPrecision_preparation_input M (B.childBudget M) pilot i r hr]
  ring_nf

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
