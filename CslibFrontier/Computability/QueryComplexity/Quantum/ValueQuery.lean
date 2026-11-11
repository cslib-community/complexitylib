/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.Search
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Quantum value-query algorithms and multi-outcome measurements

This module extends the phase-oracle quantum query model (`Cslib.Quantum.run`) in two directions:

1. **Multi-outcome measurements** (`Cslib.Quantum.measureOut`): measuring a unit state in the
   computational basis and applying a classical readout map `out : ι → β` gives a distribution
   over arbitrary outcome values `β` (for instance `ℝ` or an ordered alphabet `α`), rather than a
   single accepting subset `S`.
2. **Value-query algorithms** (`Cslib.Quantum.ValueState`, `Cslib.Quantum.valueOracle`,
   `Cslib.Quantum.runValue`): states over an arbitrary finite query index type `ι`, a finite
   value/answer register `V`, and a finite workspace `W`, where each oracle call applies an
   input-dependent unitary `step (x i)` to the `V` register controlled by the query index `i`.
   Permutation oracles (`Cslib.Quantum.permStep`), group-addition oracles
   (`Cslib.Quantum.addStep`), and XOR oracles (`BitString` as an additive group) are special cases.

For lower bounds, restricting a value-query algorithm to inputs taking only two values `a₀` and
`a₁` can be simulated in the Boolean phase-oracle model (`Cslib.Quantum.run`) on `N = |ι|` bits:

* When the relative step `(step a₀).symm.trans (step a₁)` is an involution (such as an XOR
  oracle), one binary phase query simulates each value query (`Cslib.Quantum.exists_sim_involution`).
* For an arbitrary unitary step `step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)`,
  simultaneously diagonalizing the Hermitian and skew-Hermitian parts of the relative unitary
  simulates each value query with two binary phase queries (`Cslib.Quantum.exists_sim_value`).

## Main definitions

* `Cslib.Quantum.measureOut`: distribution of a classical readout of a computational-basis
  measurement.
* `Cslib.Quantum.ValueState`: quantum states over `ι × V × W`.
* `Cslib.Quantum.valueOracle`, `Cslib.Quantum.permStep`, `Cslib.Quantum.addStep`: value-query
  oracles.
* `Cslib.Quantum.runValue`: final state of a `T`-query value-query algorithm.
* `Cslib.Quantum.embedOutcome`: embedding value-query outcomes into `Fin N × Bool × V × W`.

## Main results

* `Cslib.Quantum.measureOut_toOuterMeasure_apply`: event probabilities under `measureOut`.
* `Cslib.Quantum.norm_runValue`: value-query algorithms preserve norms.
* `Cslib.Quantum.exists_sim_involution`: simulating a two-valued restriction with an involutive
  difference by `T` binary phase queries.
* `Cslib.Quantum.exists_sim_value`: simulating an arbitrary two-valued restriction by `2 * T`
  binary phase queries.
-/

public section

namespace Cslib.Quantum

open Finset

/-! ### Multi-outcome measurements -/

/-- Measuring a unit state `ψ` in the computational basis and decoding outcomes through
`out : ι → β`. -/
@[expose] noncomputable def measureOut {ι β : Type*} [Fintype ι] (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (out : ι → β) : PMF β :=
  (measure ψ hψ).map out

@[simp] theorem measureOut_apply {ι β : Type*} [Fintype ι] (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (out : ι → β) (b : β) :
    measureOut ψ hψ out b = ∑ a : ι, by classical exact if b = out a then measure ψ hψ a else 0 := by
  classical
  simp [measureOut, PMF.map_apply]

/-- The probability that `measureOut` lands in `{b | P b}` equals `measureProb` of the preimage
subset `{y | P (out y)}`. -/
theorem measureOut_toOuterMeasure_apply {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (out : ι → β) (P : β → Prop)
    [DecidablePred P] :
    (measureOut ψ hψ out).toOuterMeasure {b | P b} =
      ENNReal.ofReal (measureProb ψ (univ.filter fun y => P (out y))) := by
  rw [measureOut, PMF.toOuterMeasure_map_apply, ← measure_toOuterMeasure_apply ψ hψ]
  congr 1
  ext y
  simp

/-! ### Fibered unitary helpers -/

section FiberHelpers

private def sliceSecond {A B : Type*} (ψ : EuclideanSpace ℂ (A × B)) (a : A) :
    EuclideanSpace ℂ B :=
  WithLp.toLp 2 fun b => ψ.ofLp (a, b)

@[simp] private theorem sliceSecond_apply {A B : Type*} (ψ : EuclideanSpace ℂ (A × B))
    (a : A) (b : B) : (sliceSecond ψ a).ofLp b = ψ.ofLp (a, b) := rfl

private theorem norm_sq_prod {A B : Type*} [Fintype A] [Fintype B]
    (ψ : EuclideanSpace ℂ (A × B)) :
    ‖ψ‖ ^ 2 = ∑ a : A, ‖sliceSecond ψ a‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  rfl

/-- Applying unitaries `F a : ℂ^B₁ ≃ₗᵢ[ℂ] ℂ^B₂` fiberwise over `a : A`. -/
private noncomputable def fiberIso {A B₁ B₂ : Type*} [Fintype A] [Fintype B₁] [Fintype B₂]
    (F : A → (EuclideanSpace ℂ B₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ B₂)) :
    EuclideanSpace ℂ (A × B₁) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B₂) where
  toFun ψ := WithLp.toLp 2 fun ⟨a, b⟩ => (F a (sliceSecond ψ a)).ofLp b
  invFun ψ := WithLp.toLp 2 fun ⟨a, b⟩ => ((F a).symm (sliceSecond ψ a)).ofLp b
  map_add' ψ₁ ψ₂ := by
    ext ⟨a, b⟩
    have h : sliceSecond (ψ₁ + ψ₂) a = sliceSecond ψ₁ a + sliceSecond ψ₂ a := rfl
    simp only [WithLp.ofLp_add, Pi.add_apply, h, map_add]
  map_smul' r ψ := by
    ext ⟨a, b⟩
    have h : sliceSecond (r • ψ) a = r • sliceSecond ψ a := rfl
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, h, map_smul]
  left_inv ψ := by
    ext ⟨a, b⟩
    have h : sliceSecond (WithLp.toLp 2 fun ⟨a, b⟩ => (F a (sliceSecond ψ a)).ofLp b) a =
        F a (sliceSecond ψ a) := rfl
    simp only [h, LinearIsometryEquiv.symm_apply_apply, sliceSecond_apply]
  right_inv ψ := by
    ext ⟨a, b⟩
    have h :
        sliceSecond (WithLp.toLp 2 fun ⟨a, b⟩ => ((F a).symm (sliceSecond ψ a)).ofLp b) a =
          (F a).symm (sliceSecond ψ a) := rfl
    simp only [h, LinearIsometryEquiv.apply_symm_apply, sliceSecond_apply]
  norm_map' ψ := by
    have hsq : ‖(WithLp.toLp 2 fun ⟨a, b⟩ => (F a (sliceSecond ψ a)).ofLp b :
        EuclideanSpace ℂ (A × B₂))‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [norm_sq_prod, norm_sq_prod]
      refine sum_congr rfl fun a _ => ?_
      have h : sliceSecond (WithLp.toLp 2 fun ⟨a, b⟩ => (F a (sliceSecond ψ a)).ofLp b) a =
          F a (sliceSecond ψ a) := rfl
      rw [h, (F a).norm_map]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

@[simp] private theorem fiberIso_apply {A B₁ B₂ : Type*} [Fintype A] [Fintype B₁] [Fintype B₂]
    (F : A → (EuclideanSpace ℂ B₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ B₂))
    (ψ : EuclideanSpace ℂ (A × B₁)) (a : A) (b : B₂) :
    (fiberIso F ψ).ofLp (a, b) = (F a (sliceSecond ψ a)).ofLp b :=
  rfl

private noncomputable def reindexProd {P Q : Type*} [Fintype P] [Fintype Q] (e : P ≃ Q) :
    EuclideanSpace ℂ P ≃ₗᵢ[ℂ] EuclideanSpace ℂ Q :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp] private theorem reindexProd_apply {P Q : Type*} [Fintype P] [Fintype Q] (e : P ≃ Q)
    (ψ : EuclideanSpace ℂ P) (q : Q) :
    (reindexProd e ψ).ofLp q = ψ.ofLp (e.symm q) :=
  rfl

end FiberHelpers

/-! ### Value-query model -/

/-- The quantum state space of a value-query algorithm with query index register `ι`, value
register `V`, and workspace `W`. -/
abbrev ValueState (ι V W : Type*) := EuclideanSpace ℂ (ι × V × W)

section ValueModel

variable {ι V W α : Type*} [Fintype ι] [Fintype V] [Fintype W]

private def valSlice (ψ : ValueState ι V W) (i : ι) (w : W) : EuclideanSpace ℂ V :=
  WithLp.toLp 2 fun v => ψ.ofLp (i, v, w)

omit [Fintype ι] [Fintype V] [Fintype W] in
@[simp] private theorem valSlice_apply (ψ : ValueState ι V W) (i : ι) (w : W) (v : V) :
    (valSlice ψ i w).ofLp v = ψ.ofLp (i, v, w) := rfl

private theorem norm_sq_valueState (ψ : ValueState ι V W) :
    ‖ψ‖ ^ 2 = ∑ i : ι, ∑ w : W, ‖valSlice ψ i w‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun w _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  rfl

/-- **Value oracle**: given per-symbol unitaries `step : α → (ℂ^V ≃ₗᵢ[ℂ] ℂ^V)` and an input
`x : ι → α`, applies `step (x i)` to the value register controlled by the query index `i`. -/
@[expose] noncomputable def valueOracle
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)) (x : ι → α) :
    ValueState ι V W ≃ₗᵢ[ℂ] ValueState ι V W where
  toFun ψ := WithLp.toLp 2 fun ⟨i, v, w⟩ =>
    (step (x i) (WithLp.toLp 2 fun v' => ψ.ofLp (i, v', w))).ofLp v
  invFun ψ := WithLp.toLp 2 fun ⟨i, v, w⟩ =>
    ((step (x i)).symm (WithLp.toLp 2 fun v' => ψ.ofLp (i, v', w))).ofLp v
  map_add' ψ₁ ψ₂ := by
    ext ⟨i, v, w⟩
    dsimp only
    have h : (WithLp.toLp 2 fun v' => (ψ₁ + ψ₂).ofLp (i, v', w)) =
        (WithLp.toLp 2 fun v' => ψ₁.ofLp (i, v', w)) +
          (WithLp.toLp 2 fun v' => ψ₂.ofLp (i, v', w)) := rfl
    rw [PiLp.toLp_apply, PiLp.add_apply, PiLp.toLp_apply, PiLp.toLp_apply, h, map_add,
      PiLp.add_apply]
  map_smul' c ψ := by
    ext ⟨i, v, w⟩
    dsimp only
    have h : (WithLp.toLp 2 fun v' => (c • ψ).ofLp (i, v', w)) =
        c • (WithLp.toLp 2 fun v' => ψ.ofLp (i, v', w)) := rfl
    rw [PiLp.toLp_apply, RingHom.id_apply, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, h,
      map_smul, PiLp.smul_apply, smul_eq_mul]
  left_inv ψ := by
    ext ⟨i, v, w⟩
    have h : (WithLp.toLp 2 fun v' => (WithLp.toLp 2 fun ⟨i, v, w⟩ =>
        (step (x i) (WithLp.toLp 2 fun v' => ψ.ofLp (i, v', w))).ofLp v).ofLp (i, v', w)) =
        step (x i) (valSlice ψ i w) := rfl
    simp only [h, LinearIsometryEquiv.symm_apply_apply, valSlice_apply]
  right_inv ψ := by
    ext ⟨i, v, w⟩
    have h : (WithLp.toLp 2 fun v' => (WithLp.toLp 2 fun ⟨i, v, w⟩ =>
        ((step (x i)).symm (WithLp.toLp 2 fun v' => ψ.ofLp (i, v', w))).ofLp v).ofLp
          (i, v', w)) = (step (x i)).symm (valSlice ψ i w) := rfl
    simp only [h, LinearIsometryEquiv.apply_symm_apply, valSlice_apply]
  norm_map' ψ := by
    have hsq : ‖(WithLp.toLp 2 fun ⟨i, v, w⟩ =>
        (step (x i) (WithLp.toLp 2 fun v' => ψ.ofLp (i, v', w))).ofLp v :
        ValueState ι V W)‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [norm_sq_valueState, norm_sq_valueState]
      refine sum_congr rfl fun i _ => sum_congr rfl fun w _ => ?_
      have h : valSlice (WithLp.toLp 2 fun ⟨i, v, w⟩ =>
          (step (x i) (WithLp.toLp 2 fun v' => ψ.ofLp (i, v', w))).ofLp v) i w =
          step (x i) (valSlice ψ i w) := rfl
      rw [h, (step (x i)).norm_map]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

@[simp] theorem valueOracle_apply (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (x : ι → α) (ψ : ValueState ι V W) (i : ι) (v : V) (w : W) :
    (valueOracle step x ψ).ofLp (i, v, w) =
      (step (x i) (WithLp.toLp 2 fun v' => ψ.ofLp (i, v', w))).ofLp v :=
  rfl

/-- Unitary step arising from a family of permutations `π : α → Equiv.Perm V`, acting as
`|v⟩ ↦ |π a v⟩`. -/
@[expose] noncomputable def permStep (π : α → Equiv.Perm V) (a : α) :
    EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (π a)

@[simp] theorem permStep_apply (π : α → Equiv.Perm V) (a : α) (φ : EuclideanSpace ℂ V) (v : V) :
    (permStep π a φ).ofLp v = φ.ofLp ((π a).symm v) :=
  rfl

/-- Unitary step for an additive group value register `V`: `|v⟩ ↦ |v + a⟩`. This covers modular
addition on `ZMod M` as well as bitwise XOR on `BitString m`. -/
@[expose] noncomputable def addStep [AddGroup V] (a : V) :
    EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V :=
  permStep (fun b => Equiv.addRight b) a

@[simp] theorem addStep_apply [AddGroup V] (a : V) (φ : EuclideanSpace ℂ V) (v : V) :
    (addStep a φ).ofLp v = φ.ofLp (v - a) := by
  simp [addStep, sub_eq_add_neg]

@[simp] theorem addStep_symm_apply [AddGroup V] (a : V) (φ : EuclideanSpace ℂ V) (v : V) :
    ((addStep a).symm φ).ofLp v = φ.ofLp (v + a) := by
  simp [addStep, permStep]

theorem addStep_ket [DecidableEq V] [AddGroup V] (a v : V) :
    addStep a (ket v) = ket (v + a) := by
  ext u
  simp only [addStep_apply, ket_apply]
  by_cases h : u = v + a
  · have hsub : u - a = v := sub_eq_of_eq_add h
    simp [h, hsub]
  · have hsub : u - a ≠ v := fun heq => h (eq_add_of_sub_eq heq)
    simp [h, hsub]

/-- When every element of `V` has order dividing `2` (such as `BitString m`), the relative step
`(addStep a₀).symm.trans (addStep a₁)` is an involution. -/
theorem addStep_rel_involutive [AddCommGroup V] (h2 : ∀ v : V, v + v = 0) (a₀ a₁ : V)
    (φ : EuclideanSpace ℂ V) :
    ((addStep a₀).symm.trans (addStep a₁))
      (((addStep a₀).symm.trans (addStep a₁)) φ) = φ := by
  have hneg : ∀ x : V, -x = x := fun x => neg_eq_iff_add_eq_zero.mpr (h2 x)
  ext v
  simp only [LinearIsometryEquiv.trans_apply, addStep_apply, addStep_symm_apply]
  refine congrArg φ.ofLp ?_
  rw [sub_eq_add_neg, sub_eq_add_neg, hneg a₁]
  calc
    v + a₁ + a₀ + a₁ + a₀ = v + (a₁ + a₁) + (a₀ + a₀) := by abel
    _ = v := by rw [h2 a₁, h2 a₀, add_zero, add_zero]

/-- The state after `t` queries of a value-query algorithm `U` starting from `ψ₀` on input
`x : ι → α`. -/
@[expose] noncomputable def runValue
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ₀ : ValueState ι V W) (x : ι → α) : ℕ → ValueState ι V W
  | 0 => U 0 ψ₀
  | t + 1 => U (t + 1) (valueOracle step x (runValue step U ψ₀ x t))

/-- Value-query algorithms preserve norms. -/
theorem norm_runValue (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ₀ : ValueState ι V W) (x : ι → α) (t : ℕ) :
    ‖runValue step U ψ₀ x t‖ = ‖ψ₀‖ := by
  induction t with
  | zero => exact (U 0).norm_map ψ₀
  | succ t ih => rw [runValue, LinearIsometry.norm_map, LinearIsometryEquiv.norm_map, ih]

end ValueModel

/-! ### Simulating two-valued restrictions in the Boolean phase-oracle model -/

/-- The injective embedding of value-query computational basis outcomes `ι × V × W` into the
`ctrl = false` sector of `Fin N × Bool × V × W` along `e : ι ≃ Fin N`. -/
@[expose] def embedOutcome {ι V W : Type*} {N : ℕ} (e : ι ≃ Fin N) :
    (ι × V × W) ↪ (Fin N × Bool × V × W) where
  toFun p := (e p.1, false, p.2)
  inj' p₁ p₂ h := by
    obtain ⟨i₁, vw₁⟩ := p₁
    obtain ⟨i₂, vw₂⟩ := p₂
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (e.injective h.1) h.2.2

@[simp] theorem embedOutcome_apply {ι V W : Type*} {N : ℕ} (e : ι ≃ Fin N)
    (i : ι) (v : V) (w : W) :
    embedOutcome (V := V) (W := W) e (i, v, w) = (e i, false, v, w) :=
  rfl

section TwoValueSim

variable {ι V W : Type*} [Fintype ι] [Fintype V] [Fintype W]

/-- Embedding `ValueState ι V W` into the `ctrl = false` sector of `State N (V × W)` along
`e : ι ≃ Fin N`. -/
private noncomputable def embedState {N : ℕ} (e : ι ≃ Fin N) (ψ : ValueState ι V W) :
    State N (V × W) :=
  WithLp.toLp 2 fun ⟨j, c, v, w⟩ => if c then 0 else ψ.ofLp (e.symm j, v, w)

omit [Fintype ι] [Fintype V] [Fintype W] in
@[simp] private theorem embedState_apply {N : ℕ} (e : ι ≃ Fin N) (ψ : ValueState ι V W)
    (j : Fin N) (c : Bool) (v : V) (w : W) :
    (embedState e ψ).ofLp (j, c, v, w) = if c then 0 else ψ.ofLp (e.symm j, v, w) :=
  rfl

private theorem norm_embedState {N : ℕ} (e : ι ≃ Fin N) (ψ : ValueState ι V W) :
    ‖embedState e ψ‖ = ‖ψ‖ := by
  have hsq : ‖embedState e ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, embedState_apply, ite_true,
      Bool.false_eq_true, ite_false, norm_zero, zero_pow two_ne_zero, Finset.sum_const_zero,
      zero_add]
    exact Fintype.sum_equiv e.symm
      (fun j => ∑ v : V, ∑ w : W, ‖ψ.ofLp (e.symm j, v, w)‖ ^ 2)
      (fun i => ∑ v : V, ∑ w : W, ‖ψ.ofLp (i, v, w)‖ ^ 2)
      fun _ => rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

omit [Fintype ι] [Fintype V] [Fintype W] in
private theorem measureProb_embedState {N : ℕ} (e : ι ≃ Fin N) (ψ : ValueState ι V W)
    (S : Finset (ι × V × W)) :
    measureProb (embedState e ψ) (S.map (embedOutcome e)) = measureProb ψ S := by
  rw [measureProb, sum_map, measureProb]
  refine sum_congr rfl fun ⟨i, v, w⟩ _ => ?_
  simp

private def falseSector {N : ℕ} (e : ι ≃ Fin N) (φ : State N (V × W)) : ValueState ι V W :=
  WithLp.toLp 2 fun ⟨i, v, w⟩ => φ.ofLp (e i, false, v, w)

omit [Fintype ι] [Fintype V] [Fintype W] in
@[simp] private theorem falseSector_embedState {N : ℕ} (e : ι ≃ Fin N) (ψ : ValueState ι V W) :
    falseSector e (embedState e ψ) = ψ := by
  ext ⟨i, v, w⟩
  simp [falseSector]

/-- Lifting any linear isometry `f : ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W` to
`State N (V × W)`, acting as `f` on the `ctrl = false` sector and the identity on `ctrl = true`. -/
private noncomputable def liftValueIso {N : ℕ} (e : ι ≃ Fin N)
    (f : ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) :
    State N (V × W) →ₗᵢ[ℂ] State N (V × W) where
  toFun φ := WithLp.toLp 2 fun ⟨j, c, v, w⟩ =>
    if c then φ.ofLp (j, true, v, w) else (f (falseSector e φ)).ofLp (e.symm j, v, w)
  map_add' φ₁ φ₂ := by
    ext ⟨j, c, v, w⟩
    have h : falseSector e (φ₁ + φ₂) = falseSector e φ₁ + falseSector e φ₂ := rfl
    cases c <;> simp [h, map_add]
  map_smul' r φ := by
    ext ⟨j, c, v, w⟩
    have h : falseSector e (r • φ) = r • falseSector e φ := rfl
    cases c <;> simp [h, map_smul]
  norm_map' φ := by
    have hsq : ‖(WithLp.toLp 2 fun ⟨j, c, v, w⟩ =>
        if c then φ.ofLp (j, true, v, w) else (f (falseSector e φ)).ofLp (e.symm j, v, w) :
        State N (V × W))‖ ^ 2 = ‖φ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
      rw [sum_add_distrib, sum_add_distrib]
      congr 1
      calc
        ∑ j : Fin N, ∑ v : V, ∑ w : W, ‖(f (falseSector e φ)).ofLp (e.symm j, v, w)‖ ^ 2
            = ∑ i : ι, ∑ v : V, ∑ w : W, ‖(f (falseSector e φ)).ofLp (i, v, w)‖ ^ 2 :=
              Fintype.sum_equiv e.symm _ _ fun _ => rfl
        _ = ‖f (falseSector e φ)‖ ^ 2 := by
              rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
              refine sum_congr rfl fun i _ => ?_
              rw [Fintype.sum_prod_type]
        _ = ‖falseSector e φ‖ ^ 2 := by rw [f.norm_map]
        _ = ∑ i : ι, ∑ v : V, ∑ w : W, ‖φ.ofLp (e i, false, v, w)‖ ^ 2 := by
              rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
              refine sum_congr rfl fun i _ => ?_
              rw [Fintype.sum_prod_type]
              rfl
        _ = ∑ j : Fin N, ∑ v : V, ∑ w : W, ‖φ.ofLp (j, false, v, w)‖ ^ 2 :=
              Fintype.sum_equiv e _ _ fun _ => rfl
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem liftValueIso_embedState {N : ℕ} (e : ι ≃ Fin N)
    (f : ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) (ψ : ValueState ι V W) :
    liftValueIso e f (embedState e ψ) = embedState e (f ψ) := by
  ext ⟨j, c, v, w⟩
  cases c <;> simp [liftValueIso]

private def bvSlice {N : ℕ} (φ : State N (V × W)) (j : Fin N) (w : W) :
    EuclideanSpace ℂ (Bool × V) :=
  WithLp.toLp 2 fun ⟨c, v⟩ => φ.ofLp (j, c, v, w)

omit [Fintype ι] [Fintype V] [Fintype W] in
@[simp] private theorem bvSlice_apply {N : ℕ} (φ : State N (V × W)) (j : Fin N) (w : W)
    (c : Bool) (v : V) : (bvSlice φ j w).ofLp (c, v) = φ.ofLp (j, c, v, w) := rfl

private def bvFiberEquiv {N : ℕ} : (Fin N × Bool × V × W) ≃ ((Fin N × W) × (Bool × V)) where
  toFun p := ((p.1, p.2.2.2), (p.2.1, p.2.2.1))
  invFun q := (q.1.1, q.2.1, q.2.2, q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def liftBoolV {N : ℕ}
    (G : EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × V)) :
    State N (V × W) ≃ₗᵢ[ℂ] State N (V × W) :=
  (reindexProd (bvFiberEquiv (N := N) (V := V) (W := W))).trans
    ((fiberIso fun _ : Fin N × W => G).trans
      (reindexProd (bvFiberEquiv (N := N) (V := V) (W := W))).symm)

private theorem bvSlice_liftBoolV {N : ℕ}
    (G : EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × V))
    (φ : State N (V × W)) (j : Fin N) (w : W) :
    bvSlice (liftBoolV G φ) j w = G (bvSlice φ j w) := by
  ext ⟨c, v⟩
  rfl

/-- Controlled `Z` on `Bool × B`: negates amplitudes with `c = true` when `flag = true`. -/
private noncomputable def ctrlZ {B : Type*} [Fintype B] (flag : Bool) :
    EuclideanSpace ℂ (Bool × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × B) where
  toFun φ := WithLp.toLp 2 fun ⟨c, v⟩ => (if flag ∧ c then (-1 : ℂ) else 1) * φ.ofLp (c, v)
  invFun φ := WithLp.toLp 2 fun ⟨c, v⟩ => (if flag ∧ c then (-1 : ℂ) else 1) * φ.ofLp (c, v)
  map_add' φ₁ φ₂ := by
    ext ⟨c, v⟩; simp only [PiLp.toLp_apply, WithLp.ofLp_add, Pi.add_apply]; ring
  map_smul' r φ := by
    ext ⟨c, v⟩; simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  left_inv φ := by ext ⟨c, v⟩; cases flag <;> cases c <;> simp
  right_inv φ := by ext ⟨c, v⟩; cases flag <;> cases c <;> simp
  norm_map' φ := by
    have hsq : ‖(WithLp.toLp 2 fun ⟨c, v⟩ =>
        (if flag ∧ c then (-1 : ℂ) else 1) * φ.ofLp (c, v) :
        EuclideanSpace ℂ (Bool × B))‖ ^ 2 = ‖φ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      refine sum_congr rfl fun ⟨c, v⟩ _ => ?_
      cases flag <;> cases c <;> simp
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

omit [Fintype ι] [Fintype W] in
private theorem bvSlice_phaseOracle {N : ℕ} (b : Fin N → Bool) (φ : State N (V × W))
    (j : Fin N) (w : W) :
    bvSlice (phaseOracle b φ) j w = ctrlZ (b j) (bvSlice φ j w) := by
  ext ⟨c, v⟩
  rcases hbj : b j with _ | _ <;> cases c <;> simp [ctrlZ, phaseOracle_apply, hbj]

private def embedBoolFalse (φ : EuclideanSpace ℂ V) : EuclideanSpace ℂ (Bool × V) :=
  WithLp.toLp 2 fun ⟨c, v⟩ => if c then 0 else φ.ofLp v

omit [Fintype ι] [Fintype V] [Fintype W] in
private theorem bvSlice_embedState {N : ℕ} (e : ι ≃ Fin N) (ψ : ValueState ι V W)
    (j : Fin N) (w : W) :
    bvSlice (embedState e ψ) j w = embedBoolFalse (valSlice ψ (e.symm j) w) := by
  ext ⟨c, v⟩
  cases c <;> simp [embedBoolFalse]

omit [Fintype ι] [Fintype V] [Fintype W] in
private theorem eq_embedState_of_bvSlice {N : ℕ} (e : ι ≃ Fin N)
    (φ : State N (V × W)) (ψ : ValueState ι V W)
    (h : ∀ j w, bvSlice φ j w = embedBoolFalse (valSlice ψ (e.symm j) w)) :
    φ = embedState e ψ := by
  ext ⟨j, c, v, w⟩
  have hjw := congrArg (fun u => u.ofLp (c, v)) (h j w)
  cases c <;> simpa [embedBoolFalse] using hjw

/-! #### 1-query simulation for involutive relative step -/

/-- Unitary `G` on `ℂ^(Bool × V)` turning controlled `Z` into controlled `R` when `R² = 1`. -/
private noncomputable def invBoolV (R : EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)
    (hR : ∀ φ, R (R φ) = φ) :
    EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × V) :=
  let s0 (ψ : EuclideanSpace ℂ (Bool × V)) : EuclideanSpace ℂ V :=
    WithLp.toLp 2 fun v => ψ.ofLp (false, v)
  let s1 (ψ : EuclideanSpace ℂ (Bool × V)) : EuclideanSpace ℂ V :=
    WithLp.toLp 2 fun v => ψ.ofLp (true, v)
  let F (ψ : EuclideanSpace ℂ (Bool × V)) : EuclideanSpace ℂ (Bool × V) :=
    WithLp.toLp 2 fun ⟨c, v⟩ =>
      (1 / 2 : ℂ) * ((s0 ψ).ofLp v + (R (s0 ψ)).ofLp v * (if c then -1 else 1) +
        (s1 ψ).ofLp v + (R (s1 ψ)).ofLp v * (if c then 1 else -1))
  have hs0 : ∀ φ, s0 (F φ) = (1 / 2 : ℂ) • (s0 φ + R (s0 φ) + s1 φ - R (s1 φ)) := by
    intro φ
    ext v
    simp only [F, s0, s1, PiLp.toLp_apply, Bool.false_eq_true, ite_false, ite_true,
      PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, smul_eq_mul]
    ring
  have hs1 : ∀ φ, s1 (F φ) = (1 / 2 : ℂ) • (s0 φ - R (s0 φ) + s1 φ + R (s1 φ)) := by
    intro φ
    ext v
    simp only [F, s0, s1, PiLp.toLp_apply, Bool.false_eq_true, ite_false, ite_true,
      PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, smul_eq_mul]
    ring
  have hFinv : ∀ ψ, F (F ψ) = ψ := fun ψ => by
    ext ⟨c, v⟩
    have h0 := hs0 ψ
    have h1 := hs1 ψ
    have hF0 : (s0 (F ψ)).ofLp v =
        (1 / 2 : ℂ) * ((s0 ψ).ofLp v + (R (s0 ψ)).ofLp v + (s1 ψ).ofLp v -
          (R (s1 ψ)).ofLp v) := by
      rw [h0]
      simp only [PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, smul_eq_mul]
    have hF1 : (s1 (F ψ)).ofLp v =
        (1 / 2 : ℂ) * ((s0 ψ).ofLp v - (R (s0 ψ)).ofLp v + (s1 ψ).ofLp v +
          (R (s1 ψ)).ofLp v) := by
      rw [h1]
      simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul]
    have hRF0 : R (s0 (F ψ)) =
        (1 / 2 : ℂ) • (R (s0 ψ) + s0 ψ + R (s1 ψ) - s1 ψ) := by
      rw [h0, map_smul, map_sub, map_add, map_add, hR, hR]
    have hRF1 : R (s1 (F ψ)) =
        (1 / 2 : ℂ) • (R (s0 ψ) - s0 ψ + R (s1 ψ) + s1 ψ) := by
      rw [h1, map_smul, map_add, map_add, map_sub, hR, hR]
    have hRF0v := congrArg (fun x => x.ofLp v) hRF0
    have hRF1v := congrArg (fun x => x.ofLp v) hRF1
    simp only [PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, smul_eq_mul] at hRF0v hRF1v
    cases c <;>
      simp only [F, PiLp.toLp_apply, Bool.false_eq_true, ite_false, ite_true, hF0, hF1, hRF0v,
        hRF1v]
    · simp only [s0, PiLp.toLp_apply]; ring
    · simp only [s1, PiLp.toLp_apply]; ring
  { toFun := F
    invFun := F
    map_add' := fun ψ₁ ψ₂ => by
      ext ⟨c, v⟩
      have h0 : s0 (ψ₁ + ψ₂) = s0 ψ₁ + s0 ψ₂ := rfl
      have h1 : s1 (ψ₁ + ψ₂) = s1 ψ₁ + s1 ψ₂ := rfl
      simp only [F, PiLp.toLp_apply, WithLp.ofLp_add, Pi.add_apply, h0, h1, map_add]
      ring
    map_smul' := fun r ψ => by
      ext ⟨c, v⟩
      have h0 : s0 (r • ψ) = r • s0 ψ := rfl
      have h1 : s1 (r • ψ) = r • s1 ψ := rfl
      simp only [F, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, h0, h1,
        map_smul]
      ring
    left_inv := hFinv
    right_inv := hFinv
    norm_map' := fun ψ => by
      let u0 := s0 ψ
      let u1 := s1 ψ
      let p0 := (1 / 2 : ℂ) • (u0 + R u0)
      let m0 := (1 / 2 : ℂ) • (u0 - R u0)
      let p1 := (1 / 2 : ℂ) • (u1 + R u1)
      let m1 := (1 / 2 : ℂ) • (u1 - R u1)
      have hRsa : ∀ x y : EuclideanSpace ℂ V, inner ℂ (R x) y = inner ℂ x (R y) := fun x y => by
        calc
          inner ℂ (R x) y = inner ℂ (R x) (R (R y)) := by rw [hR y]
          _ = inner ℂ x (R y) := R.inner_map_map x (R y)
      have hortho : ∀ x y : EuclideanSpace ℂ V,
          inner ℂ ((1 / 2 : ℂ) • (x + R x)) ((1 / 2 : ℂ) • (y - R y)) = 0 := by
        intro x y
        calc
          inner ℂ ((1 / 2 : ℂ) • (x + R x)) ((1 / 2 : ℂ) • (y - R y))
              = (1 / 4 : ℂ) * (inner ℂ x y - inner ℂ x (R y) + inner ℂ (R x) y -
                  inner ℂ (R x) (R y)) := by
                simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_sub_right]
                have hstar : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
                  simp only [map_div₀, map_one, map_ofNat]
                rw [hstar]
                ring
          _ = (1 / 4 : ℂ) * (inner ℂ x y - inner ℂ x (R y) + inner ℂ x (R y) -
                  inner ℂ x y) := by rw [hRsa x y, R.inner_map_map]
          _ = 0 := by ring
      have hsq_split : ∀ x : EuclideanSpace ℂ V,
          ‖(1 / 2 : ℂ) • (x + R x)‖ ^ 2 + ‖(1 / 2 : ℂ) • (x - R x)‖ ^ 2 = ‖x‖ ^ 2 := by
        intro x
        rw [norm_smul, norm_smul, mul_pow, mul_pow, ← mul_add, parallelogram_law_with_norm ℂ x (R x),
          R.norm_map]
        norm_num
        ring
      have hF0 : s0 (F ψ) = p0 + m1 := by
        ext v
        simp only [F, s0, s1, p0, m1, u0, u1, PiLp.toLp_apply, PiLp.add_apply, PiLp.smul_apply,
          PiLp.sub_apply, smul_eq_mul, Bool.false_eq_true, ite_false, ite_true]
        ring
      have hF1 : s1 (F ψ) = m0 + p1 := by
        ext v
        simp only [F, s0, s1, m0, p1, u0, u1, PiLp.toLp_apply, PiLp.add_apply, PiLp.smul_apply,
          PiLp.sub_apply, smul_eq_mul, ite_true, Bool.false_eq_true, ite_false]
        ring
      have hperp : ∀ a b : EuclideanSpace ℂ V, inner ℂ a b = 0 →
          ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := fun a b hab => by
        have hba : inner ℂ b a = 0 := inner_eq_zero_symm.mpr hab
        have hc : ((‖a + b‖ ^ 2 : ℝ) : ℂ) = ((‖a‖ ^ 2 + ‖b‖ ^ 2 : ℝ) : ℂ) := by
          calc
            ((‖a + b‖ ^ 2 : ℝ) : ℂ) = inner ℂ (a + b) (a + b) := by
              rw [inner_self_eq_norm_sq_to_K]; norm_cast
            _ = inner ℂ a a + inner ℂ a b + (inner ℂ b a + inner ℂ b b) := by
              rw [inner_add_left, inner_add_right, inner_add_right]
            _ = inner ℂ a a + inner ℂ b b := by rw [hab, hba, add_zero, zero_add]
            _ = ((‖a‖ ^ 2 + ‖b‖ ^ 2 : ℝ) : ℂ) := by
              rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
              push_cast; rfl
        exact_mod_cast hc
      have h0n : ‖p0 + m1‖ ^ 2 = ‖p0‖ ^ 2 + ‖m1‖ ^ 2 := hperp p0 m1 (hortho u0 u1)
      have h1n : ‖m0 + p1‖ ^ 2 = ‖m0‖ ^ 2 + ‖p1‖ ^ 2 := by
        rw [add_comm]
        calc
          ‖p1 + m0‖ ^ 2 = ‖p1‖ ^ 2 + ‖m0‖ ^ 2 := hperp p1 m0 (hortho u1 u0)
          _ = ‖m0‖ ^ 2 + ‖p1‖ ^ 2 := add_comm _ _
      have hsplit : ∀ φ : EuclideanSpace ℂ (Bool × V),
          ‖φ‖ ^ 2 = ‖s0 φ‖ ^ 2 + ‖s1 φ‖ ^ 2 := fun φ => by
        rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
        simp [EuclideanSpace.norm_sq_eq, s0, s1]
      have hsq : ‖F ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
        rw [hsplit (F ψ), hF0, hF1, h0n, h1n, hsplit ψ]
        have ha := hsq_split u0
        have hb := hsq_split u1
        change ‖p0‖ ^ 2 + ‖m0‖ ^ 2 = ‖u0‖ ^ 2 at ha
        change ‖p1‖ ^ 2 + ‖m1‖ ^ 2 = ‖u1‖ ^ 2 at hb
        linarith
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq }

private theorem invBoolV_ctrlZ_invBoolV (R : EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)
    (hR : ∀ φ, R (R φ) = φ) (flag : Bool) (φ : EuclideanSpace ℂ V) :
    invBoolV R hR (ctrlZ flag (invBoolV R hR (embedBoolFalse φ))) =
      embedBoolFalse (if flag then R φ else φ) := by
  cases flag
  · have hcz : ctrlZ false (invBoolV R hR (embedBoolFalse φ)) =
        invBoolV R hR (embedBoolFalse φ) := by
      ext ⟨c, v⟩; cases c <;> simp [ctrlZ]
    have hinv : invBoolV R hR (invBoolV R hR (embedBoolFalse φ)) = embedBoolFalse φ :=
      (invBoolV R hR).apply_symm_apply _
    simpa using congrArg (invBoolV R hR) hcz |>.trans hinv
  · ext ⟨c, v⟩
    have hzero : (WithLp.toLp 2 fun _ : V => (0 : ℂ)) = (0 : EuclideanSpace ℂ V) := rfl
    have hs0 : (WithLp.toLp 2 fun v => (ctrlZ true (invBoolV R hR (embedBoolFalse φ))).ofLp
        (false, v)) = (1 / 2 : ℂ) • (φ + R φ) := by
      ext u
      simp [ctrlZ, invBoolV, embedBoolFalse, hzero]
      ring
    have hs1 : (WithLp.toLp 2 fun v => (ctrlZ true (invBoolV R hR (embedBoolFalse φ))).ofLp
        (true, v)) = -(1 / 2 : ℂ) • (φ - R φ) := by
      ext u
      simp [ctrlZ, invBoolV, embedBoolFalse, hzero]
      ring
    have hRs0 : R (WithLp.toLp 2 fun v => (ctrlZ true (invBoolV R hR (embedBoolFalse φ))).ofLp
        (false, v)) = (1 / 2 : ℂ) • (R φ + φ) := by
      rw [hs0, map_smul, map_add, hR]
    have hRs1 : R (WithLp.toLp 2 fun v => (ctrlZ true (invBoolV R hR (embedBoolFalse φ))).ofLp
        (true, v)) = -(1 / 2 : ℂ) • (R φ - φ) := by
      rw [hs1, map_smul, map_sub, hR]
    have h0v := congrArg (fun x => x.ofLp v) hs0
    have h1v := congrArg (fun x => x.ofLp v) hs1
    have hR0v := congrArg (fun x => x.ofLp v) hRs0
    have hR1v := congrArg (fun x => x.ofLp v) hRs1
    simp only [PiLp.toLp_apply, PiLp.smul_apply, PiLp.neg_apply, PiLp.add_apply, PiLp.sub_apply,
      smul_eq_mul] at h0v h1v hR0v hR1v
    cases c
    · simp only [invBoolV, LinearIsometryEquiv.coe_mk, PiLp.toLp_apply, Bool.false_eq_true,
        ite_false, ite_true, embedBoolFalse]
      change (1 / 2 : ℂ) * ((WithLp.toLp 2 fun v => (ctrlZ true (invBoolV R hR
          (embedBoolFalse φ))).ofLp (false, v)).ofLp v +
        (R (WithLp.toLp 2 fun v => (ctrlZ true (invBoolV R hR (embedBoolFalse φ))).ofLp
          (false, v))).ofLp v * 1 +
        (WithLp.toLp 2 fun v => (ctrlZ true (invBoolV R hR (embedBoolFalse φ))).ofLp
          (true, v)).ofLp v +
        (R (WithLp.toLp 2 fun v => (ctrlZ true (invBoolV R hR (embedBoolFalse φ))).ofLp
          (true, v))).ofLp v * -1) = (R φ).ofLp v
      rw [h0v, h1v, hR0v, hR1v]
      ring
    · simp only [invBoolV, LinearIsometryEquiv.coe_mk, PiLp.toLp_apply, ite_true, embedBoolFalse]
      change (1 / 2 : ℂ) * ((WithLp.toLp 2 fun v => (ctrlZ true (invBoolV R hR
          (embedBoolFalse φ))).ofLp (false, v)).ofLp v +
        (R (WithLp.toLp 2 fun v => (ctrlZ true (invBoolV R hR (embedBoolFalse φ))).ofLp
          (false, v))).ofLp v * -1 +
        (WithLp.toLp 2 fun v => (ctrlZ true (invBoolV R hR (embedBoolFalse φ))).ofLp
          (true, v)).ofLp v +
        (R (WithLp.toLp 2 fun v => (ctrlZ true (invBoolV R hR (embedBoolFalse φ))).ofLp
          (true, v))).ofLp v * 1) = 0
      rw [h0v, h1v, hR0v, hR1v]
      ring

/-- **1-query simulation of an involutive two-valued oracle restriction**: if
`(step a₀).symm.trans (step a₁)` is an involution, any `T`-query value-query algorithm restricted
to `{a₀, a₁}` along `e : ι ≃ Fin N` can be simulated by `T` binary phase-oracle queries. -/
theorem exists_sim_involution {N : ℕ} [DecidableEq ι] [DecidableEq V] [DecidableEq W]
    {α : Type*} (e : ι ≃ Fin N)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (a₀ a₁ : α)
    (hR : ∀ φ, ((step a₀).symm.trans (step a₁)) (((step a₀).symm.trans (step a₁)) φ) = φ)
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ₀ : ValueState ι V W) (T : ℕ) :
    ∃ (Vsim : ℕ → State N (V × W) →ₗᵢ[ℂ] State N (V × W)) (φ₀ : State N (V × W)),
      ‖φ₀‖ = ‖ψ₀‖ ∧
        ∀ (b : Fin N → Bool) (S : Finset (ι × V × W)),
          measureProb (run Vsim φ₀ b T) (S.map (embedOutcome e)) =
            measureProb (runValue step U ψ₀ (fun i => if b (e i) then a₁ else a₀) T) S := by
  let R := (step a₀).symm.trans (step a₁)
  let G := invBoolV R hR
  let stepA0 : ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W :=
    (valueOracle step fun _ => a₀).toLinearIsometry
  let A0 : State N (V × W) →ₗᵢ[ℂ] State N (V × W) := liftValueIso e stepA0
  let pre : State N (V × W) →ₗᵢ[ℂ] State N (V × W) := (liftBoolV G).toLinearIsometry.comp A0
  let Vsim : ℕ → State N (V × W) →ₗᵢ[ℂ] State N (V × W) := fun s =>
    if s = 0 then
      if 0 < T then pre.comp (liftValueIso e (U 0)) else liftValueIso e (U 0)
    else if s < T then
      pre.comp ((liftValueIso e (U s)).comp (liftBoolV G).toLinearIsometry)
    else if s = T then
      (liftValueIso e (U T)).comp (liftBoolV G).toLinearIsometry
    else LinearIsometry.id
  refine ⟨Vsim, embedState e ψ₀, norm_embedState e ψ₀, fun b S => ?_⟩
  let x : ι → α := fun i => if b (e i) then a₁ else a₀
  have hstep : ∀ y : ValueState ι V W,
      liftBoolV G (phaseOracle b (liftBoolV G (A0 (embedState e y)))) =
        embedState e (valueOracle step x y) := by
    intro y
    refine eq_embedState_of_bvSlice e _ _ fun j w => ?_
    rw [bvSlice_liftBoolV, bvSlice_phaseOracle, bvSlice_liftBoolV]
    have hA0 : bvSlice (A0 (embedState e y)) j w =
        embedBoolFalse (step a₀ (valSlice y (e.symm j) w)) := by
      rw [show A0 (embedState e y) = embedState e (stepA0 y) from liftValueIso_embedState e stepA0 y,
        bvSlice_embedState]
      congr 1
      ext v
      exact valueOracle_apply step (fun _ => a₀) y (e.symm j) v w
    rw [hA0, invBoolV_ctrlZ_invBoolV]
    congr 1
    ext v
    have hv := valueOracle_apply step x y (e.symm j) v w
    simp only [x, Equiv.apply_symm_apply] at hv
    cases hbj : b j <;> simp [hbj, hv, R]
  have hrun : ∀ t ≤ T,
      run Vsim (embedState e ψ₀) b t =
        if t < T then liftBoolV G (A0 (embedState e (runValue step U ψ₀ x t)))
        else embedState e (runValue step U ψ₀ x T) := by
    intro t ht
    induction t with
    | zero =>
      simp only [run, Vsim, ite_true]
      by_cases hT : 0 < T
      · simp [hT, pre, liftValueIso_embedState, runValue]
      · have hT0 : T = 0 := by omega
        subst hT0
        simp [liftValueIso_embedState, runValue]
    | succ t ih =>
      have ht' : t < T := by omega
      have hprev := ih ht'.le
      rw [ite_eq_left.mpr fun h => absurd ht' h] at hprev
      have hV : Vsim (t + 1) =
          if t + 1 < T then
            pre.comp ((liftValueIso e (U (t + 1))).comp (liftBoolV G).toLinearIsometry)
          else (liftValueIso e (U T)).comp (liftBoolV G).toLinearIsometry := by
        simp only [Vsim, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
        by_cases hlt : t + 1 < T
        · simp [hlt]
        · have heq : t + 1 = T := by omega
          simp [hlt, heq]
      rw [run, hprev, hV]
      by_cases hlt : t + 1 < T
      · simp [hlt, pre, hstep, liftValueIso_embedState, runValue]
      · have heq : t + 1 = T := by omega
        subst heq
        simp [hstep, liftValueIso_embedState, runValue]
  have hT := hrun T le_rfl
  rw [ite_eq_right.mpr fun h => absurd h (lt_irrefl T)] at hT
  rw [hT, measureProb_embedState]

/-! #### 2-query simulation for arbitrary unitary relative step -/

/-- Any unitary on a finite-dimensional complex inner product space has an orthonormal basis of
simultaneous eigenvectors of its Hermitian and skew-Hermitian parts. -/
private theorem exists_orthonormalBasis_eigenvectors
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (R : E ≃ₗᵢ[ℂ] E) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E)
      (μ ν : Fin (Module.finrank ℂ E) → ℝ),
      (∀ k, (μ k) ^ 2 + (ν k) ^ 2 = 1) ∧
      (∀ k, R (b k) = ((μ k : ℂ) + Complex.I * (ν k : ℂ)) • b k) := by
  let U : E →ₗ[ℂ] E := R.toLinearMap
  let Um : E →ₗ[ℂ] E := R.symm.toLinearMap
  have hU : ∀ x, U x = R x := fun _ => rfl
  have hUm : ∀ x, Um x = R.symm x := fun _ => rfl
  let H : E →ₗ[ℂ] E := (1 / 2 : ℂ) • (U + Um)
  let K : E →ₗ[ℂ] E := (-Complex.I / 2 : ℂ) • (U - Um)
  have hRsa : ∀ x y : E, inner ℂ (R x) y = inner ℂ x (R.symm y) := fun x y => by
    calc
      inner ℂ (R x) y = inner ℂ (R x) (R (R.symm y)) := by rw [R.apply_symm_apply]
      _ = inner ℂ x (R.symm y) := R.inner_map_map x (R.symm y)
  have hRmsa : ∀ x y : E, inner ℂ (R.symm x) y = inner ℂ x (R y) := fun x y => by
    calc
      inner ℂ (R.symm x) y = inner ℂ (R (R.symm x)) (R y) := (R.inner_map_map _ _).symm
      _ = inner ℂ x (R y) := by rw [R.apply_symm_apply]
  have hHsym : H.IsSymmetric := fun x y => by
    simp only [H, LinearMap.smul_apply, LinearMap.add_apply, hU, hUm,
      inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, hRsa, hRmsa]
    simp only [starRingEnd_apply, star_div₀, star_one, star_ofNat]
    ring
  have hKsym : K.IsSymmetric := fun x y => by
    calc
      inner ℂ (K x) y
          = (Complex.I / 2) * (inner ℂ (R x) y - inner ℂ (R.symm x) y) := by
            simp only [K, LinearMap.smul_apply, LinearMap.sub_apply, hU, hUm, inner_smul_left,
              inner_sub_left]
            have hstar : starRingEnd ℂ (-Complex.I / 2) = Complex.I / 2 := by
              simp only [map_div₀, map_neg, Complex.conj_I, map_ofNat, neg_neg]
            rw [hstar]
      _ = (Complex.I / 2) * (inner ℂ x (R.symm y) - inner ℂ x (R y)) := by rw [hRsa, hRmsa]
      _ = inner ℂ x (K y) := by
            simp only [K, LinearMap.smul_apply, LinearMap.sub_apply, hU, hUm, inner_smul_right,
              inner_sub_right]
            ring
  have hHK : ∀ x, H (K x) = K (H x) := fun x => by
    simp only [H, K, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      map_smul, map_add, map_sub, hU, hUm, R.apply_symm_apply, R.symm_apply_apply]
    module
  have hR_decomp : ∀ x, R x = H x + Complex.I • K x := fun x => by
    simp only [H, K, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, hU, hUm]
    rw [smul_smul]
    have hI : Complex.I * (-Complex.I / 2) = 1 / 2 := by
      rw [mul_div_assoc', mul_neg, Complex.I_mul_I]
      ring
    rw [hI, ← smul_add]
    have hsum : (R x + R.symm x) + (R x - R.symm x) = (2 : ℂ) • R x := by module
    rw [hsum, smul_smul]
    norm_num
  have hind : ∀ n : ℕ, ∀ (W : Submodule ℂ E),
      (∀ x ∈ W, H x ∈ W) → (∀ x ∈ W, K x ∈ W) → Module.finrank ℂ W = n →
      ∃ (v : Fin n → E) (μ ν : Fin n → ℝ),
        Orthonormal ℂ v ∧ (∀ k, v k ∈ W) ∧ (∀ k, H (v k) = (μ k : ℂ) • v k) ∧
          (∀ k, K (v k) = (ν k : ℂ) • v k) := by
    intro n
    induction n with
    | zero =>
      intro W _ _ _
      exact ⟨Fin.elim0, Fin.elim0, Fin.elim0, orthonormal_iff_ite.mpr fun i => Fin.elim0 i,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | succ n ih =>
      intro W hHW hKW hdim
      let H_W : W →ₗ[ℂ] W := H.restrict hHW
      let K_W : W →ₗ[ℂ] W := K.restrict hKW
      have hH_W : H_W.IsSymmetric := hHsym.restrict_invariant hHW
      have hK_W : K_W.IsSymmetric := hKsym.restrict_invariant hKW
      let μ₀ : ℝ := hH_W.eigenvalues hdim ⟨0, Nat.zero_lt_succ n⟩
      have heig : Module.End.HasEigenvalue H_W (μ₀ : ℂ) :=
        hH_W.hasEigenvalue_eigenvalues hdim ⟨0, Nat.zero_lt_succ n⟩
      let S : Submodule ℂ W := Module.End.eigenspace H_W (μ₀ : ℂ)
      have hS_ne : S ≠ ⊥ := Module.End.hasEigenvalue_iff.mp heig
      have hS_pos : 0 < Module.finrank ℂ S :=
        Nat.pos_of_ne_zero fun h0 => hS_ne (Submodule.finrank_eq_zero.mp h0)
      have hKS : ∀ x ∈ S, K_W x ∈ S := by
        intro x hx
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        apply Subtype.ext
        have h1 : H (K (x : E)) = K (H (x : E)) := hHK (x : E)
        have h2 : H (x : E) = (μ₀ : ℂ) • (x : E) := congrArg Subtype.val hx
        change H (K (x : E)) = (μ₀ : ℂ) • K (x : E)
        rw [h1, h2, map_smul]
      let K_S : S →ₗ[ℂ] S := K_W.restrict hKS
      have hK_S := hK_W.restrict_invariant hKS
      let ν₀ : ℝ := hK_S.eigenvalues rfl ⟨0, hS_pos⟩
      let u₀ : S := hK_S.eigenvectorBasis rfl ⟨0, hS_pos⟩
      have hu₀_norm : ‖u₀‖ = 1 := (hK_S.eigenvectorBasis rfl).orthonormal.1 ⟨0, hS_pos⟩
      have hu₀_eig : K_S u₀ = (ν₀ : ℂ) • u₀ :=
        Module.End.mem_eigenspace_iff.mp (hK_S.hasEigenvector_eigenvectorBasis rfl ⟨0, hS_pos⟩).1
      let w₀ : W := (u₀ : W)
      let v₀ : E := (w₀ : E)
      have hv₀W : v₀ ∈ W := w₀.2
      have hv₀_norm : ‖v₀‖ = 1 := hu₀_norm
      have hv₀H : H v₀ = (μ₀ : ℂ) • v₀ := by
        have hw₀S : w₀ ∈ S := u₀.2
        rw [Module.End.mem_eigenspace_iff] at hw₀S
        exact congrArg Subtype.val hw₀S
      have hv₀K : K v₀ = (ν₀ : ℂ) • v₀ := by
        have h1 : K_W w₀ = (ν₀ : ℂ) • w₀ := congrArg Subtype.val hu₀_eig
        exact congrArg Subtype.val h1
      let L : Submodule ℂ W := Submodule.span ℂ ({w₀} : Set W)
      let L_orth : Submodule ℂ W := Lᗮ
      let W' : Submodule ℂ E := L_orth.map W.subtype
      have hw₀_ne : w₀ ≠ 0 := by
        intro h
        have h0 : ‖w₀‖ = 0 := by rw [h, norm_zero]
        have h1 : (1 : ℝ) = 0 := by simpa [v₀] using hv₀_norm.symm.trans h0
        norm_num at h1
      have hL_dim : Module.finrank ℂ L = 1 := finrank_span_singleton hw₀_ne
      have hL_orth_dim : Module.finrank ℂ L_orth = n := by
        have hsum := Submodule.finrank_add_finrank_orthogonal L
        rw [hL_dim, hdim] at hsum
        dsimp [L_orth]
        omega
      have hW'_dim : Module.finrank ℂ W' = n := by
        rw [Submodule.finrank_map_subtype_eq]
        exact hL_orth_dim
      have hv₀_orth_W' : ∀ x ∈ W', inner ℂ v₀ x = 0 := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
        exact hy w₀ (Submodule.subset_span (Set.mem_singleton w₀))
      have hW'_sub : W' ≤ W := by
        intro x hx
        obtain ⟨y, _, rfl⟩ := Submodule.mem_map.mp hx
        exact y.2
      have hHW' : ∀ x ∈ W', H x ∈ W' := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
        refine Submodule.mem_map.mpr ⟨⟨H (y : E), hHW (y : E) y.2⟩, ?_, rfl⟩
        intro z hz
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
        change inner ℂ (c • v₀) (H (y : E)) = 0
        rw [inner_smul_left, ← hHsym v₀ (y : E), hv₀H, inner_smul_left,
          hv₀_orth_W' (y : E) (Submodule.mem_map.mpr ⟨y, hy, rfl⟩)]
        simp
      have hKW' : ∀ x ∈ W', K x ∈ W' := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
        refine Submodule.mem_map.mpr ⟨⟨K (y : E), hKW (y : E) y.2⟩, ?_, rfl⟩
        intro z hz
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
        change inner ℂ (c • v₀) (K (y : E)) = 0
        rw [inner_smul_left, ← hKsym v₀ (y : E), hv₀K, inner_smul_left,
          hv₀_orth_W' (y : E) (Submodule.mem_map.mpr ⟨y, hy, rfl⟩)]
        simp
      obtain ⟨v', μ', ν', hv'_ortho, hv'W', hv'H, hv'K⟩ := ih W' hHW' hKW' hW'_dim
      refine ⟨Fin.cons v₀ v', Fin.cons μ₀ μ', Fin.cons ν₀ ν', ?_, ?_, ?_, ?_⟩
      · rw [orthonormal_iff_ite]
        intro i j
        refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
        · simp [inner_self_eq_norm_sq_to_K, hv₀_norm]
        · simp [Fin.cons_zero, Fin.cons_succ, Fin.zero_ne_succ, hv₀_orth_W' _ (hv'W' j')]
        · simp [Fin.cons_zero, Fin.cons_succ, Fin.succ_ne_zero,
            inner_eq_zero_symm.mp (hv₀_orth_W' _ (hv'W' i'))]
        · simp only [Fin.cons_succ, Fin.succ_inj]
          exact (orthonormal_iff_ite.mp hv'_ortho) i' j'
      · intro k
        refine Fin.cases hv₀W (fun k' => hW'_sub (hv'W' k')) k
      · intro k
        refine Fin.cases hv₀H (fun k' => hv'H k') k
      · intro k
        refine Fin.cases hv₀K (fun k' => hv'K k') k
  obtain ⟨v, μ, ν, hv_ortho, _, hvH, hvK⟩ :=
    hind (Module.finrank ℂ E) ⊤ (fun _ _ => trivial) (fun _ _ => trivial) (by simp)
  have hunit : ∀ k, (μ k) ^ 2 + (ν k) ^ 2 = 1 := by
    intro k
    have hRv : R (v k) = ((μ k : ℂ) + Complex.I * (ν k : ℂ)) • v k := by
      rw [hR_decomp, hvH k, hvK k, smul_smul, ← add_smul]
    have hnorm : ‖((μ k : ℂ) + Complex.I * (ν k : ℂ))‖ = 1 := by
      have h1 : ‖R (v k)‖ = 1 := by rw [R.norm_map, hv_ortho.1 k]
      rw [hRv, norm_smul, hv_ortho.1 k, mul_one] at h1
      exact h1
    have hsq : ‖((μ k : ℂ) + Complex.I * (ν k : ℂ))‖ ^ 2 = 1 := by rw [hnorm, one_pow]
    have hnsq : Complex.normSq ((μ k : ℂ) + Complex.I * (ν k : ℂ)) =
        (μ k) ^ 2 + (ν k) ^ 2 := by
      rw [Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, sq]
    rw [Complex.sq_norm] at hsq
    linarith
  rcases Nat.eq_zero_or_pos (Module.finrank ℂ E) with hdim0 | hdimpos
  · let b0 : Module.Basis (Fin (Module.finrank ℂ E)) ℂ E :=
      Module.Basis.mk (v := v) hv_ortho.linearIndependent (fun x _ => by
        have hsub : Subsingleton E := Module.finrank_zero_iff.mp hdim0
        rw [Subsingleton.elim x 0]
        exact zero_mem _)
    refine ⟨b0.toOrthonormalBasis (by simpa [b0] using hv_ortho), μ, ν, hunit, fun k =>
      Fin.elim0 (hdim0 ▸ k)⟩
  · have : Nonempty (Fin (Module.finrank ℂ E)) := ⟨⟨0, hdimpos⟩⟩
    let b := basisOfOrthonormalOfCardEqFinrank hv_ortho (by simp)
    refine ⟨b.toOrthonormalBasis (by simpa [b] using hv_ortho), μ, ν, hunit, fun k => ?_⟩
    have hb : (b.toOrthonormalBasis (by simpa [b] using hv_ortho)) k = v k := by
      simp [b, coe_basisOfOrthonormalOfCardEqFinrank]
    rw [hb, hR_decomp, hvH k, hvK k, smul_smul, ← add_smul]

/-- Choosing `(c, s)` with `c² + s² = 1`, `c² - s² = μ`, and `2 c s = ν` for any point `(μ, ν)`
on the unit circle. -/
private theorem exists_half_angle (μ ν : ℝ) (h : μ ^ 2 + ν ^ 2 = 1) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ c ^ 2 - s ^ 2 = μ ∧ 2 * c * s = ν := by
  by_cases hm : μ = -1
  · refine ⟨0, 1, by norm_num, by rw [hm]; norm_num, ?_⟩
    have hν : ν = 0 := by nlinarith
    simp [hν]
  · have hm_le : -1 ≤ μ := by nlinarith [sq_nonneg (μ + 1), sq_nonneg ν]
    have hpos : 0 < (1 + μ) / 2 := by
      have : -1 < μ := lt_of_le_of_ne hm_le (Ne.symm hm)
      linarith
    let c := Real.sqrt ((1 + μ) / 2)
    have hc_pos : 0 < c := Real.sqrt_pos.mpr hpos
    have hc2 : c ^ 2 = (1 + μ) / 2 := Real.sq_sqrt hpos.le
    let s := ν / (2 * c)
    have hs2 : s ^ 2 = (1 - μ) / 2 := by
      have h1 : ν ^ 2 = (1 - μ) * (1 + μ) := by linarith
      have hden : (2 * c) ^ 2 = 2 * (1 + μ) := by rw [mul_pow, hc2]; ring
      rw [div_pow, h1, hden]
      have hne : (1 + μ : ℝ) ≠ 0 := by linarith
      field_simp [hne]
    refine ⟨c, s, by linarith, by linarith, ?_⟩
    have hcne : c ≠ 0 := hc_pos.ne'
    calc
      2 * c * (ν / (2 * c)) = (2 * c) * (ν / (2 * c)) := by ring
      _ = ν := mul_div_cancel₀ ν (mul_ne_zero two_ne_zero hcne)

/-- 1-qubit preparation mapping `|false⟩ ↦ (|false⟩ + i |true⟩) / √2` and
`|true⟩ ↦ (|false⟩ - i |true⟩) / √2`. -/
private noncomputable def prepYBool :
    EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool where
  toFun ψ := WithLp.toLp 2 fun c =>
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (if c then Complex.I * (ψ.ofLp false - ψ.ofLp true)
      else ψ.ofLp false + ψ.ofLp true)
  invFun ψ := WithLp.toLp 2 fun c =>
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (if c then ψ.ofLp false + Complex.I * ψ.ofLp true
      else ψ.ofLp false - Complex.I * ψ.ofLp true)
  map_add' ψ₁ ψ₂ := by
    ext c
    cases c <;> simp only [PiLp.toLp_apply, WithLp.ofLp_add, Pi.add_apply, ite_true,
      Bool.false_eq_true, ite_false] <;> ring
  map_smul' r ψ := by
    ext c
    cases c <;> simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
      ite_true, Bool.false_eq_true, ite_false] <;> ring
  left_inv ψ := by
    have h2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2 = 1 / 2 := by
      rw [sq, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt zero_le_two]
      push_cast; ring
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    ext c
    cases c <;> simp only [PiLp.toLp_apply, ite_true, Bool.false_eq_true, ite_false] <;>
      (ring_nf; simp only [h2, hI]; ring)
  right_inv ψ := by
    have h2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2 = 1 / 2 := by
      rw [sq, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt zero_le_two]
      push_cast; ring
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    ext c
    cases c <;> simp only [PiLp.toLp_apply, ite_true, Bool.false_eq_true, ite_false] <;>
      (ring_nf; simp only [h2, hI]; ring)
  norm_map' ψ := by
    have hsq : ‖(WithLp.toLp 2 fun c : Bool => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
        (if c then Complex.I * (ψ.ofLp false - ψ.ofLp true) else ψ.ofLp false + ψ.ofLp true) :
        EuclideanSpace ℂ Bool)‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_bool, Fintype.sum_bool]
      simp only [PiLp.toLp_apply, ite_true, Bool.false_eq_true, ite_false, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, Real.sq_sqrt zero_le_two,
        Complex.norm_I, one_pow, one_mul, Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Real 2D rotation on `ℂ^Bool`: `[[c, -s], [s, c]]`. -/
private noncomputable def rotBool (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool where
  toFun ψ := WithLp.toLp 2 fun b => if b then (s : ℂ) * ψ.ofLp false + (c : ℂ) * ψ.ofLp true
    else (c : ℂ) * ψ.ofLp false - (s : ℂ) * ψ.ofLp true
  invFun ψ := WithLp.toLp 2 fun b => if b then -(s : ℂ) * ψ.ofLp false + (c : ℂ) * ψ.ofLp true
    else (c : ℂ) * ψ.ofLp false + (s : ℂ) * ψ.ofLp true
  map_add' ψ₁ ψ₂ := by
    ext b
    cases b <;> simp only [PiLp.toLp_apply, WithLp.ofLp_add, Pi.add_apply, ite_true,
      Bool.false_eq_true, ite_false] <;> ring
  map_smul' r ψ := by
    ext b
    cases b <;> simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
      ite_true, Bool.false_eq_true, ite_false] <;> ring
  left_inv ψ := by
    have hcsC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
    ext b
    cases b <;> simp only [PiLp.toLp_apply, ite_true, Bool.false_eq_true, ite_false]
    · linear_combination (ψ.ofLp false) * hcsC
    · linear_combination (ψ.ofLp true) * hcsC
  right_inv ψ := by
    have hcsC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
    ext b
    cases b <;> simp only [PiLp.toLp_apply, ite_true, Bool.false_eq_true, ite_false]
    · linear_combination (ψ.ofLp false) * hcsC
    · linear_combination (ψ.ofLp true) * hcsC
  norm_map' ψ := by
    have hsq : ‖(WithLp.toLp 2 fun b : Bool =>
        if b then (s : ℂ) * ψ.ofLp false + (c : ℂ) * ψ.ofLp true
        else (c : ℂ) * ψ.ofLp false - (s : ℂ) * ψ.ofLp true :
        EuclideanSpace ℂ Bool)‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_bool, Fintype.sum_bool]
      simp only [PiLp.toLp_apply, ite_true, Bool.false_eq_true, ite_false, Complex.sq_norm,
        Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        add_zero]
      linear_combination
        ((ψ.ofLp false).re ^ 2 + (ψ.ofLp false).im ^ 2 +
          (ψ.ofLp true).re ^ 2 + (ψ.ofLp true).im ^ 2) * hcs
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Controlled `Z` on a single `Bool` qubit. -/
private noncomputable def ctrlZBool (flag : Bool) :
    EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool where
  toFun ψ := WithLp.toLp 2 fun b => (if flag ∧ b then (-1 : ℂ) else 1) * ψ.ofLp b
  invFun ψ := WithLp.toLp 2 fun b => (if flag ∧ b then (-1 : ℂ) else 1) * ψ.ofLp b
  map_add' ψ₁ ψ₂ := by
    ext b; simp only [PiLp.toLp_apply, WithLp.ofLp_add, Pi.add_apply]; ring
  map_smul' r ψ := by
    ext b; simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  left_inv ψ := by ext b; cases flag <;> cases b <;> simp
  right_inv ψ := by ext b; cases flag <;> cases b <;> simp
  norm_map' ψ := by
    have hsq : ‖(WithLp.toLp 2 fun b => (if flag ∧ b then (-1 : ℂ) else 1) * ψ.ofLp b :
        EuclideanSpace ℂ Bool)‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      refine sum_congr rfl fun b _ => ?_
      cases flag <;> cases b <;> simp
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem prepYBool_symm_apply (ψ : EuclideanSpace ℂ Bool) (c : Bool) :
    (prepYBool.symm ψ).ofLp c = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
      (if c then ψ.ofLp false + Complex.I * ψ.ofLp true
      else ψ.ofLp false - Complex.I * ψ.ofLp true) :=
  rfl

private theorem prepYBool_apply (ψ : EuclideanSpace ℂ Bool) (c : Bool) :
    (prepYBool ψ).ofLp c = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
      (if c then Complex.I * (ψ.ofLp false - ψ.ofLp true)
      else ψ.ofLp false + ψ.ofLp true) :=
  rfl

private theorem rotBool_apply (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (ψ : EuclideanSpace ℂ Bool) (b : Bool) :
    (rotBool c s hcs ψ).ofLp b =
      if b then (s : ℂ) * ψ.ofLp false + (c : ℂ) * ψ.ofLp true
      else (c : ℂ) * ψ.ofLp false - (s : ℂ) * ψ.ofLp true :=
  rfl

private theorem ctrlZBool_apply (flag : Bool) (ψ : EuclideanSpace ℂ Bool) (b : Bool) :
    (ctrlZBool flag ψ).ofLp b = (if flag ∧ b then (-1 : ℂ) else 1) * ψ.ofLp b :=
  rfl

private theorem prepY_rotBool_gadget (c s μ ν : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (hmu : c ^ 2 - s ^ 2 = μ) (hnu : 2 * c * s = ν) (flag : Bool) (z : ℂ) :
    (rotBool c (-s) (by nlinarith)).trans prepYBool.symm
        (ctrlZBool flag (rotBool c s hcs (ctrlZBool flag (prepYBool (WithLp.toLp 2 fun b =>
          if b then 0 else z))))) =
      WithLp.toLp 2 fun b => if b then 0 else (if flag then (μ : ℂ) + Complex.I * ν else 1) * z := by
  have hcs' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  have hmu' : (c : ℂ) ^ 2 - (s : ℂ) ^ 2 = μ := by exact_mod_cast hmu
  have hnu' : 2 * (c : ℂ) * s = ν := by exact_mod_cast hnu
  have h2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2 = 1 / 2 := by
    rw [sq, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt zero_le_two]
    push_cast; ring
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hc2 : (c : ℂ) ^ 2 = (1 + (μ : ℂ)) / 2 := by linear_combination (1 / 2 : ℂ) * hcs' +
    (1 / 2 : ℂ) * hmu'
  have hs2 : (s : ℂ) ^ 2 = (1 - (μ : ℂ)) / 2 := by linear_combination (1 / 2 : ℂ) * hcs' -
    (1 / 2 : ℂ) * hmu'
  have hcs2 : (c : ℂ) * s = (ν : ℂ) / 2 := by linear_combination (1 / 2 : ℂ) * hnu'
  ext b
  cases flag <;> cases c' : b <;>
    simp only [LinearIsometryEquiv.trans_apply, prepYBool_symm_apply, rotBool_apply,
      ctrlZBool_apply, prepYBool_apply, PiLp.toLp_apply, ite_true, Bool.false_eq_true, ite_false,
      Bool.false_and, Bool.true_and, Complex.ofReal_neg, and_self, and_false, and_true, false_and,
      true_and] <;>
    (ring_nf; simp only [h2, hI, hc2, hs2, hcs2]; ring)

private def boolSwapEquiv (B : Type*) : (Bool × B) ≃ (B × Bool) where
  toFun p := (p.2, p.1)
  invFun q := (q.2, q.1)
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def liftBoolD {d : ℕ}
    (Q : Fin d → (EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool)) :
    EuclideanSpace ℂ (Bool × Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × Fin d) :=
  (reindexProd (boolSwapEquiv (Fin d))).trans
    ((fiberIso Q).trans (reindexProd (boolSwapEquiv (Fin d))).symm)

@[simp] private theorem liftBoolD_apply {d : ℕ}
    (Q : Fin d → (EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool))
    (φ : EuclideanSpace ℂ (Bool × Fin d)) (c : Bool) (k : Fin d) :
    (liftBoolD Q φ).ofLp (c, k) = (Q k (WithLp.toLp 2 fun b => φ.ofLp (b, k))).ofLp c :=
  rfl

private noncomputable def liftBasis {B₁ B₂ : Type*} [Fintype B₁] [Fintype B₂]
    (U : EuclideanSpace ℂ B₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ B₂) :
    EuclideanSpace ℂ (Bool × B₁) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × B₂) :=
  fiberIso fun _ : Bool => U

private theorem liftBasis_ctrlZ {B₁ B₂ : Type*} [Fintype B₁] [Fintype B₂]
    (U : EuclideanSpace ℂ B₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ B₂) (flag : Bool)
    (φ : EuclideanSpace ℂ (Bool × B₁)) :
    liftBasis U (ctrlZ flag φ) = ctrlZ flag (liftBasis U φ) := by
  have hslice : ∀ c : Bool,
      sliceSecond (ctrlZ flag φ) c = (if flag ∧ c then (-1 : ℂ) else 1) • sliceSecond φ c := by
    intro c
    ext v
    cases flag <;> cases c <;> simp [ctrlZ, sliceSecond]
  ext ⟨c, k⟩
  cases flag <;> cases c <;> simp [liftBasis, ctrlZ, hslice, map_smul]

/-- **2-query simulation of an arbitrary two-valued oracle restriction**: any `T`-query
value-query algorithm restricted to `{a₀, a₁}` along `e : ι ≃ Fin N` can be simulated by `2 * T`
binary phase-oracle queries. -/
theorem exists_sim_value {N : ℕ} [DecidableEq ι] [DecidableEq V] [DecidableEq W]
    {α : Type*} (e : ι ≃ Fin N)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (a₀ a₁ : α)
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ₀ : ValueState ι V W) (T : ℕ) :
    ∃ (Vsim : ℕ → State N (V × W) →ₗᵢ[ℂ] State N (V × W)) (φ₀ : State N (V × W)),
      ‖φ₀‖ = ‖ψ₀‖ ∧
        ∀ (b : Fin N → Bool) (S : Finset (ι × V × W)),
          measureProb (run Vsim φ₀ b (2 * T)) (S.map (embedOutcome e)) =
            measureProb (runValue step U ψ₀ (fun i => if b (e i) then a₁ else a₀) T) S := by
  let R := (step a₀).symm.trans (step a₁)
  obtain ⟨bas, μ, ν, hunit, heig⟩ := exists_orthonormalBasis_eigenvectors R
  let d := Module.finrank ℂ (EuclideanSpace ℂ V)
  have hcs_ex : ∀ k : Fin d, ∃ p : ℝ × ℝ,
      p.1 ^ 2 + p.2 ^ 2 = 1 ∧ p.1 ^ 2 - p.2 ^ 2 = μ k ∧ 2 * p.1 * p.2 = ν k := by
    intro k
    obtain ⟨c, s, h1, h2, h3⟩ := exists_half_angle (μ k) (ν k) (hunit k)
    exact ⟨(c, s), h1, h2, h3⟩
  let c : Fin d → ℝ := fun k => (Classical.choose (hcs_ex k)).1
  let s : Fin d → ℝ := fun k => (Classical.choose (hcs_ex k)).2
  have hcs : ∀ k, (c k) ^ 2 + (s k) ^ 2 = 1 := fun k => (Classical.choose_spec (hcs_ex k)).1
  have hmu : ∀ k, (c k) ^ 2 - (s k) ^ 2 = μ k := fun k => (Classical.choose_spec (hcs_ex k)).2.1
  have hnu : ∀ k, 2 * c k * s k = ν k := fun k => (Classical.choose_spec (hcs_ex k)).2.2
  let Bchg : EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × Fin d) :=
    liftBasis bas.repr
  let Qpre : EuclideanSpace ℂ (Bool × Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × Fin d) :=
    liftBoolD fun _ => prepYBool
  let Qmid : EuclideanSpace ℂ (Bool × Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × Fin d) :=
    liftBoolD fun k => rotBool (c k) (s k) (hcs k)
  let Qpost : EuclideanSpace ℂ (Bool × Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × Fin d) :=
    liftBoolD fun k => (rotBool (c k) (-s k) (by nlinarith [hcs k])).trans prepYBool.symm
  let Gpre : EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × V) :=
    Bchg.trans (Qpre.trans Bchg.symm)
  let Gmid : EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × V) :=
    Bchg.trans (Qmid.trans Bchg.symm)
  let Gpost : EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × V) :=
    Bchg.trans (Qpost.trans Bchg.symm)
  have hgadget : ∀ flag (φ : EuclideanSpace ℂ V),
      Gpost (ctrlZ flag (Gmid (ctrlZ flag (Gpre (embedBoolFalse φ))))) =
        embedBoolFalse (if flag then R φ else φ) := by
    intro flag φ
    have hBpre : Bchg (Gpre (embedBoolFalse φ)) = Qpre (Bchg (embedBoolFalse φ)) := by
      simp [Gpre]
    have hBmid : Bchg (Gmid (ctrlZ flag (Gpre (embedBoolFalse φ)))) =
        Qmid (ctrlZ flag (Qpre (Bchg (embedBoolFalse φ)))) := by
      dsimp only [Gmid]
      rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply,
        liftBasis_ctrlZ, hBpre, Bchg.apply_symm_apply]
    have hBpost : Gpost (ctrlZ flag (Gmid (ctrlZ flag (Gpre (embedBoolFalse φ))))) =
        Bchg.symm (Qpost (ctrlZ flag (Qmid (ctrlZ flag (Qpre (Bchg (embedBoolFalse φ))))))) := by
      dsimp only [Gpost]
      rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply,
        liftBasis_ctrlZ, hBmid]
    rw [hBpost]
    have hBinit : Bchg (embedBoolFalse φ) =
        WithLp.toLp 2 fun p : Bool × Fin d => if p.1 then 0 else (bas.repr φ).ofLp p.2 := by
      ext ⟨b, k⟩
      cases b
      · simp [Bchg, liftBasis, embedBoolFalse, sliceSecond]
      · have hz : (WithLp.toLp 2 fun _ : V => (0 : ℂ)) = (0 : EuclideanSpace ℂ V) := rfl
        simp [Bchg, liftBasis, embedBoolFalse, sliceSecond, hz]
    have hQ : Qpost (ctrlZ flag (Qmid (ctrlZ flag (Qpre (Bchg (embedBoolFalse φ)))))) =
        WithLp.toLp 2 fun p : Bool × Fin d =>
          if p.1 then 0 else (if flag then (μ p.2 : ℂ) + Complex.I * ν p.2 else 1) *
            (bas.repr φ).ofLp p.2 := by
      rw [hBinit]
      ext ⟨b, k⟩
      have hmid_k : ∀ x : EuclideanSpace ℂ (Bool × Fin d),
          (WithLp.toLp 2 fun b' => (ctrlZ flag x).ofLp (b', k)) =
            ctrlZBool flag (WithLp.toLp 2 fun b' => x.ofLp (b', k)) := fun x => by
        ext b'
        cases flag <;> cases b' <;> simp [ctrlZ, ctrlZBool]
      simp only [Qpost, Qmid, Qpre, liftBoolD_apply, hmid_k]
      exact congrArg (fun u => u.ofLp b)
        (prepY_rotBool_gadget (c k) (s k) (μ k) (ν k) (hcs k) (hmu k) (hnu k) flag
          ((bas.repr φ).ofLp k))
    rw [hQ]
    have hRbas : bas.repr (if flag then R φ else φ) =
        WithLp.toLp 2 fun k =>
          (if flag then (μ k : ℂ) + Complex.I * ν k else 1) * (bas.repr φ).ofLp k := by
      cases flag
      · simp
      · simp only [ite_true]
        ext k
        have hrepr : φ = ∑ j : Fin d, (bas.repr φ).ofLp j • bas j := (bas.sum_repr φ).symm
        calc
          (bas.repr (R φ)).ofLp k
              = (bas.repr (R (∑ j : Fin d, (bas.repr φ).ofLp j • bas j))).ofLp k := by
                conv_lhs => rw [hrepr]
          _ = (bas.repr (∑ j : Fin d, (bas.repr φ).ofLp j •
                (((μ j : ℂ) + Complex.I * ν j) • bas j))).ofLp k := by
                simp only [map_sum, map_smul, heig]
          _ = ∑ j : Fin d, (bas.repr φ).ofLp j * ((μ j : ℂ) + Complex.I * ν j) *
                (if k = j then 1 else 0) := by
                simp only [map_sum, map_smul, bas.repr_self]
                rw [WithLp.ofLp_sum, Finset.sum_apply]
                refine sum_congr rfl fun j _ => ?_
                simp only [PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single]
                simp only [PiLp.single_apply]
                ring
          _ = ((μ k : ℂ) + Complex.I * ν k) * (bas.repr φ).ofLp k := by
                simp [mul_comm]
    have hc0 : (WithLp.toLp 2 fun p : Bool × Fin d =>
        if p.1 then (0 : ℂ) else (if flag then (μ p.2 : ℂ) + Complex.I * ν p.2 else 1) *
          (bas.repr φ).ofLp p.2) =
        Bchg (embedBoolFalse (if flag then R φ else φ)) := by
      ext ⟨b', k'⟩
      cases b'
      · have hk := congrArg (fun u => u.ofLp k') hRbas
        simpa [Bchg, liftBasis, embedBoolFalse, sliceSecond] using hk.symm
      · have hz : (WithLp.toLp 2 fun _ : V => (0 : ℂ)) = (0 : EuclideanSpace ℂ V) := rfl
        simp [Bchg, liftBasis, embedBoolFalse, sliceSecond, hz]
    rw [hc0, Bchg.symm_apply_apply]
  let stepA0 : ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W :=
    (valueOracle step fun _ => a₀).toLinearIsometry
  let A0 : State N (V × W) →ₗᵢ[ℂ] State N (V × W) := liftValueIso e stepA0
  let pre : State N (V × W) →ₗᵢ[ℂ] State N (V × W) := (liftBoolV Gpre).toLinearIsometry.comp A0
  let Vsim : ℕ → State N (V × W) →ₗᵢ[ℂ] State N (V × W) := fun q =>
    if q = 0 then
      if 0 < T then pre.comp (liftValueIso e (U 0)) else liftValueIso e (U 0)
    else if q % 2 = 1 then
      (liftBoolV Gmid).toLinearIsometry
    else
      let r := q / 2 - 1
      if r + 1 < T then
        pre.comp ((liftValueIso e (U (r + 1))).comp (liftBoolV Gpost).toLinearIsometry)
      else if r + 1 = T then
        (liftValueIso e (U T)).comp (liftBoolV Gpost).toLinearIsometry
      else LinearIsometry.id
  refine ⟨Vsim, embedState e ψ₀, norm_embedState e ψ₀, fun b S => ?_⟩
  let x : ι → α := fun i => if b (e i) then a₁ else a₀
  have hstep : ∀ y : ValueState ι V W,
      liftBoolV Gpost (phaseOracle b (liftBoolV Gmid (phaseOracle b
          (liftBoolV Gpre (A0 (embedState e y)))))) =
        embedState e (valueOracle step x y) := by
    intro y
    refine eq_embedState_of_bvSlice e _ _ fun j w => ?_
    simp only [bvSlice_liftBoolV, bvSlice_phaseOracle]
    have hA0 : bvSlice (A0 (embedState e y)) j w =
        embedBoolFalse (step a₀ (valSlice y (e.symm j) w)) := by
      rw [show A0 (embedState e y) = embedState e (stepA0 y) from liftValueIso_embedState e stepA0 y,
        bvSlice_embedState]
      congr 1
      ext v
      exact valueOracle_apply step (fun _ => a₀) y (e.symm j) v w
    rw [hA0, hgadget]
    congr 1
    ext v
    have hv := valueOracle_apply step x y (e.symm j) v w
    simp only [x, Equiv.apply_symm_apply] at hv
    cases hbj : b j <;> simp [hbj, hv, R]
  have hrun : ∀ t ≤ T,
      run Vsim (embedState e ψ₀) b (2 * t) =
        if t < T then liftBoolV Gpre (A0 (embedState e (runValue step U ψ₀ x t)))
        else embedState e (runValue step U ψ₀ x T) := by
    intro t ht
    induction t with
    | zero =>
      simp only [run, Vsim, ite_true]
      by_cases hT : 0 < T
      · simp [hT, pre, liftValueIso_embedState, runValue]
      · have hT0 : T = 0 := by omega
        subst hT0
        simp [liftValueIso_embedState, runValue]
    | succ t ih =>
      have ht' : t < T := by omega
      have hprev := ih ht'.le
      rw [ite_eq_left.mpr fun h => absurd ht' h] at hprev
      have hVodd : Vsim (2 * t + 1) = (liftBoolV Gmid).toLinearIsometry := by
        have hmod : (2 * t + 1) % 2 = 1 := by omega
        simp [Vsim, hmod]
      have hVeven : Vsim (2 * t + 2) =
          if t + 1 < T then
            pre.comp ((liftValueIso e (U (t + 1))).comp (liftBoolV Gpost).toLinearIsometry)
          else (liftValueIso e (U T)).comp (liftBoolV Gpost).toLinearIsometry := by
        have hne : 2 * t + 2 ≠ 0 := by omega
        have hmod : (2 * t + 2) % 2 ≠ 1 := by omega
        have hr : (2 * t + 2) / 2 - 1 = t := by omega
        simp only [Vsim, hne, ite_false, hmod, hr]
        by_cases hlt : t + 1 < T
        · simp [hlt]
        · have heq : t + 1 = T := by omega
          simp [heq]
      rw [show 2 * (t + 1) = (2 * t + 1) + 1 by ring, run, run, hVodd, hVeven, hprev]
      by_cases hlt : t + 1 < T
      · simp [hlt, pre, hstep, liftValueIso_embedState, runValue]
      · have heq : t + 1 = T := by omega
        subst heq
        simp [hstep, liftValueIso_embedState, runValue]
  have hT := hrun T le_rfl
  rw [ite_eq_right.mpr fun h => absurd h (lt_irrefl T)] at hT
  rw [hT, measureProb_embedState]

end TwoValueSim

end Cslib.Quantum
