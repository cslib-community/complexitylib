/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.Search
public import CslibFrontier.Foundations.Quantum.Measurement.Readout
import CslibFrontier.Foundations.LinearAlgebra.UnitarySpectrum

/-!
# Quantum value-query algorithms

This module extends the phase-oracle quantum query model (`Cslib.Quantum.run`) to the quantum
value-query model (`Cslib.Quantum.ValueState`, `Cslib.Quantum.valueOracle`,
`Cslib.Quantum.runValue`) over an arbitrary finite query index type `ι`, finite value/answer
register `V`, and finite workspace `W`, where each oracle call applies an input-dependent unitary
`step (x i)` to the `V` register controlled by the query index `i`. Permutation oracles
(`Cslib.Quantum.permStep`), group-addition oracles (`Cslib.Quantum.addStep`), and XOR oracles
(`BitString` as an additive group) are special cases. Multi-outcome computational-basis readouts
(`Cslib.Quantum.measureOut`) are provided by
`CslibFrontier/Foundations/Quantum/Measurement/Readout.lean`.

For lower bounds, restricting a value-query algorithm to inputs taking only two values `a₀` and
`a₁` can be simulated in the Boolean phase-oracle model (`Cslib.Quantum.run`) on `N = |ι|` bits:

* When the relative step `(step a₀).symm.trans (step a₁)` is an involution (such as an XOR
  oracle), one binary phase query simulates each value query
  (`Cslib.Quantum.exists_sim_involution`).
* For an arbitrary unitary step `step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)`,
  simultaneously diagonalizing the Hermitian and skew-Hermitian parts of the relative unitary
  (`UnitarySpectrum` -> `LinearIsometryEquiv.exists_orthonormalBasis_eigenvectors`) simulates
  each value query with two binary phase queries (`Cslib.Quantum.exists_sim_value`).
* Index-returning `T`-query algorithms that read one value can be turned into `(T + 1)`-query
  value-returning algorithms (`Cslib.Quantum.exists_sim_index_to_value`,
  `Cslib.Quantum.exists_sim_index_to_value_perm`).

## Main definitions

* `Cslib.Quantum.ValueState`: quantum states over `ι × V × W`.
* `Cslib.Quantum.valueOracle`, `Cslib.Quantum.permStep`, `Cslib.Quantum.addStep`: value-query
  oracles.
* `Cslib.Quantum.runValue`: final state of a `T`-query value-query algorithm.
* `Cslib.Quantum.embedOutcome`: embedding value-query outcomes into `Fin N × Bool × V × W`.

## Main results

* `Cslib.Quantum.norm_runValue`: value-query algorithms preserve norms.
* `Cslib.Quantum.exists_sim_involution`: simulating a two-valued restriction with an involutive
  difference by `T` binary phase queries.
* `Cslib.Quantum.exists_sim_value`: simulating an arbitrary two-valued restriction by `2 * T`
  binary phase queries.
* `Cslib.Quantum.exists_sim_index_to_value`, `Cslib.Quantum.exists_sim_index_to_value_perm`:
  simulating a `T`-query index-returning value-query algorithm with `T + 1` value queries.
-/

public section

namespace Cslib.Quantum

open Finset

/-! ### Fibered unitary helpers -/

section FiberHelpers

private def sliceSecond {A B : Type*} (ψ : EuclideanSpace ℂ (A × B)) (a : A) :
    EuclideanSpace ℂ B :=
  WithLp.toLp 2 fun b => ψ.ofLp (a, b)

@[simp] private theorem sliceSecond_apply {A B : Type*} (ψ : EuclideanSpace ℂ (A × B))
    (a : A) (b : B) : (sliceSecond ψ a).ofLp b = ψ.ofLp (a, b) := rfl

private noncomputable def reindexProd {P Q : Type*} [Fintype P] [Fintype Q] (e : P ≃ Q) :
    EuclideanSpace ℂ P ≃ₗᵢ[ℂ] EuclideanSpace ℂ Q :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp] private theorem reindexProd_apply {P Q : Type*} [Fintype P] [Fintype Q] (e : P ≃ Q)
    (ψ : EuclideanSpace ℂ P) (q : Q) :
    (reindexProd e ψ).ofLp q = ψ.ofLp (e.symm q) :=
  rfl

private noncomputable def prodCurryIso (A B : Type*) [Fintype A] [Fintype B] :
    EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : A => EuclideanSpace ℂ B) :=
  (reindexProd (Equiv.sigmaEquivProd A B).symm).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 fun _ : A => fun _ : B => ℂ)

/-- Applying unitaries `F a : ℂ^B₁ ≃ₗᵢ[ℂ] ℂ^B₂` fiberwise over `a : A` using Mathlib's
`LinearIsometryEquiv.piLpCongrLeft`, `piLpCurry`, and `piLpCongrRight`. -/
private noncomputable def fiberIso {A B₁ B₂ : Type*} [Fintype A] [Fintype B₁] [Fintype B₂]
    (F : A → (EuclideanSpace ℂ B₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ B₂)) :
    EuclideanSpace ℂ (A × B₁) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B₂) :=
  (prodCurryIso A B₁).trans
    ((LinearIsometryEquiv.piLpCongrRight 2 F).trans (prodCurryIso A B₂).symm)

@[simp] private theorem fiberIso_apply {A B₁ B₂ : Type*} [Fintype A] [Fintype B₁] [Fintype B₂]
    (F : A → (EuclideanSpace ℂ B₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ B₂))
    (ψ : EuclideanSpace ℂ (A × B₁)) (a : A) (b : B₂) :
    (fiberIso F ψ).ofLp (a, b) = (F a (sliceSecond ψ a)).ofLp b :=
  rfl

/-- Conjugate a fiberwise unitary on `A × B` along a coordinate equivalence `e : P ≃ A × B`. -/
private noncomputable def conjFiberIso {P A B : Type*} [Fintype P] [Fintype A] [Fintype B]
    (e : P ≃ A × B) (F : A → (EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B)) :
    EuclideanSpace ℂ P ≃ₗᵢ[ℂ] EuclideanSpace ℂ P :=
  (reindexProd e).trans ((fiberIso F).trans (reindexProd e).symm)

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

private def valueFiberEquiv {ι V W : Type*} : (ι × V × W) ≃ ((ι × W) × V) where
  toFun | (i, v, w) => ((i, w), v)
  invFun | ((i, w), v) => (i, v, w)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Value oracle**: given per-symbol unitaries `step : α → (ℂ^V ≃ₗᵢ[ℂ] ℂ^V)` and an input
`x : ι → α`, applies `step (x i)` to the value register controlled by the query index `i`. -/
noncomputable def valueOracle
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)) (x : ι → α) :
    ValueState ι V W ≃ₗᵢ[ℂ] ValueState ι V W :=
  conjFiberIso valueFiberEquiv fun p : ι × W => step (x p.1)

/-- Coordinate evaluation of `valueOracle step x ψ` at `(i, v, w)`. -/
@[simp] theorem valueOracle_apply (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (x : ι → α) (ψ : ValueState ι V W) (i : ι) (v : V) (w : W) :
    (valueOracle step x ψ).ofLp (i, v, w) =
      (step (x i) (WithLp.toLp 2 fun v' => ψ.ofLp (i, v', w))).ofLp v := by
  rfl

/-- Unitary step arising from a family of permutations `π : α → Equiv.Perm V`, acting as
`|v⟩ ↦ |π a v⟩`. -/
@[expose] noncomputable def permStep (π : α → Equiv.Perm V) (a : α) :
    EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (π a)

/-- Coordinate evaluation of `permStep π a φ`. -/
@[simp] theorem permStep_apply (π : α → Equiv.Perm V) (a : α) (φ : EuclideanSpace ℂ V) (v : V) :
    (permStep π a φ).ofLp v = φ.ofLp ((π a).symm v) :=
  rfl

/-- Unitary step for an additive group value register `V`: `|v⟩ ↦ |v + a⟩`. This covers modular
addition on `ZMod M` as well as bitwise XOR on `BitString m`. -/
@[expose] noncomputable def addStep [AddGroup V] (a : V) :
    EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V :=
  permStep (fun b => Equiv.addRight b) a

/-- Coordinate evaluation of `addStep a φ`. -/
@[simp] theorem addStep_apply [AddGroup V] (a : V) (φ : EuclideanSpace ℂ V) (v : V) :
    (addStep a φ).ofLp v = φ.ofLp (v - a) := by
  simp [addStep, sub_eq_add_neg]

/-- Coordinate evaluation of `(addStep a).symm φ`. -/
@[simp] theorem addStep_symm_apply [AddGroup V] (a : V) (φ : EuclideanSpace ℂ V) (v : V) :
    ((addStep a).symm φ).ofLp v = φ.ofLp (v + a) := by
  simp [addStep, permStep]

/-- Action of `addStep a` on computational-basis state `ket v`. -/
theorem addStep_ket [DecidableEq V] [AddGroup V] (a v : V) :
    addStep a (ket v) = ket (v + a) := by
  ext u
  simp only [addStep_apply, ket_apply, sub_eq_iff_eq_add]

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

/-- Application formula for `embedOutcome`. -/
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
  toFun | (j, c, v, w) => ((j, w), (c, v))
  invFun | ((j, w), (c, v)) => (j, c, v, w)
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def liftBoolV {N : ℕ}
    (G : EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × V)) :
    State N (V × W) ≃ₗᵢ[ℂ] State N (V × W) :=
  conjFiberIso (bvFiberEquiv (N := N) (V := V) (W := W)) fun _ : Fin N × W => G

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
    ext ⟨c, v⟩; simp only [WithLp.ofLp_add, Pi.add_apply]; ring
  map_smul' r φ := by
    ext ⟨c, v⟩; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
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
    simp only [F, s0, s1, Bool.false_eq_true, ite_false, PiLp.smul_apply, PiLp.sub_apply,
      PiLp.add_apply, smul_eq_mul]
    ring
  have hs1 : ∀ φ, s1 (F φ) = (1 / 2 : ℂ) • (s0 φ - R (s0 φ) + s1 φ + R (s1 φ)) := by
    intro φ
    ext v
    simp only [F, s0, s1, ite_true, PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, smul_eq_mul]
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
      simp only [F, Bool.false_eq_true, ite_false, ite_true, hF0, hF1, hRF0v, hRF1v]
    · simp only [s0]; ring
    · simp only [s1]; ring
  { toFun := F
    invFun := F
    map_add' := fun ψ₁ ψ₂ => by
      ext ⟨c, v⟩
      have h0 : s0 (ψ₁ + ψ₂) = s0 ψ₁ + s0 ψ₂ := rfl
      have h1 : s1 (ψ₁ + ψ₂) = s1 ψ₁ + s1 ψ₂ := rfl
      simp only [F, WithLp.ofLp_add, Pi.add_apply, h0, h1, map_add]
      ring
    map_smul' := fun r ψ => by
      ext ⟨c, v⟩
      have h0 : s0 (r • ψ) = r • s0 ψ := rfl
      have h1 : s1 (r • ψ) = r • s1 ψ := rfl
      simp only [F, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, h0, h1, map_smul]
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
        rw [norm_smul, norm_smul, mul_pow, mul_pow, ← mul_add,
          parallelogram_law_with_norm ℂ x (R x), R.norm_map]
        norm_num
        ring
      have hF0 : s0 (F ψ) = p0 + m1 := by
        ext v
        simp only [F, s0, s1, p0, m1, u0, u1, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
          smul_eq_mul, Bool.false_eq_true, ite_false]
        ring
      have hF1 : s1 (F ψ) = m0 + p1 := by
        ext v
        simp only [F, s0, s1, m0, p1, u0, u1, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
          smul_eq_mul, ite_true]
        ring
      have h0n : ‖p0 + m1‖ ^ 2 = ‖p0‖ ^ 2 + ‖m1‖ ^ 2 := by
        simpa only [sq] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p0 m1 (hortho u0 u1)
      have h1n : ‖m0 + p1‖ ^ 2 = ‖m0‖ ^ 2 + ‖p1‖ ^ 2 := by
        rw [add_comm m0 p1, add_comm (‖m0‖ ^ 2) (‖p1‖ ^ 2)]
        simpa only [sq] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p1 m0 (hortho u1 u0)
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
    simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul] at h0v h1v hR0v hR1v
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

private theorem bvSlice_liftValueIso_valueOracle {N : ℕ} {α : Type*} (e : ι ≃ Fin N)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)) (a₀ : α)
    (y : ValueState ι V W) (j : Fin N) (w : W) :
    bvSlice (liftValueIso e (valueOracle step fun _ => a₀).toLinearIsometry (embedState e y)) j
        w =
      embedBoolFalse (step a₀ (valSlice y (e.symm j) w)) := by
  rw [liftValueIso_embedState, bvSlice_embedState]
  rfl

private theorem step_rel_ite_apply {N : ℕ} {α : Type*} (e : ι ≃ Fin N)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (a₀ a₁ : α) (b : Fin N → Bool) (y : ValueState ι V W) (j : Fin N) (v : V) (w : W) :
    (if b j then ((step a₀).symm.trans (step a₁)) ((step a₀) (valSlice y (e.symm j) w))
      else (step a₀) (valSlice y (e.symm j) w)).ofLp v =
      (valueOracle step (fun i => if b (e i) then a₁ else a₀) y).ofLp (e.symm j, v, w) := by
  have hv := valueOracle_apply step (fun i => if b (e i) then a₁ else a₀) y (e.symm j) v w
  simp only [Equiv.apply_symm_apply] at hv
  have hval : (WithLp.toLp 2 fun v' => y.ofLp (e.symm j, v', w)) = valSlice y (e.symm j) w := rfl
  rw [hval] at hv
  cases hbj : b j
  · simp only [hbj, Bool.false_eq_true, ite_false] at hv ⊢
    exact hv.symm
  · simp only [hbj, ite_true, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.symm_apply_apply] at hv ⊢
    exact hv.symm

private theorem measureProb_sim_stride {N : ℕ}
    {α : Type*} (e : ι ≃ Fin N)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ₀ : ValueState ι V W) (x : ι → α) (T stride : ℕ)
    (pre : State N (V × W) →ₗᵢ[ℂ] State N (V × W))
    (Vsim : ℕ → State N (V × W) →ₗᵢ[ℂ] State N (V × W))
    (b : Fin N → Bool) (S : Finset (ι × V × W))
    (hzero : run Vsim (embedState e ψ₀) b 0 =
      if 0 < T then pre (embedState e (runValue step U ψ₀ x 0))
      else embedState e (runValue step U ψ₀ x T))
    (hsucc : ∀ t, t < T →
      run Vsim (embedState e ψ₀) b (stride * t) =
        pre (embedState e (runValue step U ψ₀ x t)) →
      run Vsim (embedState e ψ₀) b (stride * (t + 1)) =
        if t + 1 < T then pre (embedState e (runValue step U ψ₀ x (t + 1)))
        else embedState e (runValue step U ψ₀ x T)) :
    measureProb (run Vsim (embedState e ψ₀) b (stride * T)) (S.map (embedOutcome e)) =
      measureProb (runValue step U ψ₀ x T) S := by
  classical
  have hrun : ∀ t ≤ T,
      run Vsim (embedState e ψ₀) b (stride * t) =
        if t < T then pre (embedState e (runValue step U ψ₀ x t))
        else embedState e (runValue step U ψ₀ x T) := by
    intro t ht
    induction t with
    | zero => simpa using hzero
    | succ t ih =>
      have ht' : t < T := by omega
      have hprev := ih ht'.le
      simp only [ht', ite_true] at hprev
      exact hsucc t ht' hprev
  have hT := hrun T le_rfl
  simp only [lt_irrefl, ite_false] at hT
  rw [hT, measureProb_embedState]

/-- **1-query simulation of an involutive two-valued oracle restriction**: if
`(step a₀).symm.trans (step a₁)` is an involution, any `T`-query value-query algorithm restricted
to `{a₀, a₁}` along `e : ι ≃ Fin N` can be simulated by `T` binary phase-oracle queries. -/
theorem exists_sim_involution {N : ℕ}
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
  classical
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
    rw [bvSlice_liftBoolV, bvSlice_phaseOracle, bvSlice_liftBoolV,
      bvSlice_liftValueIso_valueOracle, invBoolV_ctrlZ_invBoolV]
    congr 1
    ext v
    exact step_rel_ite_apply e step a₀ a₁ b y j v w
  conv_lhs => rw [← one_mul T]
  refine measureProb_sim_stride e step U ψ₀ x T 1 pre Vsim b S ?_ ?_
  · simp only [run, Vsim, ite_true]
    by_cases hT : 0 < T
    · simp [hT, pre, liftValueIso_embedState, runValue]
    · have hT0 : T = 0 := by omega
      subst hT0
      simp [liftValueIso_embedState, runValue]
  · intro t ht' hprev
    have hV : Vsim (t + 1) =
        if t + 1 < T then
          pre.comp ((liftValueIso e (U (t + 1))).comp (liftBoolV G).toLinearIsometry)
        else (liftValueIso e (U T)).comp (liftBoolV G).toLinearIsometry := by
      simp only [Vsim, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
      by_cases hlt : t + 1 < T
      · simp [hlt]
      · have heq : t + 1 = T := by omega
        simp [heq]
    rw [one_mul] at hprev
    rw [show 1 * (t + 1) = t + 1 by omega, run, hprev, hV]
    by_cases hlt : t + 1 < T
    · simp only [hlt, ite_true, pre, LinearIsometry.coe_comp, Function.comp_apply,
        LinearIsometryEquiv.coe_toLinearIsometry]
      rw [hstep, liftValueIso_embedState, ← runValue]
    · have heq : t + 1 = T := by omega
      subst heq
      simp only [lt_irrefl, ite_false, pre, LinearIsometry.coe_comp, Function.comp_apply,
        LinearIsometryEquiv.coe_toLinearIsometry]
      rw [hstep, liftValueIso_embedState, ← runValue]

/-! #### 2-query simulation for arbitrary unitary relative step -/

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
    cases c <;> simp only [WithLp.ofLp_add, Pi.add_apply, ite_true,
      Bool.false_eq_true, ite_false] <;> ring
  map_smul' r ψ := by
    ext c
    cases c <;> simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
      ite_true, Bool.false_eq_true, ite_false] <;> ring
  left_inv ψ := by
    have h2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2 = 1 / 2 := by
      rw [sq, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt zero_le_two]
      push_cast; ring
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    ext c
    cases c <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;>
      (ring_nf; simp only [h2, hI]; ring)
  right_inv ψ := by
    have h2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2 = 1 / 2 := by
      rw [sq, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt zero_le_two]
      push_cast; ring
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    ext c
    cases c <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;>
      (ring_nf; simp only [h2, hI]; ring)
  norm_map' ψ := by
    have hsq : ‖(WithLp.toLp 2 fun c : Bool => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
        (if c then Complex.I * (ψ.ofLp false - ψ.ofLp true) else ψ.ofLp false + ψ.ofLp true) :
        EuclideanSpace ℂ Bool)‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_bool, Fintype.sum_bool]
      simp only [ite_true, Bool.false_eq_true, ite_false, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, Real.sq_sqrt zero_le_two, Complex.norm_I,
        one_mul, Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub]
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
    cases b <;> simp only [WithLp.ofLp_add, Pi.add_apply, ite_true,
      Bool.false_eq_true, ite_false] <;> ring
  map_smul' r ψ := by
    ext b
    cases b <;> simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
      ite_true, Bool.false_eq_true, ite_false] <;> ring
  left_inv ψ := by
    have hcsC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
    ext b
    cases b <;> simp only [ite_true, Bool.false_eq_true, ite_false]
    · linear_combination (ψ.ofLp false) * hcsC
    · linear_combination (ψ.ofLp true) * hcsC
  right_inv ψ := by
    have hcsC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
    ext b
    cases b <;> simp only [ite_true, Bool.false_eq_true, ite_false]
    · linear_combination (ψ.ofLp false) * hcsC
    · linear_combination (ψ.ofLp true) * hcsC
  norm_map' ψ := by
    have hsq : ‖(WithLp.toLp 2 fun b : Bool =>
        if b then (s : ℂ) * ψ.ofLp false + (c : ℂ) * ψ.ofLp true
        else (c : ℂ) * ψ.ofLp false - (s : ℂ) * ψ.ofLp true :
        EuclideanSpace ℂ Bool)‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_bool, Fintype.sum_bool]
      simp only [ite_true, Bool.false_eq_true, ite_false, Complex.sq_norm, Complex.normSq_apply,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
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
    ext b; simp only [WithLp.ofLp_add, Pi.add_apply]; ring
  map_smul' r ψ := by
    ext b; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
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
      WithLp.toLp 2 fun b =>
        if b then 0 else (if flag then (μ : ℂ) + Complex.I * ν else 1) * z := by
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
  cases flag <;> cases b <;>
    simp only [LinearIsometryEquiv.trans_apply, prepYBool_symm_apply, rotBool_apply,
      ctrlZBool_apply, prepYBool_apply, ite_true, Bool.false_eq_true, ite_false,
      Complex.ofReal_neg, and_self, and_false, and_true]
  · ring_nf; simp only [h2, hI, hc2, hs2]; ring
  · ring_nf; simp only [h2, hI, hc2, hs2]; ring
  · ring_nf; simp only [h2, hI, hc2, hs2]
    rw [show (1 / 2 : ℂ) * (c : ℂ) * z * (s : ℂ) * Complex.I * 4 =
      2 * Complex.I * z * ((c : ℂ) * s) by ring, hcs2]
    ring
  · ring_nf; simp only [h2, hI, hc2, hs2]; ring

private def boolSwapEquiv (B : Type*) : (Bool × B) ≃ (B × Bool) where
  toFun p := (p.2, p.1)
  invFun q := (q.2, q.1)
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def liftBoolD {d : ℕ}
    (Q : Fin d → (EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool)) :
    EuclideanSpace ℂ (Bool × Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × Fin d) :=
  conjFiberIso (boolSwapEquiv (Fin d)) Q

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
  change (U (sliceSecond (ctrlZ flag φ) c)).ofLp k =
    (if flag ∧ c then (-1 : ℂ) else 1) * (U (sliceSecond φ c)).ofLp k
  rw [hslice, map_smul, PiLp.smul_apply, smul_eq_mul]

/-- **2-query simulation of an arbitrary two-valued oracle restriction**: any `T`-query
value-query algorithm restricted to `{a₀, a₁}` along `e : ι ≃ Fin N` can be simulated by `2 * T`
binary phase-oracle queries. -/
theorem exists_sim_value {N : ℕ}
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
  classical
  let R := (step a₀).symm.trans (step a₁)
  obtain ⟨bas, μ, ν, hunit, heig⟩ := LinearIsometryEquiv.exists_orthonormalBasis_eigenvectors R
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
    rw [bvSlice_liftValueIso_valueOracle, hgadget]
    congr 1
    ext v
    exact step_rel_ite_apply e step a₀ a₁ b y j v w
  refine measureProb_sim_stride e step U ψ₀ x T 2 pre Vsim b S ?_ ?_
  · simp only [run, Vsim, ite_true]
    by_cases hT : 0 < T
    · simp [hT, pre, liftValueIso_embedState, runValue]
    · have hT0 : T = 0 := by omega
      subst hT0
      simp [liftValueIso_embedState, runValue]
  · intro t ht' hprev
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
    · simp only [hlt, ite_true, pre, LinearIsometry.coe_comp, Function.comp_apply,
        LinearIsometryEquiv.coe_toLinearIsometry]
      rw [hstep, liftValueIso_embedState, ← runValue]
    · have heq : t + 1 = T := by omega
      subst heq
      simp only [lt_irrefl, ite_false, pre, LinearIsometry.coe_comp, Function.comp_apply,
        LinearIsometryEquiv.coe_toLinearIsometry]
      rw [hstep, liftValueIso_embedState, ← runValue]

end TwoValueSim

section IndexToValue

private def indexRouteFun {ι V W : Type*} [DecidableEq ι] [DecidableEq V]
    (idx : ι × V × W → ι) (v₀ : V) (i₀ : ι) :
    ι × V × Bool × V × W × ι → ι × V × Bool × V × W × ι
  | (i, v, false, v', w, i') =>
    if v' = v₀ ∧ i' = i₀ then (idx (i, v, w), v₀, true, v, w, i)
    else (i, v, false, v', w, i')
  | (i, v, true, v', w, i') =>
    if v = v₀ ∧ idx (i', v', w) = i then (i', v', false, v₀, w, i₀)
    else (i, v, true, v', w, i')

private theorem indexRouteFun_involutive {ι V W : Type*} [DecidableEq ι] [DecidableEq V]
    (idx : ι × V × W → ι) (v₀ : V) (i₀ : ι) (q : ι × V × Bool × V × W × ι) :
    indexRouteFun idx v₀ i₀ (indexRouteFun idx v₀ i₀ q) = q := by
  rcases q with ⟨i, v, b, v', w, i'⟩
  cases b <;> dsimp only [indexRouteFun] <;> split_ifs <;> simp_all

private def indexRoutePerm {ι V W : Type*} [DecidableEq ι] [DecidableEq V]
    (idx : ι × V × W → ι) (v₀ : V) (i₀ : ι) :
    Equiv.Perm (ι × V × Bool × V × W × ι) where
  toFun := indexRouteFun idx v₀ i₀
  invFun := indexRouteFun idx v₀ i₀
  left_inv := indexRouteFun_involutive idx v₀ i₀
  right_inv := indexRouteFun_involutive idx v₀ i₀

private def extProdEquiv {ι V W : Type*} :
    (ι × V × Bool × V × W × ι) ≃ ((Bool × V × ι) × (ι × V × W)) where
  toFun | (i, v, b, v', w, i') => ((b, v', i'), (i, v, w))
  invFun | ((b, v', i'), (i, v, w)) => (i, v, b, v', w, i')
  left_inv _ := rfl
  right_inv _ := rfl

private def idxProdEquiv {ι V W : Type*} :
    (ι × V × Bool × V × W × ι) ≃ ((ι × V × W) × Bool × ι × V) where
  toFun | (j, vout, b, v, w, i) => ((i, v, w), b, j, vout)
  invFun | ((i, v, w), b, j, vout) => (j, vout, b, v, w, i)
  left_inv _ := rfl
  right_inv _ := rfl

private def embedFalse {ι V W : Type*} [DecidableEq ι] [DecidableEq V] (v₀ : V) (i₀ : ι)
    (ψ : ValueState ι V W) : ValueState ι V (Bool × V × W × ι) :=
  WithLp.toLp 2 fun
    | (i, v, false, v', w, i') => if v' = v₀ ∧ i' = i₀ then ψ.ofLp (i, v, w) else 0
    | (_, _, true, _, _, _) => 0

private def sliceFalse {ι V W : Type*} (v₀ : V) (i₀ : ι)
    (ψ : ValueState ι V (Bool × V × W × ι)) : ValueState ι V W :=
  WithLp.toLp 2 fun (i, v, w) => ψ.ofLp (i, v, false, v₀, w, i₀)

private theorem norm_embedFalse {ι V W : Type*} [Fintype ι] [Fintype V] [Fintype W]
    [DecidableEq ι] [DecidableEq V] (v₀ : V) (i₀ : ι) (ψ : ValueState ι V W) :
    ‖embedFalse v₀ i₀ ψ‖ = ‖ψ‖ := by
  have hsq : ‖embedFalse v₀ i₀ ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rw [Fintype.sum_equiv extProdEquiv
      (fun q => ‖(embedFalse v₀ i₀ ψ).ofLp q‖ ^ 2)
      (fun p => ‖(embedFalse v₀ i₀ ψ).ofLp
        (p.2.1, p.2.2.1, p.1.1, p.1.2.1, p.2.2.2, p.1.2.2)‖ ^ 2)
      (fun ⟨_, _, _, _, _, _⟩ => rfl),
      Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_bool]
    have htrue : ∑ vi : V × ι, ∑ p : ι × V × W,
        ‖(embedFalse v₀ i₀ ψ).ofLp (p.1, p.2.1, true, vi.1, p.2.2, vi.2)‖ ^ 2 = 0 := by
      simp [embedFalse]
    have hfalse : ∀ vi : V × ι,
        ∑ p : ι × V × W,
          ‖(embedFalse v₀ i₀ ψ).ofLp (p.1, p.2.1, false, vi.1, p.2.2, vi.2)‖ ^ 2 =
            if vi = (v₀, i₀) then ‖ψ‖ ^ 2 else 0 := fun ⟨v', i'⟩ => by
      by_cases h : v' = v₀ ∧ i' = i₀
      · simp [embedFalse, h, EuclideanSpace.norm_sq_eq]
      · simp [embedFalse, h, Prod.ext_iff]
    rw [htrue, zero_add]
    simp [hfalse]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private noncomputable def liftFalseFun {ι V W : Type*} [Fintype ι] [Fintype V] [Fintype W]
    [DecidableEq ι] [DecidableEq V] (v₀ : V) (i₀ : ι)
    (U : ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ : ValueState ι V (Bool × V × W × ι)) : ValueState ι V (Bool × V × W × ι) :=
  WithLp.toLp 2 fun
    | (i, v, false, v', w, i') =>
      if v' = v₀ ∧ i' = i₀ then (U (sliceFalse v₀ i₀ ψ)).ofLp (i, v, w)
      else ψ.ofLp (i, v, false, v', w, i')
    | (i, v, true, v', w, i') => ψ.ofLp (i, v, true, v', w, i')

private noncomputable def liftFalse {ι V W : Type*} [Fintype ι] [Fintype V] [Fintype W]
    [DecidableEq ι] [DecidableEq V] (v₀ : V) (i₀ : ι)
    (U : ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) :
    ValueState ι V (Bool × V × W × ι) →ₗᵢ[ℂ] ValueState ι V (Bool × V × W × ι) where
  toFun := liftFalseFun v₀ i₀ U
  map_add' ψ₁ ψ₂ := by
    ext ⟨i, v, b, v', w, i'⟩
    have h : sliceFalse v₀ i₀ (ψ₁ + ψ₂) = sliceFalse v₀ i₀ ψ₁ + sliceFalse v₀ i₀ ψ₂ := rfl
    cases b <;> simp only [liftFalseFun, WithLp.ofLp_add, Pi.add_apply, h, map_add]
    split_ifs <;> rfl
  map_smul' r ψ := by
    ext ⟨i, v, b, v', w, i'⟩
    have h : sliceFalse v₀ i₀ (r • ψ) = r • sliceFalse v₀ i₀ ψ := rfl
    cases b <;> simp only [liftFalseFun, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, h,
      map_smul]
    split_ifs <;> rfl
  norm_map' ψ := by
    have hsq : ‖liftFalseFun v₀ i₀ U ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fintype.sum_equiv extProdEquiv (fun q => ‖(liftFalseFun v₀ i₀ U ψ).ofLp q‖ ^ 2)
          (fun p => ‖(liftFalseFun v₀ i₀ U ψ).ofLp
            (p.2.1, p.2.2.1, p.1.1, p.1.2.1, p.2.2.2, p.1.2.2)‖ ^ 2)
          (fun ⟨_, _, _, _, _, _⟩ => rfl),
        Fintype.sum_equiv extProdEquiv (fun q => ‖ψ.ofLp q‖ ^ 2)
          (fun p => ‖ψ.ofLp (p.2.1, p.2.2.1, p.1.1, p.1.2.1, p.2.2.2, p.1.2.2)‖ ^ 2)
          (fun ⟨_, _, _, _, _, _⟩ => rfl)]
      conv_lhs => rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_bool]
      conv_rhs => rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_bool]
      have ht :
          (∑ y : V × ι, ∑ y₁ : ι × V × W,
            ‖(liftFalseFun v₀ i₀ U ψ).ofLp (y₁.1, y₁.2.1, true, y.1, y₁.2.2, y.2)‖ ^ 2) =
          ∑ y : V × ι, ∑ y₁ : ι × V × W,
            ‖ψ.ofLp (y₁.1, y₁.2.1, true, y.1, y₁.2.2, y.2)‖ ^ 2 := rfl
      rw [ht, add_left_cancel_iff]
      refine sum_congr rfl fun ⟨v', i'⟩ _ => ?_
      by_cases h : v' = v₀ ∧ i' = i₀
      · have hL : ∑ p : ι × V × W,
            ‖(liftFalseFun v₀ i₀ U ψ).ofLp (p.1, p.2.1, false, v', p.2.2, i')‖ ^ 2 =
            ∑ p : ι × V × W, ‖(U (sliceFalse v₀ i₀ ψ)).ofLp (p.1, p.2.1, p.2.2)‖ ^ 2 :=
          sum_congr rfl fun p _ => by simp [liftFalseFun, h]
        have hR : ∑ p : ι × V × W, ‖ψ.ofLp (p.1, p.2.1, false, v', p.2.2, i')‖ ^ 2 =
            ‖sliceFalse v₀ i₀ ψ‖ ^ 2 := by
          simp [h.1, h.2, sliceFalse, EuclideanSpace.norm_sq_eq]
        rw [hL, ← EuclideanSpace.norm_sq_eq, U.norm_map, hR]
      · refine sum_congr rfl fun p _ => by simp [liftFalseFun, h]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- **Index-to-value `(T + 1)`-query simulation**: given a `T`-query value-query algorithm
`(U, ψ₀)` returning a query index `idx : ι × V × W → ι`, a basis state `ket v₀` and readout
`read : V → α` such that querying `step (X i)` prepares `read v = X i` with probability `1`
turn it into a `(T + 1)`-query value-returning algorithm with the exact same outcome
distribution. -/
theorem exists_sim_index_to_value {ι V W α : Type*} [Fintype ι] [Fintype V] [Fintype W]
    [Nonempty ι]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (v₀ : V) (read : V → α)
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ₀ : ValueState ι V W) (T : ℕ) (idx : ι × V × W → ι) :
    ∃ (U' : ℕ → ValueState ι V (Bool × V × W × ι) →ₗᵢ[ℂ] ValueState ι V (Bool × V × W × ι))
      (ψ₀' : ValueState ι V (Bool × V × W × ι)) (out' : ι × V × Bool × V × W × ι → α),
      ‖ψ₀'‖ = ‖ψ₀‖ ∧
        ∀ (X : ι → α),
          (∀ i : ι, (open Classical in
            measureProb (step (X i) (ket v₀)) (univ.filter fun v => read v = X i)) = 1) →
          ∀ (Pred : α → Prop) [DecidablePred Pred],
          measureProb (runValue step U' ψ₀' X (T + 1)) (univ.filter fun q => Pred (out' q)) =
            measureProb (runValue step U ψ₀ X T) (univ.filter fun p => Pred (X (idx p))) := by
  classical
  let i₀ : ι := Classical.arbitrary ι
  let route : ValueState ι V (Bool × V × W × ι) ≃ₗᵢ[ℂ] ValueState ι V (Bool × V × W × ι) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (indexRoutePerm idx v₀ i₀)
  let U' : ℕ → ValueState ι V (Bool × V × W × ι) →ₗᵢ[ℂ] ValueState ι V (Bool × V × W × ι) :=
    fun t =>
      if t < T then liftFalse v₀ i₀ (U t)
      else if t = T then route.toLinearIsometry.comp (liftFalse v₀ i₀ (U T))
      else LinearIsometry.id
  let ψ₀' := embedFalse v₀ i₀ ψ₀
  let out' : ι × V × Bool × V × W × ι → α := fun (_, v, _, _, _, _) => read v
  refine ⟨U', ψ₀', out', norm_embedFalse v₀ i₀ ψ₀, fun X hread Pred _ => ?_⟩
  have hlift_emb : ∀ (V₀ : ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) (ψ : ValueState ι V W),
      liftFalse v₀ i₀ V₀ (embedFalse v₀ i₀ ψ) = embedFalse v₀ i₀ (V₀ ψ) := fun V₀ ψ => by
    have hs : sliceFalse v₀ i₀ (embedFalse v₀ i₀ ψ) = ψ := by
      ext ⟨i₁, v₁, w₁⟩; simp [sliceFalse, embedFalse]
    ext ⟨i, v, b, v', w, i'⟩
    change (liftFalseFun v₀ i₀ V₀ (embedFalse v₀ i₀ ψ)).ofLp (i, v, b, v', w, i') = _
    cases b
    · dsimp only [liftFalseFun]
      rw [hs]
      by_cases h : v' = v₀ ∧ i' = i₀ <;> simp [embedFalse, h]
    · simp [liftFalseFun, embedFalse]
  have hlt_run : ∀ t ≤ T,
      runValue step U' ψ₀' X t =
        if t < T then embedFalse v₀ i₀ (runValue step U ψ₀ X t)
        else route (embedFalse v₀ i₀ (runValue step U ψ₀ X T)) := by
    intro t ht
    induction t with
    | zero =>
      dsimp only [runValue]
      by_cases h0 : 0 < T
      · simp [U', h0, ψ₀', hlift_emb]
      · have hT0 : T = 0 := by omega
        subst hT0
        simp [U', ψ₀', hlift_emb, runValue]
    | succ t ih =>
      have ht' : t < T := by omega
      have hprev := ih ht'.le
      simp only [ht', ite_true] at hprev
      have hvo : valueOracle step X (embedFalse v₀ i₀ (runValue step U ψ₀ X t)) =
          embedFalse v₀ i₀ (valueOracle step X (runValue step U ψ₀ X t)) := by
        ext ⟨i, v, b, v', w, i'⟩
        cases b
        · by_cases h : v' = v₀ ∧ i' = i₀
          · simp [valueOracle_apply, embedFalse, h]
          · have hz : (WithLp.toLp 2 fun v₁ =>
                (embedFalse v₀ i₀ (runValue step U ψ₀ X t)).ofLp (i, v₁, false, v', w, i')) =
                (0 : EuclideanSpace ℂ V) := by
              ext u; simp [embedFalse, h]
            rw [valueOracle_apply, hz, map_zero]
            simp [embedFalse, h]
        · have hz : (WithLp.toLp 2 fun v₁ =>
              (embedFalse v₀ i₀ (runValue step U ψ₀ X t)).ofLp (i, v₁, true, v', w, i')) =
              (0 : EuclideanSpace ℂ V) := by
            ext u; simp [embedFalse]
          rw [valueOracle_apply, hz, map_zero]
          simp [embedFalse]
      have hUt : U' (t + 1) =
          if t + 1 < T then liftFalse v₀ i₀ (U (t + 1))
          else route.toLinearIsometry.comp (liftFalse v₀ i₀ (U T)) := by
        dsimp only [U']
        split_ifs with h₁ h₂
        · rfl
        · rfl
        · exfalso; omega
      rw [runValue, hprev, hvo, hUt]
      by_cases hlt : t + 1 < T
      · simp only [hlt, ite_true, hlift_emb]
        rfl
      · have heq : t + 1 = T := by omega
        subst heq
        simp only [lt_irrefl, ite_false, LinearIsometry.coe_comp, Function.comp_apply,
          LinearIsometryEquiv.coe_toLinearIsometry, hlift_emb]
        rfl
  have hT := hlt_run T le_rfl
  simp only [lt_irrefl, ite_false] at hT
  have hfinal : runValue step U' ψ₀' X (T + 1) =
      valueOracle step X (route (embedFalse v₀ i₀ (runValue step U ψ₀ X T))) := by
    have hU_succ : U' (T + 1) = LinearIsometry.id := by
      simp only [U', show ¬ (T + 1 < T) by omega, show ¬ (T + 1 = T) by omega, ite_false]
    rw [runValue, hU_succ, hT, LinearIsometry.id_apply]
  rw [hfinal]
  set ψT := runValue step U ψ₀ X T
  have hprob_step : ∀ j' : ι,
      measureProb (step (X j') (ket v₀)) (univ.filter fun v => Pred (read v)) =
        if Pred (X j') then 1 else 0 := fun j' => by
    have hgood := hread j'
    have hnorm : measureProb (step (X j') (ket v₀)) univ = 1 := by
      rw [measureProb_univ, (step (X j')).norm_map, norm_ket, one_pow]
    have hzero : ∀ v : V, read v ≠ X j' → ‖(step (X j') (ket v₀)).ofLp v‖ ^ 2 = 0 := by
      intro v hv
      have hc := measureProb_compl (step (X j') (ket v₀)) (univ.filter fun u => read u = X j')
      rw [(step (X j')).norm_map, norm_ket, one_pow, hgood, sub_self] at hc
      dsimp only [measureProb] at hc
      have hmem : v ∈ (univ.filter fun u => read u = X j')ᶜ := by simpa using hv
      have hle : ‖(step (X j') (ket v₀)).ofLp v‖ ^ 2 ≤
          ∑ u ∈ (univ.filter fun u => read u = X j')ᶜ,
            ‖(step (X j') (ket v₀)).ofLp u‖ ^ 2 :=
        Finset.single_le_sum (f := fun u => ‖(step (X j') (ket v₀)).ofLp u‖ ^ 2)
          (fun _ _ => by positivity) hmem
      rw [hc] at hle
      exact le_antisymm hle (by positivity)
    by_cases hp : Pred (X j')
    · simp only [hp, ite_true]
      have hsub : univ.filter (fun u => read u = X j') ⊆ univ.filter (fun u => Pred (read u)) := by
        intro u hu
        rw [mem_filter] at hu ⊢
        exact ⟨mem_univ u, hu.2 ▸ hp⟩
      exact le_antisymm ((measureProb_mono _ (subset_univ _)).trans hnorm.le)
        (hgood ▸ measureProb_mono _ hsub)
    · simp only [hp, ite_false]
      refine le_antisymm ?_ (measureProb_nonneg _ _)
      refine sum_nonpos fun v hv => ?_
      have hv' : Pred (read v) := (mem_filter.mp hv).2
      have hne : read v ≠ X j' := fun heq => hp (heq ▸ hv')
      rw [hzero v hne]
  have hroute_apply : ∀ (j : ι) (v' : V) (b : Bool) (v : V) (w : W) (i : ι),
      (route (embedFalse v₀ i₀ ψT)).ofLp (j, v', b, v, w, i) =
        if b = true ∧ v' = v₀ ∧ idx (i, v, w) = j then ψT.ofLp (i, v, w) else 0 := by
    intro j v' b v w i
    change (embedFalse v₀ i₀ ψT).ofLp (indexRouteFun idx v₀ i₀ (j, v', b, v, w, i)) = _
    cases b <;> dsimp only [indexRouteFun]
    · by_cases h : v = v₀ ∧ i = i₀ <;> simp [h, embedFalse]
    · by_cases h : v' = v₀ ∧ idx (i, v, w) = j <;> simp [h, embedFalse]
  have hslice_true : ∀ (j : ι) (v : V) (w : W) (i : ι),
      (WithLp.toLp 2 fun v' => (route (embedFalse v₀ i₀ ψT)).ofLp (j, v', true, v, w, i)) =
        if idx (i, v, w) = j then ψT.ofLp (i, v, w) • ket v₀ else 0 := fun j v w i => by
    ext v'
    rw [hroute_apply]
    by_cases hj : idx (i, v, w) = j <;> by_cases hv' : v' = v₀ <;> simp [hj, hv', ket_apply]
  have hslice_false : ∀ (j : ι) (v : V) (w : W) (i : ι),
      (WithLp.toLp 2 fun v' => (route (embedFalse v₀ i₀ ψT)).ofLp (j, v', false, v, w, i)) = 0 :=
    fun j v w i => by
      ext v'
      simp [hroute_apply]
  rw [measureProb, measureProb, sum_filter, sum_filter, Fintype.sum_equiv idxProdEquiv
    (fun q => if Pred (out' q) then
      ‖(valueOracle step X (route (embedFalse v₀ i₀ ψT))).ofLp q‖ ^ 2 else 0)
    (fun q => if Pred (read q.2.2.2) then
      ‖(valueOracle step X (route (embedFalse v₀ i₀ ψT))).ofLp
        (q.2.2.1, q.2.2.2, q.2.1, q.1.2.1, q.1.2.2, q.1.1)‖ ^ 2 else 0)
    (fun ⟨_, _, _, _, _, _⟩ => rfl), Fintype.sum_prod_type]
  refine sum_congr rfl fun p _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  have hf : ∑ x : ι × V, (if Pred (read x.2) then
      ‖(valueOracle step X (route (embedFalse v₀ i₀ ψT))).ofLp
        (x.1, x.2, false, p.2.1, p.2.2, p.1)‖ ^ 2 else 0) = 0 := by
    refine sum_eq_zero fun x _ => ?_
    simp only [valueOracle_apply, hslice_false, map_zero, WithLp.ofLp_zero, Pi.zero_apply,
      norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ite_self]
  rw [hf, add_zero, Fintype.sum_prod_type]
  have hj_zero : ∀ j : ι, j ≠ idx p →
      ∑ vout : V, (if Pred (read vout) then
        ‖(valueOracle step X (route (embedFalse v₀ i₀ ψT))).ofLp
          (j, vout, true, p.2.1, p.2.2, p.1)‖ ^ 2 else 0) = 0 := fun j hj => by
    refine sum_eq_zero fun vout _ => ?_
    simp only [valueOracle_apply, hslice_true, hj.symm, ite_false, map_zero, WithLp.ofLp_zero,
      Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ite_self]
  rw [sum_eq_single (idx p) (fun j _ hj => hj_zero j hj) (fun h => absurd (mem_univ _) h)]
  have hval_eq : ∑ vout : V, (if Pred (read vout) then
      ‖(valueOracle step X (route (embedFalse v₀ i₀ ψT))).ofLp
        (idx p, vout, true, p.2.1, p.2.2, p.1)‖ ^ 2 else 0) =
      ‖ψT.ofLp p‖ ^ 2 *
        measureProb (step (X (idx p)) (ket v₀)) (univ.filter fun vout => Pred (read vout)) := by
    calc
      ∑ vout : V, (if Pred (read vout) then
          ‖(valueOracle step X (route (embedFalse v₀ i₀ ψT))).ofLp
            (idx p, vout, true, p.2.1, p.2.2, p.1)‖ ^ 2 else 0)
          = ∑ vout : V, if Pred (read vout) then
              ‖ψT.ofLp p‖ ^ 2 * ‖(step (X (idx p)) (ket v₀)).ofLp vout‖ ^ 2 else 0 := by
              refine sum_congr rfl fun vout _ => ?_
              simp only [valueOracle_apply, hslice_true, ite_true, map_smul, PiLp.smul_apply,
                smul_eq_mul, norm_mul, mul_pow]
      _ = ‖ψT.ofLp p‖ ^ 2 * ∑ vout : V,
            if Pred (read vout) then ‖(step (X (idx p)) (ket v₀)).ofLp vout‖ ^ 2 else 0 := by
              rw [mul_sum]
              refine sum_congr rfl fun vout _ => by split_ifs <;> ring
      _ = ‖ψT.ofLp p‖ ^ 2 *
            measureProb (step (X (idx p)) (ket v₀)) (univ.filter fun vout => Pred (read vout)) := by
              rw [measureProb, sum_filter]
  rw [hval_eq, hprob_step]
  split_ifs <;> ring

/-- Index-to-value `(T + 1)`-query simulation specialized to a permutation oracle `permStep π` on
two values `a₀, a₁` distinguished at `v₀ : V`. -/
theorem exists_sim_index_to_value_perm {ι V W α : Type*} [Fintype ι] [Fintype V] [Fintype W]
    [Nonempty ι]
    (π : α → Equiv.Perm V) (v₀ : V) (a₀ a₁ : α) (hne : π a₀ v₀ ≠ π a₁ v₀)
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ₀ : ValueState ι V W) (T : ℕ) (idx : ι × V × W → ι) :
    ∃ (U' : ℕ → ValueState ι V (Bool × V × W × ι) →ₗᵢ[ℂ] ValueState ι V (Bool × V × W × ι))
      (ψ₀' : ValueState ι V (Bool × V × W × ι)) (out' : ι × V × Bool × V × W × ι → α),
      ‖ψ₀'‖ = ‖ψ₀‖ ∧
        ∀ (X : ι → α), (∀ i : ι, X i = a₀ ∨ X i = a₁) →
          ∀ (Pred : α → Prop) [DecidablePred Pred],
          measureProb (runValue (permStep π) U' ψ₀' X (T + 1))
              (univ.filter fun q => Pred (out' q)) =
            measureProb (runValue (permStep π) U ψ₀ X T)
              (univ.filter fun p => Pred (X (idx p))) := by
  classical
  let read : V → α := fun v => if v = π a₀ v₀ then a₀ else a₁
  obtain ⟨U', ψ₀', out', hnorm, hsim⟩ :=
    exists_sim_index_to_value (permStep π) v₀ read U ψ₀ T idx
  refine ⟨U', ψ₀', out', hnorm, fun X hX Pred _ => hsim X (fun i => ?_) Pred⟩
  have hket : permStep π (X i) (ket v₀) = ket (π (X i) v₀) := by
    ext v
    simp [permStep_apply, ket_apply, Equiv.symm_apply_eq]
  rw [hket, measureProb_ket]
  rcases hX i with hi | hi <;> simp [hi, read, hne.symm]

end IndexToValue

end Cslib.Quantum
