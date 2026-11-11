/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.QueryComplexity.Quantum.PermutationInversion
import CslibFrontier.Foundations.Quantum.Measurement.ReadoutOverlap

/-!
# Tests for non-Boolean value-query adversaries and permutation inversion

Non-vacuous strict-`module` checks for:
* `CslibFrontier.Foundations.Quantum.Measurement.ReadoutOverlap`:
  `measureOut_eq_ofReal_measureProb`, `norm_inner_le_two_mul_sqrt_of_disjoint`,
  `norm_inner_le_two_mul_sqrt_of_readout_ne`, and `norm_inner_le_two_mul_sqrt_of_measureOut_ne`;
* `CslibFrontier.Computability.QueryComplexity.Quantum.ValueAdversary`: `querySlice`,
  `sum_sq_norm_querySlice`, `norm_inner_valueOracle_valueOracle_ge`, and
  `one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt_value`;
* `CslibFrontier.Computability.QueryComplexity.Quantum.PermutationInversion`: kernel `decide` checks
  of `permInvPermRel` on `Fin 3` and `Fin 4` (including Ambainis's separation `l_max = 2 < 4 = l l'`
  between Theorem 6 and Theorem 2), a `0`-query witness at `|ι| = 1`, `0`-query impossibility for
  `|ι| ≥ 2`, a `1`-query exact inverter on `Fin 2`, and a `2`-query exact inverter over the
  non-Boolean alphabet `Fin 3`.
-/

public section

namespace CslibFrontierTests.QuantumPermutationInversion

open Cslib.Quantum Finset

/-! ### Multi-outcome readout overlap (`ReadoutOverlap.lean`) -/

example :
    measureOut (ket (0 : Fin 3)) (norm_ket _) (fun i : Fin 3 => i.val) 0 =
      ENNReal.ofReal (measureProb (ket (0 : Fin 3)) {i : Fin 3 | i.val = 0}) :=
  measureOut_eq_ofReal_measureProb (ket (0 : Fin 3)) (norm_ket _) (fun i => i.val) 0

example :
    ‖inner ℂ (ket (0 : Fin 3)) (ket (1 : Fin 3))‖ ≤ 2 * √((0 : ℝ) * (1 - 0)) :=
  norm_inner_le_two_mul_sqrt_of_readout_ne (norm_ket _) (norm_ket _) id (b₁ := 0) (b₂ := 1)
    (by decide) (by rw [measureProb_ket]; simp) (by rw [measureProb_ket]; simp) (by norm_num)

example :
    ‖inner ℂ (ket (0 : Fin 3)) (ket (2 : Fin 3))‖ ≤ 2 * √((0 : ℝ) * (1 - 0)) :=
  norm_inner_le_two_mul_sqrt_of_measureOut_ne (norm_ket _) (norm_ket _) id (b₁ := 0) (b₂ := 2)
    (by decide) (by simp) (by simp) (by norm_num)

/-! ### Kernel `decide` checks on `permInvPermRel` (`Fin 3` and `Fin 4`) -/

-- Odd size `N = 3`: `|I₀| = 1`, `|I₁| = 2`, `|R| = 4`, and `l_{π, k} * l_{σ, k} ≤ 2`.
example : #(permInvLeft ({0} : Finset (Fin 3)) 0) = 2 := by decide
example : #(permInvRight ({1, 2} : Finset (Fin 3)) 0) = 4 := by decide
example : #(permInvPermRel ({0} : Finset (Fin 3)) {1, 2} 0) = 4 := by decide

example :
    ∀ p ∈ permInvPermRel ({0} : Finset (Fin 3)) {1, 2} 0, ∀ k : Fin 3, p.1 k ≠ p.2 k →
      #{q ∈ permInvPermRel ({0} : Finset (Fin 3)) {1, 2} 0 | q.1 k ≠ q.2 k ∧ q.1 = p.1} *
        #{q ∈ permInvPermRel ({0} : Finset (Fin 3)) {1, 2} 0 | q.1 k ≠ q.2 k ∧ q.2 = p.2} ≤
        2 := by
  decide

-- Even size `N = 4`: `m = m' = 2`, `|R| = 24`. On `(1, swap 0 2) ∈ rel4`, separate coordinate
-- maxima reach `l_{1, 0} = 2` and `l_{swap 0 2, 2} = 2` (`l * l' = 4`), whereas Theorem 6's
-- pairwise product bound `card_permInvPermRel_diff_mul_le` gives `l_{π, k} * l_{σ, k} ≤ 2`.
private abbrev rel4 : Finset (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)) :=
  permInvPermRel {0, 1} {2, 3} 0

example : #rel4 = 24 := by decide

example :
    (1, Equiv.swap (0 : Fin 4) 2) ∈ rel4 ∧
    #{q ∈ rel4 | q.1 0 ≠ q.2 0 ∧ q.1 = 1} = 2 ∧
    #{q ∈ rel4 | q.1 2 ≠ q.2 2 ∧ q.2 = Equiv.swap 0 2} = 2 ∧
    (∀ p ∈ rel4, ∀ k : Fin 4, p.1 k ≠ p.2 k →
      #{q ∈ rel4 | q.1 k ≠ q.2 k ∧ q.1 = p.1} * #{q ∈ rel4 | q.1 k ≠ q.2 k ∧ q.2 = p.2} ≤ 2) :=
  ⟨by decide, by decide, by decide, fun _ hp _ hk =>
    card_permInvPermRel_diff_mul_le (by decide) hp hk⟩

/-! ### Sharpness at `|ι| = 1` (`T = 0` queries) and impossibility of `T = 0` for `|ι| ≥ 2` -/

private noncomputable def step1 :
    Fin 1 → (EuclideanSpace ℂ Unit ≃ₗᵢ[ℂ] EuclideanSpace ℂ Unit) :=
  fun _ => LinearIsometryEquiv.refl ℂ _

private noncomputable def init1 : ValueState (Fin 1) Unit Unit := ket (0, (), ())

private theorem zero_query_inverts_fin1 (π : Equiv.Perm (Fin 1)) :
    1 - (0 : ℝ) ≤
      measureProb (runValue step1 (fun _ => LinearIsometry.id) init1 ⇑π 0)
        {q | q.1 = π.symm 0} := by
  have hrun : runValue step1 (fun _ => LinearIsometry.id) init1 ⇑π 0 = init1 := rfl
  rw [hrun, init1, measureProb_ket]
  have h0 : π.symm 0 = 0 := Subsingleton.elim _ _
  simp [h0]

-- At `|ι| = 1`, `T = 0` satisfies both `√⌊|ι| / 2⌋ ≤ 2 T` and `√(|ι| - 1) ≤ 2 √2 T`.
example :
    (1 - 2 * √((0 : ℝ) * (1 - 0))) * √(Fintype.card (Fin 1) - 1 : ℕ) ≤ 2 * √2 * (0 : ℕ) :=
  one_sub_two_mul_sqrt_mul_sqrt_sub_one_le_of_permInversion step1 (fun _ => LinearIsometry.id)
    (norm_ket _) 0 Prod.fst 0 zero_query_inverts_fin1 (by norm_num)

/-- No `0`-query quantum value-query algorithm can invert permutations on `ι` (`2 ≤ |ι|`) with
success probability at least `2 / 3`. -/
theorem no_zero_query_permInversion {ι V W : Type*} [Fintype ι] [Fintype V] [Fintype W]
    (hcard : 2 ≤ Fintype.card ι) (target : ι)
    (step : ι → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (out : ι × V × W → ι) :
    ¬ ∀ π : Equiv.Perm ι,
      ENNReal.ofReal (2 / 3) ≤
        measureOut (runValue step U ψ₀ ⇑π 0) (by rw [norm_runValue, hψ₀]) out (π.symm target) := by
  intro hcorr
  have h := permInversion_measureOut_lower_bound hcard step U hψ₀ 0 out target hcorr
  omega

/-! ### Non-vacuous `1`-query exact inverter on `Fin 2` -/

private noncomputable def step2 (a : Fin 2) :
    EuclideanSpace ℂ (ZMod 2) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (ZMod 2) :=
  addStep (a.val : ZMod 2)

private noncomputable def init2 : ValueState (Fin 2) (ZMod 2) Unit := ket (0, 0, ())

private def out2 : Fin 2 × ZMod 2 × Unit → Fin 2 :=
  fun (_, v, _) => if v = 0 then 0 else 1

private theorem runValue_inv2 (π : Equiv.Perm (Fin 2)) :
    runValue step2 (fun _ => LinearIsometry.id) init2 ⇑π 1 =
      ket (0, ((π 0).val : ZMod 2), ()) := by
  ext ⟨i, v, u⟩
  have hu : u = () := rfl
  subst hu
  simp only [runValue, LinearIsometry.id_apply, valueOracle_apply]
  by_cases hi : i = 0
  · subst hi
    have hslice : (WithLp.toLp 2 fun v' : ZMod 2 => init2.ofLp (0, v', ())) = ket (0 : ZMod 2) := by
      ext v'
      simp [init2, ket_apply]
    rw [hslice, step2, addStep_ket, zero_add]
    simp [ket_apply]
  · have hz : (WithLp.toLp 2 fun v' : ZMod 2 => init2.ofLp (i, v', ())) = 0 := by
      ext v'
      simp [init2, ket_apply, hi]
    rw [hz, map_zero]
    simp [ket_apply, hi]

private theorem out2_perm_eq (π : Equiv.Perm (Fin 2)) :
    out2 (0, ((π 0).val : ZMod 2), ()) = π.symm 0 := by
  revert π
  decide

private theorem inv2_exact (π : Equiv.Perm (Fin 2)) :
    1 - (0 : ℝ) ≤
      measureProb (runValue step2 (fun _ => LinearIsometry.id) init2 ⇑π 1)
        {q | out2 q = π.symm 0} := by
  rw [runValue_inv2, measureProb_ket]
  simp [out2_perm_eq]

private theorem inv2_measureOut (π : Equiv.Perm (Fin 2)) :
    ENNReal.ofReal (2 / 3) ≤
      measureOut (runValue step2 (fun _ => LinearIsometry.id) init2 ⇑π 1)
        (by rw [norm_runValue, init2, norm_ket]) out2 (π.symm 0) := by
  rw [measureOut_eq_ofReal_measureProb]
  exact ENNReal.ofReal_le_ofReal (by linarith [inv2_exact π])

-- Non-vacuous instantiations of all Theorem 7 bounds at `N = 2`, `T = 1`, `ε = 0` / `ε = 1/3`.
example :
    (1 - 2 * √((0 : ℝ) * (1 - 0))) * √(Fintype.card (Fin 2) / 2 : ℕ) ≤ 2 * (1 : ℕ) :=
  one_sub_two_mul_sqrt_mul_sqrt_div_two_le_of_permInversion step2 (fun _ => LinearIsometry.id)
    (norm_ket _) 1 out2 0 inv2_exact (by norm_num)

example :
    (1 - 2 * √((0 : ℝ) * (1 - 0))) * √(Fintype.card (Fin 2) : ℝ) ≤ 2 * √3 * (1 : ℕ) :=
  one_sub_two_mul_sqrt_mul_sqrt_card_le_of_permInversion (by simp) step2
    (fun _ => LinearIsometry.id) (norm_ket _) 1 out2 0 inv2_exact (by norm_num)

example : Fintype.card (Fin 2) ≤ 3888 * 1 ^ 2 :=
  permInversion_measureOut_lower_bound (by simp) step2 (fun _ => LinearIsometry.id)
    (norm_ket _) 1 out2 0 inv2_measureOut

/-! ### Non-Boolean alphabet (`α = Fin 3`, `|α| = 3`) `2`-query exact inverter -/

private noncomputable def step3 (a : Fin 3) :
    EuclideanSpace ℂ (ZMod 3) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (ZMod 3) :=
  addStep (a.val : ZMod 3)

private def swapStep3Fun : Fin 3 × ZMod 3 × ZMod 3 → Fin 3 × ZMod 3 × ZMod 3 :=
  fun (i, v, w) => (Equiv.swap (0 : Fin 3) 1 i, w, v)

private def swapStep3Perm : Equiv.Perm (Fin 3 × ZMod 3 × ZMod 3) where
  toFun := swapStep3Fun
  invFun := swapStep3Fun
  left_inv := fun ⟨i, v, w⟩ => by simp [swapStep3Fun]
  right_inv := fun ⟨i, v, w⟩ => by simp [swapStep3Fun]

private noncomputable def alg3 :
    ℕ → ValueState (Fin 3) (ZMod 3) (ZMod 3) →ₗᵢ[ℂ] ValueState (Fin 3) (ZMod 3) (ZMod 3)
  | 1 => (permStep (fun _ : Unit => swapStep3Perm) ()).toLinearIsometry
  | _ => LinearIsometry.id

private noncomputable def init3 : ValueState (Fin 3) (ZMod 3) (ZMod 3) := ket (0, 0, 0)

private def out3 : Fin 3 × ZMod 3 × ZMod 3 → Fin 3 :=
  fun (_, v₁, v₀) => if v₀ = 0 then 0 else if v₁ = 0 then 1 else 2

private theorem runValue_alg3 (x : Fin 3 → Fin 3) :
    runValue step3 alg3 init3 x 2 = ket (1, ((x 1).val : ZMod 3), ((x 0).val : ZMod 3)) := by
  have h1 : runValue step3 alg3 init3 x 1 = ket (1, 0, ((x 0).val : ZMod 3)) := by
    have hvo : valueOracle step3 x init3 = ket (0, ((x 0).val : ZMod 3), 0) := by
      ext ⟨i, v, w⟩
      simp only [valueOracle_apply]
      by_cases hi : i = 0 <;> by_cases hw : w = 0
      · subst hi; subst hw
        have hs : (WithLp.toLp 2 fun v' : ZMod 3 => init3.ofLp (0, v', 0)) = ket (0 : ZMod 3) := by
          ext v'; simp [init3, ket_apply]
        rw [hs, step3, addStep_ket, zero_add]
        simp [ket_apply]
      · have hz : (WithLp.toLp 2 fun v' : ZMod 3 => init3.ofLp (i, v', w)) = 0 := by
          ext v'; simp [init3, ket_apply, hw]
        rw [hz, map_zero]
        simp [ket_apply, hw]
      · have hz : (WithLp.toLp 2 fun v' : ZMod 3 => init3.ofLp (i, v', w)) = 0 := by
          ext v'; simp [init3, ket_apply, hi]
        rw [hz, map_zero]
        simp [ket_apply, hi]
      · have hz : (WithLp.toLp 2 fun v' : ZMod 3 => init3.ofLp (i, v', w)) = 0 := by
          ext v'; simp [init3, ket_apply, hi]
        rw [hz, map_zero]
        simp [ket_apply, hi]
    ext ⟨i, v, w⟩
    change (alg3 1 (valueOracle step3 x (runValue step3 alg3 init3 x 0))).ofLp (i, v, w) = _
    rw [show runValue step3 alg3 init3 x 0 = init3 from rfl, hvo]
    simp only [alg3, LinearIsometryEquiv.coe_toLinearIsometry, permStep_apply]
    change (ket (0, ((x 0).val : ZMod 3), 0) :
      ValueState (Fin 3) (ZMod 3) (ZMod 3)).ofLp (swapStep3Fun (i, v, w)) = _
    simp only [swapStep3Fun, ket_apply, Prod.mk.injEq]
    fin_cases i
    · simp
    · simp [and_comm]
    · have h2 : Equiv.swap (0 : Fin 3) 1 2 ≠ 0 := by decide
      simp [h2]
  ext ⟨i, v, w⟩
  change (valueOracle step3 x (runValue step3 alg3 init3 x 1)).ofLp (i, v, w) = _
  rw [h1]
  simp only [valueOracle_apply]
  by_cases hi : i = 1 <;> by_cases hw : w = ((x 0).val : ZMod 3)
  · subst hi
    have hs : (WithLp.toLp 2 fun v' : ZMod 3 =>
        (ket (1, (0 : ZMod 3), ((x 0).val : ZMod 3)) :
          ValueState (Fin 3) (ZMod 3) (ZMod 3)).ofLp (1, v', w)) = ket (0 : ZMod 3) := by
      ext v'
      simp [ket_apply, hw]
    rw [hs, step3, addStep_ket, zero_add]
    simp [ket_apply, hw]
  · have hz : (WithLp.toLp 2 fun v' : ZMod 3 =>
        (ket (1, (0 : ZMod 3), ((x 0).val : ZMod 3)) :
          ValueState (Fin 3) (ZMod 3) (ZMod 3)).ofLp (i, v', w)) = 0 := by
      ext v'
      simp [ket_apply, hw]
    rw [hz, map_zero]
    simp [ket_apply, hw]
  · have hz : (WithLp.toLp 2 fun v' : ZMod 3 =>
        (ket (1, (0 : ZMod 3), ((x 0).val : ZMod 3)) :
          ValueState (Fin 3) (ZMod 3) (ZMod 3)).ofLp (i, v', w)) = 0 := by
      ext v'
      simp [ket_apply, hi]
    rw [hz, map_zero]
    simp [ket_apply, hi]
  · have hz : (WithLp.toLp 2 fun v' : ZMod 3 =>
        (ket (1, (0 : ZMod 3), ((x 0).val : ZMod 3)) :
          ValueState (Fin 3) (ZMod 3) (ZMod 3)).ofLp (i, v', w)) = 0 := by
      ext v'
      simp [ket_apply, hi]
    rw [hz, map_zero]
    simp [ket_apply, hi]

private theorem out3_perm_eq (π : Equiv.Perm (Fin 3)) :
    out3 (1, ((π 1).val : ZMod 3), ((π 0).val : ZMod 3)) = π.symm 0 := by
  revert π
  decide

private theorem alg3_inverts (π : Equiv.Perm (Fin 3)) :
    1 - (0 : ℝ) ≤ measureProb (runValue step3 alg3 init3 ⇑π 2) {q | out3 q = π.symm 0} := by
  rw [runValue_alg3, measureProb_ket]
  simp [out3_perm_eq]

private theorem alg3_exact_fun (x : Fin 3 → Fin 3) :
    1 - (0 : ℝ) ≤ measureProb (runValue step3 alg3 init3 x 2)
      {q | out3 q = if x 0 = 0 then 0 else if x 1 = 0 then 1 else 2} := by
  rw [runValue_alg3, measureProb_ket]
  have h : out3 (1, ((x 1).val : ZMod 3), ((x 0).val : ZMod 3)) =
      (if x 0 = 0 then 0 else if x 1 = 0 then 1 else 2) := by
    revert x; decide
  simp [h]

-- Non-vacuous instantiation on the non-Boolean alphabet `Fin 3` (`|α| = 3`) at `T = 2`.
example :
    (1 - 2 * √((0 : ℝ) * (1 - 0))) * √(Fintype.card (Fin 3) : ℝ) ≤ 2 * √3 * (2 : ℕ) :=
  one_sub_two_mul_sqrt_mul_sqrt_card_le_of_permInversion (by simp) step3 alg3
    (norm_ket _) 2 out3 0 alg3_inverts (by norm_num)

-- Direct non-Boolean Theorem 6 instantiation on a ternary `Fin 3 → Fin 3` pair (`|α| = 3`).
private def ternaryIn0 : Fin 3 → Fin 3 := fun _ => 0
private def ternaryIn1 : Fin 3 → Fin 3 := fun i => if i = 0 then 2 else 1

example :
    (1 - 2 * √((0 : ℝ) * (1 - 0))) * √((1 : ℕ) * (1 : ℕ)) ≤ 2 * (2 : ℕ) * √(1 : ℕ) :=
  one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt_value step3 alg3 (norm_ket _) 2 out3
    (fun x => if x 0 = 0 then 0 else if x 1 = 0 then 1 else 2)
    (R := {(ternaryIn0, ternaryIn1)}) (singleton_nonempty _)
    (fun p hp => by rcases mem_singleton.1 hp with rfl; decide)
    (fun p _ => alg3_exact_fun p.1) (fun p _ => alg3_exact_fun p.2) (by norm_num)
    (fun p hp => by
      rcases mem_singleton.1 hp with rfl
      rw [filter_singleton, ite_eq_left rfl, card_singleton])
    (fun p hp => by
      rcases mem_singleton.1 hp with rfl
      rw [filter_singleton, ite_eq_left rfl, card_singleton])
    (fun p hp i hi => by
      rcases mem_singleton.1 hp with rfl
      rw [filter_singleton, filter_singleton, ite_eq_left ⟨hi, rfl⟩, ite_eq_left ⟨hi, rfl⟩,
        card_singleton])

end CslibFrontierTests.QuantumPermutationInversion
