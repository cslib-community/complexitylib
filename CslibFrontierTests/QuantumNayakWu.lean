/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.NayakWuConsequences
public import CslibFrontier.Computability.QueryComplexity.Quantum.BitQuery
public import CslibFrontierTests.QuantumPolynomial
public import CslibFrontier.Foundations.LinearAlgebra.UnitarySpectrum

/-! Nonvacuous checks and concrete witnesses for multi-outcome readouts (`Readout`), unitary
spectral diagonalization (`UnitarySpectrum`), value-query and index-to-value simulations
(`ValueQuery`), and the Nayak–Wu lower bounds (`NayakWuConsequences`, Theorem 1.5, Corollary 1.6,
Theorem 1.11). -/

namespace CslibFrontierTests.QuantumNayakWu

open Cslib Cslib.Quantum Cslib.BitString Finset
open CslibFrontierTests.QuantumPolynomial

public section

/-! ### Multi-outcome readouts (`Readout.lean`) -/

example : measureOut (ket (0 : Fin 2)) (norm_ket _) (fun i => i.val) 0 = 1 := by
  simp

example : measureOut (ket (0 : Fin 2)) (norm_ket _) (fun i => i.val) 1 = 0 := by
  simp

example :
    (1 : ℝ) ≤ (open Classical in
      measureProb (ket (0 : Fin 2))
        (univ.filter fun i : Fin 2 => (fun y : ℕ => y = 0) i.val)) := by
  have h := le_measureProb_of_le_measureOut (ket (0 : Fin 2)) (norm_ket _)
    (fun i : Fin 2 => i.val) (fun y : ℕ => y = 0) (p := 1) (by
      rw [measureOut_toOuterMeasure_apply, measureProb_ket]
      split_ifs with hm
      · rfl
      · exact absurd (by rw [mem_filter]; exact ⟨mem_univ _, rfl⟩) hm)
  convert h

/-! ### Unitary spectrum (`UnitarySpectrum.lean`) -/

noncomputable def swap2 :
    EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.swap (0 : Fin 2) 1)

example : swap2 (ket (0 : Fin 2)) = ket (1 : Fin 2) := by
  ext i
  fin_cases i <;> simp [swap2, ket_apply]

example :
    ∃ (bas : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)))
      (μ ν : Fin 2 → ℝ),
      (∀ j, (μ j) ^ 2 + (ν j) ^ 2 = 1) ∧
      ∀ j, swap2 (bas j) = ((μ j : ℂ) + Complex.I * ν j) • bas j := by
  have hd : Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) = 2 := by
    simp
  obtain ⟨bas, μ, ν, hcirc, heig⟩ := swap2.exists_orthonormalBasis_eigenvectors
  exact ⟨bas.reindex (Fintype.equivOfCardEq (by simp [hd])), μ ∘ (Fintype.equivOfCardEq (by
    simp [hd])).symm, ν ∘ (Fintype.equivOfCardEq (by simp [hd])).symm,
    fun j => hcirc _, fun j => by simpa using heig _⟩

/-! ### Value-query simulation (`ValueQuery.lean`) -/

example : ∀ (U : ℕ → ValueState (Fin 2) (BitString 1) Unit →ₗᵢ[ℂ] _)
    (ψ₀ : ValueState (Fin 2) (BitString 1) Unit) (T : ℕ),
    ∃ (Vsim : ℕ → State 2 (BitString 1 × Unit) →ₗᵢ[ℂ] State 2 (BitString 1 × Unit))
      (φ₀ : State 2 (BitString 1 × Unit)),
      ‖φ₀‖ = ‖ψ₀‖ ∧
        ∀ (b : BitString 2) (S : Finset (Fin 2 × BitString 1 × Unit)),
          measureProb (run Vsim φ₀ b T) (S.map (embedOutcome (Equiv.refl (Fin 2)))) =
            measureProb (runValue (addStep (V := BitString 1)) U ψ₀
              (fun i => if b i then fun _ => true else fun _ => false) T) S := by
  intro U ψ₀ T
  refine exists_sim_involution (Equiv.refl (Fin 2)) (addStep (V := BitString 1))
    (fun _ => false) (fun _ => true)
    (addStep_rel_involutive (by decide : ∀ v : BitString 1, v + v = 0) _ _) U ψ₀ T

/-! ### Theorem 1.11: exact (`readBit`) and `2`-query (`count2Alg`) counting -/

def readBitOut : Fin 1 × Bool × Unit → ℝ := fun p => if p.2.1 then 1 else 0

theorem readBit_exactCount (x : BitString 1) :
    1 - (0 : ℝ) ≤
      measureProb (run readBit QuantumPolynomial.ψ₀ x 1)
        (univ.filter fun p => |readBitOut p - weight x| < 1 / 2) := by
  cases hx : x 0
  · have hw : weight x = 0 := by
      rw [weight, card_eq_zero, filter_eq_empty_iff]
      intro i _
      rw [Subsingleton.elim i 0, hx]
      decide
    have hcomp : measureProb (run readBit QuantumPolynomial.ψ₀ x 1) acceptᶜ = 1 := by
      rw [measureProb_compl, norm_run, norm_ψ₀, one_pow, measureProb_readBit, hx, bitVal_false,
        sub_zero]
    have hsub : acceptᶜ ⊆ univ.filter fun p => |readBitOut p - weight x| < 1 / 2 := by
      intro p hp
      rw [mem_compl, accept, mem_singleton] at hp
      rw [mem_filter]
      refine ⟨mem_univ p, ?_⟩
      have hp1 : p.1 = 0 := Fin.eq_zero p.1
      have hp2 : p.2.2 = () := rfl
      have hpb : p.2.1 = false := by
        cases hb : p.2.1
        · rfl
        · exfalso
          exact hp (Prod.ext hp1 (Prod.ext hb hp2))
      simp [readBitOut, hpb, hw]
    linarith [measureProb_mono (run readBit QuantumPolynomial.ψ₀ x 1) hsub]
  · have hw : weight x = 1 := by
      rw [weight, card_eq_one]
      refine ⟨0, ?_⟩
      ext i
      rw [Subsingleton.elim i 0]
      simp [hx]
    have hsub : accept ⊆ univ.filter fun p => |readBitOut p - weight x| < 1 / 2 := by
      intro p hp
      rw [accept, mem_singleton] at hp
      subst hp
      simp [readBitOut, hw]
    have h1 := measureProb_readBit x
    rw [hx, bitVal_true] at h1
    linarith [measureProb_mono (run readBit QuantumPolynomial.ψ₀ x 1) hsub]

-- Exact-precision (`Δ = 1 / 2`, `n = 1`) counting bound on `readBit` (`T = 1`, `t = 1`).
example :
    (1 - 2 * √((0 : ℝ) * (1 - 0))) *
        (√((1 : ℕ) : ℝ) + √((1 : ℕ) * (((1 : ℕ) : ℝ) - (1 : ℕ)))) ≤
      4 * ((1 : ℕ) : ℝ) :=
  one_sub_mul_exactCount_le readBit norm_ψ₀ 1 readBitOut (t := 1) (Δ := 1 / 2)
    (ε := 0) le_rfl le_rfl (by norm_num) le_rfl readBit_exactCount (by norm_num)

def count2Perm : ℕ → Equiv.Perm (Fin 2 × Bool × Bool)
  | 1 =>
    { toFun := fun (i, b, w) => (Equiv.swap (0 : Fin 2) 1 i, w, b)
      invFun := fun (i, b, w) => (Equiv.swap (0 : Fin 2) 1 i, w, b)
      left_inv := fun ⟨i, b, w⟩ => by simp
      right_inv := fun ⟨i, b, w⟩ => by simp }
  | _ => 1

noncomputable def count2Alg : ℕ → State 2 Bool →ₗᵢ[ℂ] State 2 Bool :=
  bitQueryAlg 2 count2Perm LinearIsometry.id LinearIsometry.id

noncomputable def count2Init : State 2 Bool := ket (0, false, false)

def count2Out : Fin 2 × Bool × Bool → ℝ := fun (_, b, w) => (b.toNat + w.toNat : ℝ)

theorem run_count2Alg (x : BitString 2) :
    run count2Alg count2Init x 2 = ket (1, x 1, x 0) := by
  rw [count2Alg, run_bitQueryAlg, LinearIsometry.id_apply, LinearIsometry.id_apply,
    count2Init, permute_ket]
  congr 1
  simp [bitQueryPerm, count2Perm, bitFlip_apply]

theorem count2_approxCount (x : BitString 2) :
    1 - (1 / 3 : ℝ) ≤
      measureProb (run count2Alg count2Init x 2)
        (univ.filter fun p => |count2Out p - weight x| < 1 / 2) := by
  rw [run_count2Alg, measureProb_ket]
  have hw : (weight x : ℝ) = ((x 0).toNat : ℝ) + (x 1).toNat := by
    rw [weight_eq_sum_toNat, Fin.sum_univ_two]
    push_cast
    rfl
  have hmem : (1, x 1, x 0) ∈ univ.filter fun p => |count2Out p - weight x| < 1 / 2 := by
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    simp [count2Out, hw, add_comm]
  simp only [hmem, ite_true]
  norm_num

-- Theorem 1.11 (`n = 2`, `Δ = 1 / 2`, `t = 1`) applied to `count2Alg` (`T = 2`).
example : √((2 : ℕ) / (1 / 2 : ℝ)) + √((1 : ℕ) * ((2 : ℕ) - 1)) / (1 / 2 : ℝ) ≤ 288 * 2 := by
  simpa using approxCount_lower_bound count2Alg (norm_ket _) 2 count2Out (t := 1) (Δ := 1 / 2)
    (by omega) le_rfl (by norm_num) count2_approxCount

/-! ### Theorems 1.5 and Corollary 1.6: exact 4-query value-query sorter (`Fin 4 → Bool`) -/

def flipBitPerm : Bool → Equiv.Perm Bool
  | true => Equiv.swap false true
  | false => Equiv.refl Bool

noncomputable def stepBool : Bool → (EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool) :=
  permStep flipBitPerm

theorem stepBool_ket {inst : DecidableEq Bool} (a v : Bool) :
    stepBool a (@ket Bool inst v) = @ket Bool inst (flipBitPerm a v) := by
  ext b
  cases a <;> cases v <;> cases b <;> simp [stepBool, permStep_apply, flipBitPerm, ket_apply]

theorem stepBool_rel_involutive (φ : EuclideanSpace ℂ Bool) :
    ((stepBool false).symm.trans (stepBool true))
      (((stepBool false).symm.trans (stepBool true)) φ) = φ := by
  ext b
  simp only [LinearIsometryEquiv.trans_apply, stepBool, permStep,
    LinearIsometryEquiv.piLpCongrLeft_symm, LinearIsometryEquiv.piLpCongrLeft_apply, flipBitPerm]
  cases b <;> simp

def swapBit4 (t : Fin 4) : Equiv.Perm (Fin 4 × Bool × (Fin 4 → Bool)) where
  toFun | (i, b, w) => if i = t then (t, w t, Function.update w t b) else (i, b, w)
  invFun | (i, b, w) => if i = t then (t, w t, Function.update w t b) else (i, b, w)
  left_inv q := by
    rcases q with ⟨i, b, w⟩
    by_cases h : i = t
    · subst h
      simp only [ite_true, Function.update_self, Prod.mk.injEq, true_and]
      ext j
      by_cases hj : j = i <;> simp [hj, Function.update]
    · simp [h]
  right_inv q := by
    rcases q with ⟨i, b, w⟩
    by_cases h : i = t
    · subst h
      simp only [ite_true, Function.update_self, Prod.mk.injEq, true_and]
      ext j
      by_cases hj : j = i <;> simp [hj, Function.update]
    · simp [h]

def stagePerm4 : ℕ → Equiv.Perm (Fin 4 × Bool × (Fin 4 → Bool))
  | 1 => ((Equiv.swap (0 : Fin 4) 1).prodCongr (Equiv.refl _)) * swapBit4 0
  | 2 => ((Equiv.swap (1 : Fin 4) 2).prodCongr (Equiv.refl _)) * swapBit4 1
  | 3 => ((Equiv.swap (2 : Fin 4) 3).prodCongr (Equiv.refl _)) * swapBit4 2
  | 4 => swapBit4 3
  | _ => 1

noncomputable def readAll4 :
    ℕ → ValueState (Fin 4) Bool (Fin 4 → Bool) →ₗᵢ[ℂ] ValueState (Fin 4) Bool (Fin 4 → Bool) :=
  fun t => (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (stagePerm4 t)).toLinearIsometry

noncomputable def initAll4 : ValueState (Fin 4) Bool (Fin 4 → Bool) :=
  ket (0, false, fun _ => false)

theorem valueOracle_stepBool_ket (X : Fin 4 → Bool) (i : Fin 4) (b : Bool)
    (w : Fin 4 → Bool) :
    valueOracle stepBool X (ket (i, b, w)) = ket (i, b ^^ X i, w) := by
  ext ⟨i', b', w'⟩
  by_cases hi : i' = i <;> by_cases hw : w' = w
  · subst hi hw
    simp only [valueOracle_apply, stepBool, permStep_apply, ket_apply, Prod.mk.injEq,
      true_and, and_true]
    cases hx : X i' <;> cases b <;> cases b' <;> simp [flipBitPerm]
  · simp [valueOracle_apply, stepBool, permStep_apply, ket_apply, hi, hw]
  · simp [valueOracle_apply, stepBool, permStep_apply, ket_apply, hi, hw]
  · simp [valueOracle_apply, stepBool, permStep_apply, ket_apply, hi, hw]

theorem piLpCongrLeft_ket {γ : Type*} [Fintype γ] [DecidableEq γ] (p : Equiv.Perm γ)
    (q : γ) : LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ p (ket q) = ket (p q) := by
  ext q'
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, ket_apply, Equiv.symm_apply_eq]

theorem run_readAll4 (X : Fin 4 → Bool) :
    runValue stepBool readAll4 initAll4 X 4 = ket (3, false, X) := by
  rw [runValue, runValue, runValue, runValue, runValue]
  dsimp only [initAll4, readAll4]
  simp only [LinearIsometryEquiv.coe_toLinearIsometry, piLpCongrLeft_ket]
  rw [show stagePerm4 0 (0, false, fun _ => false) = (0, false, fun _ => false) by rfl]
  rw [valueOracle_stepBool_ket, piLpCongrLeft_ket]
  have h1 : stagePerm4 1 (0, false ^^ X 0, fun _ => false) =
      (1, false, Function.update (fun _ : Fin 4 => false) 0 (X 0)) := by
    simp [stagePerm4, swapBit4]
  rw [h1, valueOracle_stepBool_ket, piLpCongrLeft_ket]
  have h2 : stagePerm4 2 (1, false ^^ X 1, Function.update (fun _ : Fin 4 => false) 0 (X 0)) =
      (2, false, Function.update (Function.update (fun _ : Fin 4 => false) 0 (X 0)) 1 (X 1)) := by
    simp [stagePerm4, swapBit4]
  rw [h2, valueOracle_stepBool_ket, piLpCongrLeft_ket]
  have h3 : stagePerm4 3 (2, false ^^ X 2,
        Function.update (Function.update (fun _ : Fin 4 => false) 0 (X 0)) 1 (X 1)) =
      (3, false, Function.update
        (Function.update (Function.update (fun _ : Fin 4 => false) 0 (X 0)) 1 (X 1)) 2 (X 2)) := by
    simp [stagePerm4, swapBit4]
  rw [h3, valueOracle_stepBool_ket, piLpCongrLeft_ket]
  congr 1
  simp only [stagePerm4, swapBit4, Bool.false_xor]
  refine Prod.ext rfl (Prod.ext (by simp) ?_)
  ext j
  fin_cases j <;> simp [Function.update]

def out4 : Fin 4 × Bool × (Fin 4 → Bool) → Bool :=
  fun (_, _, w) => decide (3 ≤ #{i : Fin 4 | w i = true})

theorem card_bool_part {ι : Type*} [Fintype ι] (X : ι → Bool) :
    #{i : ι | X i = false} + #{i : ι | X i = true} = Fintype.card ι := by
  have hs := card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun i => X i = true)
  simp only [card_univ] at hs
  have h2 : #{i : ι | X i = false} = #{a : ι | ¬ X a = true} :=
    congrArg card (filter_congr fun i _ => by cases X i <;> simp)
  omega

theorem out4_isKthSmallest (X : Fin 4 → Bool) :
    IsKthSmallest X 2 (out4 (3, false, X)) := by
  have hpart := card_bool_part X
  simp only [Fintype.card_fin] at hpart
  dsimp only [out4]
  by_cases hw : 3 ≤ #{i : Fin 4 | X i = true}
  · simp only [hw, decide_true]
    refine ⟨?_, ?_⟩
    · have hlt : #{i : Fin 4 | X i < true} = #{i : Fin 4 | X i = false} :=
        congrArg card (filter_congr fun i _ => by cases X i <;> simp)
      omega
    · have hle : #{i : Fin 4 | X i ≤ true} = 4 := by simp
      omega
  · simp only [hw, decide_false]
    refine ⟨?_, ?_⟩
    · have hlt : #{i : Fin 4 | X i < false} = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]
        intro i _
        cases X i <;> simp
      omega
    · have hle : #{i : Fin 4 | X i ≤ false} = #{i : Fin 4 | X i = false} :=
        congrArg card (filter_congr fun i _ => by cases X i <;> simp)
      omega

theorem out4_isApproxKthSmallest (X : Fin 4 → Bool) :
    IsApproxKthSmallest X 2 1 (out4 (3, false, X)) :=
  ⟨2, by omega, by simp, by norm_num, by norm_num, out4_isKthSmallest X⟩

theorem out4_isApproxMedian (X : Fin 4 → Bool) :
    IsApproxMedian X (1 / 3) (out4 (3, false, X)) := by
  have hpart := card_bool_part X
  simp only [Fintype.card_fin] at hpart
  dsimp only [out4, IsApproxMedian]
  simp only [Fintype.card_fin]
  by_cases hw : 3 ≤ #{i : Fin 4 | X i = true}
  · simp only [hw, decide_true]
    have h1 : #{i : Fin 4 | X i < true} = #{i : Fin 4 | X i = false} :=
      congrArg card (filter_congr fun i _ => by cases X i <;> simp)
    have h2 : #{i : Fin 4 | true < X i} = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro i _
      cases X i <;> simp
    have h1R : (#{i : Fin 4 | X i < true} : ℝ) ≤ 1 := by
      exact_mod_cast (by omega : #{i | X i < true} ≤ 1)
    rw [h2, Nat.cast_zero]
    constructor <;> linarith
  · simp only [hw, decide_false]
    have h1 : #{i : Fin 4 | X i < false} = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro i _
      cases X i <;> simp
    have h2 : #{i : Fin 4 | false < X i} = #{i : Fin 4 | X i = true} :=
      congrArg card (filter_congr fun i _ => by cases X i <;> simp)
    have h2R : (#{i : Fin 4 | false < X i} : ℝ) ≤ 2 := by
      exact_mod_cast (by omega : #{i | false < X i} ≤ 2)
    rw [h1, Nat.cast_zero]
    constructor <;> linarith

theorem readAll4_kthSmallest_good (X : Fin 4 → Bool) :
    1 - (1 / 3 : ℝ) ≤ (open Classical in
      measureProb (runValue stepBool readAll4 initAll4 X 4)
        (univ.filter fun p => IsApproxKthSmallest X 2 1 (out4 p))) := by
  classical
  rw [run_readAll4, measureProb_ket]
  split_ifs with hmem
  · norm_num
  · exact absurd (by rw [mem_filter]; exact ⟨mem_univ _, out4_isApproxKthSmallest X⟩) hmem

theorem readAll4_median_good (X : Fin 4 → Bool) :
    1 - (1 / 3 : ℝ) ≤ (open Classical in
      measureProb (runValue stepBool readAll4 initAll4 X 4)
        (univ.filter fun p => IsApproxMedian X (1 / 3) (out4 p))) := by
  classical
  rw [run_readAll4, measureProb_ket]
  split_ifs with hmem
  · norm_num
  · exact absurd (by rw [mem_filter]; exact ⟨mem_univ _, out4_isApproxMedian X⟩) hmem

-- Theorem 1.5 (`k = 2, Δ = 1, n = 4, T = 4`) for general and involutive-difference oracles.
example : √((Fintype.card (Fin 4) : ℝ) / 1) +
    √((2 : ℕ) * ((Fintype.card (Fin 4) : ℝ) - 2)) / 1 ≤ 576 * 4 :=
  kthSmallest_lower_bound stepBool readAll4 (norm_ket _) 4 out4 (k := 2) (Δ := 1)
    (by omega) (by simp) le_rfl (by simp) readAll4_kthSmallest_good

example : √((Fintype.card (Fin 4) : ℝ) / 1) +
    √((2 : ℕ) * ((Fintype.card (Fin 4) : ℝ) - 2)) / 1 ≤ 288 * 4 :=
  kthSmallest_involution_lower_bound stepBool readAll4 (norm_ket _) 4 out4 false true
    (by decide) stepBool_rel_involutive (k := 2) (Δ := 1) (by omega) (by simp) le_rfl (by simp)
    (fun X _ => readAll4_kthSmallest_good X)

-- Corollary 1.6 (`δ = 1 / 3, n = 4, T = 4`) for general, `1 / δ`, and involutive oracles.
example : min (1 / (1 / 3 : ℝ)) (Fintype.card (Fin 4)) ≤ 432 * 4 :=
  median_lower_bound stepBool readAll4 (norm_ket _) 4 out4 (δ := 1 / 3) (by simp) (by norm_num)
    (by norm_num) readAll4_median_good

example : 1 / (1 / 3 : ℝ) ≤ 432 * 4 :=
  median_inv_delta_lower_bound stepBool readAll4 (norm_ket _) 4 out4 (δ := 1 / 3) (by norm_num)
    (by norm_num) (by simp; norm_num) readAll4_median_good

example : min (1 / (1 / 3 : ℝ)) (Fintype.card (Fin 4)) ≤ 216 * 4 :=
  median_involution_lower_bound stepBool readAll4 (norm_ket _) 4 out4 false true (by decide)
    stepBool_rel_involutive (δ := 1 / 3) (by simp) (by norm_num) (by norm_num)
    (fun X _ => readAll4_median_good X)

/-! ### Index-returning `0`-query vs `1`-query witness at `n = 3, δ = 1 / 3` -/

noncomputable def unif3Init : ValueState (Fin 3) Bool Unit :=
  ((1 / Real.sqrt 3 : ℝ) : ℂ) • ∑ i : Fin 3, ket (i, false, ())

theorem norm_unif3Init : ‖unif3Init‖ = 1 := by
  have hsum : ‖∑ i : Fin 3, (ket (i, false, ()) : ValueState (Fin 3) Bool Unit)‖ = Real.sqrt 3 := by
    have hsq : ‖∑ i : Fin 3, (ket (i, false, ()) : ValueState (Fin 3) Bool Unit)‖ ^ 2 = 3 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp_rw [Fintype.sum_prod_type]
      have hcoord : ∀ (i : Fin 3) (b : Bool) (u : Unit),
          (∑ j : Fin 3, (ket (j, false, ()) : ValueState (Fin 3) Bool Unit)).ofLp (i, b, u) =
            if b then 0 else 1 := fun i b u => by
        rw [WithLp.ofLp_sum, Finset.sum_apply]
        cases b
        · simp [ket_apply]
        · simp [ket_apply]
      simp [hcoord]
    have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [norm_nonneg (∑ i : Fin 3, (ket (i, false, ()) : ValueState (Fin 3) Bool Unit)),
      Real.sqrt_nonneg 3]
  rw [unif3Init, norm_smul, Complex.norm_real, hsum, Real.norm_of_nonneg (by positivity),
    one_div_mul_cancel (by positivity)]

noncomputable def zeroQueryAlg :
    ℕ → ValueState (Fin 3) Bool Unit →ₗᵢ[ℂ] ValueState (Fin 3) Bool Unit :=
  fun _ => LinearIsometry.id

theorem zeroQuery_median_good (X : Fin 3 → Bool) :
    1 - (1 / 3 : ℝ) ≤ (open Classical in
      measureProb (runValue stepBool zeroQueryAlg unif3Init X 0)
        (univ.filter fun p : Fin 3 × Bool × Unit => IsApproxMedian X (1 / 3) (X p.1))) := by
  classical
  have hrun : runValue stepBool zeroQueryAlg unif3Init X 0 = unif3Init := rfl
  rw [hrun]
  have hpart := card_bool_part X
  simp only [Fintype.card_fin] at hpart
  have hsub_val : ∀ (m : Bool), 2 ≤ #{i : Fin 3 | X i = m} → IsApproxMedian X (1 / 3) m := by
    intro m hm
    dsimp only [IsApproxMedian]
    simp only [Fintype.card_fin]
    cases m
    · have hlt : #{i : Fin 3 | X i < false} = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]; intro i _; cases X i <;> simp
      have hgt : #{i : Fin 3 | false < X i} = #{i : Fin 3 | X i = true} :=
        congrArg card (filter_congr fun i _ => by cases X i <;> simp)
      have h2R : (#{i : Fin 3 | false < X i} : ℝ) ≤ 1 := by
        exact_mod_cast (by omega : #{i | false < X i} ≤ 1)
      rw [hlt, Nat.cast_zero]
      constructor <;> linarith
    · have hlt : #{i : Fin 3 | X i < true} = #{i : Fin 3 | X i = false} :=
        congrArg card (filter_congr fun i _ => by cases X i <;> simp)
      have hgt : #{i : Fin 3 | true < X i} = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]; intro i _; cases X i <;> simp
      have h1R : (#{i : Fin 3 | X i < true} : ℝ) ≤ 1 := by
        exact_mod_cast (by omega : #{i | X i < true} ≤ 1)
      rw [hgt, Nat.cast_zero]
      constructor <;> linarith
  obtain ⟨m, hm⟩ : ∃ m : Bool, 2 ≤ #{i : Fin 3 | X i = m} := by
    by_cases h : 2 ≤ #{i : Fin 3 | X i = true}
    · exact ⟨true, h⟩
    · exact ⟨false, by omega⟩
  have hm_good := hsub_val m hm
  have hsub : (univ.filter fun i : Fin 3 => X i = m).map
      ⟨fun i => (i, false, ()), fun a b hab => by cases hab; rfl⟩ ⊆
      univ.filter fun p : Fin 3 × Bool × Unit => IsApproxMedian X (1 / 3) (X p.1) := by
    intro p hp
    rcases mem_map.mp hp with ⟨i, hi, rfl⟩
    rw [mem_filter] at hi ⊢
    exact ⟨mem_univ _, hi.2 ▸ hm_good⟩
  have hmeas : measureProb unif3Init ((univ.filter fun i : Fin 3 => X i = m).map
      ⟨fun i => (i, false, ()), fun a b hab => by cases hab; rfl⟩) =
      (#{i : Fin 3 | X i = m} : ℝ) / 3 := by
    rw [measureProb, sum_map]
    have hterm : ∀ i : Fin 3,
        ‖unif3Init.ofLp (i, false, ())‖ ^ 2 = (1 / 3 : ℝ) := fun i => by
      have hamp : unif3Init.ofLp (i, false, ()) = ((1 / Real.sqrt 3 : ℝ) : ℂ) := by
        rw [unif3Init, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply]
        simp [ket_apply]
      rw [hamp, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_pow, one_pow,
        Real.sq_sqrt (by norm_num)]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => hterm i) ?_
    simp [div_eq_mul_inv]
  have hmR : (2 : ℝ) / 3 ≤ (#{i : Fin 3 | X i = m} : ℝ) / 3 := by
    have : (2 : ℝ) ≤ #{i : Fin 3 | X i = m} := by exact_mod_cast hm
    linarith
  have hmono := measureProb_mono unif3Init hsub
  rw [hmeas] at hmono
  linarith

-- `T = 0` random-index median satisfies Corollary 1.6 with the `T + 1` shift (`min 3 3 ≤ 432 * 1`).
example : min (1 / (1 / 3 : ℝ)) (Fintype.card (Fin 3)) ≤ 432 * ((0 : ℕ) + 1 : ℝ) :=
  median_index_lower_bound stepBool (false : Bool) (fun b => b) false true (by decide)
    (by
      rw [stepBool_ket (inst := fun a b => Classical.propDecidable (a = b)),
        measureProb, Finset.sum_filter, Fintype.sum_bool]
      simp [flipBitPerm, ket_apply])
    (by
      rw [stepBool_ket (inst := fun a b => Classical.propDecidable (a = b)),
        measureProb, Finset.sum_filter, Fintype.sum_bool]
      simp [flipBitPerm, ket_apply])
    zeroQueryAlg norm_unif3Init 0 (fun p => p.1) (δ := 1 / 3) (by simp) (by norm_num)
    (by norm_num) (fun X _ => zeroQuery_median_good X)


end
end CslibFrontierTests.QuantumNayakWu
