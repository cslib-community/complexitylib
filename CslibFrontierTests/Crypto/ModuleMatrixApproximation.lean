/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.Module.ApproximateSampling
import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption.Native
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! Actual prime-modulus bias and native conditional key generation with one sampled matrix. -/

namespace ComplexityTests.Crypto.ModuleMatrixApproximation

open Cslib Cslib.Crypto Probability ProbComp Interactive Turing.MultiTapeTM
open scoped Matrix ENNReal

private abbrev Matrix3 := Matrix (Fin 1) (Fin 1) (Fin 2 → ZMod 3)

private theorem zero_encoded_iff (A : Matrix3) :
    ModuleSIS.encodeMatrix (0 : Matrix3) = ModuleSIS.encodeMatrix A ↔ A = 0 := by
  constructor
  · intro h
    have hrows := (encList (encList encNat)).injective h
    have h0 := congrArg (fun rows : List (List ℕ) => (rows.getD 0 []).getD 0 0) hrows
    have h1 := congrArg (fun rows : List (List ℕ) => (rows.getD 1 []).getD 0 0) hrows
    change 0 = (A 0 0 0).val at h0
    change 0 = (A 0 0 1).val at h1
    ext i j l
    fin_cases i
    fin_cases j
    fin_cases l
    · exact ZMod.val_injective 3 h0.symm
    · exact ZMod.val_injective 3 h1.symm
  · rintro rfl
    rfl

private theorem scalar_zero_mass :
    ((eval (sampleModNat 4 3)).map (Nat.cast : ℕ → ZMod 3)) 0 = 3 / 8 := by
  rw [eval_sampleModNat, PMF.map_comp]
  change ((PMF.uniformOfFintype (Fin 16)).map (fun i => ((i.val % 3 : ℕ) : ZMod 3))) 0 = _
  have hz (i : Fin 16) : (0 : ZMod 3) = ((i.val % 3 : ℕ) : ZMod 3) ↔ i.val % 3 = 0 := by
    rw [← (ZMod.val_injective 3).eq_iff]
    simp [ZMod.val_natCast, eq_comm]
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (by finiteness)).mp
  simp only [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply, hz]
  norm_num [Fin.sum_univ_succ, ENNReal.toReal_add]

private theorem zero_mass_map (μ : PMF Matrix3) :
    μ.map ModuleSIS.encodeMatrix (ModuleSIS.encodeMatrix (0 : Matrix3)) = μ 0 := by
  simp only [PMF.map_apply, zero_encoded_iff, tsum_ite_eq]

private theorem actual_zero_mass :
    ((PMF.pi fun _ : Fin 1 => PMF.pi fun _ : Fin 1 => PMF.pi fun _ : Fin 2 =>
      (eval (sampleModNat 4 3)).map (Nat.cast : ℕ → ZMod 3)).map
        ModuleSIS.encodeMatrix) (ModuleSIS.encodeMatrix (0 : Matrix3)) = 9 / 64 := by
  refine (zero_mass_map _).trans ?_
  change (PMF.pi fun _ : Fin 1 => PMF.pi fun _ : Fin 1 => PMF.pi fun _ : Fin 2 =>
    (eval (sampleModNat 4 3)).map (Nat.cast : ℕ → ZMod 3)) (fun _ _ _ => 0) = _
  simp only [PMF.pi_apply, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, scalar_zero_mass]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

private theorem ideal_zero_mass :
    ((PMF.uniformOfFintype Matrix3).map ModuleSIS.encodeMatrix)
      (ModuleSIS.encodeMatrix (0 : Matrix3)) = 1 / 9 := by
  rw [zero_mass_map, PMF.uniformOfFintype_apply]
  rw [show Fintype.card Matrix3 = 9 by decide]
  simp

/-- Four fair bits modulo three produce a genuinely biased two-coefficient matrix law. -/
example : ∃ sample : (((ℕ × ℕ) × ℕ) × ℕ × ℕ) → ProbComp (List Bool),
    IsPPTOn
      (encPair (encPair (encPair encUnary encUnary) encUnary) (encPair encUnary encNat))
      encBits sample ∧
    CloseTo ((PMF.uniformOfFintype Matrix3).map ModuleSIS.encodeMatrix)
      (eval (sample (((1, 1), 2), 4, 3))) (3 / 8) ∧
    eval (sample (((1, 1), 2), 4, 3)) (ModuleSIS.encodeMatrix (0 : Matrix3)) = 9 / 64 ∧
    eval (sample (((1, 1), 2), 4, 3)) ≠
      (PMF.uniformOfFintype Matrix3).map ModuleSIS.encodeMatrix := by
  obtain ⟨sample, hppt, hlaw⟩ := exists_isPPTOn_approximateEncodedModuleMatrix
  obtain ⟨heq, hclose⟩ := hlaw 1 1 2 4 3 (by decide)
  refine ⟨sample, hppt, ?_, ?_, ?_⟩
  · convert hclose using 1
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  · rw [heq]
    exact actual_zero_mass
  · intro h
    have hm := congrArg (fun p : PMF (List Bool) => p (ModuleSIS.encodeMatrix (0 : Matrix3))) h
    rw [heq, actual_zero_mass, ideal_zero_mass] at hm
    have hr := congrArg ENNReal.toReal hm
    norm_num at hr

/-- One sampled matrix and the same obtained key generator compose uniformly, with binary
modulus and complete supplied signed secret/error words. The concrete conditional law retains
its `3/8` error against the existing ideal structured key-generation law. -/
example : ∃ sample run,
    IsPPTOn
      (encPair (encPair (encPair encUnary encUnary) encUnary) (encPair encUnary encNat))
      encBits sample ∧
    ComputableInPolyTime run
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair encBits (encPair encBits encBits))) encBits ∧
    IsPPTOn
      (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encNat)
        (encPair encBits encBits)) encBits
      (fun p : (((ℕ × ℕ) × ℕ) × ℕ) × List Bool × List Bool => do
        let word ← sample (((p.1.1.1.1, p.1.1.1.1), p.1.1.1.2), p.1.1.2, p.1.2)
        return run ((p.1.1.1, p.1.2), (word, p.2.1, p.2.2))) ∧
    CloseTo
      ((PMF.uniformOfFintype Matrix3).map (fun A => ModuleLWE.encodeSample
        (moduleLWEKeyGen A
          (fun j i => ((![![-1, 2]] : Fin 1 → Fin 2 → ℤ) j i : ZMod 3))
          (fun j i => ((![![1, -1]] : Fin 1 → Fin 2 → ℤ) j i : ZMod 3)))))
      (eval (do
        let word ← sample (((1, 1), 2), 4, 3)
        return run (((1, 2), 3), (word,
          (ModuleSIS.encodeVec (![![-1, 2]]), ModuleSIS.encodeVec (![![1, -1]]))))))
      (3 / 8) := by
  obtain ⟨sample, hppt, hlaw⟩ := exists_isPPTOn_approximateEncodedModuleMatrix
  obtain ⟨run, hnative, hrun⟩ := exists_computableInPolyTime_moduleLWEKeyGen
  have hprepare : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × ℕ) × ℕ) × List Bool × List Bool =>
        (((p.1.1.1.1, p.1.1.1.1), p.1.1.1.2), p.1.1.2, p.1.2))
      (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encNat)
        (encPair encBits encBits))
      (encPair (encPair (encPair encUnary encUnary) encUnary) (encPair encUnary encNat)) := by
    fun_prop
  have hcallback : ComputableInPolyTime
      (fun p : ((((ℕ × ℕ) × ℕ) × ℕ) × List Bool × List Bool) × List Bool =>
        ((p.1.1.1.1, p.1.1.2), (p.2, p.1.2.1, p.1.2.2)))
      (encPair
        (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encNat)
          (encPair encBits encBits)) encBits)
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair encBits (encPair encBits encBits))) := by fun_prop
  refine ⟨sample, run, hppt, hnative, ?_, ?_⟩
  · simpa only [bind_pure_comp] using
      (hppt.preprocess hprepare).map_with (hnative.comp hcallback)
  · have hc := (hlaw 1 1 2 4 3 (by decide)).2.map
      (fun word => run (((1, 2), 3), (word,
        (ModuleSIS.encodeVec (![![-1, 2]]), ModuleSIS.encodeVec (![![1, -1]])))))
    have hideal : ((PMF.uniformOfFintype Matrix3).map ModuleSIS.encodeMatrix).map
        (fun word => run (((1, 2), 3), (word,
          (ModuleSIS.encodeVec (![![-1, 2]]), ModuleSIS.encodeVec (![![1, -1]]))))) =
        (PMF.uniformOfFintype Matrix3).map (fun A => ModuleLWE.encodeSample
          (moduleLWEKeyGen A
            (fun j i => ((![![-1, 2]] : Fin 1 → Fin 2 → ℤ) j i : ZMod 3))
            (fun j i => ((![![1, -1]] : Fin 1 → Fin 2 → ℤ) j i : ZMod 3)))) := by
      rw [PMF.map_comp]
      congr 1
      funext A
      exact hrun 1 2 3 (by decide) A (![![-1, 2]]) (![![1, -1]])
    rw [hideal] at hc
    simp only [eval_bind, eval_pure]
    convert hc using 1
    · rfl
    · apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num

/-- The precision schedule is native for large binary moduli, including modulus one. -/
example : ∃ sample,
    IsPPTOn
      (encPair (encPair (encPair encUnary encUnary) encUnary) (encPair encUnary encNat))
      encBits sample ∧
    CloseTo
      ((PMF.uniformOfFintype (Matrix (Fin 2) (Fin 1) (Fin 3 → ZMod (2 ^ 128 + 1)))).map
        ModuleSIS.encodeMatrix)
      (eval (sample (((2, 1), 3), 10, 2 ^ 128 + 1))) (6 / 1024) ∧
    CloseTo
      ((PMF.uniformOfFintype (Matrix (Fin 1) (Fin 1) (Fin 1 → ZMod 1))).map
        ModuleSIS.encodeMatrix)
      (eval (sample (((1, 1), 1), 0, 1))) 1 := by
  obtain ⟨sample, hppt, hlaw⟩ := exists_isPPTOn_sampleEncodedModuleMatrixWithPrecision
  refine ⟨sample, hppt, ?_, ?_⟩
  · convert (hlaw 2 1 3 10 (2 ^ 128 + 1) (by decide)).2 using 1
    norm_num
  · convert (hlaw 1 1 1 0 1 (by decide)).2 using 1
    norm_num

private theorem pi_pure_const {α : Type} [Finite α] (n : ℕ) (a : α) :
    (PMF.pi fun _ : Fin n => PMF.pure a) = PMF.pure (fun _ : Fin n => a) := by
  simpa only [eval_pi, eval_pure] using eval_pi_pure (fun _ : Fin n => a)

private theorem width_zero_scalar :
    eval (sampleModNat 0 3) = PMF.pure 0 := by
  rw [eval_sampleModNat]
  convert PMF.map_const (PMF.uniformOfFintype (Fin 1)) (0 : ℕ) using 1
  congr 1
  funext i
  simp

/-- Width zero, modulus one, and both empty expanded shapes have their actual degenerate laws. -/
example : ∃ sample,
    IsPPTOn
      (encPair (encPair (encPair encUnary encUnary) encUnary) (encPair encUnary encNat))
      encBits sample ∧
    eval (sample (((1, 1), 2), 0, 3)) =
      PMF.pure (ModuleSIS.encodeMatrix (0 : Matrix3)) ∧
    eval (sample (((1, 1), 1), 4, 1)) = PMF.pure (encList (encList encNat) [[0]]) ∧
    eval (sample (((2, 3), 0), 4, 3)) = PMF.pure [] ∧
    eval (sample (((2, 0), 1), 4, 3)) = PMF.pure (encList (encList encNat) [[], []]) := by
  obtain ⟨sample, hppt, hlaw⟩ := exists_isPPTOn_approximateEncodedModuleMatrix
  refine ⟨sample, hppt, ?_, ?_, ?_, ?_⟩
  · rw [(hlaw 1 1 2 0 3 (by decide)).1]
    simp only [width_zero_scalar, PMF.pure_map, Nat.cast_zero, pi_pure_const]
    exact PMF.pure_map _ _
  · rw [(hlaw 1 1 1 4 1 (by decide)).1]
    convert PMF.map_const
      (PMF.pi fun _ : Fin 1 => PMF.pi fun _ : Fin 1 => PMF.pi fun _ : Fin 1 =>
        (eval (sampleModNat 4 1)).map (Nat.cast : ℕ → ZMod 1))
      (encList (encList encNat) [[0]]) using 1
    congr 1
    funext A
    have hA : A = 0 := by
      ext i j l
      apply ZMod.val_injective 1
      have hlt := ZMod.val_lt (A i j l)
      change (A i j l).val = 0
      omega
    subst A
    decide
  · rw [(hlaw 2 3 0 4 3 (by decide)).1]
    convert PMF.map_const
      (PMF.pi fun _ : Fin 2 => PMF.pi fun _ : Fin 3 => PMF.pi fun _ : Fin 0 =>
        (eval (sampleModNat 4 3)).map (Nat.cast : ℕ → ZMod 3)) [] using 1
    congr 1
  · rw [(hlaw 2 0 1 4 3 (by decide)).1]
    convert PMF.map_const
      (PMF.pi fun _ : Fin 2 => PMF.pi fun _ : Fin 0 => PMF.pi fun _ : Fin 1 =>
        (eval (sampleModNat 4 3)).map (Nat.cast : ℕ → ZMod 3))
      (encList (encList encNat) [[], []]) using 1
    congr 1

end ComplexityTests.Crypto.ModuleMatrixApproximation
