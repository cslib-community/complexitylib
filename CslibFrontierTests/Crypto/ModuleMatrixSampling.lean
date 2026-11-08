/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.Module.MatrixSampling
import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption.Native
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! Actual structured expansion, exact sampling and conditional native key generation. -/

namespace CslibFrontierTests.Crypto.ModuleMatrixSampling

open Cslib Cslib.Crypto Probability ProbComp Turing.MultiTapeTM
open scoped Matrix

private def rectangular : Matrix (Fin 2) (Fin 1) (Fin 2 → ZMod 6) :=
  !![![1, 2]; ![3, 4]]

/-- A single implementation handles rectangular blocks, empty dimensions and binary moduli. -/
example : ∃ expand : ((((ℕ × ℕ) × ℕ) × ℕ) × List (List (List ℕ))) → List Bool,
    ComputableInPolyTime expand
      (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encNat)
        (encList (encList (encList encNat)))) encBits ∧
    expand ((((2, 1), 2), 6), [[[1, 2]], [[3, 4]]]) =
      encList (encList encNat) [[1, 4], [2, 1], [3, 2], [4, 3]] ∧
    expand ((((1, 2), 1), 1), [[[0], [0]]]) = encList (encList encNat) [[0, 0]] ∧
    expand ((((2, 3), 0), 6), [[[], [], []], [[], [], []]]) =
      encList (encList encNat) [] ∧
    expand ((((2, 0), 1), 6), [[], []]) = encList (encList encNat) [[], []] ∧
    expand ((((1, 1), 2), 2 ^ 128 + 1), [[[1, 2 ^ 128]]]) =
      encList (encList encNat) [[1, 1], [2 ^ 128, 1]] := by
  obtain ⟨expand, hnative, hexpand⟩ := exists_computableInPolyTime_encodeModuleMatrix
  refine ⟨expand, hnative, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hexpand 2 1 2 6 (by decide) rectangular
    convert h using 1 <;> congr 1
  · have h := hexpand 1 2 1 1 (by decide)
      (0 : Matrix (Fin 1) (Fin 2) (Fin 1 → ZMod 1))
    convert h using 1 <;> congr 1
  · have h := hexpand 2 3 0 6 (by decide)
      (0 : Matrix (Fin 2) (Fin 3) (Fin 0 → ZMod 6))
    convert h using 1 <;> congr 1
  · have h := hexpand 2 0 1 6 (by decide)
      (0 : Matrix (Fin 2) (Fin 0) (Fin 1 → ZMod 6))
    convert h using 1 <;> congr 1
  · have h := hexpand 1 1 2 (2 ^ 128 + 1) (by decide)
      (!![![1, -1]] : Matrix (Fin 1) (Fin 1) (Fin 2 → ZMod (2 ^ 128 + 1)))
    convert h using 1 <;> congr 1

private def nonrotation : Matrix (Fin 2) (Fin 2) (ZMod 4) := !![0, 0; 0, 1]

private theorem nonrotation_not_encoded
    (A : Matrix (Fin 1) (Fin 1) (Fin 2 → ZMod 4)) :
    ModuleSIS.encodeMatrix A ≠ GeneralSIS.encodeMatrix nonrotation := by
  intro h
  have hrows := (encList (encList encNat)).injective h
  have h00 := congrArg (fun rows : List (List ℕ) => (rows.getD 0 []).getD 0 0) hrows
  have h11 := congrArg (fun rows : List (List ℕ) => (rows.getD 1 []).getD 1 0) hrows
  change (expandModuleMatrix A 0 0).val = 0 at h00
  change (expandModuleMatrix A 1 1).val = 1 at h11
  have hd : (expandModuleMatrix A 0 0).val = (expandModuleMatrix A 1 1).val := rfl
  omega

/-- The actual sampler has signed rotation blocks and excludes a positive scalar-uniform event. -/
example : ∃ sample : (((ℕ × ℕ) × ℕ) × ℕ) → ProbComp (List Bool),
    IsPPTOn (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encBits sample ∧
    GeneralSIS.encodeMatrix (!![1, 3; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod 4)) ∈
      (ProbComp.eval (sample (((1, 1), 2), 2))).support ∧
    (ProbComp.eval (sample (((1, 1), 2), 2))) (GeneralSIS.encodeMatrix nonrotation) = 0 ∧
    GeneralSIS.encodeMatrix nonrotation ∈
      ((PMF.uniformOfFintype (Matrix (Fin 2) (Fin 2) (ZMod 4))).map
        GeneralSIS.encodeMatrix).support := by
  obtain ⟨sample, hppt, hlaw⟩ := exists_isPPTOn_sampleEncodedModuleMatrix
  refine ⟨sample, hppt, ?_, ?_, ?_⟩
  · rw [hlaw, PMF.mem_support_map_iff]
    refine ⟨!![![1, 1]], PMF.mem_support_uniformOfFintype _, ?_⟩
    decide
  · rw [hlaw, PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
    rintro ⟨A, _, h⟩
    exact nonrotation_not_encoded A h
  · exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨nonrotation, PMF.mem_support_uniformOfFintype _, rfl⟩

/-- The same sampler law covers width zero and zero polynomial degree. -/
example : ∃ sample : (((ℕ × ℕ) × ℕ) × ℕ) → ProbComp (List Bool),
    IsPPTOn (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encBits sample ∧
    ProbComp.eval (sample (((1, 2), 1), 0)) =
      PMF.pure (encList (encList encNat) [[0, 0]]) ∧
    ProbComp.eval (sample (((2, 3), 0), 5)) = PMF.pure [] := by
  obtain ⟨sample, hppt, hlaw⟩ := exists_isPPTOn_sampleEncodedModuleMatrix
  refine ⟨sample, hppt, ?_, ?_⟩
  · rw [hlaw]
    convert PMF.map_const (PMF.uniformOfFintype
      (Matrix (Fin 1) (Fin 2) (Fin 1 → ZMod (2 ^ 0))))
      (encList (encList encNat) [[0, 0]]) using 1
    congr 1
    funext A
    have : A = 0 := by
      ext i j l
      exact (ZMod.val_injective 1) (by
        have hv := ZMod.val_lt (A i j l)
        simpa using Nat.eq_zero_of_le_zero (by omega : (A i j l).val ≤ 0))
    subst A
    decide
  · rw [hlaw]
    convert PMF.map_const (PMF.uniformOfFintype
      (Matrix (Fin 2) (Fin 3) (Fin 0 → ZMod (2 ^ 5)))) [] using 1
    congr 1

/-- The sampled encoded matrix feeds the same obtained native key generator, with actual
nonzero signed secret and error inputs. This is a conditional law, not full random key sampling. -/
example : ∃ sample run,
    IsPPTOn (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encBits sample ∧
    ComputableInPolyTime run
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair encBits (encPair encBits encBits))) encBits ∧
    IsPPTOn
      (encPair (encPair (encPair encUnary encUnary) encUnary) (encPair encBits encBits)) encBits
      (fun p : ((ℕ × ℕ) × ℕ) × List Bool × List Bool => do
        let word ← sample (((p.1.1.1, p.1.1.1), p.1.1.2), p.1.2)
        return run ((p.1.1, 2 ^ p.1.2), (word, p.2.1, p.2.2))) ∧
    ProbComp.eval (do
      let word ← sample (((1, 1), 2), 2)
      return run (((1, 2), 4), (word,
        (ModuleSIS.encodeVec (![![-1, 2]]), ModuleSIS.encodeVec (![![1, -1]]))))) =
      (PMF.uniformOfFintype (Matrix (Fin 1) (Fin 1) (Fin 2 → ZMod 4))).map
        (fun A => ModuleLWE.encodeSample (moduleLWEKeyGen A
          (fun j i => ((![![-1, 2]] : Fin 1 → Fin 2 → ℤ) j i : ZMod 4))
          (fun j i => ((![![1, -1]] : Fin 1 → Fin 2 → ℤ) j i : ZMod 4)))) := by
  obtain ⟨sample, hppt, hlaw⟩ := exists_isPPTOn_sampleEncodedModuleMatrix
  obtain ⟨run, hnative, hrun⟩ := exists_computableInPolyTime_moduleLWEKeyGen
  have hprepare : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × List Bool × List Bool =>
        (((p.1.1.1, p.1.1.1), p.1.1.2), p.1.2))
      (encPair (encPair (encPair encUnary encUnary) encUnary) (encPair encBits encBits))
      (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) := by fun_prop
  have hcallback : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × ℕ) × List Bool × List Bool) × List Bool =>
        ((p.1.1.1, 2 ^ p.1.1.2), (p.2, p.1.2.1, p.1.2.2)))
      (encPair
        (encPair (encPair (encPair encUnary encUnary) encUnary) (encPair encBits encBits)) encBits)
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair encBits (encPair encBits encBits))) := by fun_prop
  refine ⟨sample, run, hppt, hnative, ?_, ?_⟩
  · simpa only [bind_pure_comp] using
      (hppt.preprocess hprepare).map_with (hnative.comp hcallback)
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure, hlaw, PMF.bind_map]
    change (PMF.uniformOfFintype (Matrix (Fin 1) (Fin 1) (Fin 2 → ZMod 4))).map
      (fun A => run (((1, 2), 4), (ModuleSIS.encodeMatrix A,
        (ModuleSIS.encodeVec (![![-1, 2]]), ModuleSIS.encodeVec (![![1, -1]]))))) = _
    congr 1
    funext A
    exact hrun 1 2 4 (by decide) A (![![-1, 2]]) (![![1, -1]])

end CslibFrontierTests.Crypto.ModuleMatrixSampling
