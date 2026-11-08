/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption.Sampling.Native
import CslibFrontier.Languages.Probabilistic.Vector

/-! Joint secret/public-key laws of the actual native randomized key generator. -/

namespace ComplexityTests.Crypto.ModuleKeyGenJoint

open Cslib Cslib.Crypto Probability ProbComp Interactive Turing.MultiTapeTM
open scoped Matrix ENNReal

private abbrev Matrix3 := Matrix (Fin 1) (Fin 1) (Fin 1 → ZMod 3)

private def output (z : ℤ) (a e : ZMod 3) : List Bool × List Bool :=
  (ModuleSIS.encodeVec (![![z]]), ModuleLWE.encodeSample
    (moduleLWEKeyGen (!![![a]]) (![![(z : ZMod 3)]]) (![![e]])))

private theorem output_eq_iff (z : ℤ) (a e : ZMod 3) :
    output (-1) 1 1 = output z a e ↔ z = -1 ∧ a = 1 ∧ e = 1 := by
  constructor
  · intro h
    have hs := (encList encIntBin).injective (congrArg Prod.fst h)
    change [-1] = [z] at hs
    have hz : z = -1 := (List.cons.inj hs).1.symm
    subst z
    have hp := (encPair encBits (encList encNat)).injective (congrArg Prod.snd h)
    have ha := (encList (encList encNat)).injective (congrArg Prod.fst hp)
    change [[1]] = [[a.val]] at ha
    have hva : a.val = 1 := (List.cons.inj (List.cons.inj ha).1).1.symm
    have hae : a = 1 := ZMod.val_injective 3 hva
    subst a
    have hb := congrArg Prod.snd hp
    change [0] = [((1 : ZMod 3) * (-1) + e).val] at hb
    have hbe : (1 : ZMod 3) * (-1) + e = 0 :=
      ZMod.val_injective 3 (List.cons.inj hb).1.symm
    refine ⟨rfl, rfl, ?_⟩
    linear_combination hbe
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private theorem singleton_rows_eval (η : ℕ) :
    eval (OracleComp.replicateFin 1 (OracleComp.replicateFin 1 (sampleCenteredBinomial η))) =
      (eval (sampleCenteredBinomial η)).map (fun z => (![![z]] : Fin 1 → Fin 1 → ℤ)) := by
  simp only [OracleComp.replicateFin_succ, OracleComp.replicateFin_zero,
    eval_bind, eval_map, eval_pure, PMF.bind_bind, PMF.pure_bind,
    PMF.map, Function.comp_def]
  congr 1

private theorem cbd_one_neg_mass : eval (sampleCenteredBinomial 1) (-1) = 1 / 4 := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (by finiteness)).mp
  rw [eval_sampleCenteredBinomial]
  norm_num [BitString.uniformList_succ, BitString.uniformList_zero, PMF.bind_apply,
    tsum_fintype, PMF.uniformOfFintype_apply]

private theorem cbd_one_mod_mass :
    ((eval (sampleCenteredBinomial 1)).map (Int.cast : ℤ → ZMod 3)) 1 = 1 / 4 := by
  have hneq : (1 : ZMod 3) ≠ -1 := by decide
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (by finiteness)).mp
  rw [eval_sampleCenteredBinomial]
  norm_num [BitString.uniformList_succ, BitString.uniformList_zero, PMF.map_bind,
    PMF.bind_apply, tsum_fintype, PMF.uniformOfFintype_apply, hneq]

private theorem modNat_three_one_mass :
    ((eval (sampleModNat 4 3)).map (Nat.cast : ℕ → ZMod 3)) 1 = 5 / 16 := by
  rw [eval_sampleModNat, PMF.map_comp]
  change ((PMF.uniformOfFintype (Fin 16)).map
    (fun i => ((i.val % 3 : ℕ) : ZMod 3))) 1 = _
  have heq (i : Fin 16) : (1 : ZMod 3) = ((i.val % 3 : ℕ) : ZMod 3) ↔ i.val % 3 = 1 := by
    rw [← (ZMod.val_injective 3).eq_iff]
    rw [ZMod.val_natCast, Nat.mod_mod]
    change (1 = i.val % 3 ↔ i.val % 3 = 1)
    exact eq_comm
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (by finiteness)).mp
  simp only [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply, heq]
  norm_num [Fin.sum_univ_succ, ENNReal.toReal_add]

private theorem pi_singleton {α : Type} [Finite α] (μ : PMF α) :
    (PMF.pi fun _ : Fin 1 => μ) = μ.map (fun x => (![x] : Fin 1 → α)) := by
  rw [← PMF.iid_eq_pi]
  simp only [PMF.iid, PMF.monad_bind_eq_bind, PMF.pure_bind, PMF.map, Function.comp_def]
  congr 1

private theorem matrix_singleton (μ : PMF (ZMod 3)) :
    (PMF.pi fun _ : Fin 1 => PMF.pi fun _ : Fin 1 => PMF.pi fun _ : Fin 1 => μ) =
      μ.map (fun a => (!![![a]] : Matrix3)) := by
  simp only [pi_singleton, PMF.map_comp, Function.comp_def]
  congr 1

private theorem joint_mass (μ : PMF (ZMod 3)) :
    (do
      let z ← eval (sampleCenteredBinomial 1)
      let a ← μ
      let e ← (eval (sampleCenteredBinomial 1)).map (Int.cast : ℤ → ZMod 3)
      return output z a e) (output (-1) 1 1) = (1 / 4) * μ 1 * (1 / 4) := by
  classical
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_apply,
    PMF.pure_apply, output_eq_iff]
  simp only [ite_and, mul_ite, mul_zero]
  rw [tsum_eq_single (-1)]
  · rw [tsum_eq_single 1]
    · simp only [ite_true, mul_one, tsum_ite_eq, cbd_one_neg_mass, cbd_one_mod_mass, mul_assoc]
    · intro a ha
      simp [ha]
  · intro z hz
    simp [hz]


private theorem cast_singleton (z : ℤ) :
    (fun j i => ((![![z]] : Fin 1 → Fin 1 → ℤ) j i : ZMod 3)) = ![![(z : ZMod 3)]] := by
  ext j i
  fin_cases j
  fin_cases i
  rfl

private theorem source_joint_eq (μ : PMF (ZMod 3)) :
    (do
      let z ← eval (OracleComp.replicateFin 1
        (OracleComp.replicateFin 1 (sampleCenteredBinomial 1)))
      let A ← PMF.pi fun _ : Fin 1 => PMF.pi fun _ : Fin 1 => PMF.pi fun _ : Fin 1 => μ
      let e ← eval (OracleComp.replicateFin 1
        (OracleComp.replicateFin 1 (sampleCenteredBinomial 1)))
      return (ModuleSIS.encodeVec z, ModuleLWE.encodeSample
        (moduleLWEKeyGen A (fun j i => (z j i : ZMod 3)) (fun j i => (e j i : ZMod 3))))) =
    (do
      let z ← eval (sampleCenteredBinomial 1)
      let a ← μ
      let e ← (eval (sampleCenteredBinomial 1)).map (Int.cast : ℤ → ZMod 3)
      return output z a e) := by
  simp only [singleton_rows_eval, matrix_singleton, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_map, Function.comp_def, cast_singleton, output]
  congr 1
  funext z
  change ((μ.map (fun a => (!![![a]] : Matrix3))).bind
    (fun A : Matrix3 => (eval (sampleCenteredBinomial 1)).bind fun e =>
      PMF.pure (ModuleSIS.encodeVec (![![z]]), ModuleLWE.encodeSample
        (moduleLWEKeyGen A (![![(z : ZMod 3)]]) (![![(e : ZMod 3)]]))))) = _
  rw [PMF.bind_map]
  rfl

private theorem ideal_joint_eq :
    (do
      let z ← eval (OracleComp.replicateFin 1
        (OracleComp.replicateFin 1 (sampleCenteredBinomial 1)))
      let pk ← moduleLWEPublicKeyLaw 1 1 3
        ((eval (OracleComp.replicateFin 1 (sampleCenteredBinomial 1))).map
          (fun (z : Fin 1 → ℤ) i => (z i : ZMod 3))) (PMF.pure (fun j i => (z j i : ZMod 3)))
      return (ModuleSIS.encodeVec z, ModuleLWE.encodeSample pk)) =
    (do
      let z ← eval (sampleCenteredBinomial 1)
      let a ← PMF.uniformOfFintype (ZMod 3)
      let e ← (eval (sampleCenteredBinomial 1)).map (Int.cast : ℤ → ZMod 3)
      return output z a e) := by
  have he : (PMF.pi fun _ : Fin 1 =>
      (eval (OracleComp.replicateFin 1 (sampleCenteredBinomial 1))).map
        (fun z i => (z i : ZMod 3))) =
      (eval (OracleComp.replicateFin 1 (OracleComp.replicateFin 1
        (sampleCenteredBinomial 1)))).map (fun e j i => (e j i : ZMod 3)) := by
    simpa only [eval_replicateFin, eval_map] using
      eval_replicateFin_map_coords 1 (OracleComp.replicateFin 1 (sampleCenteredBinomial 1))
        (fun z i => (z i : ZMod 3))
  have hu : PMF.uniformOfFintype Matrix3 =
      (PMF.pi fun _ : Fin 1 => PMF.pi fun _ : Fin 1 => PMF.pi fun _ : Fin 1 =>
        PMF.uniformOfFintype (ZMod 3)) := by
    simp only [PMF.pi_uniformOfFintype]
    congr 1
  simp only [moduleLWEPublicKeyLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.pure_bind, PMF.bind_bind, he, PMF.bind_map, Function.comp_def]
  rw [hu]
  have h := source_joint_eq (PMF.uniformOfFintype (ZMod 3))
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map,
    Function.comp_def] at h
  convert h using 1
  congr 1

/-- The ideal joint event retains secret `-1`; its public key has `A=1,b=0`, forcing error `1`. -/
example : (do
    let z ← eval (OracleComp.replicateFin 1 (OracleComp.replicateFin 1 (sampleCenteredBinomial 1)))
    let pk ← moduleLWEPublicKeyLaw 1 1 3
      ((eval (OracleComp.replicateFin 1 (sampleCenteredBinomial 1))).map
        (fun (z : Fin 1 → ℤ) i => (z i : ZMod 3))) (PMF.pure (fun j i => (z j i : ZMod 3)))
    return (ModuleSIS.encodeVec z, ModuleLWE.encodeSample pk)) (output (-1) 1 1) =
      (1 / 48 : ℝ≥0∞) := by
  rw [ideal_joint_eq, joint_mass, PMF.uniformOfFintype_apply]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

private theorem modNat_one_cast (width : ℕ) :
    (eval (sampleModNat width 1)).map (Nat.cast : ℕ → ZMod 1) = PMF.pure 0 := by
  convert PMF.map_const (eval (sampleModNat width 1)) (0 : ZMod 1) using 1
  congr 1
  funext z
  apply ZMod.val_injective 1
  have hz := ZMod.val_lt (z : ZMod 1)
  change (z : ZMod 1).val = 0
  omega

/-- The same native witness has actual joint event mass `5/256`, different from ideal `1/48`. -/
example : ∃ generate : (((ℕ × ℕ) × ℕ × ℕ) × ℕ × ℕ) → ProbComp (List Bool × List Bool),
    IsPPTOn
      (encPair (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))
        (encPair encUnary encNat)) (encPair encBits encBits) generate ∧
    eval (generate (((1, 1), 1, 1), 2, 3)) (output (-1) 1 1) = 5 / 256 ∧
    (eval (generate (((1, 1), 1, 1), 2, 3)) (output (-1) 1 1)).toReal =
      1 / 48 - 1 / 768 ∧
    eval (generate (((1, 1), 0, 0), 0, 1)) = PMF.pure
      (ModuleSIS.encodeVec (0 : Fin 1 → Fin 1 → ℤ),
        ModuleLWE.encodeSample (0 : ModuleLWEPublicKey 1 1 1)) ∧
    eval (generate (((0, 2), 1, 1), 0, 3)) = PMF.pure
      (ModuleSIS.encodeVec (0 : Fin 0 → Fin 2 → ℤ),
        ModuleLWE.encodeSample (0 : ModuleLWEPublicKey 0 2 3)) ∧
    eval (generate (((2, 0), 1, 1), 0, 3)) = PMF.pure
      (ModuleSIS.encodeVec (0 : Fin 2 → Fin 0 → ℤ),
        ModuleLWE.encodeSample (0 : ModuleLWEPublicKey 2 0 3)) ∧
    CloseTo
      ((moduleLWEPublicKeyLaw 2 2 (2 ^ 128 + 1)
        ((eval (OracleComp.replicateFin 2 (sampleCenteredBinomial 1))).map
          (fun (z : Fin 2 → ℤ) i => (z i : ZMod (2 ^ 128 + 1))))
        ((eval (OracleComp.replicateFin 2 (OracleComp.replicateFin 2
          (sampleCenteredBinomial 1)))).map
            (fun z j i => (z j i : ZMod (2 ^ 128 + 1))))).map ModuleLWE.encodeSample)
      ((eval (generate (((2, 2), 1, 1), 4, 2 ^ 128 + 1))).map Prod.snd) (1 / 2) := by
  obtain ⟨generate, hppt, hlaw⟩ := exists_isPPTOn_moduleLWEKeyGenJoint
  have hactual := (hlaw 1 1 1 1 2 3 (by decide)).1
  have hmass : eval (generate (((1, 1), 1, 1), 2, 3)) (output (-1) 1 1) = 5 / 256 := by
    rw [hactual, source_joint_eq, joint_mass]
    change (1 / 4 : ℝ≥0∞) *
      ((eval (sampleModNat 4 3)).map (Nat.cast : ℕ → ZMod 3)) 1 * (1 / 4) = _
    rw [modNat_three_one_mass]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  refine ⟨generate, hppt, hmass, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmass]
    norm_num
  · have h := (hlaw 1 1 0 0 0 1 (by decide)).1
    simp only [singleton_rows_eval] at h
    simp only [sampleCenteredBinomial_zero, eval_pure, PMF.pure_map,
      modNat_one_cast, pi_singleton, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.pure_bind] at h
    convert h using 1
    congr 1
  · have h := (hlaw 0 2 1 1 0 3 (by decide)).1
    simp only [OracleComp.replicateFin_zero, eval_pure, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.pure_bind] at h
    rw [h]
    change (PMF.map (fun _ => _) _) = _
    convert PMF.map_const
      (PMF.pi fun _ : Fin 0 => PMF.pi fun _ : Fin 0 => PMF.pi fun _ : Fin 2 =>
        (eval (sampleModNat (Nat.size 3) 3)).map (Nat.cast : ℕ → ZMod 3))
      (ModuleSIS.encodeVec (0 : Fin 0 → Fin 2 → ℤ),
        ModuleLWE.encodeSample (0 : ModuleLWEPublicKey 0 2 3)) using 1
    congr 1
  · have h := (hlaw 2 0 1 1 0 3 (by decide)).1
    simp only [OracleComp.replicateFin_zero] at h
    simp only [OracleComp.replicateFin_eq_pi, eval_pi_pure, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.pure_bind] at h
    rw [h]
    change (PMF.map (fun _ => _) _) = _
    convert PMF.map_const
      (PMF.pi fun _ : Fin 2 => PMF.pi fun _ : Fin 2 => PMF.pi fun _ : Fin 0 =>
        (eval (sampleModNat (Nat.size 3) 3)).map (Nat.cast : ℕ → ZMod 3))
      (ModuleSIS.encodeVec (0 : Fin 2 → Fin 0 → ℤ),
        ModuleLWE.encodeSample (0 : ModuleLWEPublicKey 2 0 3)) using 1
    congr 1
  · convert (hlaw 2 2 1 1 4 (2 ^ 128 + 1) (by decide)).2.2 using 1
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num

end ComplexityTests.Crypto.ModuleKeyGenJoint
