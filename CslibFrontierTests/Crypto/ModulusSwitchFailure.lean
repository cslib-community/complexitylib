/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.ModulusSwitch.Failure
import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption.Sampling
import CslibFrontier.Probability.PMF.Uniform

/-! Actual sampled switching: zero failure, a nonzero CBD tail and a supported failure. -/

namespace CslibFrontierTests.Crypto.ModulusSwitchFailure

open Cslib Cslib.Crypto Probability ProbComp
open scoped Matrix ENNReal

private noncomputable def noise (η : ℕ) : PMF (Fin 1 → ZMod 32) :=
  PMF.pi fun _ => LWE.noiseLaw 5 η

private noncomputable def secrets : PMF (Fin 1 → Fin 1 → ZMod 32) := PMF.pi fun _ => noise 1

private noncomputable def sampledView (η : ℕ) := do
  let s ← secrets
  let view ← encryptionViewOfKeyLaw
    (moduleLWEPublicKeyLaw 1 1 32 (noise η) (PMF.pure s)) (noise η) ![true] secrets
  pure (s, view)

private def failure : Set ((Fin 1 → Fin 1 → ZMod 32) ×
    (ModuleLWEPublicKey 1 1 32 × ModuleLWECiphertext 1 1 32)) :=
  {out | moduleLWEDecrypt
    (fun j i => (SIS.liftCentered (out.1 j) i : ZMod 16))
    (moduleLWEModulusSwitch 16 out.2.2) ≠ ![true]}

private theorem secrets_bound {s} (hs : s ∈ secrets.support) :
    ModuleSIS.inInfNormBound 1 s :=
  moduleLWECenteredBinomial_inInfNormBound (by decide) hs

private theorem noise_eq_map (η : ℕ) :
    noise η = (LWE.noiseLaw 5 η).map (fun z => ![z]) := by
  have h := congrArg (fun law : PMF (ZMod 32) => law.map (fun z => ![z]))
    (PMF.pi_map_eval (fun _ : Fin 1 => LWE.noiseLaw 5 η) 0)
  rw [PMF.map_comp] at h
  have hid : (fun f : Fin 1 → ZMod 32 => ![f 0]) = id := by
    funext f i
    fin_cases i
    rfl
  change (noise η).map (fun f => ![f 0]) = _ at h
  rw [hid, PMF.map_id] at h
  exact h

private theorem noise_one_tail :
    (noise 1).toOuterMeasure {e | ¬ SIS.inInfNormBound 1 e} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro e he hbad
  apply hbad
  have h := (PMF.mem_support_pi_iff _ _).mp he
  intro i
  obtain ⟨z, hz, hzi⟩ := (PMF.mem_support_map_iff _ _ _).mp (h i)
  have hb := (mem_support_sampleCenteredBinomial_iff 1 z).mp hz
  have hlift : (z : ZMod 32).valMinAbs = z := by
    rw [ZMod.valMinAbs_spec]
    exact ⟨rfl, by omega, by omega⟩
  rw [← hzi, hlift, Int.abs_eq_natAbs]
  exact_mod_cast hb

private theorem noise_two_tail :
    (noise 2).toOuterMeasure {e | ¬ SIS.inInfNormBound 1 e} = (1 / 8 : ℝ≥0∞) := by
  classical
  rw [noise_eq_map, LWE.noiseLaw, eval_sampleCenteredBinomial_eq_map]
  simp only [PMF.map_comp, BitString.uniformList, PMF.toOuterMeasure_map_apply]
  rw [PMF.toOuterMeasure_uniformOfFintype]
  have hc : (Finset.univ.filter (fun bits : Fin 4 → Bool =>
      ¬ SIS.inInfNormBound 1
        (![((((List.ofFn bits).take 2).count true : ℤ) -
          ((List.ofFn bits).drop 2).count true : ZMod 32)]))).card = 2 := by decide
  change (↑(Finset.univ.filter _).card : ℝ≥0∞) / Fintype.card (Fin 4 → Bool) = _
  simp only [Function.comp_apply, Set.mem_preimage, Set.mem_ofPred_eq, Int.cast_sub,
    Int.cast_natCast] at *
  rw [hc]
  change (2 : ℝ≥0∞) / 16 = 1 / 8
  rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The actual native small-secret law with width-one errors has zero switched failure. -/
example : (sampledView 1).toOuterMeasure failure = 0 := by
  unfold sampledView failure
  apply le_antisymm _ zero_le
  have h := toOuterMeasure_moduleLWEModulusSwitch_failure_le
    (k := 1) (n := 1) (q := 32) (p := 16) (Bs := 1) (Br := 1) (Be := 1) (Bp := 3)
    (by decide) (noise 1) ![true] secrets secrets
    (fun _ => secrets_bound) (fun _ => secrets_bound) (by norm_num)
  simpa only [noise_one_tail, mul_zero] using h

/-- A positive noise tail gives a nontrivial upper bound for the same actual experiment. -/
example : (sampledView 2).toOuterMeasure failure ≤ (3 / 8 : ℝ≥0∞) := by
  unfold sampledView failure
  have h := toOuterMeasure_moduleLWEModulusSwitch_failure_le
    (k := 1) (n := 1) (q := 32) (p := 16) (Bs := 1) (Br := 1) (Be := 1) (Bp := 3)
    (by decide) (noise 2) ![true] secrets secrets
    (fun _ => secrets_bound) (fun _ => secrets_bound) (by norm_num)
  norm_num only [noise_two_tail] at h
  simpa only [mul_one_div] using h

private theorem mem_noise (η : ℕ) (z : ℤ) (hz : z.natAbs ≤ η) :
    (![z] : Fin 1 → ZMod 32) ∈ (noise η).support := by
  rw [noise, PMF.mem_support_pi_iff]
  intro i
  fin_cases i
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨z, (mem_support_sampleCenteredBinomial_iff η z).mpr hz, rfl⟩

private theorem mem_secrets (z : ℤ) (hz : z.natAbs ≤ 1) :
    (![![z]] : Fin 1 → Fin 1 → ZMod 32) ∈ secrets.support := by
  rw [secrets, PMF.mem_support_pi_iff]
  intro j
  fin_cases j
  exact mem_noise 1 z hz

private def key : ModuleLWEPublicKey 1 1 32 :=
  moduleLWEKeyGen (!![![1]]) (![![-1]]) (![![2]])

private def ciphertext : ModuleLWECiphertext 1 1 32 :=
  moduleLWEEncrypt key (![![1]]) (![![2]]) (![2]) ![true]

private theorem switched_ciphertext :
    moduleLWEModulusSwitch 16 ciphertext = (![![2]], ![10]) := by
  have hct : ciphertext = (![![3]], ![19]) := by decide
  rw [hct]
  apply Prod.ext
  · ext j i
    fin_cases j
    fin_cases i
    norm_num [moduleLWEModulusSwitch, ZMod.modulusSwitch, round_eq,
      show (3 : ZMod 32).valMinAbs = 3 by decide]
  · ext i
    fin_cases i
    norm_num [moduleLWEModulusSwitch, ZMod.modulusSwitch, round_eq,
      show (19 : ZMod 32).valMinAbs = -13 by decide]
    decide

/-- The supported width-two error witness reaches the exact target decoder threshold. -/
example : (moduleLWEModulusSwitch 16 ciphertext).2 -
    innerPoly (moduleLWEModulusSwitch 16 ciphertext).1 (![![-1]]) = ![12] := by
  rw [switched_ciphertext]
  decide

private theorem witness_support :
    ((![![-1]], (key, ciphertext)) : (Fin 1 → Fin 1 → ZMod 32) ×
      (ModuleLWEPublicKey 1 1 32 × ModuleLWECiphertext 1 1 32)) ∈ (sampledView 2).support := by
  have hsneg : (![![-1]] : Fin 1 → Fin 1 → ZMod 32) ∈ secrets.support := by
    simpa using mem_secrets (-1) (by decide)
  have hspos : (![![1]] : Fin 1 → Fin 1 → ZMod 32) ∈ secrets.support := by
    simpa using mem_secrets 1 (by decide)
  have he : (![2] : Fin 1 → ZMod 32) ∈ (noise 2).support := by
    simpa using mem_noise 2 2 (by decide)
  simp only [sampledView, encryptionViewOfKeyLaw, moduleLWEPublicKeyLaw,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.bind_bind,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  refine ⟨![![-1]], hsneg, ?_⟩
  refine ⟨!![![1]], PMF.mem_support_uniformOfFintype _, ?_⟩
  refine ⟨![![2]], ?_, ?_⟩
  · rw [PMF.mem_support_pi_iff]
    intro j
    fin_cases j
    exact he
  refine ⟨![![1]], hspos, ?_⟩
  refine ⟨![2], he, ?_⟩
  refine ⟨![![2]], ?_, rfl⟩
  all_goals
    rw [PMF.mem_support_pi_iff]
    intro j
    fin_cases j
    exact he

/-- Positive actual failure accompanies the strict upper bound; the event is not empty. -/
example : 0 < ((sampledView 2).toOuterMeasure failure).toReal := by
  rw [PMF.toOuterMeasure_toReal_pos_iff]
  refine ⟨(![![-1]], (key, ciphertext)), ?_, witness_support⟩
  change moduleLWEDecrypt
    (fun j i => (SIS.liftCentered ((![![-1]] : Fin 1 → Fin 1 → ZMod 32) j) i :
      ZMod 16)) (moduleLWEModulusSwitch 16 ciphertext) ≠ ![true]
  rw [switched_ciphertext]
  decide

end CslibFrontierTests.Crypto.ModulusSwitchFailure
