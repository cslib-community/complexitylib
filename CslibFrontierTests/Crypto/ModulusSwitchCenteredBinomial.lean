/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.ModulusSwitch.CenteredBinomial
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption.Sampling
import CslibFrontier.Probability.PMF.Uniform

/-! Growing sampled switching: the smallest parameter has supported positive failure. -/

namespace ComplexityTests.Crypto.ModulusSwitchCenteredBinomial

open Cslib Cslib.Crypto Probability ProbComp
open scoped Matrix ENNReal

example : moduleLWECBDRadius 1 = 7 := by decide
example : moduleLWECBDWidth 1 = 5 := by decide

example (l : ℕ) : 2 ^ (moduleLWECBDWidth (l + 1) + 1) ≤ 136 * (l + 1) ^ 3 :=
  moduleLWECBD_sourceModulus_le (by omega)

open Turing.MultiTapeTM in
example : IsPPTOn encUnary (encList (encList encIntBin))
    (fun l : ℕ => OracleComp.replicate (l + 1)
      (OracleComp.replicate (l + 1) (sampleCenteredBinomial (8 * (l + 1))))) := by
  fun_prop

open Turing.MultiTapeTM in
example : IsPPTOn encUnary (encList encNat)
    (fun l : ℕ => OracleComp.replicate ((l + 1) ^ 3)
      (sampleBinaryNat (moduleLWECBDWidth (l + 1) + 1))) := by
  have hw : ComputableInPolyTime (fun l : ℕ => moduleLWECBDWidth (l + 1))
      encUnary encUnary := computableInPolyTime_moduleLWECBDWidth.comp (by fun_prop)
  fun_prop

/-- The growing integer rows have exactly the modular law used for sampled error vectors. -/
example (l : ℕ) :
    (eval (OracleComp.replicateFin (l + 1)
      (OracleComp.replicateFin (l + 1) (sampleCenteredBinomial (8 * (l + 1)))))).map
        (fun values j i => (values j i : ZMod (2 ^ (moduleLWECBDWidth (l + 1) + 1)))) =
      PMF.pi (fun _ : Fin (l + 1) => PMF.pi (fun _ : Fin (l + 1) =>
        Homomorphic.GSW.noiseLaw (moduleLWECBDWidth (l + 1) + 1) (8 * (l + 1)))) :=
  eval_moduleLWECenteredBinomial_mod _ _ _ _

/-- Power-of-two matrix entries use the exact finite uniform law, not arbitrary uniform sampling. -/
example (l : ℕ) : eval (sampleBinaryNat (moduleLWECBDWidth (l + 1) + 1)) =
    (PMF.uniformOfFintype (Fin (2 ^ (moduleLWECBDWidth (l + 1) + 1)))).map Fin.val :=
  eval_sampleBinaryNat _

/-- The displayed bound is already nontrivial at the concrete growing dimension ten. -/
example : 4 * (2 * (10 : ℝ) + 1) * 10 * Real.exp (-10) < 1 := by
  rw [Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos 10)]
  have h : (2 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 :=
    pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
  rw [← Real.exp_nat_mul] at h
  norm_num at h ⊢
  linarith

private noncomputable def noise (η : ℕ) : PMF (Fin 1 → ZMod 64) :=
  PMF.pi fun _ => Homomorphic.GSW.noiseLaw 6 η

private noncomputable def secrets : PMF (Fin 1 → Fin 1 → ZMod 64) := PMF.pi fun _ => noise 1

private noncomputable def sampledView (η : ℕ) := do
  let s ← secrets
  let view ← encryptionViewOfKeyLaw
    (moduleLWEPublicKeyLaw 1 1 64 (noise η) (PMF.pure s)) (noise η) ![true] secrets
  pure (s, view)

private def failure : Set ((Fin 1 → Fin 1 → ZMod 64) ×
    (ModuleLWEPublicKey 1 1 64 × ModuleLWECiphertext 1 1 64)) :=
  {out | moduleLWEDecrypt
    (fun j i => (GeneralSIS.liftCentered (out.1 j) i : ZMod 32))
    (moduleLWEModulusSwitch 32 out.2.2) ≠ ![true]}

/-- The supported witness below belongs to exactly the first member of the proved family. -/
example : (sampledView 8).toOuterMeasure failure ≤ ENNReal.ofReal (12 * Real.exp (-1)) := by
  have h := toOuterMeasure_moduleLWECBD_switch_failure_le 0 ![true]
  dsimp [moduleLWECBDWidth, moduleLWECBDRadius] at h
  erw [show Nat.size 30 = 5 by decide, show (5 + 1 : ℕ) = 6 by decide] at h
  norm_num only at h
  unfold sampledView noise secrets failure
  with_unfolding_all exact h

private theorem mem_noise (η : ℕ) (z : ℤ) (hz : z.natAbs ≤ η) :
    (![z] : Fin 1 → ZMod 64) ∈ (noise η).support := by
  rw [noise, PMF.mem_support_pi_iff]
  intro i
  fin_cases i
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨z, (mem_support_sampleCenteredBinomial_iff η z).mpr hz, rfl⟩

private theorem mem_secrets (z : ℤ) (hz : z.natAbs ≤ 1) :
    (![![z]] : Fin 1 → Fin 1 → ZMod 64) ∈ secrets.support := by
  rw [secrets, PMF.mem_support_pi_iff]
  intro j
  fin_cases j
  exact mem_noise 1 z hz

private def key : ModuleLWEPublicKey 1 1 64 :=
  moduleLWEKeyGen (!![![1]]) (![![-1]]) (![![8]])

private def ciphertext : ModuleLWECiphertext 1 1 64 :=
  moduleLWEEncrypt key (![![1]]) (![![8]]) (![8]) ![true]

private theorem switched_ciphertext :
    moduleLWEModulusSwitch 32 ciphertext = (![![5]], ![24]) := by
  have hct : ciphertext = (![![9]], ![47]) := by decide
  rw [hct]
  apply Prod.ext
  · ext j i
    fin_cases j
    fin_cases i
    norm_num [moduleLWEModulusSwitch, ZMod.modulusSwitch, round_eq,
      show (9 : ZMod 64).valMinAbs = 9 by decide]
  · ext i
    fin_cases i
    norm_num [moduleLWEModulusSwitch, ZMod.modulusSwitch, round_eq,
      show (47 : ZMod 64).valMinAbs = -17 by decide]
    decide

/-- The smallest family member has a supported error witness outside the target decoding region. -/
example : (moduleLWEModulusSwitch 32 ciphertext).2 -
    innerPoly (moduleLWEModulusSwitch 32 ciphertext).1 (![![-1]]) = ![29] := by
  rw [switched_ciphertext]
  decide

private theorem witness_support :
    ((![![-1]], (key, ciphertext)) : (Fin 1 → Fin 1 → ZMod 64) ×
      (ModuleLWEPublicKey 1 1 64 × ModuleLWECiphertext 1 1 64)) ∈ (sampledView 8).support := by
  have hsneg : (![![-1]] : Fin 1 → Fin 1 → ZMod 64) ∈ secrets.support := by
    simpa using mem_secrets (-1) (by decide)
  have hspos : (![![1]] : Fin 1 → Fin 1 → ZMod 64) ∈ secrets.support := by
    simpa using mem_secrets 1 (by decide)
  have he : (![8] : Fin 1 → ZMod 64) ∈ (noise 8).support := by
    simpa using mem_noise 8 8 (by decide)
  simp only [sampledView, encryptionViewOfKeyLaw, moduleLWEPublicKeyLaw,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.bind_bind,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  refine ⟨![![-1]], hsneg, ?_⟩
  refine ⟨!![![1]], PMF.mem_support_uniformOfFintype _, ?_⟩
  refine ⟨![![8]], ?_, ?_⟩
  · rw [PMF.mem_support_pi_iff]
    intro j
    fin_cases j
    exact he
  refine ⟨![![1]], hspos, ?_⟩
  refine ⟨![8], he, ?_⟩
  refine ⟨![![8]], ?_, rfl⟩
  all_goals
    rw [PMF.mem_support_pi_iff]
    intro j
    fin_cases j
    exact he

/-- The smallest family member has positive actual failure; negligibility is asymptotic. -/
example : 0 < ((sampledView 8).toOuterMeasure failure).toReal := by
  rw [PMF.toOuterMeasure_toReal_pos_iff]
  refine ⟨(![![-1]], (key, ciphertext)), ?_, witness_support⟩
  change moduleLWEDecrypt
    (fun j i => (GeneralSIS.liftCentered ((![![-1]] : Fin 1 → Fin 1 → ZMod 64) j) i :
      ZMod 32)) (moduleLWEModulusSwitch 32 ciphertext) ≠ ![true]
  rw [switched_ciphertext]
  decide

end ComplexityTests.Crypto.ModulusSwitchCenteredBinomial
