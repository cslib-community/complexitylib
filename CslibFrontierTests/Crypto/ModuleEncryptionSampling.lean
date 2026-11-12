/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption.Sampling
import CslibFrontier.Probability.PMF.Uniform

/-! Sampling compatibility, small-secret support, native boundaries and a uniform-law failure. -/

namespace CslibFrontierTests.Crypto.ModuleEncryptionSampling

open Cslib Cslib.Crypto Probability ProbComp Turing.MultiTapeTM
open scoped Matrix ENNReal

/-- Old calls still mean uniform long-term and ephemeral secrets. -/
example : realEncryptionView 1 2 32 (PMF.pure 0) ![true, false] =
    realEncryptionView 1 2 32 (PMF.pure 0) ![true, false]
      (PMF.uniformOfFintype _) (PMF.uniformOfFintype _) := rfl

/-- A genuine small-secret law, with nonzero values in its support. -/
private noncomputable def smallLaw : PMF (Fin 1 → Fin 2 → ZMod 32) :=
  PMF.pi (fun _ => PMF.pi fun _ => LWE.noiseLaw 5 1)

example : (![![1, -1]] : Fin 1 → Fin 2 → ZMod 32) ∈ smallLaw.support := by
  rw [smallLaw, PMF.mem_support_pi_iff]
  intro j
  rw [PMF.mem_support_pi_iff]
  intro i
  fin_cases j
  fin_cases i
  all_goals
    apply (PMF.mem_support_map_iff _ _ _).mpr
  · exact ⟨1, (mem_support_sampleCenteredBinomial_iff 1 1).mpr (by decide), rfl⟩
  · exact ⟨-1, (mem_support_sampleCenteredBinomial_iff 1 (-1)).mpr (by decide), rfl⟩

example {s : Fin 1 → Fin 2 → ZMod 32} (hs : s ∈ smallLaw.support) :
    ModuleSIS.inInfNormBound 1 s :=
  moduleLWECenteredBinomial_inInfNormBound (by decide) hs

/-- Retaining the actual sampled secret preserves a concrete noisy small-secret public view. -/
example : (do
    let s ← smallLaw
    let view ← encryptionViewOfKeyLaw
      (moduleLWEPublicKeyLaw 1 2 32 (PMF.pi fun _ => LWE.noiseLaw 5 1) (PMF.pure s))
      (PMF.pi fun _ => LWE.noiseLaw 5 1) ![true, false] smallLaw
    pure (s, view)).map Prod.snd =
      realEncryptionView 1 2 32 (PMF.pi fun _ => LWE.noiseLaw 5 1)
        ![true, false] smallLaw smallLaw :=
  realEncryptionView_retained_secret_marginal _ _ _ _

/-- The runtime sampler handles zero dimensions and width without hidden fixed-size assumptions. -/
example : ProbComp.eval (OracleComp.replicate 0
    (OracleComp.replicate 3 (sampleCenteredBinomial 2))) = PMF.pure [] := by simp
example : ProbComp.eval (OracleComp.replicate 2
    (OracleComp.replicate 0 (sampleCenteredBinomial 2))) = PMF.pure [[], []] := by
  simp [OracleComp.replicate]
example : ProbComp.eval (OracleComp.replicate 2
    (OracleComp.replicate 1 (sampleCenteredBinomial 0))) = PMF.pure [[0], [0]] := by
  simp [OracleComp.replicate]

example {s : Fin 1 → Fin 1 → ZMod (2 ^ 0)}
    (hs : s ∈ (PMF.pi (fun _ : Fin 1 => PMF.pi
      (fun _ : Fin 1 => LWE.noiseLaw 0 0))).support) :
    ModuleSIS.inInfNormBound 0 s :=
  moduleLWECenteredBinomial_inInfNormBound (by decide) hs

/-- A variable-row client composes the uniform native sampler with unary parameter arithmetic. -/
example : IsPPTOn encUnary (encList (encList encIntBin))
    (fun k : ℕ => OracleComp.replicate (k + 1)
      (OracleComp.replicate 2 (sampleCenteredBinomial 1))) := by
  have hinput : ComputableInPolyTime (fun k : ℕ => ((k + 1, 2), 1)) encUnary
      (encPair (encPair encUnary encUnary) encUnary) := by fun_prop
  exact isPPTOn_moduleLWECenteredBinomialRows.preprocess hinput

/-- A uniform scalar is exactly the uniform rank-one, degree-one secret used below. -/
example : (PMF.uniformOfFintype (ZMod 16)).map (fun z => (![![z]] : Fin 1 → Fin 1 → ZMod 16)) =
    PMF.uniformOfFintype (Fin 1 → Fin 1 → ZMod 16) := by
  let e := (Equiv.funUnique (Fin 1) (Fin 1 → ZMod 16)).trans
    (Equiv.funUnique (Fin 1) (ZMod 16))
  convert PMF.uniformOfFintype_map_equiv e.symm using 1
  congr 1 with z : 1
  ext j i
  fin_cases j; fin_cases i
  rfl

private def outcome (a s r : ZMod 16) : Bool :=
  moduleLWEDecrypt (![![s]])
    (moduleLWEEncrypt (moduleLWEKeyGen (!![![a]]) (![![s]]) (![![1]]))
      (![![r]]) (![![1]]) (![1]) (![true])) 0

private theorem outcome_eq (a s r : ZMod 16) :
    outcome a s r = decide (4 < (9 + r - s).valMinAbs.natAbs) := by
  have hphase :
      (moduleLWEEncrypt (moduleLWEKeyGen (!![![a]]) (![![s]]) (![![1]]))
        (![![r]]) (![![1]]) (![1]) (![true])).2 -
        innerPoly (moduleLWEEncrypt (moduleLWEKeyGen (!![![a]]) (![![s]]) (![![1]]))
          (![![r]]) (![![1]]) (![1]) (![true])).1 (![![s]]) = ![9 + r - s] := by
    rw [moduleLWEDecrypt_phase_eq]
    ext i
    fin_cases i
    simpa [encodePolyMsg, innerPoly, negacyclicMul, rotMatrix, Pi.smul_apply,
      smul_eq_mul, Function.comp_def, Matrix.vecHead] using
      (show (8 : ZMod 16) + (r - s + 1) = 9 + r - s by ring)
  unfold outcome moduleLWEDecrypt
  rw [hphase]
  rfl

private theorem uniform_outcome (a s : ZMod 16) :
    (PMF.uniformOfFintype (ZMod 16)).map (outcome a s) =
      (PMF.uniformOfFintype (ZMod 16)).map (fun x => decide (4 < x.valMinAbs.natAbs)) := by
  have hshift := PMF.uniformOfFintype_map_equiv (Equiv.addRight (9 - s))
  calc
    _ = ((PMF.uniformOfFintype (ZMod 16)).map (Equiv.addRight (9 - s))).map
        (fun x => decide (4 < x.valMinAbs.natAbs)) := by
      rw [PMF.map_comp]
      congr 1 with r : 1
      rw [outcome_eq]
      congr 4
      change 9 + r - s = r + (9 - s)
      ring
    _ = _ := by rw [hshift]

/-- For every public matrix coefficient, uniform secrets and ephemeral values with errors one
succeed on the true message with probability only 7/16. Each scalar is the sole module/ring
coefficient, so these are exactly the one-dimensional uniform secret laws. -/
example (a : ZMod 16) : (do
    let s ← PMF.uniformOfFintype (ZMod 16)
    let r ← PMF.uniformOfFintype (ZMod 16)
    pure (outcome a s r)) true = (7 / 16 : ℝ≥0∞) := by
  have hlaw : (do
      let s ← PMF.uniformOfFintype (ZMod 16)
      let r ← PMF.uniformOfFintype (ZMod 16)
      pure (outcome a s r)) =
        (PMF.uniformOfFintype (ZMod 16)).map (fun x => decide (4 < x.valMinAbs.natAbs)) := by
    change (PMF.uniformOfFintype (ZMod 16)).bind
      (fun s => (PMF.uniformOfFintype (ZMod 16)).map (outcome a s)) = _
    simp only [uniform_outcome, PMF.bind_const]
  rw [hlaw, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  change (PMF.uniformOfFintype (ZMod 16)).toOuterMeasure
    {x | decide (4 < x.valMinAbs.natAbs) = true} = _
  rw [PMF.toOuterMeasure_uniformOfFintype]
  have hcard : (Finset.univ.filter (fun x : ZMod 16 =>
      decide (4 < x.valMinAbs.natAbs) = true)).card = 7 := by decide
  simp only [Set.mem_ofPred_eq] at *
  rw [hcard]
  norm_num [div_eq_mul_inv]

end CslibFrontierTests.Crypto.ModuleEncryptionSampling
