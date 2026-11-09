/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption.Native
public import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption.Sampling
public import CslibFrontier.Crypto.Computational.SIS.Module.ApproximateSampling
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.List.RowMajor

/-!
# Native randomized Module-LWE key generation

The existing centered-binomial samplers, structured matrix sampler and key generator compose
into a joint sampler of the actual signed secret and its public key. Rank, degree, both noise
widths and precision are unary; the modulus is binary. The existing secret/public codecs are
paired directly. These are original composition results, with no security assertion.

## Main results

* `exists_isPPTOn_moduleLWEKeyGenJoint`: native joint law, approximation and public marginal.

The native joint sampler retains the same secret used by `moduleLWEKeyGen`. Exact CBD draws
introduce no approximation error; only the structured matrix sampler contributes error.
No no-wrap margin is needed: the signed secret is interpreted by its residue when used.
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM Probability ProbComp Interactive
open scoped ENNReal

private abbrev Params := ((ℕ × ℕ) × ℕ × ℕ) × ℕ × ℕ
private abbrev Rows := List (List ℤ)

private def inputEncoding : Params ↪ List Bool :=
  encPair (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))
    (encPair encUnary encNat)

private def rowEncoding : Rows ↪ List Bool := encList (encList encIntBin)

private def encodeRows (rows : Rows) : List Bool := encList encIntBin rows.flatten

private theorem encodeRows_polyTime :
    ComputableInPolyTime encodeRows rowEncoding encBits := by
  have h : ComputableInPolyTime (fun rows : Rows => rows.flatMap id)
      rowEncoding (encList encIntBin) := by
    apply ComputableInPolyTime.flatMapWithInput (encA := encList encIntBin)
    · exact .id'
    · exact .snd _ _
  apply h.of_enc_eq
  intro rows
  change encList encIntBin rows.flatten = encList encIntBin (rows.flatMap id)
  rw [List.flatten_eq_flatMap]

private theorem encodeRows_ofFn {k n : ℕ} (z : Fin k → Fin n → ℤ) :
    encodeRows (List.ofFn fun j => List.ofFn (z j)) = ModuleSIS.encodeVec z := by
  unfold encodeRows ModuleSIS.encodeVec GeneralSIS.encodeVec flattenPolyVec
  congr 1
  simpa only [List.ofFn_eq_map, List.flatMap_def, Function.comp_def, Function.uncurry] using
    List.flatMap_ofFn_prod z

private noncomputable def sampledKeys
    (sample : (((ℕ × ℕ) × ℕ) × ℕ × ℕ) → ProbComp (List Bool))
    (run : (((ℕ × ℕ) × ℕ) × List Bool × List Bool × List Bool) → List Bool)
    (a : Params) : ProbComp (List Bool × List Bool) := do
  let secret ← OracleComp.replicate a.1.1.1
    (OracleComp.replicate a.1.1.2 (sampleCenteredBinomial a.1.2.1))
  let matrix ← sample (((a.1.1.1, a.1.1.1), a.1.1.2), a.2.1, a.2.2)
  let error ← OracleComp.replicate a.1.1.1
    (OracleComp.replicate a.1.1.2 (sampleCenteredBinomial a.1.2.2))
  return (encodeRows secret,
    run ((a.1.1, a.2.2), (matrix, encodeRows secret, encodeRows error)))

private theorem sampledKeys_ppt
    (sample : (((ℕ × ℕ) × ℕ) × ℕ × ℕ) → ProbComp (List Bool))
    (run : (((ℕ × ℕ) × ℕ) × List Bool × List Bool × List Bool) → List Bool)
    (hsample : IsPPTOn
      (encPair (encPair (encPair encUnary encUnary) encUnary) (encPair encUnary encNat))
      encBits sample)
    (hrun : ComputableInPolyTime run
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair encBits (encPair encBits encBits))) encBits) :
    IsPPTOn inputEncoding (encPair encBits encBits) (sampledKeys sample run) := by
  have hs := isPPTOn_moduleLWECenteredBinomialRows.preprocess
    (show ComputableInPolyTime (fun a : Params => (a.1.1, a.1.2.1)) inputEncoding
      (encPair (encPair encUnary encUnary) encUnary) by unfold inputEncoding; fun_prop)
  have hm := hsample.preprocess
    (show ComputableInPolyTime (fun p : Params × Rows =>
      (((p.1.1.1.1, p.1.1.1.1), p.1.1.1.2), p.1.2.1, p.1.2.2))
      (encPair inputEncoding rowEncoding)
      (encPair (encPair (encPair encUnary encUnary) encUnary) (encPair encUnary encNat)) by
      unfold inputEncoding rowEncoding; fun_prop)
  have he := isPPTOn_moduleLWECenteredBinomialRows.preprocess
    (show ComputableInPolyTime (fun p : (Params × Rows) × List Bool =>
      (p.1.1.1.1, p.1.1.1.2.2)) (encPair (encPair inputEncoding rowEncoding) encBits)
      (encPair (encPair encUnary encUnary) encUnary) by unfold inputEncoding rowEncoding; fun_prop)
  have hfinish : ComputableInPolyTime
      (fun p : ((Params × Rows) × List Bool) × Rows =>
        (encodeRows p.1.1.2,
          run ((p.1.1.1.1.1, p.1.1.1.2.2),
            (p.1.2, encodeRows p.1.1.2, encodeRows p.2))))
      (encPair (encPair (encPair inputEncoding rowEncoding) encBits) rowEncoding)
      (encPair encBits encBits) := by
    apply ComputableInPolyTime.prod
    · exact encodeRows_polyTime.comp (by fun_prop)
    · apply hrun.comp
      apply ComputableInPolyTime.prod
      · unfold inputEncoding rowEncoding
        fun_prop
      · apply ComputableInPolyTime.prod
        · fun_prop
        · exact (encodeRows_polyTime.comp (by fun_prop)).prod
            (encodeRows_polyTime.comp (by fun_prop))
  unfold sampledKeys
  apply hs.bind_with
  apply hm.bind_with
  simpa only [bind_pure_comp] using he.map_with hfinish

private theorem sampledKeys_eval
    (sample : (((ℕ × ℕ) × ℕ) × ℕ × ℕ) → ProbComp (List Bool))
    (run : (((ℕ × ℕ) × ℕ) × List Bool × List Bool × List Bool) → List Bool)
    (k n ηs ηe precision q : ℕ) :
    eval (sampledKeys sample run (((k, n), ηs, ηe), precision, q)) = (do
      let z ← eval (OracleComp.replicateFin k (OracleComp.replicateFin n
        (sampleCenteredBinomial ηs)))
      let word ← eval (sample (((k, k), n), precision, q))
      let e ← eval (OracleComp.replicateFin k (OracleComp.replicateFin n
        (sampleCenteredBinomial ηe)))
      return (ModuleSIS.encodeVec z,
        run (((k, n), q), (word, ModuleSIS.encodeVec z, ModuleSIS.encodeVec e)))) := by
  simp only [sampledKeys, eval_bind, eval_pure, eval_moduleLWECenteredBinomialRows,
    PMF.bind_map, Function.comp_def, encodeRows_ofFn, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]

/-- One native randomized key generator returns the actual signed CBD secret and its public
key, using the existing codecs. Its exact joint law uses the actual bounded modular matrix
sampler; the ideal joint law retains that same secret and uses `moduleLWEPublicKeyLaw`.
Only the matrix introduces approximation: the CBD secret and error are sampled exactly.
All dimensions, CBD widths and precision are unary inputs; the modulus is binary. -/
theorem exists_isPPTOn_moduleLWEKeyGenJoint :
    ∃ generate : (((ℕ × ℕ) × ℕ × ℕ) × ℕ × ℕ) → ProbComp (List Bool × List Bool),
      IsPPTOn
        (encPair (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))
          (encPair encUnary encNat)) (encPair encBits encBits) generate ∧
      ∀ (k n ηs ηe precision q : ℕ) (hq : 0 < q),
        let : NeZero q := ⟨hq.ne'⟩
        let secrets := eval (OracleComp.replicateFin k
          (OracleComp.replicateFin n (sampleCenteredBinomial ηs)))
        let errors := eval (OracleComp.replicateFin k
          (OracleComp.replicateFin n (sampleCenteredBinomial ηe)))
        let noise := (eval (OracleComp.replicateFin n (sampleCenteredBinomial ηe))).map
          (fun z i => (z i : ZMod q))
        let actual := eval (generate (((k, n), ηs, ηe), precision, q))
        actual = (do
          let z ← secrets
          let A ← PMF.pi fun _ : Fin k => PMF.pi fun _ : Fin k => PMF.pi fun _ : Fin n =>
            (eval (sampleModNat (q.size + precision) q)).map (Nat.cast : ℕ → ZMod q)
          let e ← errors
          return (ModuleSIS.encodeVec z, ModuleLWE.encodeSample
            (moduleLWEKeyGen A (fun j i => (z j i : ZMod q)) (fun j i => (e j i : ZMod q))))) ∧
        CloseTo (do
          let z ← secrets
          let pk ← moduleLWEPublicKeyLaw k n q noise (PMF.pure (fun j i => (z j i : ZMod q)))
          return (ModuleSIS.encodeVec z, ModuleLWE.encodeSample pk)) actual
          ((k : ℝ≥0∞) * k * n / 2 ^ precision) ∧
        CloseTo
          ((moduleLWEPublicKeyLaw k n q noise
            (secrets.map (fun z j i => (z j i : ZMod q)))).map ModuleLWE.encodeSample)
          (actual.map Prod.snd) ((k : ℝ≥0∞) * k * n / 2 ^ precision) := by
  obtain ⟨sample, hppt, hlaw⟩ := exists_isPPTOn_sampleEncodedModuleMatrixWithPrecision
  obtain ⟨run, hnative, hrun⟩ := exists_computableInPolyTime_moduleLWEKeyGen
  refine ⟨sampledKeys sample run, sampledKeys_ppt sample run hppt hnative, ?_⟩
  intro k n ηs ηe precision q hq
  let : NeZero q := ⟨hq.ne'⟩
  dsimp only
  have hraw := sampledKeys_eval sample run k n ηs ηe precision q
  obtain ⟨hmatrix, hclose⟩ := hlaw k k n precision q hq
  let matrices : PMF (Matrix (Fin k) (Fin k) (Fin n → ZMod q)) :=
    PMF.pi fun _ : Fin k => PMF.pi fun _ : Fin k => PMF.pi fun _ : Fin n =>
      (eval (sampleModNat (q.size + precision) q)).map (Nat.cast : ℕ → ZMod q)
  change eval (sample (((k, k), n), precision, q)) = matrices.map ModuleSIS.encodeMatrix at hmatrix
  have he : (PMF.pi fun _ : Fin k =>
      (eval (OracleComp.replicateFin n (sampleCenteredBinomial ηe))).map
        (fun z i => (z i : ZMod q))) =
      (eval (OracleComp.replicateFin k (OracleComp.replicateFin n
        (sampleCenteredBinomial ηe)))).map (fun e j i => (e j i : ZMod q)) := by
    simpa only [eval_replicateFin, eval_map] using
      eval_replicateFin_map_coords k (OracleComp.replicateFin n (sampleCenteredBinomial ηe))
        (fun z i => (z i : ZMod q))
  have hj := CloseTo.bind_right
    (eval (OracleComp.replicateFin k (OracleComp.replicateFin n (sampleCenteredBinomial ηs))))
    (fun z _ => hclose.bind_left (fun word =>
      (eval (OracleComp.replicateFin k (OracleComp.replicateFin n
        (sampleCenteredBinomial ηe)))).map (fun e =>
          (ModuleSIS.encodeVec z,
            run (((k, n), q), (word, ModuleSIS.encodeVec z, ModuleSIS.encodeVec e))))))
  refine ⟨?_, ?_, ?_⟩
  · rw [hraw, hmatrix]
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map,
      Function.comp_def, hrun k n q hq]
    rfl
  · rw [hraw]
    simp only [moduleLWEPublicKeyLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.pure_bind, PMF.bind_bind, PMF.bind_map, Function.comp_def, he]
    simp only [PMF.bind_map, Function.comp_def, hrun k n q hq] at hj
    simpa only [PMF.map, Function.comp_def] using hj
  · have hm := hj.map Prod.snd
    rw [hraw]
    simp only [moduleLWEPublicKeyLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.map_bind, PMF.pure_map, PMF.bind_map, Function.comp_def, he]
    simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def,
      hrun k n q hq] at hm
    simpa only [PMF.map, Function.comp_def] using hm

end Cslib.Crypto
