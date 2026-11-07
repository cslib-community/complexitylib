/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.SIS.Module
public import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.Data.ZMod.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Probabilistic.Repeat
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Languages.Probabilistic.Vector
import Complexity.Probability.PMF.Uniform

/-!
# Native structured module matrices

Private total implementations realize the existing `ModuleSIS.encodeMatrix` representation for
arbitrary positive binary moduli and sample its exact structured uniform law for power-of-two
moduli `2 ^ w`. Dimensions and sampling width are unary; coefficient lists and the deterministic
modulus are binary. Every input entry and output frame is charged. Polynomial coefficients are
sampled independently before rotation-block expansion; expanded scalar entries are not independent.
This is original implementation and sampling algebra.

## Main results

* `exists_computableInPolyTime_encodeModuleMatrix`: canonical native rectangular expansion.
* `exists_isPPTOn_sampleEncodedModuleMatrix`: exact sampling of the encoded structured matrix law
  for power-of-two moduli `2 ^ w`.

The canonical expansion identity requires a positive modulus, including one. Zero dimensions
and width are permitted. Exact sampling here is restricted to moduli `2 ^ w`; see
`Complexity.Crypto.Computational.SIS.Module.ApproximateSampling` for arbitrary positive binary
moduli. These results supply no seed compression, rejection policy or security claim, and do not
implement the entire randomized encryption scheme.
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM Probability ProbComp

private abbrev MatrixParams := ((ℕ × ℕ) × ℕ) × ℕ
private abbrev MatrixCoefficients := List (List (List ℕ))

private def matrixParamEncoding : MatrixParams ↪ List Bool :=
  encPair (encPair (encPair encUnary encUnary) encUnary) encNat

private def matrixCoefficientEncoding : MatrixCoefficients ↪ List Bool :=
  encList (encList (encList encNat))

private def rotationResidue (n q : ℕ) (a : List ℕ) (r s : ℕ) : ℕ :=
  let value : ℤ := (a.getD (if s ≤ r then r - s else n + r - s) 0 : ℕ)
  ((if s ≤ r then value else -value) % (q : ℤ)).toNat

private theorem rotationResidue_polyTime :
    ComputableInPolyTime
      (fun a : (ℕ × ℕ) × List ℕ × ℕ × ℕ =>
        rotationResidue a.1.1 a.1.2 a.2.1 a.2.2.1 a.2.2.2)
      (encPair (encPair encUnary encNat)
        (encPair (encList encNat) (encPair encUnary encUnary))) encNat := by
  unfold rotationResidue
  apply ComputableInPolyTime.intBin_emodNat'
  · fun_prop
  · fun_prop

private def expandedRows (d k n q : ℕ) (a : MatrixCoefficients) : List (List ℕ) :=
  (List.range (d * n)).map fun i => (List.range (k * n)).map fun j =>
    rotationResidue n q ((a.getD (i / n) []).getD (j / n) []) (i % n) (j % n)

private theorem expandedRows_polyTime :
    ComputableInPolyTime
      (fun a : MatrixParams × MatrixCoefficients =>
        expandedRows a.1.1.1.1 a.1.1.1.2 a.1.1.2 a.1.2 a.2)
      (encPair matrixParamEncoding matrixCoefficientEncoding) (encList (encList encNat)) := by
  have hpre : ComputableInPolyTime
      (fun p : ((MatrixParams × MatrixCoefficients) × ℕ) × ℕ =>
        ((p.1.1.1.1.2, p.1.1.1.2),
          ((p.1.1.2.getD (p.1.2 / p.1.1.1.1.2) []).getD (p.2 / p.1.1.1.1.2) [],
            p.1.2 % p.1.1.1.1.2, p.2 % p.1.1.1.1.2)))
      (encPair (encPair (encPair matrixParamEncoding matrixCoefficientEncoding) encUnary) encUnary)
      (encPair (encPair encUnary encNat)
        (encPair (encList encNat) (encPair encUnary encUnary))) := by
    unfold matrixParamEncoding matrixCoefficientEncoding
    fun_prop
  unfold expandedRows
  apply ComputableInPolyTime.mapWithInput (encA := encUnary)
  · unfold matrixParamEncoding matrixCoefficientEncoding
    fun_prop
  · apply ComputableInPolyTime.mapWithInput (encA := encUnary)
    · unfold matrixParamEncoding matrixCoefficientEncoding
      fun_prop
    · exact rotationResidue_polyTime.comp hpre

private def expandedWord (a : MatrixParams × MatrixCoefficients) : List Bool :=
  encList (encList encNat)
    (expandedRows a.1.1.1.1 a.1.1.1.2 a.1.1.2 a.1.2 a.2)

private theorem expandedWord_polyTime :
    ComputableInPolyTime expandedWord
      (encPair matrixParamEncoding matrixCoefficientEncoding) encBits :=
  expandedRows_polyTime.of_enc_eq fun _ => rfl

private theorem rotationResidue_ofFn {n q : ℕ} (hq : 0 < q)
    (a : Fin n → ZMod q) (r s : Fin n) :
    rotationResidue n q (List.ofFn fun i => (a i).val) r.val s.val =
      (rotMatrix a r s).val := by
  let : NeZero q := ⟨hq.ne'⟩
  unfold rotationResidue rotMatrix
  simp only [Matrix.of_apply]
  split_ifs with h
  · rw [List.getD_ofFn_of_lt _ (by omega)]
    have hv := congrArg Int.toNat (ZMod.val_intCast (n := q)
      ((a ⟨r.val - s.val, by omega⟩).val : ℤ))
    simpa only [Int.toNat_natCast, Int.cast_natCast, ZMod.natCast_zmod_val] using hv.symm
  · rw [List.getD_ofFn_of_lt _ (by omega)]
    have hv := congrArg Int.toNat (ZMod.val_intCast (n := q)
      (-((a ⟨n + r.val - s.val, by omega⟩).val : ℤ)))
    simpa only [Int.toNat_natCast, Int.cast_neg, Int.cast_natCast,
      ZMod.natCast_zmod_val] using hv.symm

private theorem expandedWord_ofFn {d k n q : ℕ} (hq : 0 < q)
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) :
    expandedWord ((((d, k), n), q),
      List.ofFn fun i => List.ofFn fun j => List.ofFn fun l => (A i j l).val) =
      ModuleSIS.encodeMatrix A := by
  unfold expandedWord expandedRows ModuleSIS.encodeMatrix GeneralSIS.encodeMatrix
  simp only [List.map_range_eq_ofFn]
  congr 1
  congr 1
  funext i
  congr 1
  funext j
  change rotationResidue n q
    (((List.ofFn fun i => List.ofFn fun j => List.ofFn fun l => (A i j l).val).getD
      (finProdFinEquiv.symm i).1.val []).getD (finProdFinEquiv.symm j).1.val [])
    (finProdFinEquiv.symm i).2.val (finProdFinEquiv.symm j).2.val = _
  simp only [List.getD_ofFn]
  exact rotationResidue_ofFn hq _ _ _

/-- One total native implementation of the existing rectangular structured-matrix codec.
The modulus and all coefficients are binary, the three dimensions unary, and the runtime
charges the complete nested input. Positivity is only a canonical-interpretation hypothesis. -/
theorem exists_computableInPolyTime_encodeModuleMatrix :
    ∃ expand : ((((ℕ × ℕ) × ℕ) × ℕ) × List (List (List ℕ))) → List Bool,
      ComputableInPolyTime expand
        (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encNat)
          (encList (encList (encList encNat)))) encBits ∧
      ∀ (d k n q : ℕ) (_hq : 0 < q)
        (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)),
        expand ((((d, k), n), q),
          List.ofFn fun i => List.ofFn fun j => List.ofFn fun l => (A i j l).val) =
          ModuleSIS.encodeMatrix A :=
  ⟨expandedWord, expandedWord_polyTime, fun _ _ _ _ hq A => expandedWord_ofFn hq A⟩

private def matrixSamplerEncoding : MatrixParams ↪ List Bool :=
  encPair (encPair (encPair encUnary encUnary) encUnary) encUnary

private noncomputable def sampledMatrixWord (a : MatrixParams) : ProbComp (List Bool) :=
  (fun coefficients => expandedWord ((a.1, 2 ^ a.2), coefficients)) <$>
    OracleComp.replicate a.1.1.1
      (OracleComp.replicate a.1.1.2 (OracleComp.replicate a.1.2 (sampleBinaryNat a.2)))

private theorem sampledMatrixWord_ppt :
    IsPPTOn matrixSamplerEncoding encBits sampledMatrixWord := by
  have hw : ComputableInPolyTime (fun a : MatrixParams => a.2)
      matrixSamplerEncoding encUnary := by unfold matrixSamplerEncoding; fun_prop
  have h := ((hw.sampleBinaryNat.replicate
      (show ComputableInPolyTime (fun a : MatrixParams => a.1.2)
        matrixSamplerEncoding encUnary by unfold matrixSamplerEncoding; fun_prop)).replicate
      (show ComputableInPolyTime (fun a : MatrixParams => a.1.1.2)
        matrixSamplerEncoding encUnary by unfold matrixSamplerEncoding; fun_prop)).replicate
      (show ComputableInPolyTime (fun a : MatrixParams => a.1.1.1)
        matrixSamplerEncoding encUnary by unfold matrixSamplerEncoding; fun_prop)
  have hpre : ComputableInPolyTime
      (fun p : MatrixParams × MatrixCoefficients => ((p.1.1, 2 ^ p.1.2), p.2))
      (encPair matrixSamplerEncoding matrixCoefficientEncoding)
      (encPair matrixParamEncoding matrixCoefficientEncoding) := by
    unfold matrixSamplerEncoding matrixParamEncoding matrixCoefficientEncoding
    fun_prop
  exact h.map_with (expandedWord_polyTime.comp hpre)

private theorem eval_binaryNat_uniform_residue (w : ℕ) :
    ProbComp.eval (sampleBinaryNat w) =
      (ProbComp.eval (ProbComp.uniform (ZMod (2 ^ w)))).map ZMod.val := by
  rw [eval_sampleBinaryNat, ProbComp.eval_uniform,
    ← PMF.uniformOfFintype_map_equiv (ZMod.finEquiv (2 ^ w)).toEquiv, PMF.map_comp]
  simp only [Function.comp_def, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ZMod.val_finEquiv]

private theorem eval_matrixCoefficients (d k n w : ℕ) :
    ProbComp.eval (OracleComp.replicate d
      (OracleComp.replicate k (OracleComp.replicate n (sampleBinaryNat w)))) =
      (PMF.uniformOfFintype (Matrix (Fin d) (Fin k) (Fin n → ZMod (2 ^ w)))).map
        (fun A => List.ofFn fun i => List.ofFn fun j => List.ofFn fun l => (A i j l).val) := by
  have h := ProbComp.eval_replicateFin_map
    (ProbComp.eval_replicateFin_map
      (ProbComp.eval_replicateFin_map (eval_binaryNat_uniform_residue w) n) k) d
  simp only [ProbComp.eval_replicateFin, ProbComp.eval_uniform, PMF.pi_uniformOfFintype] at h
  rw [h]
  congr 1

private theorem sampledMatrixWord_eval (d k n w : ℕ) :
    ProbComp.eval (sampledMatrixWord (((d, k), n), w)) =
      (PMF.uniformOfFintype (Matrix (Fin d) (Fin k) (Fin n → ZMod (2 ^ w)))).map
        ModuleSIS.encodeMatrix := by
  rw [sampledMatrixWord, ProbComp.eval_map, eval_matrixCoefficients, PMF.map_comp]
  congr 1
  funext A
  exact expandedWord_ofFn (by positivity) A

/-- An exact strict-PPT sampler for the existing structured module-matrix encoding at power-of-two
moduli `2 ^ w` (for arbitrary positive binary moduli, see
`Complexity.Crypto.Computational.SIS.Module.ApproximateSampling`). All three dimensions and the
bit width `w` are unary runtime inputs. The `d*k*n` independent coefficients are expanded into
rotation blocks; the expanded scalar entries are not independent. -/
theorem exists_isPPTOn_sampleEncodedModuleMatrix :
    ∃ sample : (((ℕ × ℕ) × ℕ) × ℕ) → ProbComp (List Bool),
      IsPPTOn (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encBits sample ∧
      ∀ (d k n w : ℕ),
        ProbComp.eval (sample (((d, k), n), w)) =
          (PMF.uniformOfFintype (Matrix (Fin d) (Fin k) (Fin n → ZMod (2 ^ w)))).map
            ModuleSIS.encodeMatrix :=
  ⟨sampledMatrixWord, sampledMatrixWord_ppt, sampledMatrixWord_eval⟩

end Cslib.Crypto
