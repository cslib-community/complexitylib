/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.Module.MatrixSampling
public import CslibFrontier.Crypto.Game.CloseTo.UniformNat
public import CslibFrontier.Probability.Product
import CslibFrontier.Computability.Interactive.Security.Repeat
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Probability.PMF.Uniform

/-!
# Approximate native sampling of structured module matrices

The existing bounded modular sampler draws independent polynomial coefficients, followed by
native rotation-block expansion. The error counts polynomial coefficients, not the correlated
expanded scalar entries. Dimensions and fair-bit width are unary, while the modulus is binary.
All implementation helpers are private; the sampled law uses the existing module-matrix codec.

## Main results

* `exists_isPPTOn_approximateEncodedModuleMatrix`: exact actual law and uniform approximation.
* `exists_isPPTOn_sampleEncodedModuleMatrixWithPrecision`: binary-modulus precision schedule.

These are original composition results for the existing sampler, not security claims or an
exact arbitrary-modulus uniform sampler. Positivity is required only by the semantic laws.
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM Probability ProbComp Interactive
open scoped ENNReal

private abbrev Params := ((ℕ × ℕ) × ℕ) × ℕ × ℕ
private abbrev Coefficients := List (List (List ℕ))

private def inputEncoding : Params ↪ List Bool :=
  encPair (encPair (encPair encUnary encUnary) encUnary) (encPair encUnary encNat)

private noncomputable def sampledWord
    (expand : ((((ℕ × ℕ) × ℕ) × ℕ) × Coefficients) → List Bool)
    (a : Params) : ProbComp (List Bool) :=
  (fun coefficients => expand ((a.1, a.2.2), coefficients)) <$>
    OracleComp.replicate a.1.1.1 (OracleComp.replicate a.1.1.2
      (OracleComp.replicate a.1.2 (sampleModNat a.2.1 a.2.2)))

private theorem sampledWord_ppt
    (expand : ((((ℕ × ℕ) × ℕ) × ℕ) × Coefficients) → List Bool)
    (hexpand : ComputableInPolyTime expand
      (encPair (encPair (encPair (encPair encUnary encUnary) encUnary) encNat)
        (encList (encList (encList encNat)))) encBits) :
    IsPPTOn inputEncoding encBits (sampledWord expand) := by
  have h := isPPTOn_sampleModNat
    (show ComputableInPolyTime (fun a : Params => a.2.1) inputEncoding encUnary by
      unfold inputEncoding; fun_prop)
    (show ComputableInPolyTime (fun a : Params => a.2.2) inputEncoding encNat by
      unfold inputEncoding; fun_prop)
  have hr := ((h.replicate
      (show ComputableInPolyTime (fun a : Params => a.1.2) inputEncoding encUnary by
        unfold inputEncoding; fun_prop)).replicate
      (show ComputableInPolyTime (fun a : Params => a.1.1.2) inputEncoding encUnary by
        unfold inputEncoding; fun_prop)).replicate
      (show ComputableInPolyTime (fun a : Params => a.1.1.1) inputEncoding encUnary by
        unfold inputEncoding; fun_prop)
  exact hr.map_with (hexpand.comp (by unfold inputEncoding; fun_prop))

private theorem eval_modNat_residue (width q : ℕ) :
    eval (sampleModNat width q) =
      (eval ((Nat.cast : ℕ → ZMod q) <$> sampleModNat width q)).map ZMod.val := by
  rw [eval_map, eval_sampleModNat, PMF.map_comp, PMF.map_comp]
  congr 1 with i : 1
  simp only [Function.comp_apply, ZMod.val_natCast, Nat.mod_mod]

private theorem eval_coefficients (d k n width q : ℕ) [NeZero q] :
    eval (OracleComp.replicate d (OracleComp.replicate k
      (OracleComp.replicate n (sampleModNat width q)))) =
      (PMF.pi fun _ : Fin d => PMF.pi fun _ : Fin k => PMF.pi fun _ : Fin n =>
        (eval (sampleModNat width q)).map (Nat.cast : ℕ → ZMod q)).map
          (fun A => List.ofFn fun i => List.ofFn fun j => List.ofFn fun l => (A i j l).val) := by
  have h := eval_replicateFin_map
    (eval_replicateFin_map (eval_replicateFin_map (eval_modNat_residue width q) n) k) d
  simpa only [eval_replicateFin, eval_map] using h

/-- One uniform native sampler for binary moduli. Its exact law draws the existing bounded
modular sampler independently for every polynomial coefficient, then applies the existing
structured codec. The all-event error is at most `d*k*n*q/2^width`; no expanded scalar entry
is treated as an independent draw. The same total program also handles modulus zero. -/
theorem exists_isPPTOn_approximateEncodedModuleMatrix :
    ∃ sample : (((ℕ × ℕ) × ℕ) × ℕ × ℕ) → ProbComp (List Bool),
      IsPPTOn
        (encPair (encPair (encPair encUnary encUnary) encUnary) (encPair encUnary encNat))
        encBits sample ∧
      ∀ (d k n width q : ℕ) (hq : 0 < q),
        letI : NeZero q := ⟨hq.ne'⟩
        eval (sample (((d, k), n), width, q)) =
          (PMF.pi fun _ : Fin d => PMF.pi fun _ : Fin k => PMF.pi fun _ : Fin n =>
            (eval (sampleModNat width q)).map (Nat.cast : ℕ → ZMod q)).map
              ModuleSIS.encodeMatrix ∧
        CloseTo
          ((PMF.uniformOfFintype (Matrix (Fin d) (Fin k) (Fin n → ZMod q))).map
            ModuleSIS.encodeMatrix)
          (eval (sample (((d, k), n), width, q)))
          ((d : ℝ≥0∞) * k * n * q / 2 ^ width) := by
  obtain ⟨expand, hnative, hexpand⟩ := exists_computableInPolyTime_encodeModuleMatrix
  refine ⟨sampledWord expand, sampledWord_ppt expand hnative, ?_⟩
  intro d k n width q hq
  let : NeZero q := ⟨hq.ne'⟩
  have hlaw : eval (sampledWord expand (((d, k), n), width, q)) =
      (PMF.pi fun _ : Fin d => PMF.pi fun _ : Fin k => PMF.pi fun _ : Fin n =>
        (eval (sampleModNat width q)).map (Nat.cast : ℕ → ZMod q)).map
          ModuleSIS.encodeMatrix := by
    rw [sampledWord, eval_map, eval_coefficients, PMF.map_comp]
    congr 1 with A : 1
    exact hexpand d k n q hq A
  refine ⟨hlaw, ?_⟩
  rw [hlaw]
  have h := (((closeTo_uniform_sampleModNat width q).iid n).iid k).iid d
  simp only [PMF.iid_eq_pi, PMF.pi_uniformOfFintype] at h
  convert h.map ModuleSIS.encodeMatrix using 1 <;>
    first | rfl | simp only [mul_div_assoc, mul_assoc]

/-- Setting the fair-bit width to `q.size + precision` gives error at most
`d*k*n/2^precision`. The modulus remains binary and the precision unary; computing its bit
length does not charge the numerical value of the modulus as a unary input. -/
theorem exists_isPPTOn_sampleEncodedModuleMatrixWithPrecision :
    ∃ sample : (((ℕ × ℕ) × ℕ) × ℕ × ℕ) → ProbComp (List Bool),
      IsPPTOn
        (encPair (encPair (encPair encUnary encUnary) encUnary) (encPair encUnary encNat))
        encBits sample ∧
      ∀ (d k n precision q : ℕ) (hq : 0 < q),
        letI : NeZero q := ⟨hq.ne'⟩
        eval (sample (((d, k), n), precision, q)) =
          (PMF.pi fun _ : Fin d => PMF.pi fun _ : Fin k => PMF.pi fun _ : Fin n =>
            (eval (sampleModNat (q.size + precision) q)).map (Nat.cast : ℕ → ZMod q)).map
              ModuleSIS.encodeMatrix ∧
        CloseTo
          ((PMF.uniformOfFintype (Matrix (Fin d) (Fin k) (Fin n → ZMod q))).map
            ModuleSIS.encodeMatrix)
          (eval (sample (((d, k), n), precision, q)))
          ((d : ℝ≥0∞) * k * n / 2 ^ precision) := by
  obtain ⟨sample, hppt, hlaw⟩ := exists_isPPTOn_approximateEncodedModuleMatrix
  refine ⟨fun a => sample (a.1, a.2.2.size + a.2.1, a.2.2), hppt.preprocess ?_, ?_⟩
  · fun_prop
  · intro d k n precision q hq
    obtain ⟨heq, hclose⟩ := hlaw d k n (q.size + precision) q hq
    refine ⟨heq, hclose.mono ?_⟩
    have hqle : (q : ℝ≥0∞) ≤ 2 ^ q.size := by
      exact_mod_cast (Nat.lt_size_self q).le
    calc
      (d : ℝ≥0∞) * k * n * q / 2 ^ (q.size + precision) ≤
          d * k * n * (2 ^ q.size) / 2 ^ (q.size + precision) :=
        by gcongr
      _ = d * k * n / 2 ^ precision := by
        rw [pow_add, mul_comm (2 ^ q.size), ENNReal.mul_div_mul_right]
        · positivity
        · finiteness

end Cslib.Crypto
