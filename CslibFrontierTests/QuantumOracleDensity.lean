/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Density
public import CslibFrontierTests.QuantumOracleUniform
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Probability.PMF.Map
import Mathlib.LinearAlgebra.Matrix.Vec

/-! Ordinary-module clients of mixed oracle execution: an unequal mixture of phase inputs,
coherent Bell correlations through a native initializer, and zero-qubit boundaries. -/

public section

namespace CslibFrontierTests.QuantumOracleDensity

open Cslib Cslib.Quantum Turing.MultiTapeTM Matrix
open CslibFrontierTests.QuantumInput CslibFrontierTests.QuantumOracleUniform
open scoped ComplexOrder Kronecker

/-- An unequal classical mixture of the two imaginary-phase input states. -/
noncomputable def mixedPhase : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ :=
  (1 / 3 : ℂ) • pureState (phaseInput false) + (2 / 3 : ℂ) • pureState (phaseInput true)

theorem isDensityMatrix_mixedPhase : IsDensityMatrix mixedPhase := by
  refine ⟨(posSemidef_pureState _).smul (by norm_num [Complex.nonneg_iff]) |>.add
    ((posSemidef_pureState _).smul (by norm_num [Complex.nonneg_iff])), ?_⟩
  simp only [mixedPhase, trace_add, trace_smul, trace_pureState, norm_phaseInput,
    one_pow, Complex.ofReal_one, smul_eq_mul, mul_one]
  ring

/-- The growing circuit retains the mixture weights and the full encoded classical input. -/
theorem runDensity_mixedPhase (n : ℕ) (x : List Bool)
    (H : (Fin 1 → Bool) → Fin 1 → Bool) :
    phaseFamily.runDensity n x H mixedPhase =
      (1 / 3 : ℂ) • pureState (ket (inputState (2 * n + 1 + x.length + 1)
        (encPair encUnary encBits (n, x) ++ [false]))) +
      (2 / 3 : ℂ) • pureState (ket (inputState (2 * n + 1 + x.length + 1)
        (encPair encUnary encBits (n, x) ++ [true]))) := by
  rw [mixedPhase, map_add, map_smul, map_smul,
    UniformOracleCircuitFamily.runDensity_pureState,
    UniformOracleCircuitFamily.runDensity_pureState, run_phaseFamily, run_phaseFamily]

example (n : ℕ) (x : List Bool) (H : (Fin 1 → Bool) → Fin 1 → Bool) :
    IsDensityMatrix (phaseFamily.runDensity n x H mixedPhase) :=
  phaseFamily.isDensityMatrix_runDensity n x H isDensityMatrix_mixedPhase

/-- A concrete mixed execution has both unequal, nonzero diagonal probabilities. -/
theorem runDensity_mixedPhase_diagonal (b : Bool) :
    phaseFamily.runDensity 0 [] (fun _ _ => false) mixedPhase
    (inputState 2 [false, b]) (inputState 2 [false, b]) = if b then 2 / 3 else 1 / 3 := by
  rw [runDensity_mixedPhase,
    show encPair encUnary encBits (0, []) = [false] from rfl]
  cases b <;> norm_num [Matrix.add_apply, Matrix.smul_apply, pureState_apply, ket_apply,
    inputState, funext_iff, Fin.forall_fin_succ]

-- Terminal output retains the unequal mixture weights in its observable word probabilities.
example (b : Bool) :
    phaseFamily.outputDensity 0 [] (fun _ _ => false) mixedPhase isDensityMatrix_mixedPhase
      [false, b] = if b then 2 / 3 else 1 / 3 := by
  rw [UniformOracleCircuitFamily.outputDensity_eq]
  change (POVM.basis.measureDensity _ _).map List.ofFn [false, b] = _
  have hout : List.ofFn (inputState 2 [false, b]) = [false, b] := by
    simpa using ofFn_inputState (m := 2) (x := [false, b]) (by simp)
  rw [← hout, Probability.PMF.map_apply_of_injective _ List.ofFn_injective,
    POVM.measureDensity_apply, POVM.densityProb_basis, runDensity_mixedPhase_diagonal]
  cases b <;> norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]

-- The same interface recovers the established pure-state output for all classical inputs.
example (n : ℕ) (x : List Bool) (H : (Fin 1 → Bool) → Fin 1 → Bool) (b : Bool) :
    phaseFamily.outputDensity n x H (pureState (phaseInput b))
      (isDensityMatrix_pureState (norm_phaseInput b)) =
      PMF.pure (encPair encUnary encBits (n, x) ++ [b]) := by
  exact (phaseFamily.outputDensity_pureState n x H (phaseInput b) (norm_phaseInput b)).trans
    (output_phaseFamily n x H b)

/-- This family only initializes the classical input before the supplied quantum register. -/
abbrev idleDescription (p n ℓ : ℕ) : OracleCircuitDescription where
  width := 2 * n + 1 + ℓ + p
  queryWidth := 0
  responseWidth := 0
  quantumInputWidth := p
  outputWidth := 2 * n + 1 + ℓ + p
  instructions := []

private theorem polyTime_idleDescription (p : ℕ) : ComputableInPolyTime
    (fun s : OracleInputSize => idleDescription p s.securityParameter s.classicalInputLength)
    encOracleInputSize encOracleCircuitDescription := by
  dsimp only [idleDescription]
  fun_prop

private theorem wellFormed_idleDescription (p n ℓ : ℕ) :
    (idleDescription p n ℓ).WellFormed ⟨n, ℓ⟩ :=
  ⟨le_rfl, by simp, le_rfl, by simp⟩

/-- One native generator for every security parameter and classical input length. -/
abbrev idleFamily (p : ℕ) : UniformOracleCircuitFamily :=
  ⟨idleDescription p, by exact polyTime_idleDescription p, by exact wellFormed_idleDescription p⟩

abbrev emptyOracle : (Fin 0 → Bool) → Fin 0 → Bool := fun _ => Fin.elim0

/-- The initializer embeds a basis input after the classical word. -/
theorem run_idleFamily_ket (p n : ℕ) (x : List Bool) (z : Fin p → Bool) :
    (idleFamily p).run n x emptyOracle (ket z) =
      ket (inputState (2 * n + 1 + x.length + p)
        (encPair encUnary encBits (n, x) ++ List.ofFn z)) := by
  rw [UniformOracleCircuitFamily.run_apply]
  change Circuit.eval [] ((idleFamily p).initialState n x (ket z)) = _
  rw [Circuit.eval_nil, UniformOracleCircuitFamily.initialState_ket]

private theorem runMatrix_idleFamily (p n : ℕ) (x : List Bool)
    (y : Fin (2 * n + 1 + x.length + p) → Bool) (z : Fin p → Bool) :
    Matrix.toEuclideanLin.symm ((idleFamily p).run n x emptyOracle).toLinearMap y z =
      if y = inputState (2 * n + 1 + x.length + p)
        (encPair encUnary encBits (n, x) ++ List.ofFn z) then 1 else 0 := by
  change (((idleFamily p).run n x emptyOracle) (ket z)).ofLp y = _
  rw [run_idleFamily_ket, ket_apply]

/-- Every joint Bell-output entry, including the coherence between distinct correlated states.
The untouched reference is a one-qubit register. -/
theorem runDensityWithReference_idle_bell_apply (n : ℕ) (x : List Bool)
    (y y' : Fin (2 * n + 1 + x.length + 1) → Bool) (b c : Fin 1 → Bool) :
    (idleFamily 1).runDensityWithReference n x emptyOracle (Fin 1 → Bool)
        (pureState (maxEntangled (Fin 1 → Bool))) (y, b) (y', c) =
      if y = inputState (2 * n + 1 + x.length + 1)
          (encPair encUnary encBits (n, x) ++ List.ofFn b) ∧
        y' = inputState (2 * n + 1 + x.length + 1)
          (encPair encUnary encBits (n, x) ++ List.ofFn c)
      then (2 : ℂ)⁻¹ else 0 := by
  let V := Matrix.toEuclideanLin.symm ((idleFamily 1).run n x emptyOracle).toLinearMap
  have hvec : (maxEntangled (Fin 1 → Bool)).ofLp =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ).vec := by
    ext ⟨b, c⟩
    simp [maxEntangled_apply, Matrix.one_apply, eq_comm]
  have haction (z : Fin (2 * n + 1 + x.length + 1) → Bool) (b : Fin 1 → Bool) :
      ((V ⊗ₖ (1 : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ)).toEuclideanLin
        (maxEntangled (Fin 1 → Bool))).ofLp (z, b) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
        (if z = inputState (2 * n + 1 + x.length + 1)
          (encPair encUnary encBits (n, x) ++ List.ofFn b) then 1 else 0) := by
    rw [Matrix.toLpLin_apply, hvec, Matrix.mulVec_smul, Matrix.kronecker_mulVec_vec,
      Matrix.one_mul, Matrix.one_mul]
    simp only [Pi.smul_apply, Matrix.vec, transpose_apply, smul_eq_mul, V]
    rw [runMatrix_idleFamily 1 n x z b]
  have hcoeff : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * star (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) =
      (2 : ℂ)⁻¹ := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [UniformOracleCircuitFamily.runDensityWithReference_apply, densityConj_pureState]
  change pureState ((V ⊗ₖ (1 : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ)).toEuclideanLin
    (maxEntangled (Fin 1 → Bool))) (y, b) (y', c) = _
  rw [pureState_apply, haction, haction]
  split_ifs <;> simp_all

-- The two distinct correlated basis states retain their off-diagonal coherence.
example (n : ℕ) (x : List Bool) :
    (idleFamily 1).runDensityWithReference n x emptyOracle (Fin 1 → Bool)
      (pureState (maxEntangled (Fin 1 → Bool)))
      (inputState (2 * n + 1 + x.length + 1)
        (encPair encUnary encBits (n, x) ++ [false]), fun _ => false)
      (inputState (2 * n + 1 + x.length + 1)
        (encPair encUnary encBits (n, x) ++ [true]), fun _ => true) = (2 : ℂ)⁻¹ := by
  rw [runDensityWithReference_idle_bell_apply]
  simp

-- The full joint state is a density matrix, with the maximally mixed reference marginal.
example (n : ℕ) (x : List Bool) :
    IsDensityMatrix ((idleFamily 1).runDensityWithReference n x emptyOracle (Fin 1 → Bool)
      (pureState (maxEntangled (Fin 1 → Bool)))) :=
  (idleFamily 1).isDensityMatrix_runDensityWithReference n x emptyOracle (Fin 1 → Bool)
    (isDensityMatrix_pureState norm_maxEntangled)

example (n : ℕ) (x : List Bool) :
    partialTraceLeft ((idleFamily 1).runDensityWithReference n x emptyOracle (Fin 1 → Bool)
      (pureState (maxEntangled (Fin 1 → Bool)))) =
      (2 : ℂ)⁻¹ • (1 : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) := by
  rw [UniformOracleCircuitFamily.partialTraceLeft_runDensityWithReference,
    partialTraceLeft_pureState_maxEntangled]
  norm_num

-- Zero quantum-input and reference qubits each mean a one-dimensional basis, not an empty type.
example (n : ℕ) (x : List Bool) :
    (idleFamily 0).runDensityWithReference n x emptyOracle (Fin 0 → Bool)
        (pureState (ket ((Fin.elim0 : Fin 0 → Bool), (Fin.elim0 : Fin 0 → Bool)))) =
      pureState (ket (inputState (2 * n + 1 + x.length) (encPair encUnary encBits (n, x)),
        (Fin.elim0 : Fin 0 → Bool))) := by
  rw [UniformOracleCircuitFamily.runDensityWithReference_apply, densityConj_pureState]
  congr 1
  ext ⟨y, r⟩
  rw [Matrix.toLpLin_apply]
  change ((Matrix.toEuclideanLin.symm ((idleFamily 0).run n x emptyOracle).toLinearMap ⊗ₖ
    (1 : Matrix (Fin 0 → Bool) (Fin 0 → Bool) ℂ)) *ᵥ
      Pi.single (Fin.elim0, Fin.elim0) 1) (y, r) = _
  rw [Matrix.mulVec_single_one]
  simp only [Matrix.col_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    runMatrix_idleFamily 0 n x y Fin.elim0, List.ofFn_zero, List.append_nil, ket_apply,
    Prod.mk.injEq, Subsingleton.elim r Fin.elim0, and_true, ite_true, mul_one]
  rfl

end CslibFrontierTests.QuantumOracleDensity
