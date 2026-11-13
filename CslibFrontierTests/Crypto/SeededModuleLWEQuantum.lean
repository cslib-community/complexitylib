/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontierTests.Crypto.SeededModuleLWE
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Uniform
import CslibFrontier.Computability.Circuit.Quantum.PhaseOracle
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! A growing native quantum circuit uses phase interference to read the complemented first
challenge bit. All its quantum inputs are initialized; it receives no quantum advice. -/

public section

namespace CslibFrontierTests.SeededModuleLWEQuantum

open Cslib Cslib.Quantum Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

private theorem phase_sq : Gate.ctrlPhase 1 * Gate.ctrlPhase 1 =
    Gate.hadamard * Gate.not * Gate.hadamard := by
  apply Subtype.ext
  have hs : (Gate.ctrlPhase 1 : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) =
      Matrix.diagonal (fun x => if x 0 then Complex.I else 1) := by
    ext y x
    by_cases h : y = x
    · subst y
      simpa [Matrix.diagonal_apply, Fin.forall_fin_one] using
        Gate.ctrlPhase_cond_apply 1 false x x
    · simpa [Matrix.diagonal_apply, h] using Gate.ctrlPhase_cond_apply 1 false y x
  rw [Submonoid.coe_mul, hs, Matrix.diagonal_mul_diagonal,
    Gate.hadamard_mul_not_mul_hadamard]
  congr 1
  funext x
  cases x 0 <;> simp

private theorem hadamard_phase_sq_hadamard :
    Gate.hadamard * (Gate.ctrlPhase 1 * Gate.ctrlPhase 1) * Gate.hadamard = Gate.not := by
  rw [phase_sq]
  simp only [← mul_assoc, Gate.hadamard_mul_self, one_mul]
  rw [mul_assoc, Gate.hadamard_mul_self, mul_one]

private theorem eval_phase_flip {m t : ℕ} (ht : t < m) (ψ : Qubits m) :
    (Circuit.ofPhaseCodes m
      [(false, true, t, []), (true, false, t, []),
        (true, false, t, []), (false, true, t, [])]).eval ψ =
      (Circuit.ofCodes m [(false, t, [])]).eval ψ := by
  let e : Fin 1 ↪ Fin m := ⟨![⟨t, ht⟩], fun i j _ => Subsingleton.elim i j⟩
  have hs : (PlacedGate.ctrlPhase false e).matrix = place e (Gate.ctrlPhase 1) :=
    PlacedGate.ctrlPhase_matrix false e
  simp only [Circuit.ofPhaseCodes, Circuit.ofCodes, List.filterMap_cons,
    PhaseGateCode.toPlacedGate?, GateCode.toPlacedGate?, ht, ↓reduceDIte,
    List.filterMap_nil, Circuit.eval_cons, Circuit.eval_nil, PlacedGate.eval]
  change unitaryEquiv (place e Gate.hadamard)
    (unitaryEquiv (PlacedGate.ctrlPhase false e).matrix
      (unitaryEquiv (PlacedGate.ctrlPhase false e).matrix
        (unitaryEquiv (place e Gate.hadamard) ψ))) = unitaryEquiv (place e Gate.not) ψ
  rw [hs, ← unitaryEquiv_mul, ← unitaryEquiv_mul, ← unitaryEquiv_mul,
    ← map_mul, ← map_mul, ← map_mul]
  rw [mul_assoc Gate.hadamard (Gate.ctrlPhase 1) (Gate.ctrlPhase 1),
    hadamard_phase_sq_hadamard]

/-- Phase interference `H S S H`, followed by the existing three-CNOT swap to the output. -/
abbrev description (n ℓ : ℕ) : OracleCircuitDescription where
  width := 2 * n + 1 + ℓ + 1
  queryWidth := 0
  responseWidth := 0
  quantumInputWidth := 0
  outputWidth := 1
  instructions :=
    [.gate (false, true, 2 * n + 1, []), .gate (true, false, 2 * n + 1, []),
      .gate (true, false, 2 * n + 1, []), .gate (false, true, 2 * n + 1, [])] ++
      (GateCode.swapCodes (2 * n + 1)).map (fun g => .gate (false, g))

private theorem polyTime_description : ComputableInPolyTime
    (fun s : OracleInputSize => description s.securityParameter s.classicalInputLength)
    encOracleInputSize encOracleCircuitDescription := by
  dsimp only [description, GateCode.swapCodes, List.map]
  fun_prop

private theorem wellFormed_description (n ℓ : ℕ) :
    (description n ℓ).WellFormed ⟨n, ℓ⟩ := by
  refine ⟨by dsimp only [description]; omega, by dsimp only [description]; omega,
    by dsimp only [description]; omega, ?_⟩
  intro g hg
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at hg
  rcases hg with (rfl | rfl | rfl | rfl) | ⟨c, hc, rfl⟩
  · simp [OracleGateCode.WellFormed, PhaseGateCode.WellFormed, GateCode.WellFormed]
  · simp [OracleGateCode.WellFormed, PhaseGateCode.WellFormed]
  · simp [OracleGateCode.WellFormed, PhaseGateCode.WellFormed]
  · simp [OracleGateCode.WellFormed, PhaseGateCode.WellFormed, GateCode.WellFormed]
  · exact (GateCode.isClassical_swapCodes (N := 2 * n + 1 + ℓ + 1)
      (by omega) (by omega) c hc).2

/-- One native generator handles every security parameter and every classical input length. -/
abbrev family : UniformOracleCircuitFamily :=
  ⟨description, by exact polyTime_description, by exact wellFormed_description⟩

example (n ℓ : ℕ) : (family.description n ℓ).width = 2 * n + ℓ + 2 := by
  change 2 * n + 1 + ℓ + 1 = _
  omega

example (n ℓ : ℕ) : (family.description n ℓ).instructions.gateCount = 7 := rfl

example (n ℓ : ℕ) : (family.description n ℓ).instructions.queryCount = 0 := rfl

private theorem eval_description (n ℓ : ℕ) (H : (Fin 0 → Bool) → Fin 0 → Bool)
    (ψ : Qubits (2 * n + 1 + ℓ + 1)) :
    (OracleCircuit.toCircuit _ H (description n ℓ).instructions).eval ψ =
      (Circuit.ofCodes _ ((false, 2 * n + 1, []) ::
        GateCode.swapCodes (2 * n + 1))).eval ψ := by
  have hc : (description n ℓ).instructions =
      ([(false, true, 2 * n + 1, []), (true, false, 2 * n + 1, []),
        (true, false, 2 * n + 1, []), (false, true, 2 * n + 1, [])] : List PhaseGateCode).map
        OracleGateCode.gate ++
      ((GateCode.swapCodes (2 * n + 1)).map (fun g => (false, g))).map OracleGateCode.gate := rfl
  rw [hc, OracleCircuit.toCircuit_append, OracleCircuit.toCircuit_map_gate,
    OracleCircuit.toCircuit_map_gate, Circuit.ofPhaseCodes_map, Circuit.eval_append,
    eval_phase_flip (by omega), ← Circuit.eval_append, ← Circuit.ofCodes_append]
  rfl

private theorem classical_description (n ℓ : ℕ) :
    GateCode.IsClassical (2 * n + 1 + ℓ + 1)
      ((false, 2 * n + 1, []) :: GateCode.swapCodes (2 * n + 1)) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact ⟨rfl, by simp [GateCode.WellFormed]⟩
  · exact GateCode.isClassical_swapCodes (by omega) (by omega) g hg

/-- No quantum advice is supplied: the zero-qubit input is the unique normalized basis state. -/
theorem output_family (n : ℕ) (b : Bool) (rest : List Bool)
    (H : (Fin 0 → Bool) → Fin 0 → Bool) :
    family.output n (b :: rest) H (ket Fin.elim0) (norm_ket _) = PMF.pure [!b] := by
  rw [UniformOracleCircuitFamily.output_eq]
  have hrun : family.run n (b :: rest) H (ket Fin.elim0) =
      ket (GateCode.classicalRun
        ((false, 2 * n + 1, []) :: GateCode.swapCodes (2 * n + 1))
        (inputState (2 * n + 1 + (b :: rest).length + 1)
          (encPair encUnary encBits (n, b :: rest)))) := by
    rw [UniformOracleCircuitFamily.run_apply, eval_description,
      UniformOracleCircuitFamily.initialState_ket]
    simp only [List.ofFn_zero, List.append_nil]
    exact Circuit.eval_ofCodes_ket (classical_description n (b :: rest).length) _
  simp only [hrun, measureOut_ket]
  apply congrArg PMF.pure
  change [GateCode.classicalRun _ _ ⟨0, by omega⟩] = [!b]
  apply congrArg List.singleton
  let y := GateCode.classicalRun
    ((false, 2 * n + 1, []) :: GateCode.swapCodes (2 * n + 1))
    (inputState (2 * n + 1 + (b :: rest).length + 1)
      (encPair encUnary encBits (n, b :: rest)))
  change y ⟨0, _⟩ = !b
  rw [← readBit_of_lt y (by omega : 0 < 2 * n + 1 + (b :: rest).length + 1)]
  dsimp only [y]
  rw [GateCode.classicalRun_cons,
    GateCode.readBit_classicalRun_swapCodes (by omega) (by omega),
    GateCode.readBit_classicalStep]
  simp only [List.all_nil, Bool.and_true]
  rw [readBit_inputState (by simp)]
  simp [encPair_apply, encUnary_apply, encBits_apply]

/-- The complete rank-one, degree-one target modulo two is one bit. -/
@[expose] def targetBitEquiv : (Fin 1 → Fin 1 → ZMod 2) ≃ Bool :=
  (Equiv.funUnique (Fin 1) (Fin 1 → ZMod 2)).trans
    ((Equiv.funUnique (Fin 1) (ZMod 2)).trans finTwoEquiv)

/-- The two-bit challenge word retains both the complete target and the complete seed. -/
@[expose] def challengeWord (view : Bool × (Fin 1 → Fin 1 → ZMod 2)) : List Bool :=
  [targetBitEquiv view.2, view.1]

example : Function.Injective challengeWord := by
  intro a b h
  have he : a.2 = b.2 ∧ a.1 = b.1 := by simpa [challengeWord] using h
  exact Prod.ext he.2 he.1

/-- The native family consumes the full classical view and returns its measured first bit. -/
@[expose] noncomputable def distinguish (n : ℕ)
    (view : Bool × (Fin 1 → Fin 1 → ZMod 2)) : Game :=
  (family.output n (challengeWord view) (fun _ => Fin.elim0)
    (ket Fin.elim0) (norm_ket _)).map (fun word => word.headD false)

private theorem distinguish_eq (n : ℕ) (view : Bool × (Fin 1 → Fin 1 → ZMod 2)) :
    distinguish n view = PMF.pure (!(targetBitEquiv view.2)) := by
  rw [distinguish, challengeWord, output_family, PMF.pure_map]
  rfl

/-- Zero expander and zero noise, with an independently sampled public seed. -/
@[expose] noncomputable def realLaw : PMF (Bool × (Fin 1 → Fin 1 → ZMod 2)) :=
  ModuleLWE.seededSampleLaw (PMF.uniformOfFintype Bool)
    (fun _ => (0 : Matrix (Fin 1) (Fin 1) (Fin 1 → ZMod 2)))
    (PMF.pure 0) (PMF.pure 0)

-- The zero-noise law is also the actual ideal CBD sampler at width zero.
example : ModuleLWE.seededSampleLaw (PMF.uniformOfFintype Bool)
    (fun _ => (0 : Matrix (Fin 1) (Fin 1) (Fin 1 → ZMod 2)))
    (ProbComp.eval (MLKEM.sampleVecCBD 1 1 2 0))
    (ProbComp.eval (MLKEM.sampleVecCBD 1 1 2 0)) = realLaw := by
  rw [CslibFrontierTests.SeededModuleLWE.vecCBD_zero]
  rfl

/-- The ideal comparison retains the same public seed and replaces the target by uniform. -/
@[expose] noncomputable def idealLaw : PMF (Bool × (Fin 1 → Fin 1 → ZMod 2)) := do
  let seed ← PMF.uniformOfFintype Bool
  let target ← PMF.uniformOfFintype (Fin 1 → Fin 1 → ZMod 2)
  return (seed, target)

theorem real_output (n : ℕ) : realLaw.bind (distinguish n) = PMF.pure true := by
  simp only [realLaw, ModuleLWE.seededSampleLaw, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.bind_bind, distinguish_eq,
    ModuleLWE.sample, moduleSISMap_zero, zero_add]
  change (PMF.uniformOfFintype Bool).bind (fun _ => PMF.pure true) = _
  exact PMF.bind_const _ _

theorem ideal_output (n : ℕ) : idealLaw.bind (distinguish n) = PMF.uniformOfFintype Bool := by
  simp only [idealLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind, distinguish_eq, PMF.bind_const]
  change (PMF.uniformOfFintype (Fin 1 → Fin 1 → ZMod 2)).map
    (targetBitEquiv.trans Bool.involutive_not.toPerm) = _
  exact PMF.uniformOfFintype_map_equiv _

/-- An exact gap for every parameter, witnessed by the growing native quantum circuit above.
This deliberately easy instance rules out interpreting the seeded law as a hardness assertion. -/
theorem advantage_eq_half (n : ℕ) :
    Game.advantage (realLaw.bind (distinguish n)) (idealLaw.bind (distinguish n)) =
      (1 / 2 : ℝ≥0) := by
  rw [real_output, ideal_output, Game.advantage_pure_true_left]
  norm_num [Game.failProbability, PMF.uniformOfFintype_apply, ENNReal.toNNReal_ofNat]

end CslibFrontierTests.SeededModuleLWEQuantum
