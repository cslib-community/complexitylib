/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.InteractionResources
public import CslibFrontierTests.QuantumOracleDecapsulation
public import CslibFrontierTests.QuantumOracleShared
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.BitString.List

/-! Growing native stages, retained coherence, and the actual toy decapsulation handler. -/

public section

namespace CslibFrontierTests.QuantumOracleInteraction

open Cslib Cslib.Quantum Matrix Finset Turing.MultiTapeTM
open scoped Kronecker ENNReal

/-- Prepare a fresh last qubit in `|+⟩`, outside the two-bit request prefix. The growing even
query prefix cancels for every fixed oracle, including on arbitrary auxiliary states. -/
abbrev firstDescription (n ℓ : ℕ) : OracleCircuitDescription where
  width := 2 * n + 1 + ℓ + 2
  queryWidth := 1
  responseWidth := 1
  quantumInputWidth := 0
  outputWidth := 2
  instructions := List.replicate (2 * (n + ℓ)) .query ++
    [.gate (false, true, 2 * n + 1 + ℓ + 1, [])]

private theorem polyTime_firstDescription : ComputableInPolyTime
    (fun s : OracleInputSize => firstDescription s.securityParameter s.classicalInputLength)
    encOracleInputSize encOracleCircuitDescription := by
  dsimp only [firstDescription]
  fun_prop

private theorem wellFormed_firstDescription (n ℓ : ℕ) :
    (firstDescription n ℓ).WellFormed ⟨n, ℓ⟩ := by
  refine ⟨by dsimp only [firstDescription]; omega, by dsimp only [firstDescription]; omega,
    by dsimp only [firstDescription]; omega, ?_⟩
  intro g hg
  simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
    or_false] at hg
  rcases hg with ⟨_, rfl⟩ | rfl
  · change 1 + 1 ≤ 2 * n + 1 + ℓ + 2
    omega
  · simp [OracleGateCode.WellFormed, PhaseGateCode.WellFormed, GateCode.WellFormed]

abbrev firstFamily : UniformOracleCircuitFamily :=
  ⟨firstDescription, by exact polyTime_firstDescription, by exact wellFormed_firstDescription⟩

/-- The transcript adds four bits. For every original length, retain the entire first register.
Hadamard first decodes its last qubit; the remaining gates compare an oracle answer to the reply.
Short inputs outside the interaction layout still have well-formed generated circuits. -/
abbrev nextDescription (n t : ℕ) : OracleCircuitDescription where
  width := (2 * n + 1 + t) + (2 * n + 1 + (t - 4) + 2)
  queryWidth := 1
  responseWidth := 1
  quantumInputWidth := 2 * n + 1 + (t - 4) + 2
  outputWidth := (2 * n + 1 + t) + (2 * n + 1 + (t - 4) + 2)
  instructions :=
    [.gate (false, true, (2 * n + 1 + t) + (2 * n + 1 + (t - 4) + 2) - 1, []), .query] ++
      if 4 ≤ t then [.gate (false, false, 1, [2 * n + t])] else []

private theorem polyTime_nextDescription : ComputableInPolyTime
    (fun s : OracleInputSize => nextDescription s.securityParameter s.classicalInputLength)
    encOracleInputSize encOracleCircuitDescription := by
  dsimp only [nextDescription]
  fun_prop

private theorem wellFormed_nextDescription (n t : ℕ) :
    (nextDescription n t).WellFormed ⟨n, t⟩ := by
  refine ⟨le_rfl, by dsimp only [nextDescription]; omega, le_rfl, ?_⟩
  intro g hg
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (rfl | rfl) | hg
  · simp [OracleGateCode.WellFormed, PhaseGateCode.WellFormed, GateCode.WellFormed]
  · change 1 + 1 ≤ (2 * n + 1 + t) + (2 * n + 1 + (t - 4) + 2)
    omega
  · split_ifs at hg with ht
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      subst g
      simp [OracleGateCode.WellFormed, PhaseGateCode.WellFormed, GateCode.WellFormed]
      omega
    · simp at hg

abbrev nextFamily : UniformOracleCircuitFamily :=
  ⟨nextDescription, by exact polyTime_nextDescription, by exact wellFormed_nextDescription⟩

theorem firstSignature (L : ℕ → ℕ) :
    firstFamily.HasOracleSignature (fun _ => 1) (fun _ => 1) L :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem nextSignature (L : ℕ → ℕ) :
    nextFamily.HasOracleSignature (fun _ => 1) (fun _ => 1) L :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem firstSignature_oracle {L : ℕ → ℕ}
    (h : firstFamily.HasOracleSignature (fun _ => 1) (fun _ => 1) L)
    (n ℓ : ℕ) (hℓ : ℓ ≤ L n)
    (H : QuantumOracleDecapsulation.Hash) : h.oracle n ℓ hℓ H = H := by
  ext q j
  rw [UniformOracleCircuitFamily.HasOracleSignature.oracle_apply]
  rfl

theorem nextSignature_oracle (L : ℕ → ℕ) (n ℓ : ℕ) (hℓ : ℓ ≤ L n)
    (H : QuantumOracleDecapsulation.Hash) : (nextSignature L).oracle n ℓ hℓ H = H := by
  ext q j
  rw [UniformOracleCircuitFamily.HasOracleSignature.oracle_apply]
  rfl

/-- Compatibility holds for every parameter and original input length, not only the finite
probability instance below. -/
theorem memory_compatible (n ℓ : ℕ) :
    (nextFamily.description n (ℓ + 2 + 2)).quantumInputWidth =
      (firstFamily.description n ℓ).width := by
  dsimp only [nextFamily, firstFamily, nextDescription, firstDescription]
  omega

-- Both width and the first query count genuinely grow with the original input length.
example (n ℓ : ℕ) : (firstFamily.description n ℓ).instructions.queryCount = 2 * (n + ℓ) := by
  simp [OracleCircuit.queryCount, List.countP_replicate, OracleGateCode.isQuery]

example : ∃ B : ℕ → ℕ, ComputableInPolyTime B encUnary encUnary ∧ PolynomiallyBounded B ∧
    ∀ n ℓ, ℓ ≤ n →
      let first := firstFamily.description n ℓ
      let next := nextFamily.description n (ℓ + first.outputWidth + 2)
      first.width + next.width ≤ B n ∧
      first.instructions.gateCount + next.instructions.gateCount ≤ B n ∧
      first.instructions.queryCount + next.instructions.queryCount ≤ B n ∧
      ℓ + first.outputWidth + 2 ≤ B n ∧ 1 ≤ B n :=
  firstFamily.exists_classicalQuery_resource_bound nextFamily
    PolynomiallyBounded.id (PolynomiallyBounded.const 2)

/-- Use the existing native decapsulation caller and its fixed two-bit replies. -/
noncomputable def fixedService (H : QuantumOracleDecapsulation.Hash)
    (request : Fin 2 → Bool) : PMF (Fin 2 → Bool) :=
  (QuantumOracleDecapsulation.service H (List.ofFn request)).map (BitString.ofList 2)

/-- The fixed-width adapter preserves every supported reply exactly, with no padding or loss. -/
theorem fixedService_roundTrip (H : QuantumOracleDecapsulation.Hash) (request : Fin 2 → Bool) :
    (fixedService H request).map List.ofFn =
      QuantumOracleDecapsulation.service H (List.ofFn request) := by
  rw [fixedService, PMF.map_comp]
  refine (Probability.PMF.map_congr_on_support _ _ id fun reply hreply => ?_).trans
    (PMF.map_id _)
  exact BitString.ofFn_ofList
    (QuantumOracleDecapsulation.length_of_mem_support_service H _ reply hreply)

theorem fixedService_honest (H : QuantumOracleDecapsulation.Hash) :
    fixedService H (fun _ => false) = PMF.pure ![true, H (fun _ => false) 0] := by
  rw [fixedService]
  change (QuantumOracleDecapsulation.service H
    (QuantumOracleDecapsulation.requestWord .honest)).map _ = _
  rw [QuantumOracleDecapsulation.service_honest]
  simp only [PMF.pure_map]
  congr 1
  ext i
  fin_cases i <;> rfl

noncomputable def h₃ : PlacedGate 3 := ⟨1, Gate.hadamard, ⟨![2], by decide⟩⟩

/-- The concrete first stage has classical request `00` and a coherent last work qubit. -/
noncomputable def prepared : Qubits 3 := h₃.eval (ket (fun _ => false))

theorem norm_prepared : ‖prepared‖ = 1 := by
  rw [prepared, LinearIsometryEquiv.norm_map, norm_ket]

/-- Both Hadamard basis states of the saved work qubit, with the same classical request. -/
noncomputable def memoryState (b : Bool) : Qubits 3 := h₃.eval (ket ![false, false, b])

theorem memoryState_false : memoryState false = prepared := by
  unfold memoryState prepared
  congr 2
  ext i
  fin_cases i <;> rfl

theorem memoryState_expansion (b : Bool) : memoryState b =
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket ![false, false, false] +
    ((if b then -1 else 1) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) • ket ![false, false, true] := by
  have h := GateCode.eval_toPlacedGate_hadamard_ket
    (g := h₃) (t := 2) (by rfl) (by decide) ![false, false, b]
  have hu (c : Bool) : Function.update ![false, false, b] (2 : Fin 3) c = ![false, false, c] := by
    ext i
    fin_cases i <;> simp
  simpa [memoryState, Fintype.sum_bool, hu, add_comm] using h

theorem memoryState_apply (b : Bool) (z : Fin 3 → Bool) :
    (memoryState b).ofLp z = if z 0 = false ∧ z 1 = false then
      (if b && z 2 then -1 else 1) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0 := by
  rw [memoryState_expansion]
  cases b <;> cases h₀ : z 0 <;> cases h₁ : z 1 <;> cases h₂ : z 2 <;>
    simp [ket_apply, funext_iff, Fin.forall_fin_succ, h₀, h₁, h₂]

theorem prepared_apply (z : Fin 3 → Bool) :
    prepared.ofLp z = if z 0 = false ∧ z 1 = false then
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0 := by
  simpa [memoryState_false] using memoryState_apply false z

theorem first_run (H : QuantumOracleDecapsulation.Hash) :
    firstFamily.run 0 [] H (ket (fun i => Fin.elim0 i)) = prepared := by
  rw [UniformOracleCircuitFamily.run_apply, UniformOracleCircuitFamily.initialState_ket]
  change Circuit.eval (OracleCircuit.toCircuit 3 H [.gate (false, true, 2, [])])
    (ket (inputState 3 [false])) = prepared
  simp only [OracleCircuit.toCircuit, List.filterMap_cons, OracleGateCode.toPlacedGate?,
    PhaseGateCode.toPlacedGate?, GateCode.toPlacedGate?, show (2 : ℕ) < 3 by decide,
    ↓reduceDIte, List.filterMap_nil,
    Circuit.eval_cons, Circuit.eval_nil]
  change h₃.eval (ket (inputState 3 [false])) = h₃.eval (ket (fun _ => false))
  congr 2
  ext i
  fin_cases i <;> simp [inputState]

theorem branch_prepared (request : Fin 2 → Bool) :
    classicalDensityBranch
      (fun z : (Fin 3 → Bool) × Unit => fun i : Fin 2 => z.1 (Fin.castLEEmb (by decide) i))
      request (pureState (prodState prepared (ket ()))) =
      if request = (fun _ => false) then pureState (prodState prepared (ket ())) else 0 := by
  rw [classicalDensityBranch_pureState]
  by_cases hr : request = fun _ => false
  · rw [ite_eq_left hr]
    congr 1
    ext ⟨z, u⟩
    cases h₀ : z 0 <;> cases h₁ : z 1 <;>
      simp [projOutcomes_apply, prodState_apply, prepared_apply, hr,
        funext_iff, Fin.forall_fin_succ, h₀, h₁]
  · rw [ite_eq_right hr]
    have hz : projOutcomes
        (fun z : (Fin 3 → Bool) × Unit =>
          (fun i : Fin 2 => z.1 (Fin.castLEEmb (by decide) i)) = request)
        (prodState prepared (ket ())) = 0 := by
      ext ⟨z, u⟩
      cases h₀ : z 0 <;> cases h₁ : z 1 <;>
        simp_all [projOutcomes_apply, prodState_apply, prepared_apply,
          funext_iff, Fin.forall_fin_succ]
    rw [hz]
    ext i j
    simp [pureState_apply]

@[expose] noncomputable def h₈ : PlacedGate 8 := ⟨1, Gate.hadamard, ⟨![7], by decide⟩⟩

@[expose] noncomputable def compareReply : PlacedGate 8 := ⟨2, Gate.cnot, ⟨![4, 1], by decide⟩⟩

abbrev baseWord (key memory : Bool) : Fin 8 → Bool :=
  ![false, false, false, true, key, false, false, memory]

noncomputable def queriedWord (H : QuantumOracleDecapsulation.Hash)
    (key memory : Bool) : Fin 8 → Bool :=
  (queryRegisters (a := 1) (b := 1) (Fin.castLEEmb (by decide : 2 ≤ 8))).symm
    (fun _ => false, H (fun _ => false), fun j => baseWord key memory j.1)

theorem queriedWord_response (H : QuantumOracleDecapsulation.Hash) (key memory : Bool) :
    queriedWord H key memory 1 = H (fun _ => false) 0 :=
  queryRegisters_symm_response _ _ _ _ 0

theorem queriedWord_key (H : QuantumOracleDecapsulation.Hash) (key memory : Bool) :
    queriedWord H key memory 4 = key := by
  exact queryRegisters_symm_workspace _ _ _ _ 4 (by decide)

theorem queriedWord_memory (H : QuantumOracleDecapsulation.Hash) (key memory : Bool) :
    queriedWord H key memory 7 = memory := by
  exact queryRegisters_symm_workspace _ _ _ _ 7 (by decide)

noncomputable def answerWord (H : QuantumOracleDecapsulation.Hash)
    (key memory : Bool) : Fin 8 → Bool :=
  Function.update (queriedWord H key memory) 1 (H (fun _ => false) 0 ^^ key)

theorem answerWord_response (H : QuantumOracleDecapsulation.Hash) (key memory : Bool) :
    answerWord H key memory 1 = (H (fun _ => false) 0 ^^ key) := Function.update_self ..

theorem answerWord_memory (H : QuantumOracleDecapsulation.Hash) (key memory : Bool) :
    answerWord H key memory 7 = memory := by
  rw [answerWord, Function.update_of_ne (by decide), queriedWord_memory]

theorem query_baseWord (H : QuantumOracleDecapsulation.Hash) (key memory : Bool) :
    (xorQuery H (Fin.castLEEmb (by decide : 2 ≤ 8))).eval (ket (baseWord key memory)) =
      ket (queriedWord H key memory) := by
  have hs : (queryRegisters (a := 1) (b := 1) (Fin.castLEEmb (by decide : 2 ≤ 8))).symm
      (fun _ => false, fun _ => false, fun j => baseWord key memory j.1) = baseWord key memory := by
    apply (queryRegisters (a := 1) (b := 1) (Fin.castLEEmb (by decide : 2 ≤ 8))).injective
    simp only [Equiv.apply_symm_apply, queryRegisters_apply]
    apply Prod.ext (by funext i; fin_cases i; rfl)
    exact Prod.ext (by funext i; fin_cases i; rfl) rfl
  rw [← hs, xorQuery_eval_ket]
  change ket ((queryRegisters (Fin.castLEEmb (by decide : 2 ≤ 8))).symm
    ((fun _ => false), 0 + H (fun _ => false), (fun j => baseWord key memory j.1))) = _
  rw [zero_add]
  rfl

theorem compareReply_queriedWord (H : QuantumOracleDecapsulation.Hash) (key memory : Bool) :
    compareReply.eval (ket (queriedWord H key memory)) = ket (answerWord H key memory) := by
  have h := GateCode.eval_toPlacedGate_ket (g := compareReply) (t := 1) (cs := [4])
    (by rfl) (by decide) (queriedWord H key memory)
  simpa [answerWord, List.getD_eq_getElem?_getD, queriedWord_response, queriedWord_key] using h

theorem decode_embedded_memory (key memory : Bool) :
    h₈.eval (embedState (blockEmb 5 (by decide : 5 + 3 ≤ 8))
      (inputState 8 [false, false, false, true, key]) (memoryState memory)) =
      ket (baseWord key memory) := by
  have hm := Circuit.eval_mapWires_embedState [h₃]
    (blockEmb 5 (by decide : 5 + 3 ≤ 8)) (inputState 8 [false, false, false, true, key])
    (memoryState memory)
  have hmap : Circuit.mapWires (blockEmb 5 (by decide : 5 + 3 ≤ 8)) [h₃] = [h₈] := by
    unfold Circuit.mapWires PlacedGate.mapWires h₃ h₈
    simp only [List.map_cons, List.map_nil]
    congr 3
    ext i
    fin_cases i
    rw [Function.Embedding.trans_apply, blockEmb_apply_val]
    rfl
  rw [hmap] at hm
  simp only [Circuit.eval_cons, Circuit.eval_nil] at hm
  rw [hm]
  have hh : h₃.eval (memoryState memory) = ket ![false, false, memory] := by
    change unitaryEquiv (place ⟨![2], by decide⟩ Gate.hadamard)
      (unitaryEquiv (place ⟨![2], by decide⟩ Gate.hadamard) (ket ![false, false, memory])) = _
    rw [← unitaryEquiv_mul, ← map_mul, Gate.hadamard_mul_self, map_one, unitaryEquiv_one]
  rw [hh, embedState_ket, glue_blockEmb_inputState _ _ (by simp)]
  congr 1
  ext i
  fin_cases i <;> simp [inputState, baseWord]

/-- A real second-stage native run consumes the retained superposition and compares its query
to the service reply. No measurement of the work qubit was inserted at the boundary. -/
theorem resume_memoryState (H : QuantumOracleDecapsulation.Hash) (key memory : Bool) :
    nextFamily.resumeRun (nextSignature (fun _ => 4)) 0 [] (by decide)
      (memory_compatible 0 0) H (fun _ : Fin 2 => false) ![true, key] (memoryState memory) =
      ket (answerWord H key memory) := by
  have hr := UniformOracleCircuitFamily.resumeRun_apply nextFamily
    (nextSignature (fun _ => 4)) 0 [] (by decide) (memory_compatible 0 0)
    H (fun _ : Fin 2 => false) ![true, key] (memoryState memory)
  rw [hr]
  rw [nextSignature_oracle]
  simp only [nextFamily, nextDescription, List.length_nil, Nat.zero_add, Nat.mul_zero,
    Nat.sub_self, Nat.reduceAdd, List.nil_append, List.ofFn_succ, List.ofFn_zero,
    List.cons_append, encPair, encUnary, encBits]
  change Circuit.eval
    (OracleCircuit.toCircuit 8 H [.gate (false, true, 7, []), .query,
      .gate (false, false, 1, [4])])
    (embedState (blockEmb 5 (by decide : 5 + 3 ≤ 8))
      (inputState 8 [false, false, false, true, key]) (memoryState memory)) = _
  have hc : OracleCircuit.toCircuit 8 H [.gate (false, true, 7, []), .query,
      .gate (false, false, 1, [4])] =
      [h₈, xorQuery H (Fin.castLEEmb (by decide : 2 ≤ 8)), compareReply] := by
    simp [OracleCircuit.toCircuit, OracleGateCode.toPlacedGate?, PhaseGateCode.toPlacedGate?,
      GateCode.toPlacedGate?, h₈, compareReply]
  rw [hc]
  simp only [Circuit.eval_cons, Circuit.eval_nil, decode_embedded_memory,
    query_baseWord, compareReply_queriedWord]

theorem resume_prepared (H : QuantumOracleDecapsulation.Hash) (key : Bool) :
    nextFamily.resumeRun (nextSignature (fun _ => 4)) 0 [] (by decide)
      (memory_compatible 0 0) H (fun _ : Fin 2 => false) ![true, key] prepared =
      ket (answerWord H key false) := by
  rw [← memoryState_false, resume_memoryState]

/-- The second table argument is only for the negative redraw test. In the actual shared
experiment it is the same table as the first argument. -/
noncomputable def nativeState (H Hservice : QuantumOracleDecapsulation.Hash) :
    Matrix ((Fin 8 → Bool) × Unit) ((Fin 8 → Bool) × Unit) ℂ :=
  nextFamily.runClassicalQuery (nextSignature (fun _ => 4)) 0 [] H Unit
    firstFamily (firstSignature (fun _ => 0)) (by decide) 2 (by decide)
    (memory_compatible 0 0) (fun _ => fixedService Hservice)
    (pureState (prodState (ket (fun i => Fin.elim0 i)) (ket ())))

/-- The accepted toy ML-KEM path is executed through the measured native boundary. Its
output records the comparison bit and the coherently decoded work bit. -/
theorem nativeState_eq (H Hservice : QuantumOracleDecapsulation.Hash) :
    nativeState H Hservice =
      pureState (prodState (ket (answerWord H (Hservice (fun _ => false) 0) false)) (ket ())) := by
  have hfirst : firstFamily.runDensityWithReference 0 [] H Unit
      (pureState (prodState (ket (fun i => Fin.elim0 i)) (ket ()))) =
      pureState (prodState prepared (ket ())) := by
    rw [UniformOracleCircuitFamily.runDensityWithReference_apply,
      densityConj_kronecker_pureState, LinearEquiv.apply_symm_apply]
    exact congrArg (fun ψ => pureState (prodState ψ (ket ()))) (first_run H)
  unfold nativeState
  rw [UniformOracleCircuitFamily.runClassicalQuery_apply]
  rw [firstSignature_oracle]
  change (∑ request : Fin 2 → Bool,
    nextFamily.resumeDensity (nextSignature (fun _ => 4)) 0 [] (by decide)
      (memory_compatible 0 0) H Unit request (fixedService Hservice request)
      (classicalDensityBranch
        (fun z : (Fin 3 → Bool) × Unit => fun i : Fin 2 => z.1 (Fin.castLEEmb (by decide) i))
        request (firstFamily.runDensityWithReference 0 [] H Unit
          (pureState (prodState (ket (fun i => Fin.elim0 i)) (ket ())))))) = _
  rw [hfirst]
  simp only [branch_prepared, apply_ite, map_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, fixedService_honest]
  rw [nextFamily.resumeDensity_pure (nextSignature (fun _ => 4)) 0 [] (by decide)
    (memory_compatible 0 0) H Unit, densityConj_kronecker_pureState,
    LinearEquiv.apply_symm_apply]
  exact congrArg (fun ψ => pureState (prodState ψ (ket ()))) (resume_prepared H _)

theorem isDensityMatrix_nativeState (H Hservice : QuantumOracleDecapsulation.Hash) :
    IsDensityMatrix (nativeState H Hservice) := by
  rw [nativeState_eq, prodState_ket]
  exact isDensityMatrix_pureState (norm_ket _)

/-- Observe either the comparison wire or the saved work wire after the complete interaction. -/
noncomputable def nativeRead (H Hservice : QuantumOracleDecapsulation.Hash) (wire : Fin 8) :
    PMF Bool :=
  (POVM.basis.measureDensity (nativeState H Hservice) (isDensityMatrix_nativeState H Hservice)).map
    (fun z => z.1 wire)

theorem nativeRead_eq (H Hservice : QuantumOracleDecapsulation.Hash) (wire : Fin 8) :
    nativeRead H Hservice wire =
      PMF.pure (answerWord H (Hservice (fun _ => false) 0) false wire) := by
  unfold nativeRead
  simp only [nativeState_eq, prodState_ket, POVM.measureDensity_pureState _ _ (norm_ket _),
    POVM.measure_basis, measure_ket, PMF.pure_map]

/-- Under the same sampled oracle, the accepted key and coherent query agree certainly. -/
theorem nativeRead_shared (H : QuantumOracleDecapsulation.Hash) :
    nativeRead H H 1 = PMF.pure false := by
  rw [nativeRead_eq, answerWord_response, Bool.xor_self]

/-- The retained `|+⟩` qubit is decoded to zero with probability one across the service call. -/
theorem nativeRead_memory (H Hservice : QuantumOracleDecapsulation.Hash) :
    nativeRead H Hservice 7 = PMF.pure false := by
  rw [nativeRead_eq, answerWord_memory]

/-- Measuring the whole active register erases the work coherence. The resulting operator is
also the fair mixture of the two Hadamard basis states, which the continuation distinguishes. -/
theorem full_measurement_prepared :
    (∑ z : Fin 3 → Bool, classicalDensityBranch Prod.fst z
      (pureState (prodState prepared (ket ())))) =
      ∑ b : Bool, (Probability.PMF.uniformOfFintype Bool b).toReal •
        pureState (prodState (memoryState b) (ket ())) := by
  ext ⟨i, u⟩ ⟨j, v⟩
  cases u
  cases v
  simp only [Matrix.sum_apply, classicalDensityBranch_apply, ite_and,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  cases hi₀ : i 0 <;> cases hi₁ : i 1 <;> cases hi₂ : i 2 <;>
    cases hj₀ : j 0 <;> cases hj₁ : j 1 <;> cases hj₂ : j 2 <;>
    norm_num [pureState_apply, prodState_apply, prepared_apply, memoryState_apply, ket_apply,
      Fintype.sum_bool, Probability.PMF.uniformOfFintype_apply, Matrix.smul_apply,
      funext_iff, Fin.forall_fin_succ, hi₀, hi₁, hi₂, hj₀, hj₁, hj₂,
      Complex.star_def, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt]

/-- The deliberately incorrect boundary measures all memory, then runs the same accepted
classical service and native continuation as the correct boundary. -/
noncomputable def fullMeasurementState (H Hservice : QuantumOracleDecapsulation.Hash) :
    Matrix ((Fin 8 → Bool) × Unit) ((Fin 8 → Bool) × Unit) ℂ :=
  nextFamily.resumeDensity (nextSignature (fun _ => 4)) 0 [] (by decide)
    (memory_compatible 0 0) H Unit (fun _ : Fin 2 => false)
    (fixedService Hservice (fun _ => false))
    (∑ z : Fin 3 → Bool, classicalDensityBranch Prod.fst z
      (pureState (prodState prepared (ket ()))))

theorem fullMeasurementState_eq (H Hservice : QuantumOracleDecapsulation.Hash) :
    fullMeasurementState H Hservice =
      ∑ b : Bool, (Probability.PMF.uniformOfFintype Bool b).toReal •
        pureState (prodState (ket (answerWord H (Hservice (fun _ => false) 0) b)) (ket ())) := by
  unfold fullMeasurementState
  rw [full_measurement_prepared, map_sum]
  simp only [LinearMap.map_smul_of_tower, fixedService_honest]
  apply sum_congr rfl
  intro b _
  rw [nextFamily.resumeDensity_pure (nextSignature (fun _ => 4)) 0 [] (by decide)
    (memory_compatible 0 0) H Unit, densityConj_kronecker_pureState,
    LinearEquiv.apply_symm_apply]
  exact congrArg (fun ψ => (Probability.PMF.uniformOfFintype Bool b).toReal •
    pureState (prodState ψ (ket ()))) (resume_memoryState H _ b)

theorem isDensityMatrix_fullMeasurementState (H Hservice : QuantumOracleDecapsulation.Hash) :
    IsDensityMatrix (fullMeasurementState H Hservice) := by
  rw [fullMeasurementState_eq]
  apply isDensityMatrix_pmf_sum
  intro b
  rw [prodState_ket]
  exact isDensityMatrix_pureState (norm_ket _)

noncomputable def fullMeasurementRead (H Hservice : QuantumOracleDecapsulation.Hash) : PMF Bool :=
  (POVM.basis.measureDensity (fullMeasurementState H Hservice)
    (isDensityMatrix_fullMeasurementState H Hservice)).map (fun z => z.1 7)

/-- Accidental full-register measurement makes the final Hadamard bit fair, losing the
probability-one zero outcome proved for the native retained-memory boundary. -/
theorem fullMeasurementRead_eq (H Hservice : QuantumOracleDecapsulation.Hash) :
    fullMeasurementRead H Hservice = Probability.PMF.uniformOfFintype Bool := by
  unfold fullMeasurementRead
  simp only [fullMeasurementState_eq, prodState_ket]
  rw [POVM.measureDensity_pmf_sum _ _ _ (fun b => isDensityMatrix_pureState (norm_ket _))]
  simp only [PMF.map_bind, POVM.measureDensity_pureState _ _ (norm_ket _), POVM.measure_basis,
    measure_ket, PMF.pure_map, answerWord_memory, PMF.bind_pure]

/-- One ideal table is sampled outside both native stages and the decapsulation service. -/
noncomputable def sharedExperiment : PMF Bool := do
  let H ← Probability.PMF.uniformOfFintype QuantumOracleDecapsulation.Hash
  nativeRead H H 1

theorem sharedExperiment_eq : sharedExperiment = PMF.pure false := by
  simp [sharedExperiment, nativeRead_shared]

/-- The negative experiment redraws only the table used by the classical service. -/
noncomputable def redrawnExperiment : PMF Bool := do
  let H ← Probability.PMF.uniformOfFintype QuantumOracleDecapsulation.Hash
  let Hservice ← Probability.PMF.uniformOfFintype QuantumOracleDecapsulation.Hash
  nativeRead H Hservice 1

/-- Independent tables destroy the exact shared-oracle comparison through the native boundary. -/
theorem redrawnExperiment_eq : redrawnExperiment = Probability.PMF.uniformOfFintype Bool := by
  have h : ((Probability.PMF.uniformOfFintype QuantumOracleDecapsulation.Hash).map
      (fun H => H (fun _ => false) 0)).bind (fun b =>
        ((Probability.PMF.uniformOfFintype QuantumOracleDecapsulation.Hash).map
          (fun H => H (fun _ => false) 0)).map (fun c => b ^^ c)) =
      Probability.PMF.uniformOfFintype Bool := by
    rw [QuantumOracleShared.uniform_answer]
    ext b
    cases b <;> norm_num [PMF.bind_apply, PMF.map_apply, Probability.PMF.uniformOfFintype_apply,
      tsum_fintype, Fintype.sum_bool]
    all_goals simp only [← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), one_mul]
  simpa only [redrawnExperiment, nativeRead_eq, answerWord_response,
    Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, PMF.map,
    PMF.bind_bind, PMF.pure_bind] using h

-- Both distinctions are probabilities of actual native continuations, not just state inequalities.
example (H : QuantumOracleDecapsulation.Hash) :
    nativeRead H H 7 false = 1 ∧ fullMeasurementRead H H false = 1 / 2 := by
  rw [nativeRead_memory, fullMeasurementRead_eq]
  norm_num [Probability.PMF.uniformOfFintype_apply]

example : sharedExperiment false = 1 ∧ redrawnExperiment false = 1 / 2 := by
  rw [sharedExperiment_eq, redrawnExperiment_eq]
  norm_num [Probability.PMF.uniformOfFintype_apply]

end CslibFrontierTests.QuantumOracleInteraction
