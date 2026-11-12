/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.PairedPorts

/-!
# Tests for paired-port matrices and logarithmic-space time-layered reductions

Concrete and non-vacuity checks for:
* `Matrix.PairedPorts`, `Matrix.PairedPorts.ofLists`, and `Matrix.PairedPorts.finTimeLayer` on a
  concrete 3-vertex matrix over `ℚ` having a split row (`1/2, 1/2`), a merged row (`1`), and a zero
  row;
* `Turing.MultiTapePTM.ConfigurationGraph.clockedOutPort`, `clockedInPort`, `clockedOutCount`, and
  `clockedCompactPairedPorts` on concrete fair-coin machines (`splitCoinMachine` with distinct coin
  branches and `mergedCoinMachine` with coincident coin branches), including halted self-loops,
  terminal clock exhaustion, mutual port inversion, and out-of-range queries;
* `Cslib.Complexity.exists_pairedTimeLayerFamily_of_mem_RL` and
  `Cslib.Complexity.exists_pairedTimeLayerFamily_of_mem_BPL` on a nontrivial language (`{true}` on
  `Bool`), verifying both accepting and rejecting inputs and instantiating all six
  `ComputableInLogSpace` certificates.
-/

public section

namespace CslibFrontierTests.LogSpace.PairedPorts

open Matrix Turing Turing.MultiTapeTM Turing.MultiTapeNTM.ConfigurationGraph
  Turing.MultiTapePTM.ConfigurationGraph Cslib.Complexity

/-! ### 1. Concrete `Matrix.PairedPorts` and `finTimeLayer` checks over `ℚ` -/

section MatrixPairedPortsTests

/-- Test matrix on `Fin 3` over `ℚ`: row `0` splits `1/2, 1/2` to `0` and `1`; row `1` sends `1`
to `2`; row `2` is zero. -/
def testBaseMatrix : Matrix (Fin 3) (Fin 3) ℚ := fun u v =>
  match u.val, v.val with
  | 0, 0 => 1 / 2
  | 0, 1 => 1 / 2
  | 1, 2 => 1
  | _, _ => 0

/-- Outgoing target lists for `testBaseMatrix`. -/
def testOutList : Fin 3 → List (Fin 3)
  | ⟨0, _⟩ => [0, 1]
  | ⟨1, _⟩ => [2]
  | ⟨2, _⟩ => []

/-- Incoming source lists for `testBaseMatrix`. -/
def testInList : Fin 3 → List (Fin 3)
  | ⟨0, _⟩ => [0]
  | ⟨1, _⟩ => [0]
  | ⟨2, _⟩ => [1]

/-- Paired-port representation of `testBaseMatrix` built via `Matrix.PairedPorts.ofLists`. -/
def testBasePorts : testBaseMatrix.PairedPorts 2 2 :=
  Matrix.PairedPorts.ofLists testBaseMatrix 2 2 testOutList testInList
    (by intro u; fin_cases u <;> decide)
    (by intro v; fin_cases v <;> decide)
    (by intro u; fin_cases u <;> decide)
    (by intro v; fin_cases v <;> decide)
    (by intro u v; fin_cases u <;> fin_cases v <;> decide)
    (by
      intro u v hne
      fin_cases u <;> fin_cases v
      · decide
      · decide
      · exact absurd rfl hne
      · exact absurd rfl hne
      · exact absurd rfl hne
      · decide
      · exact absurd rfl hne
      · exact absurd rfl hne
      · exact absurd rfl hne)

example : testBasePorts.outPort 0 0 = some (0, 0) ∧
    testBasePorts.outPort 0 1 = some (1, 0) ∧
    testBasePorts.outWeight 0 0 = 1 / 2 ∧
    testBasePorts.outWeight 0 1 = 1 / 2 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · simp [testBasePorts, Matrix.PairedPorts.ofLists, Matrix.PairedPorts.listPortLookup,
      testOutList, testBaseMatrix]
  · simp [testBasePorts, Matrix.PairedPorts.ofLists, Matrix.PairedPorts.listPortLookup,
      testOutList, testBaseMatrix]

example : testBasePorts.outPort 1 0 = some (2, 0) ∧
    testBasePorts.outPort 1 1 = none ∧
    testBasePorts.outWeight 1 0 = 1 ∧
    testBasePorts.outWeight 1 1 = 0 ∧
    testBasePorts.inPort 2 0 = some (1, 0) ∧
    testBasePorts.inWeight 2 0 = 1 := by
  refine ⟨by decide, by decide, ?_, ?_, by decide, ?_⟩
  · simp [testBasePorts, Matrix.PairedPorts.ofLists, Matrix.PairedPorts.listPortLookup,
      testOutList, testBaseMatrix]
  · simp [testBasePorts, Matrix.PairedPorts.ofLists, Matrix.PairedPorts.listPortLookup,
      testOutList, testBaseMatrix]
  · simp [Matrix.PairedPorts.inWeight, testBasePorts, Matrix.PairedPorts.ofLists,
      Matrix.PairedPorts.listPortLookup, testOutList, testInList, testBaseMatrix]

/-- Time-layered paired ports on `Fin ((2 + 1) * 3) = Fin 9` at horizon `T = 2`. -/
def testLayeredPorts : (Matrix.finTimeLayer 2 testBaseMatrix).PairedPorts 2 2 :=
  testBasePorts.finTimeLayer 2

example :
    testLayeredPorts.outPort ⟨0, by decide⟩ 0 = some (⟨3, by decide⟩, 0) ∧
    testLayeredPorts.outPort ⟨0, by decide⟩ 1 = some (⟨4, by decide⟩, 0) ∧
    testLayeredPorts.outPort ⟨4, by decide⟩ 0 = some (⟨8, by decide⟩, 0) ∧
    testLayeredPorts.outPort ⟨4, by decide⟩ 1 = none ∧
    testLayeredPorts.outPort ⟨6, by decide⟩ 0 = none ∧
    testLayeredPorts.inPort ⟨0, by decide⟩ 0 = none ∧
    testLayeredPorts.inPort ⟨4, by decide⟩ 0 = some (⟨0, by decide⟩, 1) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

example (x : Fin 9 → ℚ) (u : Fin 9) :
    (Matrix.finTimeLayer 2 testBaseMatrix *ᵥ x) u =
      ∑ p : Fin 2,
        match testLayeredPorts.outPort u p with
        | none => (0 : ℚ)
        | some (v, _) => testLayeredPorts.outWeight u p * x v := by
  rw [testLayeredPorts.mulVec_apply_eq_sum_outPort]
  refine Finset.sum_congr rfl fun p _ => ?_
  cases testLayeredPorts.outPort u p <;> rfl

example (x : Fin 9 → ℚ) (v : Fin 9) :
    ((Matrix.finTimeLayer 2 testBaseMatrix)ᵀ *ᵥ x) v =
      ∑ q : Fin 2,
        match testLayeredPorts.inPort v q with
        | none => (0 : ℚ)
        | some (u, p) => testLayeredPorts.outWeight u p * x u := by
  rw [testLayeredPorts.transpose_mulVec_apply_eq_sum_inPort_outWeight]
  refine Finset.sum_congr rfl fun q _ => ?_
  cases testLayeredPorts.inPort v q <;> rfl

end MatrixPairedPortsTests

/-! ### 2. Concrete fair-coin machine paired-port checks -/

section FairCoinMachineTests

/-- Halting action emitting `[b]` with zero work tapes (`k = 0`) and `State = Unit`. -/
def haltEmitAct (b : Bool) : Turing.Action 0 Bool Unit :=
  ⟨0, Fin.elim0, some b, none⟩

/-- One-step fair-coin machine (`k = 0`, `State = Unit`) whose coin `false` halts with `[false]`
and whose coin `true` halts with `[true]`. -/
def splitCoinMachine : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit := .step (haltEmitAct bit) Empty.elim Empty.elim

/-- One-step fair-coin machine whose two coin branches coincide and halt with `[true]`. -/
def mergedCoinMachine : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ _ := .step (haltEmitAct true) Empty.elim Empty.elim

/-- Ambient radix `radix 2 0 = 4` for empty-input tests. -/
abbrev testB : ℕ := radix 2 0

/-- Ambient base vertex count `vertexBound (radix 2 0) = 64` for empty-input tests. -/
abbrev testN : ℕ := vertexBound (k := 0) testB

/-- Every `FiniteCfg 0 Bool Unit` on empty input `[]` fits radix `testB = 4`. -/
theorem fits_empty_radix2 (v : FiniteCfg 0 Bool Unit) (hv : v.input = []) :
    Fits testB (registers v) := by
  intro i
  have hB : testB = 4 := rfl
  rw [hB]
  cases i with
  | inputPos =>
    dsimp only [registers]
    have hlt := v.inputPos.isLt
    have hlen : v.input.length = 0 := by simp [hv]
    omega
  | control =>
    dsimp only [registers]
    have hlt : stateCode v.state < Fintype.card (Option Unit) :=
      (Fintype.equivFin (Option Unit) v.state).isLt
    have hcard : Fintype.card (Option Unit) = 2 := by decide
    omega
  | output =>
    dsimp only [registers]
    have hlt := outputCode_lt v.output
    omega
  | head j => exact Fin.elim0 j
  | left j => exact Fin.elim0 j
  | right j => exact Fin.elim0 j

/-- On `splitCoinMachine` from the initial vertex on `[]`, the two coin branches produce distinct
compact target IDs, so both outgoing ports `0` and `1` are active with multiplicity `1` each. -/
example :
    let u₀ := startID splitCoinMachine.toNTM testB
    ∃ b₀ q₀ b₁ q₁,
      b₀ ≠ b₁ ∧
      clockedOutPort splitCoinMachine 2 0 [] u₀ 0 = some (b₀, q₀) ∧
      clockedOutPort splitCoinMachine 2 0 [] u₀ 1 = some (b₁, q₁) ∧
      clockedInPort splitCoinMachine 2 0 [] b₀ q₀ = some (u₀, 0) ∧
      clockedInPort splitCoinMachine 2 0 [] b₁ q₁ = some (u₀, 1) ∧
      clockedOutCount splitCoinMachine 2 0 [] u₀ 0 = 1 ∧
      clockedOutCount splitCoinMachine 2 0 [] u₀ 1 = 1 := by
  let v₀ : FiniteCfg 0 Bool Unit := splitCoinMachine.toNTM.initView []
  let vF : FiniteCfg 0 Bool Unit := (v₀.step (haltEmitAct false)).summarizeOutput
  let vT : FiniteCfg 0 Bool Unit := (v₀.step (haltEmitAct true)).summarizeOutput
  have hf₀ : Fits testB (registers v₀) := fits_empty_radix2 v₀ rfl
  have hfF : Fits testB (registers vF) := fits_empty_radix2 vF rfl
  have hfT : Fits testB (registers vT) := fits_empty_radix2 vT rfl
  have hu₀_eq : vertexID testB v₀ = startID splitCoinMachine.toNTM testB :=
    vertexID_init splitCoinMachine.toNTM testB []
  have hv₀_in : v₀.input = [] := rfl
  have hv₀_out : v₀.output = [] := rfl
  have hstepF : stepTargetWithSymbol (splitCoinMachine.withCoin false).toTM testB 0
      (vertexID testB v₀) none = some (vertexID testB vF) := by
    rw [stepTargetWithSymbol_eq_some_iff]
    have hview : (splitCoinMachine.withCoin false).toTM.toMultiTapeNTM.ViewStep v₀ vF := by
      refine ⟨haltEmitAct false, ?_, rfl⟩
      rw [MultiTapeTM.tr_iff]
      simp [MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr, MultiTapePTM.withCoin,
        splitCoinMachine, MultiTapeMachine.Action.emptyOracleEquiv]
    have hedge := edge_complete hf₀ hfF hview
    rw [Edge, hv₀_in] at hedge
    simpa using hedge
  have hstepT : stepTargetWithSymbol (splitCoinMachine.withCoin true).toTM testB 0
      (vertexID testB v₀) none = some (vertexID testB vT) := by
    rw [stepTargetWithSymbol_eq_some_iff]
    have hview : (splitCoinMachine.withCoin true).toTM.toMultiTapeNTM.ViewStep v₀ vT := by
      refine ⟨haltEmitAct true, ?_, rfl⟩
      rw [MultiTapeTM.tr_iff]
      simp [MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr, MultiTapePTM.withCoin,
        splitCoinMachine, MultiTapeMachine.Action.emptyOracleEquiv]
    have hedge := edge_complete hf₀ hfT hview
    rw [Edge, hv₀_in] at hedge
    simpa using hedge
  have hne_FT : vertexID testB vF ≠ vertexID testB vT := by
    intro heq
    have hreg := (readRegisters_vertexID hfF).symm.trans
      (congrArg (readRegisters (k := 0) testB) heq |>.trans (readRegisters_vertexID hfT))
    have hout : registers vF .output = registers vT .output := congrFun hreg .output
    have hF_out : registers vF .output = 2 := by
      dsimp only [registers, vF, FiniteCfg.summarizeOutput, FiniteCfg.step, haltEmitAct]
      rw [hv₀_out, outputCode_append [] (some false)]
      rfl
    have hT_out : registers vT .output = 1 := by
      dsimp only [registers, vT, FiniteCfg.summarizeOutput, FiniteCfg.step, haltEmitAct]
      rw [hv₀_out, outputCode_append [] (some true)]
      rfl
    omega
  have hu₀_lt : startID splitCoinMachine.toNTM testB < testN := hu₀_eq ▸ vertexID_lt hf₀
  have ha_lt : startID splitCoinMachine.toNTM testB < clockedVertexBound (k := 0) 2 0 0 := by
    dsimp only [clockedVertexBound]
    calc startID splitCoinMachine.toNTM testB < 1 * testN := by omega
      _ ≤ (polyClock 0 0 + 1) * testN := Nat.mul_le_mul_right testN (by decide)
  have hdiv : startID splitCoinMachine.toNTM testB / testN = 0 := Nat.div_eq_of_lt hu₀_lt
  have hmod : startID splitCoinMachine.toNTM testB % testN = vertexID testB v₀ := by
    rw [Nat.mod_eq_of_lt hu₀_lt, hu₀_eq]
  have htargets :
      coinOutTargetsWithSymbol splitCoinMachine testB 0 (vertexID testB v₀) none =
        if vertexID testB vF < vertexID testB vT then [vertexID testB vF, vertexID testB vT]
        else [vertexID testB vT, vertexID testB vF] := by
    by_cases hlt : vertexID testB vF < vertexID testB vT
    · rw [ite_eq_left hlt]
      exact coinOutTargetsWithSymbol_eq_pair_of_lt splitCoinMachine hstepF hstepT hlt
    · have hgt : vertexID testB vT < vertexID testB vF := by omega
      rw [ite_eq_right hlt]
      exact coinOutTargetsWithSymbol_eq_pair_of_gt splitCoinMachine hstepF hstepT hgt
  have hcountF :
      coinCountWithSymbol splitCoinMachine testB 0
        (vertexID testB v₀) (vertexID testB vF) none = 1 := by
    have heF := (stepTargetWithSymbol_eq_some_iff _ _ _ _ _ _).mp hstepF
    have heT : edgeWithSymbol (splitCoinMachine.withCoin true).toTM.toMultiTapeNTM testB 0
        (vertexID testB v₀) (vertexID testB vF) none = false := by
      cases h : edgeWithSymbol (splitCoinMachine.withCoin true).toTM.toMultiTapeNTM testB 0
          (vertexID testB v₀) (vertexID testB vF) none with
      | false => rfl
      | true =>
        have hs := (stepTargetWithSymbol_eq_some_iff _ _ _ _ _ _).mpr h
        rw [hstepT, Option.some.injEq] at hs
        exact absurd hs.symm hne_FT
    simp [coinCountWithSymbol, heF, heT]
  have hcountT :
      coinCountWithSymbol splitCoinMachine testB 0
        (vertexID testB v₀) (vertexID testB vT) none = 1 := by
    have heT := (stepTargetWithSymbol_eq_some_iff _ _ _ _ _ _).mp hstepT
    have heF : edgeWithSymbol (splitCoinMachine.withCoin false).toTM.toMultiTapeNTM testB 0
        (vertexID testB v₀) (vertexID testB vT) none = false := by
      cases h : edgeWithSymbol (splitCoinMachine.withCoin false).toTM.toMultiTapeNTM testB 0
          (vertexID testB v₀) (vertexID testB vT) none with
      | false => rfl
      | true =>
        have hs := (stepTargetWithSymbol_eq_some_iff _ _ _ _ _ _).mpr h
        rw [hstepF, Option.some.injEq] at hs
        exact absurd hs hne_FT
    simp [coinCountWithSymbol, heF, heT]
  have hc0 : startID splitCoinMachine.toNTM testB < clockedVertexBound (k := 0) 2 0 0 ∧
      0 < 2 ∧ startID splitCoinMachine.toNTM testB / testN < polyClock 0 0 :=
    ⟨ha_lt, by decide, by simp [hdiv, polyClock]⟩
  have hc1 : startID splitCoinMachine.toNTM testB < clockedVertexBound (k := 0) 2 0 0 ∧
      1 < 2 ∧ startID splitCoinMachine.toNTM testB / testN < polyClock 0 0 :=
    ⟨ha_lt, by decide, by simp [hdiv, polyClock]⟩
  by_cases hlt : vertexID testB vF < vertexID testB vT
  · have ht : coinOutTargetsWithSymbol splitCoinMachine testB 0 (vertexID testB v₀) none =
        [vertexID testB vF, vertexID testB vT] := by simp [htargets, hlt]
    have hp0 : clockedOutPort splitCoinMachine 2 0 [] (startID splitCoinMachine.toNTM testB) 0 =
        some (testN + vertexID testB vF,
          (coinInSources splitCoinMachine testB [] (vertexID testB vF)).idxOf
            (vertexID testB v₀)) := by
      dsimp only [clockedOutPort, List.length_nil]
      rw [ite_eq_left hc0]
      simp [hdiv, hmod, ht]
    have hp1 : clockedOutPort splitCoinMachine 2 0 [] (startID splitCoinMachine.toNTM testB) 1 =
        some (testN + vertexID testB vT,
          (coinInSources splitCoinMachine testB [] (vertexID testB vT)).idxOf
            (vertexID testB v₀)) := by
      dsimp only [clockedOutPort, List.length_nil]
      rw [ite_eq_left hc1]
      simp [hdiv, hmod, ht]
    refine ⟨_, _, _, _, by omega, hp0, hp1,
      (clockedOutPort_eq_some_iff splitCoinMachine 2 0 [] _ _ _ _).mp hp0,
      (clockedOutPort_eq_some_iff splitCoinMachine 2 0 [] _ _ _ _).mp hp1, ?_, ?_⟩
    · dsimp only [clockedOutCount, clockedOutCountWithSymbol, List.length_nil]
      rw [ite_eq_left hc0]
      simp [hmod, ht, hcountF]
    · dsimp only [clockedOutCount, clockedOutCountWithSymbol, List.length_nil]
      rw [ite_eq_left hc1]
      simp [hmod, ht, hcountT]
  · have ht : coinOutTargetsWithSymbol splitCoinMachine testB 0 (vertexID testB v₀) none =
        [vertexID testB vT, vertexID testB vF] := by simp [htargets, hlt]
    have hp0 : clockedOutPort splitCoinMachine 2 0 [] (startID splitCoinMachine.toNTM testB) 0 =
        some (testN + vertexID testB vT,
          (coinInSources splitCoinMachine testB [] (vertexID testB vT)).idxOf
            (vertexID testB v₀)) := by
      dsimp only [clockedOutPort, List.length_nil]
      rw [ite_eq_left hc0]
      simp [hdiv, hmod, ht]
    have hp1 : clockedOutPort splitCoinMachine 2 0 [] (startID splitCoinMachine.toNTM testB) 1 =
        some (testN + vertexID testB vF,
          (coinInSources splitCoinMachine testB [] (vertexID testB vF)).idxOf
            (vertexID testB v₀)) := by
      dsimp only [clockedOutPort, List.length_nil]
      rw [ite_eq_left hc1]
      simp [hdiv, hmod, ht]
    refine ⟨_, _, _, _, by omega, hp0, hp1,
      (clockedOutPort_eq_some_iff splitCoinMachine 2 0 [] _ _ _ _).mp hp0,
      (clockedOutPort_eq_some_iff splitCoinMachine 2 0 [] _ _ _ _).mp hp1, ?_, ?_⟩
    · dsimp only [clockedOutCount, clockedOutCountWithSymbol, List.length_nil]
      rw [ite_eq_left hc0]
      simp [hmod, ht, hcountT]
    · dsimp only [clockedOutCount, clockedOutCountWithSymbol, List.length_nil]
      rw [ite_eq_left hc1]
      simp [hmod, ht, hcountF]

/-- Accepting halted view reached in one step by `mergedCoinMachine` on `[]`. -/
noncomputable abbrev mergedAcceptView : FiniteCfg 0 Bool Unit :=
  ((mergedCoinMachine.toNTM.initView []).step (haltEmitAct true)).summarizeOutput

/-- On `mergedCoinMachine`, coincident coin branches merge onto port `0` with multiplicity `2`
while port `1` is `none` with multiplicity `0`; at clock `1` the halted target advances along port
`0` with multiplicity `2`; at terminal clock `2` all outgoing ports vanish and `clockedAccept`
evaluates to `true`. -/
example :
    let u₀ := startID mergedCoinMachine.toNTM testB
    let vT := vertexID testB mergedAcceptView
    (∃ q₀, clockedOutPort mergedCoinMachine 2 0 [] u₀ 0 = some (testN + vT, q₀)) ∧
    clockedOutPort mergedCoinMachine 2 0 [] u₀ 1 = none ∧
    clockedOutCount mergedCoinMachine 2 0 [] u₀ 0 = 2 ∧
    clockedOutCount mergedCoinMachine 2 0 [] u₀ 1 = 0 ∧
    (∃ q₁, clockedOutPort mergedCoinMachine 2 0 [] (testN + vT) 0 = some (2 * testN + vT, q₁)) ∧
    clockedOutPort mergedCoinMachine 2 0 [] (testN + vT) 1 = none ∧
    clockedOutCount mergedCoinMachine 2 0 [] (testN + vT) 0 = 2 ∧
    clockedOutPort mergedCoinMachine 2 0 [] (2 * testN + vT) 0 = none ∧
    clockedOutCount mergedCoinMachine 2 0 [] (2 * testN + vT) 0 = 0 ∧
    clockedAccept (k := 0) (State := Unit) testB 0 2 (2 * testN + vT) = true := by
  dsimp only
  let v₀ : FiniteCfg 0 Bool Unit := mergedCoinMachine.toNTM.initView []
  have hf₀ : Fits testB (registers v₀) := fits_empty_radix2 v₀ rfl
  have hfT : Fits testB (registers mergedAcceptView) := fits_empty_radix2 mergedAcceptView rfl
  have hu₀_eq : vertexID testB v₀ = startID mergedCoinMachine.toNTM testB :=
    vertexID_init mergedCoinMachine.toNTM testB []
  have hv₀_in : v₀.input = [] := rfl
  have hvT_in : mergedAcceptView.input = [] := rfl
  have hv₀_out : v₀.output = [] := rfl
  have hstep₀ (bit : Bool) : stepTargetWithSymbol (mergedCoinMachine.withCoin bit).toTM testB 0
      (vertexID testB v₀) none = some (vertexID testB mergedAcceptView) := by
    rw [stepTargetWithSymbol_eq_some_iff]
    have hview : (mergedCoinMachine.withCoin bit).toTM.toMultiTapeNTM.ViewStep v₀
        mergedAcceptView := by
      refine ⟨haltEmitAct true, ?_, rfl⟩
      rw [MultiTapeTM.tr_iff]
      simp [MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr, MultiTapePTM.withCoin,
        mergedCoinMachine, MultiTapeMachine.Action.emptyOracleEquiv]
    have hedge := edge_complete hf₀ hfT hview
    rw [Edge, hv₀_in] at hedge
    simpa using hedge
  have hstepT (bit : Bool) : stepTargetWithSymbol (mergedCoinMachine.withCoin bit).toTM testB 0
      (vertexID testB mergedAcceptView) none = some (vertexID testB mergedAcceptView) := by
    rw [stepTargetWithSymbol_eq_some_iff]
    have hview : (mergedCoinMachine.withCoin bit).toTM.toMultiTapeNTM.ViewStep
        mergedAcceptView mergedAcceptView := by
      have hs : mergedAcceptView.state = none := rfl
      simp [MultiTapeNTM.ViewStep, hs]
    have hedge := edge_complete hfT hfT hview
    rw [Edge, hvT_in] at hedge
    simpa using hedge
  have ht₀ : coinOutTargetsWithSymbol mergedCoinMachine testB 0 (vertexID testB v₀) none =
      [vertexID testB mergedAcceptView] :=
    coinOutTargetsWithSymbol_eq_singleton mergedCoinMachine (hstep₀ false) (hstep₀ true)
  have htT : coinOutTargetsWithSymbol mergedCoinMachine testB 0
      (vertexID testB mergedAcceptView) none = [vertexID testB mergedAcceptView] :=
    coinOutTargetsWithSymbol_eq_singleton mergedCoinMachine (hstepT false) (hstepT true)
  have hc₀ :
      coinCountWithSymbol mergedCoinMachine testB 0
        (vertexID testB v₀) (vertexID testB mergedAcceptView) none = 2 := by
    have heF := (stepTargetWithSymbol_eq_some_iff _ _ _ _ _ _).mp (hstep₀ false)
    have heT := (stepTargetWithSymbol_eq_some_iff _ _ _ _ _ _).mp (hstep₀ true)
    simp [coinCountWithSymbol, heF, heT]
  have hcT :
      coinCountWithSymbol mergedCoinMachine testB 0
        (vertexID testB mergedAcceptView) (vertexID testB mergedAcceptView) none = 2 := by
    have heF := (stepTargetWithSymbol_eq_some_iff _ _ _ _ _ _).mp (hstepT false)
    have heT := (stepTargetWithSymbol_eq_some_iff _ _ _ _ _ _).mp (hstepT true)
    simp [coinCountWithSymbol, heF, heT]
  have hu₀_lt : startID mergedCoinMachine.toNTM testB < testN := hu₀_eq ▸ vertexID_lt hf₀
  have hvT_lt : vertexID testB mergedAcceptView < testN := vertexID_lt hfT
  have hN_pos : 0 < testN := Nat.zero_lt_of_lt hvT_lt
  have hdiv₀ : startID mergedCoinMachine.toNTM testB / testN = 0 := Nat.div_eq_of_lt hu₀_lt
  have hmod₀ : startID mergedCoinMachine.toNTM testB % testN = vertexID testB v₀ := by
    rw [Nat.mod_eq_of_lt hu₀_lt, hu₀_eq]
  have hdiv₁ : (testN + vertexID testB mergedAcceptView) / testN = 1 := by
    have h1 : testN + vertexID testB mergedAcceptView =
        vertexID testB mergedAcceptView + 1 * testN := by omega
    rw [h1, Nat.add_mul_div_right _ _ hN_pos, Nat.div_eq_of_lt hvT_lt, Nat.zero_add]
  have hmod₁ : (testN + vertexID testB mergedAcceptView) % testN =
      vertexID testB mergedAcceptView := by
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hvT_lt]
  have hdiv₂ : (2 * testN + vertexID testB mergedAcceptView) / testN = 2 := by
    have h2 : 2 * testN + vertexID testB mergedAcceptView =
        vertexID testB mergedAcceptView + 2 * testN := by omega
    rw [h2, Nat.add_mul_div_right _ _ hN_pos, Nat.div_eq_of_lt hvT_lt, Nat.zero_add]
  have hmod₂ : (2 * testN + vertexID testB mergedAcceptView) % testN =
      vertexID testB mergedAcceptView := by
    have h2 : 2 * testN + vertexID testB mergedAcceptView =
        vertexID testB mergedAcceptView + testN * 2 := by ring
    rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hvT_lt]
  have hlt₀ : startID mergedCoinMachine.toNTM testB < clockedVertexBound (k := 0) 2 0 0 := by
    dsimp only [clockedVertexBound]
    calc startID mergedCoinMachine.toNTM testB < 1 * testN := by omega
      _ ≤ (polyClock 0 0 + 1) * testN := Nat.mul_le_mul_right testN (by decide)
  have hlt₁ : testN + vertexID testB mergedAcceptView < clockedVertexBound (k := 0) 2 0 0 := by
    dsimp only [clockedVertexBound]
    calc testN + vertexID testB mergedAcceptView < 2 * testN := by omega
      _ ≤ (polyClock 0 0 + 1) * testN := Nat.mul_le_mul_right testN (by decide)
  have hc0_0 : startID mergedCoinMachine.toNTM testB < clockedVertexBound (k := 0) 2 0 0 ∧
      0 < 2 ∧ startID mergedCoinMachine.toNTM testB / testN < polyClock 0 0 :=
    ⟨hlt₀, by decide, by simp [hdiv₀, polyClock]⟩
  have hc0_1 : startID mergedCoinMachine.toNTM testB < clockedVertexBound (k := 0) 2 0 0 ∧
      1 < 2 ∧ startID mergedCoinMachine.toNTM testB / testN < polyClock 0 0 :=
    ⟨hlt₀, by decide, by simp [hdiv₀, polyClock]⟩
  have hc1_0 : testN + vertexID testB mergedAcceptView < clockedVertexBound (k := 0) 2 0 0 ∧
      0 < 2 ∧ (testN + vertexID testB mergedAcceptView) / testN < polyClock 0 0 :=
    ⟨hlt₁, by decide, by simp [hdiv₁, polyClock]⟩
  have hc1_1 : testN + vertexID testB mergedAcceptView < clockedVertexBound (k := 0) 2 0 0 ∧
      1 < 2 ∧ (testN + vertexID testB mergedAcceptView) / testN < polyClock 0 0 :=
    ⟨hlt₁, by decide, by simp [hdiv₁, polyClock]⟩
  have hp₀_1 : clockedOutPort mergedCoinMachine 2 0 [] (startID mergedCoinMachine.toNTM testB) 1 =
      none := by
    dsimp only [clockedOutPort, List.length_nil]
    rw [ite_eq_left hc0_1]
    simp [hmod₀, ht₀]
  have hp₂_0 : clockedOutPort mergedCoinMachine 2 0 []
      (2 * testN + vertexID testB mergedAcceptView) 0 = none := by
    dsimp only [clockedOutPort, List.length_nil]
    have hc : ¬ (2 * testN + vertexID testB mergedAcceptView < clockedVertexBound (k := 0) 2 0 0 ∧
        0 < 2 ∧
        (2 * testN + vertexID testB mergedAcceptView) / testN < polyClock 0 0) := by
      simp [hdiv₂, polyClock]
    rw [ite_eq_right hc]
  refine ⟨?_, hp₀_1, ?_,
    clockedOutCount_eq_zero_of_outPort_eq_none mergedCoinMachine hp₀_1,
    ?_, ?_, ?_, hp₂_0,
    clockedOutCount_eq_zero_of_outPort_eq_none mergedCoinMachine hp₂_0, ?_⟩
  · refine ⟨(coinInSources mergedCoinMachine testB [] (vertexID testB mergedAcceptView)).idxOf
      (vertexID testB v₀), ?_⟩
    dsimp only [clockedOutPort, List.length_nil]
    rw [ite_eq_left hc0_0]
    simp [hdiv₀, hmod₀, ht₀]
  · dsimp only [clockedOutCount, clockedOutCountWithSymbol, List.length_nil]
    rw [ite_eq_left hc0_0]
    simp [hmod₀, ht₀, hc₀]
  · refine ⟨(coinInSources mergedCoinMachine testB [] (vertexID testB mergedAcceptView)).idxOf
      (vertexID testB mergedAcceptView), ?_⟩
    dsimp only [clockedOutPort, List.length_nil]
    rw [ite_eq_left hc1_0]
    have hmul : (1 + 1) * testN + vertexID testB mergedAcceptView =
        2 * testN + vertexID testB mergedAcceptView := by ring
    simp [hdiv₁, hmod₁, htT, hmul]
  · dsimp only [clockedOutPort, List.length_nil]
    rw [ite_eq_left hc1_1]
    simp [hmod₁, htT]
  · dsimp only [clockedOutCount, clockedOutCountWithSymbol, List.length_nil]
    rw [ite_eq_left hc1_0]
    simp [hmod₁, htT, hcT]
  · dsimp only [clockedAccept]
    rw [hdiv₂, ite_eq_left rfl, hmod₂]
    have hout : mergedAcceptView.output = [true] := by
      dsimp only [mergedAcceptView, FiniteCfg.summarizeOutput, FiniteCfg.step, haltEmitAct]
      rw [hv₀_out]
      rfl
    have hbad : bad (k := 0) (State := Unit) testB mergedAcceptView.input.length
        (vertexID testB mergedAcceptView) = true :=
      (bad_vertexID hfT).mpr ⟨rfl, hout⟩
    rw [hvT_in] at hbad
    exact hbad

/-- Out-of-range vertex and port arguments return `none` / `0` / `false`. -/
example :
    let bound := clockedVertexBound (k := 0) 2 0 0
    clockedOutPort splitCoinMachine 2 0 [] bound 0 = none ∧
    clockedOutPort splitCoinMachine 2 0 [] 0 2 = none ∧
    clockedInPort splitCoinMachine 2 0 [] bound 0 = none ∧
    clockedInPort splitCoinMachine 2 0 [] 0 (inPortBound splitCoinMachine) = none ∧
    clockedOutCount splitCoinMachine 2 0 [] bound 0 = 0 ∧
    clockedOutCount splitCoinMachine 2 0 [] 0 2 = 0 ∧
    clockedAccept (k := 0) (State := Unit) testB 0 2 bound = false :=
  ⟨clockedOutPort_eq_none_of_ge_bound splitCoinMachine le_rfl 0,
    clockedOutPort_eq_none_of_port_ge splitCoinMachine 0 le_rfl,
    clockedInPort_eq_none_of_ge_bound splitCoinMachine le_rfl 0,
    clockedInPort_eq_none_of_port_ge splitCoinMachine 0 le_rfl,
    clockedOutCount_eq_zero_of_ge_bound splitCoinMachine le_rfl 0,
    clockedOutCount_eq_zero_of_port_ge splitCoinMachine 0 le_rfl,
    clockedAccept_eq_false_of_ge_bound (k := 0) (State := Unit) (D := 2) (d := 0) (n := 0) le_rfl⟩

end FairCoinMachineTests

/-! ### 3. Non-vacuous `RL` / `BPL` `PairedTimeLayerFamily` and `ComputableInLogSpace` checks -/

section ComplexityClassTests

/-- Nontrivial test language `{true}` on `Bool`, containing `true` and excluding `false`. -/
def trueSet : Set Bool := {b | b = true}

theorem trueSet_mem_L : trueSet ∈ L encBool :=
  ⟨id, ComputableInLogSpace.id, fun _ => Iff.rfl⟩

theorem trueSet_mem_RL : trueSet ∈ RL encBool :=
  L_subset_RL trueSet_mem_L

theorem trueSet_mem_BPL : trueSet ∈ BPL encBool :=
  L_subset_BPL trueSet_mem_L

/-- Non-vacuous instantiation of `exists_pairedTimeLayerFamily_of_mem_RL` on `trueSet`, checking
both accepting (`true`) and rejecting (`false`) potentials and all six `ComputableInLogSpace`
evaluators. -/
example :
    ∃ F : PairedTimeLayerFamily encBool,
      0 < F.dIn ∧
      0 < F.dim true ∧
      1 / 2 ≤ F.potential true (F.start true) ∧
      F.potential false (F.start false) = 0 ∧
      ComputableInLogSpace F.dim encBool encNat ∧
      ComputableInLogSpace F.startNat encBool encNat ∧
      ComputableInLogSpace (fun (b, u) => F.acceptBool b u)
        (encPair encBool encNat) encBool ∧
      ComputableInLogSpace (fun (b, u, p) => F.outCount b u p)
        (encPair encBool (encPair encNat encNat)) encNat ∧
      ComputableInLogSpace (fun (b, u, p) => F.outPortNat b u p)
        (encPair encBool (encPair encNat encNat)) (encOption (encPair encNat encNat)) ∧
      ComputableInLogSpace (fun (b, v, q) => F.inPortNat b v q)
        (encPair encBool (encPair encNat encNat)) (encOption (encPair encNat encNat)) := by
  obtain ⟨F, hF⟩ := exists_pairedTimeLayerFamily_of_mem_RL trueSet_mem_RL
  refine ⟨F, F.dIn_pos, F.dim_pos true, (hF true).1 rfl,
    (hF false).2 (by simp [trueSet]),
    F.computableInLogSpace_dim, F.computableInLogSpace_startNat,
    F.computableInLogSpace_acceptBool, F.computableInLogSpace_outCount,
    F.computableInLogSpace_outPortNat, F.computableInLogSpace_inPortNat⟩

/-- Non-vacuous instantiation of `exists_pairedTimeLayerFamily_of_mem_BPL` on `trueSet`, checking
both accepting (`≥ 2/3`) and rejecting (`≤ 1/3`) potentials, active-port positivity, and strict
topological progress `u < v`. -/
example :
    ∃ F : PairedTimeLayerFamily encBool,
      2 / 3 ≤ F.potential true (F.start true) ∧
      F.potential false (F.start false) ≤ 1 / 3 ∧
      (∀ b u p, F.outCount b u p = 0 ↔ F.outPortNat b u p = none) ∧
      (∀ b {u p v q}, F.outPortNat b u p = some (v, q) →
        0 < F.outCount b u p ∧ u < v ∧ v < F.dim b ∧ q < F.dIn) := by
  obtain ⟨F, hF⟩ := exists_pairedTimeLayerFamily_of_mem_BPL trueSet_mem_BPL
  refine ⟨F, (hF true).1 rfl, (hF false).2 (by simp [trueSet]), F.outCount_eq_zero_iff, ?_⟩
  intro b u p v q h
  obtain ⟨_, _, hv, hq⟩ := F.bounds_of_outPortNat_eq_some b h
  exact ⟨F.outCount_pos_of_outPortNat_eq_some b h, F.lt_of_outPortNat_eq_some b h, hv, hq⟩

/-- Direct check of `PairedTimeLayerFamily.ofMachine_potential_start` on `splitCoinMachine`
(`k = 0`, so `RunsInSpace w 0` holds unconditionally). -/
example :
    let hs : ∀ _ : Unit, splitCoinMachine.toNTM.RunsInSpace ([] : List Bool)
        (0 * (Nat.log2 ([] : List Bool).length + 1)) := by
      intro _ f
      change (∑ i : Fin 0, MultiTapeNTM.RunPath.spaceUsedByTape f.toRunPath i) ≤ _
      simp
    let encUnit : Unit ↪ List Bool := ⟨fun _ => [], fun _ _ _ => rfl⟩
    let F := PairedTimeLayerFamily.ofMachine encUnit splitCoinMachine 0 0 hs
    F.potential () (F.start ()) =
      (splitCoinMachine.acceptCoins [] 2 : ℝ) / 2 ^ 2 :=
  PairedTimeLayerFamily.ofMachine_potential_start _ splitCoinMachine 0 0 _ ()

end ComplexityClassTests

end CslibFrontierTests.LogSpace.PairedPorts
