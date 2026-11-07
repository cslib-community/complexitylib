/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.LogSpace.Randomized.ConfigurationReader

/-!
# Fair-coin compact-reader tests

A zero-work-tape machine either outputs its coin or outputs true on both branches. The tests
derive all representation hypotheses from its actual space bound and reachable configurations,
then evaluate the matrix entries through the new local reader. They distinguish zero, one and
two coin branches, and distinguish an absorbing halted row from the zero live row. Invalid IDs
and a native space certificate on the exact binary query tuple are also checked.
-/

namespace ComplexityTests.FairCoinConfigurationReader

open Cslib.Turing Turing MultiTapeTM
open MultiTapeNTM.ConfigurationGraph MultiTapePTM.ConfigurationGraph

/-- With `different = true`, output the coin; otherwise both branches output true. -/
private def machine (different : Bool) : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit :=
    .step
      { inputTape := 0
        workTapes := Fin.elim0
        output := some (if different then bit else true)
        state := none }
      Empty.elim Empty.elim

private def stopped (input : List Bool) (bit : Bool) : FiniteCfg 0 Bool Unit :=
  ⟨input, none, 1, Fin.elim0, [bit]⟩

private theorem viewCoinStep_start (different bit : Bool) (input : List Bool) :
    (machine different).viewCoinStep ((machine different).toNTM.initView input) bit =
      stopped input (if different then bit else true) := by
  cases different <;> cases bit <;>
    simp [MultiTapePTM.viewCoinStep, machine, MultiTapePTM.withCoin, MultiTapeMachine.toTM,
      MultiTapeMachine.Action.emptyOracleEquiv,
      MultiTapeNTM.initView, MultiTapePTM.toNTM, MultiTapePTM.branches, MultiTapeMachine.toNTM,
      FiniteCfg.init, FiniteCfg.step, FiniteCfg.summarizeOutput, MultiTapeNTM.outputClass,
      stopped, funext_iff]

private theorem stopped_injective (input : List Bool) : Function.Injective (stopped input) := by
  intro a b h
  have ho := congrArg FiniteCfg.output h
  simpa only [stopped, List.cons.injEq, and_true] using ho

private theorem stopped_ne_start (different bit : Bool) (input : List Bool) :
    stopped input bit ≠ (machine different).toNTM.initView input := by
  intro h
  have hs := congrArg FiniteCfg.state h
  cases hs

private abbrev radixFor (input : List Bool) : ℕ := radix (radixExponent Unit 0) input.length

private noncomputable def readCount (different : Bool) (input : List Bool)
    (x y : FiniteCfg 0 Bool Unit) : ℕ :=
  coinCountWithSymbol (machine different) (radixFor input) input.length
    (vertexID (radixFor input) x) (vertexID (radixFor input) y)
    input[queryIndex (k := 0) (radixFor input) (vertexID (radixFor input) x)]?

private noncomputable def readLiveCount (different : Bool) (input : List Bool)
    (x y : FiniteCfg 0 Bool Unit) : ℕ :=
  liveCoinCountWithSymbol (machine different) (radixFor input) input.length
    (vertexID (radixFor input) x) (vertexID (radixFor input) y)
    input[queryIndex (k := 0) (radixFor input) (vertexID (radixFor input) x)]?

private theorem reader_counts (different : Bool) (input : List Bool) :
    readCount different input ((machine different).toNTM.initView input) (stopped input true) =
        (if different then 1 else 2) ∧
      readCount different input ((machine different).toNTM.initView input)
        ((machine different).toNTM.initView input) = 0 ∧
      readCount different input (stopped input true) (stopped input true) = 2 ∧
      readLiveCount different input (stopped input true) (stopped input true) = 0 := by
  classical
  have hs := MultiTapeNTM.runsInSpace_zero_tapes (machine different).toNTM input 0
  obtain ⟨V, hreach, hclosed, _⟩ := (machine different).exists_finset_reachable hs
  have hinit : (machine different).toNTM.initView input ∈ V := (hreach _).mpr .refl
  have hstop : stopped input true ∈ V := by
    have h := hclosed _ hinit true
    simp only [viewCoinStep_start, ite_self] at h
    exact h
  let x : V := ⟨(machine different).toNTM.initView input, hinit⟩
  let y : V := ⟨stopped input true, hstop⟩
  have hV v hv := (hreach v).mp hv
  have hspace : (machine different).toNTM.RunsInSpace input
      (0 * (Nat.log2 input.length + 1)) := by
    rw [Nat.zero_mul]
    exact hs
  have hxy := coinCountWithSymbol_eq_configMatrix_of_reachable (R := ℕ)
    (machine different) 0 hspace hV x y
  have hxx := coinCountWithSymbol_eq_configMatrix_of_reachable (R := ℕ)
    (machine different) 0 hspace hV x x
  have hyy := coinCountWithSymbol_eq_configMatrix_of_reachable (R := ℕ)
    (machine different) 0 hspace hV y y
  have hlyy := liveCoinCountWithSymbol_eq_liveConfigMatrix_of_reachable (R := ℕ)
    (machine different) 0 hspace hV y y
  change readCount different input _ _ = _ at hxy hxx hyy
  change readLiveCount different input _ _ = _ at hlyy
  rw [hxy, hxx, hyy, hlyy]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [MultiTapePTM.configMatrix, Matrix.coinStepMatrix, Fintype.sum_bool, x, y,
      viewCoinStep_start, (stopped_injective input).eq_iff]
    cases different <;> decide
  · simp [MultiTapePTM.configMatrix, Matrix.coinStepMatrix, x, viewCoinStep_start,
      stopped_ne_start]
  · simp [MultiTapePTM.configMatrix, Matrix.coinStepMatrix, MultiTapePTM.viewCoinStep, y, stopped]
  · simp [MultiTapePTM.liveConfigMatrix, Matrix.liveCoinStepMatrix, y, stopped]

-- The actual encoded reader sees one coin edge, including on the empty input boundary.
example : readCount true [] ((machine true).toNTM.initView []) (stopped [] true) = 1 :=
  (reader_counts true []).1

-- Coincident successor branches contribute two, rather than one Boolean adjacency edge.
example : readCount false [true, false] ((machine false).toNTM.initView [true, false])
    (stopped [true, false] true) = 2 := (reader_counts false [true, false]).1

-- There is no transition back to the initial running view.
example (input : List Bool) :
    readCount true input ((machine true).toNTM.initView input)
      ((machine true).toNTM.initView input) = 0 := (reader_counts true input).2.1

-- Halting is absorbing in the count matrix and has zero outgoing weight in the live matrix.
example : readCount true [] (stopped [] true) (stopped [] true) = 2 ∧
    readLiveCount true [] (stopped [] true) (stopped [] true) = 0 :=
  (reader_counts true []).2.2

-- Out-of-box IDs cannot create a spurious transition for either supplied input symbol.
example (B n v : ℕ) (symbol : Option Bool) :
    coinCountWithSymbol (machine true) B n (vertexBound (k := 0) B) v symbol = 0 :=
  coinCountWithSymbol_eq_zero_of_source_ge _ (le_refl _) _

example (B n u : ℕ) (symbol : Option Bool) :
    coinCountWithSymbol (machine true) B n u (vertexBound (k := 0) B) symbol = 0 :=
  coinCountWithSymbol_eq_zero_of_target_ge _ (le_refl _) _

/-- The runtime query stores only its radix, input length, two IDs, and one supplied symbol. -/
private abbrev encQuery : ℕ × ℕ × ℕ × ℕ × Option Bool ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encPair encNat (encOption encBool))))

open ComputableInSpace in
-- A concrete query on its exact binary argument encoding has a native linear-space certificate.
example : ComputableInSpace
    (fun a : ℕ × ℕ × ℕ × ℕ × Option Bool =>
      liveCoinCountWithSymbol (machine true) a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    encQuery encNat (fun a => (encQuery a).length) := by
  have hr₁ := snd encNat (encPair encNat (encPair encNat (encPair encNat (encOption encBool))))
  have hr₂ := budget_comp_linear (snd _ _) hr₁
  have hr₃ := budget_comp_linear (snd _ _) hr₂
  exact liveCoinCountWithSymbol_budget (machine true) (fst _ _)
    (budget_comp_linear (fst _ _) hr₁) (budget_comp_linear (fst _ _) hr₂)
    (budget_comp_linear (fst _ _) hr₃) (budget_comp_linear (snd _ _) hr₃) (.refl _)

end ComplexityTests.FairCoinConfigurationReader
