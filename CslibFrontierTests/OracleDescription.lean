/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.Description

/-!
# Tests for finite oracle-machine descriptions

This module exercises the public description API across an ordinary module boundary. The machine
makes an empty first query, reads the reply symbol `7`, writes it into the next query buffer, and
submits `[7]` as its second query. A shared stateful handler logs both requests and returns `9` to
the second call; the machine reads and outputs that reply.

The example also checks zero clock, an empty table, out-of-range operation and successor tags,
and an invalid initial state tag. These are semantic boundary checks, not resource or security
claims.

The library's `Desc.runWith_toMachine` theorem gives denotational equality for an arbitrary shared
stateful handler. This client separately chooses one fixed logging handler and checks its complete
output/log law, plus zero-clock, empty-table and malformed-tag boundaries; that concrete trace is
not a claim about every handler.

## References

This checked client example is original to this module.
-/

@[expose] public section

namespace CslibFrontierTests.OracleDescription

open Cslib Cslib.Probability Turing Turing.MultiTapeMachine Turing.MultiTapePTM.Universal

/-- A deterministic ordinary action with no work tapes. -/
def ordinary (next output : Option ℕ) : Turing.MultiTapeTM.Universal.Act where
  inputTape := 0
  workTapes := []
  output := output
  state := next

/-- Store the same action for either private coin value. -/
def either (action : Act) : Branches := ⟨action, action⟩

/-- One blank work-head vector. -/
def noWork : Fin 0 → Option ℕ := Fin.elim0

/-- The sole channel's answer-head vector. -/
def oneAnswer (answer : Option ℕ) : Fin 1 → Option ℕ := fun _ => answer

/-- A four-step adaptive description:

1. query channel zero with `[]`;
2. read reply `7` and append it to channel zero's query buffer;
3. query channel zero with `[7]`;
4. read reply `9`, output it and halt.
-/
def description : Desc where
  tapes := 0
  states := 4
  operations := 1
  q₀ := 0
  table :=
    [ (key 0 none noWork (oneAnswer none), either (.query 0 1))
    , (key 1 none noWork (oneAnswer (some 7)),
        either (.step (ordinary (some 2) none) [some 7] []))
    , (key 2 none noWork (oneAnswer (some 7)), either (.query 0 3))
    , (key 3 none noWork (oneAnswer (some 9)),
        either (.step (ordinary none (some 9)) [] [])) ]

/-- The handler shares one log across both calls. It returns `[7]` to the first request and `[9]`
to every later request, while appending each request word to the log. -/
noncomputable def handler (_operationAndRequest : Fin 1 × List ℕ) :
    StateT (List (List ℕ)) PMF (List ℕ) := fun log =>
  PMF.pure ((if log.isEmpty then [7] else [9]), log ++ [_operationAndRequest.2])

private abbrev Control := Option (Fin 4)

private def operation : Fin 1 := 0

private def machine : MultiTapePTM 0 ℕ Control (Fin 1) := description.toMachine

private def cfg₀ : Config 0 ℕ Control (Fin 1) [] := machine.initialConfig []

private def cfg₁ : Config 0 ℕ Control (Fin 1) [] :=
  cfg₀.receive operation (some (1 : Fin 4)) [7]

private def cfg₂ : Config 0 ℕ Control (Fin 1) [] :=
  cfg₁.step (localAction 0 4 (ordinary (some 2) none))
    (fun op => [some 7].getD op.val none) (fun op => [].getD op.val 0)

private def cfg₃ : Config 0 ℕ Control (Fin 1) [] :=
  cfg₂.receive operation (some (3 : Fin 4)) [9]

private def cfg₄ : Config 0 ℕ Control (Fin 1) [] :=
  cfg₃.step (localAction 0 4 (ordinary none (some 9)))
    (fun op => [].getD op.val none) (fun op => [].getD op.val 0)

@[simp] private theorem cfg₀_state : cfg₀.tapes.state = some (some (0 : Fin 4)) := rfl

@[simp] private theorem cfg₀_queryBuffer : (cfg₀.channels (0 : Fin 1)).queryBuffer = [] := rfl

@[simp] private theorem cfg₁_state : cfg₁.tapes.state = some (some (1 : Fin 4)) := rfl

@[simp] private theorem cfg₂_state : cfg₂.tapes.state = some (some (2 : Fin 4)) := rfl

@[simp] private theorem cfg₂_queryBuffer : (cfg₂.channels (0 : Fin 1)).queryBuffer = [7] := rfl

@[simp] private theorem cfg₃_state : cfg₃.tapes.state = some (some (3 : Fin 4)) := rfl

@[simp] private theorem cfg₄_output : cfg₄.tapes.output = [9] := rfl

private theorem transition₀ (coin : Bool) :
    machine.tr (some (0 : Fin 4)) cfg₀.tapes.inputSymbol
      cfg₀.tapes.workTapeSymbols cfg₀.answerSymbols coin =
      .query operation (some (1 : Fin 4)) := by
  change description.action (some (0 : Fin 4)) cfg₀.tapes.inputSymbol
    cfg₀.tapes.workTapeSymbols cfg₀.answerSymbols coin = _
  have hfind : description.table.find?
      (·.1 = key (0 : Fin 4).val cfg₀.tapes.inputSymbol
        cfg₀.tapes.workTapeSymbols cfg₀.answerSymbols) =
      some (key 0 none noWork (oneAnswer none), either (.query 0 1)) := by
    rfl
  rw [Desc.action_of_find_eq_some description (0 : Fin 4) cfg₀.tapes.inputSymbol
    cfg₀.tapes.workTapeSymbols cfg₀.answerSymbols coin _ hfind]
  cases coin <;> rfl

private theorem transition₁ (coin : Bool) :
    machine.tr (some (1 : Fin 4)) cfg₁.tapes.inputSymbol
      cfg₁.tapes.workTapeSymbols cfg₁.answerSymbols coin =
      .step (localAction 0 4 (ordinary (some 2) none))
        (fun op => [some 7].getD op.val none) (fun op => [].getD op.val 0) := by
  change description.action (some (1 : Fin 4)) cfg₁.tapes.inputSymbol
    cfg₁.tapes.workTapeSymbols cfg₁.answerSymbols coin = _
  have hfind : description.table.find?
      (·.1 = key (1 : Fin 4).val cfg₁.tapes.inputSymbol
        cfg₁.tapes.workTapeSymbols cfg₁.answerSymbols) =
      some (key 1 none noWork (oneAnswer (some 7)),
        either (.step (ordinary (some 2) none) [some 7] [])) := by
    rfl
  rw [Desc.action_of_find_eq_some description (1 : Fin 4) cfg₁.tapes.inputSymbol
    cfg₁.tapes.workTapeSymbols cfg₁.answerSymbols coin _ hfind]
  cases coin <;> rfl

private theorem transition₂ (coin : Bool) :
    machine.tr (some (2 : Fin 4)) cfg₂.tapes.inputSymbol
      cfg₂.tapes.workTapeSymbols cfg₂.answerSymbols coin =
      .query operation (some (3 : Fin 4)) := by
  change description.action (some (2 : Fin 4)) cfg₂.tapes.inputSymbol
    cfg₂.tapes.workTapeSymbols cfg₂.answerSymbols coin = _
  have hfind : description.table.find?
      (·.1 = key (2 : Fin 4).val cfg₂.tapes.inputSymbol
        cfg₂.tapes.workTapeSymbols cfg₂.answerSymbols) =
      some (key 2 none noWork (oneAnswer (some 7)), either (.query 0 3)) := by
    rfl
  rw [Desc.action_of_find_eq_some description (2 : Fin 4) cfg₂.tapes.inputSymbol
    cfg₂.tapes.workTapeSymbols cfg₂.answerSymbols coin _ hfind]
  cases coin <;> rfl

private theorem transition₃ (coin : Bool) :
    machine.tr (some (3 : Fin 4)) cfg₃.tapes.inputSymbol
      cfg₃.tapes.workTapeSymbols cfg₃.answerSymbols coin =
      .step (localAction 0 4 (ordinary none (some 9)))
        (fun op => [].getD op.val none) (fun op => [].getD op.val 0) := by
  change description.action (some (3 : Fin 4)) cfg₃.tapes.inputSymbol
    cfg₃.tapes.workTapeSymbols cfg₃.answerSymbols coin = _
  have hfind : description.table.find?
      (·.1 = key (3 : Fin 4).val cfg₃.tapes.inputSymbol
        cfg₃.tapes.workTapeSymbols cfg₃.answerSymbols) =
      some (key 3 none noWork (oneAnswer (some 9)),
        either (.step (ordinary none (some 9)) [] [])) := by
    rfl
  rw [Desc.action_of_find_eq_some description (3 : Fin 4) cfg₃.tapes.inputSymbol
    cfg₃.tapes.workTapeSymbols cfg₃.answerSymbols coin _ hfind]
  cases coin <;> rfl

/-- Interpret a private fair coin before proving that it is irrelevant. This keeps the draw in the
open program and discards it only after every interpreted branch has the same full stateful law. -/
private theorem runWith_uniformBool_bind_const {Query State α : Type}
    {spec : Query → Type} (oracle : (q : Query) → StateT State PMF (spec q))
    (next : Bool → ProbOracleComp spec α) (state : State) (target : PMF (α × State))
    (hnext : ∀ bit, ProbOracleComp.runWith oracle (next bit) state = target) :
    ProbOracleComp.runWith oracle
      (ProbOracleComp.sample (ProbComp.uniform Bool) >>= next) state = target := by
  rw [ProbOracleComp.runWith_sample_bind, ProbComp.eval_uniform]
  simpa only [hnext] using PMF.bind_const (PMF.uniformOfFintype Bool) target

/-- The second request contains the first reply, and the final output contains the second reply. -/
theorem run_description :
    ProbOracleComp.runWith handler (description.runOracle 4 []) [] =
      PMF.pure ([9], [[], [7]]) := by
  unfold Desc.runOracle MultiTapePTM.runOracle MultiTapePTM.run
  change ProbOracleComp.runWith handler
    (machine.runFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun op word => ProbOracleComp.query (op, word)) 4 cfg₀) [] = _
  have h₀ : ProbOracleComp.runWith handler
      (machine.runFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
        (fun op word => ProbOracleComp.query (op, word)) 4 cfg₀) [] =
      ProbOracleComp.runWith handler
        (machine.runFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun op word => ProbOracleComp.query (op, word)) 3 cfg₁) [[]] := by
    rw [show 4 = 3 + 1 by omega, MultiTapePTM.runFrom_succ]
    simp only [cfg₀_state, Fin.isValue]
    apply runWith_uniformBool_bind_const
    intro bit
    simp [transition₀, handler, cfg₁, operation, cfg₀_queryBuffer]
  rw [h₀]
  have h₁ : ProbOracleComp.runWith handler
      (machine.runFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
        (fun op word => ProbOracleComp.query (op, word)) 3 cfg₁) [[]] =
      ProbOracleComp.runWith handler
        (machine.runFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun op word => ProbOracleComp.query (op, word)) 2 cfg₂) [[]] := by
    rw [show 3 = 2 + 1 by omega, MultiTapePTM.runFrom_succ]
    simp only [cfg₁_state, Fin.isValue]
    apply runWith_uniformBool_bind_const
    intro bit
    simp [transition₁, cfg₂]
  rw [h₁]
  have h₂ : ProbOracleComp.runWith handler
      (machine.runFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
        (fun op word => ProbOracleComp.query (op, word)) 2 cfg₂) [[]] =
      ProbOracleComp.runWith handler
        (machine.runFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun op word => ProbOracleComp.query (op, word)) 1 cfg₃) [[], [7]] := by
    rw [show 2 = 1 + 1 by omega, MultiTapePTM.runFrom_succ]
    simp only [cfg₂_state, Fin.isValue]
    apply runWith_uniformBool_bind_const
    intro bit
    simp [transition₂, handler, cfg₃, operation, cfg₂_queryBuffer]
  rw [h₂]
  change ProbOracleComp.runWith handler
    (machine.runFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun op word => ProbOracleComp.query (op, word)) (0 + 1) cfg₃) [[], [7]] = _
  rw [MultiTapePTM.runFrom_succ]
  simp only [cfg₃_state, Fin.isValue]
  apply runWith_uniformBool_bind_const
  intro bit
  simp only [transition₃]
  simp only [MultiTapePTM.runFrom_zero, ProbOracleComp.runWith_pure]
  change PMF.pure (cfg₄.tapes.output, [[], [7]]) = PMF.pure ([9], [[], [7]])
  rw [cfg₄_output]

/-- With zero clock, the description makes no query and produces no output. -/
theorem run_zero :
    ProbOracleComp.runWith handler (description.runOracle 0 []) [] = PMF.pure ([], []) := by
  simp [description]

/-- The all-zero, empty-table boundary has only the four unary structure fields in its encoding. -/
def emptyDescription : Desc where
  tapes := 0
  states := 0
  operations := 0
  q₀ := 0
  table := []

theorem empty_description_length : descLen emptyDescription = 4 := rfl

/-- An empty table selects the local halting action. -/
theorem empty_action (coin : Bool) :
    ({ tapes := 0, states := 1, operations := 1, q₀ := 0, table := [] } : Desc).action
      (some 0) none noWork (oneAnswer none) coin = haltAction 0 1 1 := by
  exact Desc.action_empty 0 1 1 0 (some 0) none noWork (oneAnswer none) coin

/-- An out-of-range operation tag halts locally instead of invoking a dispatch callback. -/
theorem invalid_query_action :
    (Act.query 1 0).toAction 0 1 1 = haltAction 0 1 1 := by
  exact Act.toAction_query_of_operation_not_lt 0 1 1 1 0 (by omega)

/-- An out-of-range query successor tag halts locally. -/
theorem invalid_query_next_action :
    (Act.query 0 1).toAction 0 1 1 = haltAction 0 1 1 := by
  exact Act.toAction_query_of_next_not_lt 0 1 1 0 1 (by omega) (by omega)

/-- An out-of-range ordinary successor becomes the machine's local halting state. -/
theorem invalid_ordinary_next_control : nextControl 1 (some 1) = none := by
  exact nextControl_some_of_not_lt 1 1 (by omega)

/-- An invalid initial state tag enters the finite trap control, whose transition halts locally. -/
theorem invalid_initial_action (coin : Bool) :
    let malformed : Desc :=
      { tapes := 0, states := 1, operations := 1, q₀ := 1, table := description.table }
    malformed.action malformed.toMachine.initial none noWork (oneAnswer none) coin =
      haltAction 0 1 1 := by
  dsimp
  simp only [Fin.ofNat?_eq_none_of_not_lt 1 1 (by omega)]
  rfl

end CslibFrontierTests.OracleDescription
