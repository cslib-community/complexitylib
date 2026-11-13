/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.CompleteSender.PolyTime
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-! # Complete-sender protocol and global-runtime clients -/

public section

open Cslib Cslib.Probability Cslib.Crypto.Protocols.MPC
open Cslib.Crypto.Protocols.MPC.OTCommitment
open Cslib.Crypto.Protocols.Commitment Turing.MultiTapeTM
open scoped ENNReal

namespace CompleteSenderTests

private def commands : List (SenderOperation × List Bool) → WordOracleComp SenderOperation Unit
  | [] => pure ()
  | request :: rest => do
      let _ ← ProbOracleComp.query request
      commands rest

-- Early open does not prevent a later genuine seal/open; the first valid seal gives a receipt.
example : Session.advance 0 (.open false, [])
    ((Session.initial.advance 0 (.open true, [])).advance 0 (.seal, [])) =
    { sealed := true, stopped := true, submission := some (false, []) } := rfl

-- Excess tables abort without receipt. A malformed opening cannot retry after a successful seal.
example : Session.advance 0 (.seal, [])
    (Session.initial.advance 0 (.table (table false false), [])) =
    { stopped := true } := rfl

example : Session.advance 0 (.open false, [])
    ((Session.initial.advance 0 (.seal, [])).advance 0 (.open true, [false])) =
    { sealed := true, stopped := true, submission := some (true, [false]) } := rfl

-- Actual empty-session execution retains no-receipt versus receipt and keeps zero-round release.
example : ProbComp.eval (completeSenderReal 0 (commands [])) =
    pure (Phased.Observation.idle, .idle, ()) := by
  simp [completeSenderReal, commands, BitString.sampleList, Session.receipt, Session.observation,
    Session.initial, OracleComp.interpret_pure, StateT.run_pure]

example : ProbComp.eval (completeSenderIdeal 0 (commands [(.abort, []), (.seal, [])])) =
    pure (Phased.Observation.idle, .aborted, ()) := by
  have hs : sessionProgram 0 (commands [(.abort, []), (.seal, [])]) =
      pure ((), { stopped := true }) := rfl
  simp [eval_completeSenderIdeal, hs, Session.receipt, Session.idealStore, Phased.observe]

example : ProbComp.eval (completeSenderReal 0
    (commands [(.open true, []), (.seal, []), (.open false, []), (.abort, [])])) =
    pure (Phased.Observation.receipt, .opened false, ()) := by
  have hs : sessionProgram 0
      (commands [(.open true, []), (.seal, []), (.open false, []), (.abort, [])]) =
      pure ((), { sealed := true, stopped := true, submission := some (false, []) }) := rfl
  simp [eval_completeSenderReal, hs, Session.receipt, Session.observation, Session.opening,
    selectedBits, openPairs]

-- A malformed first attempt is terminal even when the next command would be a valid opening.
example : ProbComp.eval (completeSenderReal 0
    (commands [(.seal, []), (.open true, [false]), (.open false, [])])) =
    pure (Phased.Observation.receipt, .aborted, ()) := by
  have hs : sessionProgram 0
      (commands [(.seal, []), (.open true, [false]), (.open false, [])]) =
      pure ((), { sealed := true, stopped := true, submission := some (true, [false]) }) := rfl
  simp [eval_completeSenderReal, hs, Session.receipt, Session.observation, Session.opening,
    selectedBits, openPairs]

-- A globally polynomial complete adversary grows its private buffer by k bits in each of k
-- rounds. The old fixed-additive callback premise fails, but the complete execution is strict PPT.
def paddingStep (p : ℕ × Unit) (state : List Bool) :
    WordOracleComp SenderOperation (List Bool) := do
  let _ ← List.take 0 <$> ProbOracleComp.query (.table (table false false), [])
  return List.replicate p.1 false ++ state

private theorem paddingStep_isOraclePPT :
    IsOraclePPTOn (encPair (encPair encUnary (encFinite Unit)) encBits) encBits
      (fun p => paddingStep p.1 p.2) := by
  have hquery : IsOraclePPTOn (encPair (encPair encUnary (encFinite Unit)) encBits) encBits
      (fun _ => List.take 0 <$> ProbOracleComp.query
        (SenderOperation.table (table false false), [])) :=
    IsOraclePPTOn.query_take' _ (.const []) (.const 0)
  have hout : ComputableInPolyTime
      (fun p : ((ℕ × Unit) × List Bool) × List Bool =>
        List.replicate p.1.1.1 false ++ p.1.2)
      (encPair (encPair (encPair encUnary (encFinite Unit)) encBits) encBits) encBits := by fun_prop
  simpa only [paddingStep, map_eq_pure_bind] using hquery.map_with' hout

private theorem paddingStep_support (p : ℕ × Unit) (state next : List Bool)
    (h : next ∈ OracleComp.support (paddingStep p state)) :
    next = List.replicate p.1 false ++ state := by
  symm
  simpa [paddingStep, OracleComp.support, ProbOracleComp.query] using h

def paddingProgram (p : ℕ × Unit) : WordOracleComp SenderOperation (List Bool) := do
  let buffer ← OracleComp.iterate p.1 (paddingStep p) []
  let _ ← List.take 0 <$> ProbOracleComp.query (.seal, [])
  let _ ← List.take 0 <$> ProbOracleComp.query (.open false, List.replicate (2 * p.1) false)
  return buffer

private theorem paddingProgram_isOraclePPT :
    IsOraclePPTOn (encPair encUnary (encFinite Unit)) encBits paddingProgram := by
  have hloop : IsOraclePPTOn (encPair encUnary (encFinite Unit)) encBits
      (fun p => OracleComp.iterate p.1 (paddingStep p) []) :=
    IsOraclePPTOn.iterateWith_of_bounded_growth' (by fun_prop) (.const [])
      paddingStep_isOraclePPT
      ((ComputableInPolyTime.fst encUnary (encFinite Unit)).polyBounded)
      (fun p state next hnext => by
        rw [paddingStep_support p state next hnext]
        simp [encBits_apply, List.length_append, Nat.add_comm])
  unfold paddingProgram
  apply hloop.bind_with
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · exact IsOraclePPTOn.query_take' SenderOperation.seal (.const []) (.const 0)
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · exact IsOraclePPTOn.query_take' (SenderOperation.open false) (by fun_prop) (.const 0)
  exact ComputableInPolyTime.isOraclePPTOn (by fun_prop)

-- Both actual executions, on charged (unary k, unit) input, inherit this global certificate.
example : IsPPTOn (encPair encUnary (encFinite Unit))
    (encPair (encFinite Phased.Observation) (encPair (encFinite Phased.Observation) encBits))
    (fun p => completeSenderIdeal p.1 (paddingProgram p)) :=
  (completeSender_isPPT (encFinite Unit) encBits paddingProgram paddingProgram_isOraclePPT).2

example : ¬ ∃ growth : ℕ, ∀ p state next,
    next ∈ OracleComp.support (paddingStep p state) → next.length ≤ state.length + growth := by
  rintro ⟨growth, hgrowth⟩
  have h := hgrowth (growth + 1, ()) [] (List.replicate (growth + 1) false) (by
    simp [paddingStep, OracleComp.support, ProbOracleComp.query])
  simp at h

-- The global certificate itself supplies query and payload budgets, with unary k in the input.
example : ∃ c d : ℕ, ∀ p : ℕ × Unit,
    (paddingProgram p).IsQueryBounded
      (c * ((encPair encUnary (encFinite Unit) p).length + 1) ^ d) ∧
    (paddingProgram p).QueriesSatisfy fun request => request.2.length ≤
      c * ((encPair encUnary (encFinite Unit) p).length + 1) ^ d :=
  paddingProgram_isOraclePPT.query_bounds

private def mixedCommands : List (SenderOperation × List Bool) :=
  [(.table (table false false), []), (.table (table true false), []), (.seal, []),
    (.open true, [false, false, true, true])]

private def mixedSession : Session :=
  { tables := [table false false, table true false], sealed := true, stopped := true,
    submission := some (true, [false, false, true, true]) }

private theorem mixed_session : sessionProgram 2 (commands mixedCommands) =
    pure ((), mixedSession) := rfl

-- The same concrete full command program, including actual OT rows, has sharp real success 1/2.
private theorem mixed_real_half :
    (ProbComp.eval (completeSenderReal 2 (commands mixedCommands)))
      (.receipt, .opened true, ()) = (2 : ℝ≥0∞)⁻¹ := by
  have hobs (c : Fin 2 → Bool) :
      mixedSession.observation 2 (List.ofFn c)
        (selectedBits mixedSession.tables (List.ofFn c)) =
      if c 0 then .aborted else .opened true := by
    cases hzero : c 0 <;> cases hone : c 1 <;>
      simp [mixedSession, Session.observation, Session.opening, selectedBits, openPairs,
        List.ofFn_succ, table, fin4ToBoolPair_boolPairToFin4, hzero, hone]
  have hr : ProbComp.eval (completeSenderReal 2 (commands mixedCommands)) =
      (PMF.uniformOfFintype (Fin 2 → Bool)).map (fun c =>
        (Phased.Observation.receipt, if c 0 then .aborted else .opened true, ())) := by
    simp only [eval_completeSenderReal, mixed_session, ProbComp.eval_pure, PMF.pure_bind,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, hobs, PMF.map]
    rfl
  rw [hr, PMF.uniformOfFintype_map_apply]
  have hc : Nat.card {c : Fin 2 → Bool //
      (Phased.Observation.receipt, if c 0 then Phased.Observation.aborted
        else Phased.Observation.opened true, ()) =
        (Phased.Observation.receipt, Phased.Observation.opened true, ())} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hc]
  norm_num only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_ofNat,
    Nat.reducePow]
  rw [← ENNReal.coe_ofNat 2, ← ENNReal.coe_ofNat 4,
    ← ENNReal.coe_div (by norm_num), ← ENNReal.coe_inv (by norm_num)]
  norm_num

private theorem mixed_ideal_aborts :
    ProbComp.eval (completeSenderIdeal 2 (commands mixedCommands)) =
    pure (Phased.Observation.receipt, .aborted, ()) := by
  have he : mixedSession.extracted = false := by decide
  have hr (choices : List Bool) :
      openPairs choices (selectedBits mixedSession.tables choices) (mixedSession.opening 2) ≠
        some false := by
    change (if _ then some true else none) ≠ some false
    split <;> simp
  have ho (c : Fin 2 → Bool) : Phased.observe (mixedSession.idealStore 2
      (List.ofFn c) (selectedBits mixedSession.tables (List.ofFn c))) = .aborted := by
    change Phased.observe (if openPairs _ _ _ == some mixedSession.extracted
      then .opened mixedSession.extracted else .aborted) = .aborted
    rw [he]
    simp [hr, Phased.observe]
  calc
    _ = (PMF.uniformOfFintype (Fin 2 → Bool)).map
        (fun _ => (Phased.Observation.receipt, Phased.Observation.aborted, ())) := by
      simp only [eval_completeSenderIdeal, mixed_session, ProbComp.eval_pure, PMF.pure_bind,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ho, PMF.map]
      rfl
    _ = _ := PMF.map_const _ _

-- A correctly sized but rejected first opening cannot be repaired by a later valid opening.
example : (Session.initial.advance 1 (.table (table false false), []) |>.advance 1 (.seal, [])
    |>.advance 1 (.open true, [true, true]) |>.advance 1 (.open false, [false, false])).submission =
    some (true, [true, true]) := rfl

-- Full native client execution: two updates retain four padding bits and release the honest bit.
example : ProbComp.eval (completeSenderReal 2 (paddingProgram (2, ()))) =
    pure (Phased.Observation.receipt, .opened false, [false, false, false, false]) := by
  let s : Session :=
    { tables := [table false false, table false false], sealed := true,
      stopped := true, submission := some (false, [false, false, false, false]) }
  have hs : sessionProgram 2 (paddingProgram (2, ())) =
      pure ([false, false, false, false], s) := rfl
  have ho (c : Fin 2 → Bool) :
      s.observation 2 (List.ofFn c) (selectedBits s.tables (List.ofFn c)) = .opened false := by
    cases hzero : c 0 <;> cases hone : c 1 <;>
      simp [s, Session.observation, Session.opening, selectedBits, openPairs,
        List.ofFn_succ, table, fin4ToBoolPair_boolPairToFin4, hzero, hone]
  calc
    _ = (PMF.uniformOfFintype (Fin 2 → Bool)).map
        (fun _ => (Phased.Observation.receipt, Phased.Observation.opened false,
          [false, false, false, false])) := by
      simp only [eval_completeSenderReal, hs, ProbComp.eval_pure, PMF.pure_bind,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ho, PMF.map]
      rfl
    _ = _ := PMF.map_const _ _

-- Premature sealing aborts; an ignored post-seal table cannot overwrite the committed transcript.
example : (Session.initial.advance 1 (.seal, [])).stopped = true := rfl

example : ((Session.initial.advance 0 (.seal, [])).advance 0
    (.table (table true false), []) |>.advance 0 (.seal, [])).tables = [] := rfl

-- First rejection is terminal in actual execution, even when a subsequent opening would pass.
example : ProbComp.eval (completeSenderReal 1 (commands
    [(.table (table false false), []), (.seal, []), (.open true, [true, true]),
      (.open false, [false, false])])) =
    pure (Phased.Observation.receipt, .aborted, ()) := by
  let s : Session :=
    { tables := [table false false], sealed := true, stopped := true,
      submission := some (true, [true, true]) }
  have hs : sessionProgram 1 (commands
      [(.table (table false false), []), (.seal, []), (.open true, [true, true]),
        (.open false, [false, false])]) = pure ((), s) := rfl
  have ho (c : Fin 1 → Bool) :
      s.observation 1 (List.ofFn c) (selectedBits s.tables (List.ofFn c)) = .aborted := by
    cases hzero : c 0 <;>
      simp [s, Session.observation, Session.opening, selectedBits, openPairs, List.ofFn_succ,
        table, fin4ToBoolPair_boolPairToFin4, hzero]
  calc
    _ = (PMF.uniformOfFintype (Fin 1 → Bool)).map
        (fun _ => (Phased.Observation.receipt, Phased.Observation.aborted, ())) := by
      simp only [eval_completeSenderReal, hs, ProbComp.eval_pure, PMF.pure_bind,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ho, PMF.map]
      rfl
    _ = _ := PMF.map_const _ _

-- Private randomness survives jointly in the adversary output, even with no public commands.
example : ProbComp.eval (completeSenderReal 0
    (ProbOracleComp.sample (ProbComp.uniform Bool))) =
    (PMF.uniformOfFintype Bool).map (fun bit =>
      (Phased.Observation.idle, Phased.Observation.idle, bit)) := by
  simp [completeSenderReal, BitString.sampleList, ProbOracleComp.interpret_sample,
    OracleComp.run_interpret_lift, ProbComp.interpret_unifFin, Session.initial, Session.receipt,
    Session.observation]

-- Zero rounds permit a real opening to true, while the tie-false ideal extractor aborts it.
example : ProbComp.eval (completeSenderIdeal 0 (commands [(.seal, []), (.open true, [])])) =
    pure (Phased.Observation.receipt, .aborted, ()) := by
  have hs : sessionProgram 0 (commands [(.seal, []), (.open true, [])]) =
      pure ((), { sealed := true, stopped := true, submission := some (true, []) }) := rfl
  simp [eval_completeSenderIdeal, hs, Session.receipt, Session.idealStore, Session.extracted,
    Session.opening, extractPairs, BitString.listStrictMajority, selectedBits, openPairs,
    Phased.observe]

example : Session.opening 1 { submission := some (false, []) } = none := rfl
example : Session.opening 1 { submission := some (false, [false, false, false]) } = none := rfl

end CompleteSenderTests
