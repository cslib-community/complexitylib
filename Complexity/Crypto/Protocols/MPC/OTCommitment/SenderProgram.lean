/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.MPC.OTCommitment.World
public import Complexity.Crypto.Protocols.MPC.OTCommitment.PolyTime
public import Complexity.Crypto.Protocols.MPC.OTCommitment.Opening.PolyTime
public import Complexity.Languages.Probabilistic.BitString
public import Complexity.Languages.Probabilistic.Oracle.QueryCount
public import Complexity.Crypto.Negligible.Basic
import Complexity.Languages.Probabilistic.Norm
import Mathlib.Data.List.GetD

/-!
# Programs for the corrupted-sender commitment simulation

The supplied choose and finish callbacks are closed probabilistic programs. The sender receives
only the ideal OT sender's Unit reply, never the honest receiver's choices or selected bits.
Only the simulator reads the corrupted sender's OT table inputs. It fixes the extracted bit in
the actual phased world before invoking finish. List-valued openings of the wrong length are
rejected, and both public observations, commit-final sender state and auxiliary output survive.

## Main definitions

* `senderOfPrograms`: interpret callbacks in the existing semantic Sender interface.
* `senderViewProgram`: the common sender recursion with an explicit table list.
* `decodeOpening`: reject malformed lengths before converting to the finite semantic opening.
* `selectedBits`: selected OT answers from explicit table and choice lists.
* `senderIdealProgram`, `senderClosedProgram`: typed phased-world driver and its actual closure.

## Main results

* `eval_senderViewProgram`: exact relation to the existing sender-table execution.
* `openPairs_decodeOpening`: exact list checker semantics, including malformed lengths.
* `eval_senderClosedProgram`: exact interpretation in the existing phased-world experiment.
* `senderClosedProgram_coupled`: joint simulation error `2⁻⌈k/2⌉`.
* `senderClosedProgram_coupled_two_mul`, `senderClosedProgram_negligible_error`: geometric
  negligible error on the concrete growing schedule `k = 2n`.
* `senderIdealProgram_schedule`, `senderIdealProgram_queryBound`: the four actual public calls.

This is an original fixed-schedule single-session program refinement, not a universal realization
for all globally PPT adversaries, arbitrary scheduling, composition or UC security.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment

open Probability Crypto.Protocols.Commitment
open scoped ENNReal NNReal

variable {State Output : Type}

/-- Interpret closed table-selection programs in the existing semantic Sender interface. -/
noncomputable def senderOfPrograms
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State) : Sender State where
  choose k st := ProbComp.eval (choose k st)
  receive := receive

/-- The common recursion, with its growing table transcript represented as an explicit list. -/
noncomputable def senderViewProgram
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State) (k : ℕ) (st : State) :
    ProbComp (List (Fin 4 → Bool) × State) :=
  (fun (ts, final) => (List.ofFn ts, final)) <$> senderTablesWith choose receive k st

private theorem eval_senderTablesWith
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State) (k : ℕ) (st : State) :
    ProbComp.eval (senderTablesWith choose receive k st) =
      senderTables (senderOfPrograms choose receive) k st := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih =>
    simp only [pmf_norm, senderTablesWith, senderTables_succ, senderOfPrograms]
    exact congrArg ((ProbComp.eval (choose k st)).bind) (funext fun ts => by rw [ih]; rfl)

/-- Program interpretation preserves the semantic sender transcript and commit-final state. -/
theorem eval_senderViewProgram
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State) (k : ℕ) (st : State) :
    ProbComp.eval (senderViewProgram choose receive k st) =
      (senderTables (senderOfPrograms choose receive) k st).map
        (fun (ts, final) => (List.ofFn ts, final)) := by
  simp only [senderViewProgram, ProbComp.eval_map, eval_senderTablesWith]

/-- No table is generated at zero rounds. -/
theorem senderViewProgram_zero
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State) (st : State) :
    senderViewProgram choose receive 0 st = pure ([], st) := rfl

/-- One round samples its table, updates private sender state and continues. -/
theorem senderViewProgram_succ
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State) (k : ℕ) (st : State) :
    senderViewProgram choose receive (k + 1) st = (do
      let (t, next) ← choose k st
      let (rest, final) ← senderViewProgram choose receive k (receive next ())
      return (t :: rest, final)) := by
  simp [senderViewProgram, senderTablesWith, map_bind, List.ofFn_succ]

/-- Semantic adapter for an arbitrary list submission. Incorrect length is rejection; no bytes
or unchecked lookup defaults are interpreted as a valid finite opening. -/
def decodeOpening (k : ℕ) (submission : Option (Bool × List (Bool × Bool))) :
    Option (Bool × Opening k) :=
  submission.bind fun (b, pairs) =>
    if pairs.length = k then
      some (b, fun i c => if c then (pairs.getD i.val (false, false)).2
        else (pairs.getD i.val (false, false)).1)
    else none

/-- The total list checker exactly implements the finite verifier after length rejection. -/
theorem openPairs_decodeOpening {k : ℕ} (choices received : Fin k → Bool)
    (submission : Option (Bool × List (Bool × Bool))) :
    openPairs (List.ofFn choices) (List.ofFn received) submission =
      openResult choices received (decodeOpening k submission) := by
  cases submission with
  | none => rfl
  | some s =>
    rcases s with ⟨b, pairs⟩
    by_cases h : pairs.length = k
    · subst k
      simpa [decodeOpening, List.ofFn_getElem] using
        openPairs_ofFn choices received (decodeOpening pairs.length (some (b, pairs)))
    · have hd : decodeOpening k (some (b, pairs)) = none := by simp [decodeOpening, h]
      rw [hd]
      change (if _ then some b else none) = none
      split
      · rename_i ha
        simp only [Bool.and_eq_true, beq_iff_eq, List.length_ofFn] at ha
        exact (h ha.1.2.symm).elim
      · rfl

/-- Explicit selected answers for the honest receiver's private list of choices. -/
def selectedBits (tables : List (Fin 4 → Bool)) (choices : List Bool) : List Bool :=
  (tables.zip choices).map fun (t, c) => t (boolPairToFin4 (false, c))

/-- Explicit selected bits agree with every actual OT table lookup. -/
theorem selectedBits_ofFn {k : ℕ} (ts : Fin k → Fin 4 → Bool) (choices : Fin k → Bool) :
    selectedBits (List.ofFn ts) (List.ofFn choices) =
      List.ofFn (fun i => ts i (boolPairToFin4 (false, choices i))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [selectedBits, List.ofFn_succ, List.zip_cons_cons, List.map_cons]
    exact congrArg (List.cons _) (ih _ _)

/-- Exactly four public calls. The committed bit is fixed before finish samples; callbacks cannot
query the world or learn the simulator's privately sampled honest choices. -/
noncomputable def senderIdealProgram
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State) (k : ℕ) (st : State)
    (finish : ℕ → State → ProbComp (Option (Bool × List (Bool × Bool)) × Output)) :
    ProbOracleComp (Phased.senderSpec ⊕ₒ Phased.receiverSpec)
      (Phased.Observation × Phased.Observation × State × Output) := do
  let (tables, final) ← ProbOracleComp.sample (senderViewProgram choose receive k st)
  let committed := extractPairs (tables.map fun t =>
    (t (boolPairToFin4 (false, false)), t (boolPairToFin4 (false, true))))
  ProbOracleComp.query (spec := Phased.senderSpec ⊕ₒ Phased.receiverSpec)
    (.inl (.commit committed))
  let received ← ProbOracleComp.query (.inr ())
  let choices ← ProbOracleComp.sample (BitString.sampleList k)
  let (submission, out) ← ProbOracleComp.sample (finish k final)
  let result := openPairs choices (selectedBits tables choices) submission
  ProbOracleComp.query (spec := Phased.senderSpec ⊕ₒ Phased.receiverSpec)
    (.inl (if result == some committed then .open else .abort))
  let observed ← ProbOracleComp.query (.inr ())
  return (received, observed, final, out)

/-- Run the actual finite handler from idle, hiding only final functionality state. -/
noncomputable def senderClosedProgram
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State) (k : ℕ) (st : State)
    (finish : ℕ → State → ProbComp (Option (Bool × List (Bool × Bool)) × Output)) :
    ProbComp (Phased.Observation × Phased.Observation × State × Output) :=
  Prod.fst <$> ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) Phased.handler)
      (senderIdealProgram choose receive k st finish)).run .idle)

/-- Exact closed local computation obtained by executing all four actual world calls. -/
theorem senderClosedProgram_eq
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State) (k : ℕ) (st : State)
    (finish : ℕ → State → ProbComp (Option (Bool × List (Bool × Bool)) × Output)) :
    senderClosedProgram choose receive k st finish = (do
      let (tables, final) ← senderViewProgram choose receive k st
      let committed := extractPairs (tables.map fun t =>
        (t (boolPairToFin4 (false, false)), t (boolPairToFin4 (false, true))))
      let choices ← BitString.sampleList k
      let (submission, out) ← finish k final
      let result := openPairs choices (selectedBits tables choices) submission
      let observed := if result == some committed then Phased.Observation.opened committed
        else .aborted
      return (Phased.Observation.receipt, observed, final, out)) := by
  simp only [senderClosedProgram, senderIdealProgram,
    OracleComp.interpret_bind, OracleComp.interpret_pure,
    ProbOracleComp.interpret_query, Phased.interpret_sample]
  simp only [StateT.run_bind, StateT.run_pure]
  simp only [StateT.lift, StateT.run, Phased.handler, OracleComp.sumHandler,
    Phased.advance, Phased.observe, bind_assoc, pure_bind, map_bind, map_pure]
  apply congrArg (Bind.bind (senderViewProgram choose receive k st))
  apply funext
  rintro ⟨tables, final⟩
  apply congrArg (Bind.bind (BitString.sampleList k))
  funext choices
  apply congrArg (Bind.bind (finish k final))
  apply funext
  rintro ⟨submission, out⟩
  by_cases h : openPairs choices (selectedBits tables choices) submission =
      some (extractPairs (tables.map fun t =>
        (t (boolPairToFin4 (false, false)), t (boolPairToFin4 (false, true)))))
  all_goals simp [h]

/-- Exact evaluation in the existing semantic phased-world experiment. Malformed list openings
become rejection before any finite opening is used; the final world store alone is hidden. -/
theorem eval_senderClosedProgram
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State) (k : ℕ) (st : State)
    (finish : ℕ → State → ProbComp (Option (Bool × List (Bool × Bool)) × Output)) :
    ProbComp.eval (senderClosedProgram choose receive k st finish) =
      (senderIdeal (senderOfPrograms choose receive) k (pure st)
        (fun final => (ProbComp.eval (finish k final)).map
          (fun (submission, out) => (decodeOpening k submission, out))) .idle).map Prod.fst := by
  rw [senderClosedProgram_eq, senderIdeal_run]
  simp only [pmf_norm, eval_senderViewProgram, BitString.eval_sampleList, BitString.uniformList,
    simulatedOpening]
  apply congrArg ((senderTables (senderOfPrograms choose receive) k st).bind)
  apply funext
  rintro ⟨ts, final⟩
  apply congrArg ((PMF.uniformOfFintype (Fin k → Bool)).bind)
  funext choices
  apply congrArg ((ProbComp.eval (finish k final)).bind)
  apply funext
  rintro ⟨submission, out⟩
  simp only [List.map_ofFn, Function.comp_def, extractPairs_ofFn, selectedBits_ofFn,
    openPairs_decodeOpening]
  by_cases h : openResult choices (fun i => ts i (boolPairToFin4 (false, choices i)))
      (decodeOpening k submission) = some (extract ts)
  all_goals simp [h]

/-- The actual closed simulator inherits the majority-extraction coupling, retaining public
observations, commit-final state and arbitrary auxiliary output jointly. -/
theorem senderClosedProgram_coupled
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State) (k : ℕ) (st : State)
    (finish : ℕ → State → ProbComp (Option (Bool × List (Bool × Bool)) × Output)) :
    PMF.CoupledWithin
      ((realOpening (senderOfPrograms choose receive) k (pure st)
        (fun final => (ProbComp.eval (finish k final)).map
          (fun (submission, out) => (decodeOpening k submission, out)))).map
        (fun (result, final, out) =>
          (Phased.Observation.receipt, result.elim .aborted .opened, final, out)))
      (ProbComp.eval (senderClosedProgram choose receive k st finish))
      ((2 : ℝ≥0∞)⁻¹ ^ (k - k / 2)) := by
  rw [eval_senderClosedProgram]
  exact senderIdeal_coupled _ _ _ _

/-- Twice the security parameter in OT rounds gives the geometric extraction error `2⁻ⁿ`. -/
theorem senderClosedProgram_coupled_two_mul
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State) (n : ℕ) (st : State)
    (finish : ℕ → State → ProbComp (Option (Bool × List (Bool × Bool)) × Output)) :
    PMF.CoupledWithin
      ((realOpening (senderOfPrograms choose receive) (2 * n) (pure st)
        (fun final => (ProbComp.eval (finish (2 * n) final)).map
          (fun (submission, out) => (decodeOpening (2 * n) submission, out)))).map
        (fun (result, final, out) =>
          (Phased.Observation.receipt, result.elim .aborted .opened, final, out)))
      (ProbComp.eval (senderClosedProgram choose receive (2 * n) st finish))
      ((2 : ℝ≥0∞)⁻¹ ^ n) := by
  have hcount : 2 * n - (2 * n) / 2 = n := by omega
  simpa only [hcount] using senderClosedProgram_coupled choose receive (2 * n) st finish

/-- The actual majority-extraction error along the schedule `k = 2n` is negligible. -/
theorem senderClosedProgram_negligible_error :
    Crypto.Negligible (fun n => (2 : ℝ≥0)⁻¹ ^ (2 * n - (2 * n) / 2)) := by
  have hcount (n : ℕ) : 2 * n - (2 * n) / 2 = n := by omega
  simp only [hcount]
  exact Crypto.negligible_geometric (by norm_num)

/-- The actual world transcript has exactly commit, receipt poll, release-or-abort and terminal
poll, in reverse chronological order. All private callbacks and coin draws are absent from it. -/
theorem senderIdealProgram_schedule
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State) (k : ℕ) (st : State)
    (finish : ℕ → State → ProbComp (Option (Bool × List (Bool × Bool)) × Output))
    {result : Phased.Observation × Phased.Observation × State × Output} {store : Phased.Store}
    {log : OracleComp.Transcript (Phased.senderSpec ⊕ₒ Phased.receiverSpec)}
    (h : (result, store, log) ∈ (ProbOracleComp.runWith
      (OracleComp.withTranscript Phased.world.impl)
      (senderIdealProgram choose receive k st finish) (.idle, [])).support) :
    ∃ committed release : Bool, log.map Sigma.fst =
      [.inr (), .inl (if release then .open else .abort), .inr (), .inl (.commit committed)] := by
  simp only [pmf_norm, senderIdealProgram, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, ProbOracleComp.runWith_sample, ProbOracleComp.runWith_pure,
    OracleComp.withTranscript, Phased.handler, OracleComp.sumHandler, Phased.advance,
    Phased.observe] at h
  simp only [PMF.mem_support_bind_iff] at h
  obtain ⟨⟨tables, final⟩, _, choices, _, ⟨submission, out⟩, _, h⟩ := h
  let committed := extractPairs (tables.map fun t =>
    (t (boolPairToFin4 (false, false)), t (boolPairToFin4 (false, true))))
  let release := openPairs choices (selectedBits tables choices) submission == some committed
  refine ⟨committed, release, ?_⟩
  simp only [PMF.mem_support_pure_iff] at h
  cases h
  rfl

/-- Callback runtimes do not affect the fixed structural budget of four external calls. Native
runtime, including private samples, is charged separately by the strict-PPT certificate. -/
theorem senderIdealProgram_queryBound
    (choose : ℕ → State → ProbComp ((Fin 4 → Bool) × State))
    (receive : State → Unit → State) (k : ℕ) (st : State)
    (finish : ℕ → State → ProbComp (Option (Bool × List (Bool × Bool)) × Output)) :
    ProbOracleComp.IsQueryBounded (senderIdealProgram choose receive k st finish) 4 := by
  unfold senderIdealProgram
  apply (ProbOracleComp.IsQueryBounded.sample _).bind (m := 4)
  rintro ⟨tables, final⟩
  apply (ProbOracleComp.IsQueryBounded.query _).bind (m := 3)
  intro _
  apply (ProbOracleComp.IsQueryBounded.query _).bind (m := 2)
  intro _
  apply (ProbOracleComp.IsQueryBounded.sample _).bind (m := 2)
  intro choices
  apply (ProbOracleComp.IsQueryBounded.sample _).bind (m := 2)
  rintro ⟨submission, out⟩
  apply (ProbOracleComp.IsQueryBounded.query _).bind (m := 1)
  intro _
  apply (ProbOracleComp.IsQueryBounded.query _).bind (m := 0)
  intro _
  exact .pure _ 0

end Cslib.Crypto.Protocols.MPC.OTCommitment
