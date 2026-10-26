/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Deterministic replay of Boolean oracle replies

One transcript bit is assigned to every native instruction. A query installs that bit as its
one-symbol reply; a local instruction ignores it. Thus replay requires no external oracle and
is polynomial-time in the input and transcript lengths, including the construction of adaptive
requests. The canonical transcript records the actual oracle reply at query instructions and
`false` elsewhere. Replaying it recovers the complete coin-fixed configuration and output.

The `replay*` declarations here replay supplied oracle replies with the coin fixed to `false`.
The saved-coin controller `Turing.MultiTapePTM.replay` in
`Complexity/Computability/Machines/Turing/MultiTape/Probabilistic/Replay.lean` instead replays
supplied random coins for a closed machine using an additional work tape.

## Main definitions

* `Turing.MultiTapePTM.replyStep`: one native instruction with a supplied Boolean reply.
* `Turing.MultiTapePTM.replayConfig`: replay a transcript from the initial configuration.
* `Turing.MultiTapePTM.replayPrefix`: replay only the given prefix of a transcript.
* `Turing.MultiTapePTM.oracleReplies`: the canonical instruction-indexed oracle transcript.

## Main results

* `Turing.MultiTapePTM.replayConfig_pt`: replay is polynomial-time.
* `Turing.MultiTapePTM.replayPrefix_pt`: prefix configurations are uniformly polynomial-time.
* `Turing.MultiTapePTM.length_pendingRequest_replayPrefix_le`: request size is bounded by the
  number of elapsed instructions.
* `Turing.MultiTapePTM.replayOutput_oracleReplies`: canonical replay is the certified oracle run.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 3.4.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine MultiTapeTM

variable {k : ℕ} {Control Operation : Type} [DecidableEq Operation]
  (machine : MultiTapePTM k Bool Control Operation)

/-- Execute one native instruction, using `bit` only if that instruction makes a query. -/
def replyStep (cfg : FiniteConfig k Bool Control Operation) (bit : Bool) :
    FiniteConfig k Bool Control Operation :=
  if (machine.pendingQuery cfg).isSome then machine.receiveBit (cfg, bit)
    else machine.localStep cfg

/-- Replay assigns one bit to every native instruction, including local and halted ones. -/
def replayFrom (cfg : FiniteConfig k Bool Control Operation) (answers : List Bool) :
    FiniteConfig k Bool Control Operation :=
  answers.foldl machine.replyStep cfg

/-- Replay the given instruction-indexed replies from the initial configuration. -/
def replayConfig (input answers : List Bool) : FiniteConfig k Bool Control Operation :=
  machine.replayFrom (FiniteConfig.init machine.initial input) answers

/-- The configuration immediately before instruction `index`, or after the whole transcript if
`index` exceeds its length. -/
def replayPrefix (input answers : List Bool) (index : ℕ) :
    FiniteConfig k Bool Control Operation :=
  machine.replayConfig input (answers.take index)

/-- The output tape after replaying the entire transcript. -/
def replayOutput (input answers : List Bool) : List Bool :=
  (machine.replayConfig input answers).tapes.output

/-- A supplied bit is equivalent to a constant one-bit oracle for this instruction. -/
private theorem replyStep_eq_answerStep (cfg : FiniteConfig k Bool Control Operation) (bit : Bool) :
    machine.replyStep cfg bit = machine.answerStep (fun _ => [bit]) cfg :=
  (machine.answerStep_bit (fun _ => bit) cfg).symm

/-- Supplying the answer to the pending request recovers an instruction against that oracle. -/
theorem replyStep_pendingRequest (g : List Bool → Bool)
    (cfg : FiniteConfig k Bool Control Operation) :
    machine.replyStep cfg (g (machine.pendingRequest cfg)) =
      machine.answerStep (fun q => [g q.2]) cfg := by
  rw [answerStep_bit]
  rfl

/-- A local instruction ignores its transcript bit. -/
theorem replyStep_of_pendingQuery_eq_none {cfg : FiniteConfig k Bool Control Operation}
    (h : machine.pendingQuery cfg = none) (bit : Bool) :
    machine.replyStep cfg bit = machine.localStep cfg := by
  simp [replyStep, h]

/-- Replaying concatenated transcripts is sequential replay. -/
theorem replayFrom_append (cfg : FiniteConfig k Bool Control Operation)
    (first second : List Bool) :
    machine.replayFrom cfg (first ++ second) =
      machine.replayFrom (machine.replayFrom cfg first) second :=
  List.foldl_append

/-- Appending a bit executes exactly one further instruction. -/
private theorem replayConfig_append_singleton (input answers : List Bool) (bit : Bool) :
    machine.replayConfig input (answers ++ [bit]) =
      machine.replyStep (machine.replayConfig input answers) bit := by
  simp only [replayConfig, replayFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Advancing a transcript prefix executes its next bit, whenever that bit is present. -/
theorem replayPrefix_succ (input answers : List Bool) (index : ℕ)
    (hindex : index < answers.length) :
    machine.replayPrefix input answers (index + 1) =
      machine.replyStep (machine.replayPrefix input answers index) answers[index] := by
  unfold replayPrefix
  rw [List.take_succ_eq_append_getElem hindex, replayConfig_append_singleton]

/-- Every replayed instruction preserves the native one-bit-reply storage bound. -/
private theorem spaceBound_replyStep {inputSize steps : ℕ}
    {cfg : FiniteConfig k Bool Control Operation}
    (h : FiniteConfig.SpaceBound inputSize steps 1 cfg) (bit : Bool) :
    FiniteConfig.SpaceBound inputSize (steps + 1) 1 (machine.replyStep cfg bit) := by
  rw [replyStep_eq_answerStep]
  exact machine.spaceBound_answerStep (fun _ => bit) h

/-- A transcript of length `r` executes `r` instructions with replies of length one. -/
private theorem spaceBound_replayFrom {inputSize steps : ℕ}
    {cfg : FiniteConfig k Bool Control Operation}
    (h : FiniteConfig.SpaceBound inputSize steps 1 cfg) (answers : List Bool) :
    FiniteConfig.SpaceBound inputSize (steps + answers.length) 1
      (machine.replayFrom cfg answers) := by
  induction answers generalizing steps cfg with
  | nil => simpa only [replayFrom, List.foldl_nil, List.length_nil, Nat.add_zero] using h
  | cons bit answers ih =>
    simpa only [replayFrom, List.foldl_cons, List.length_cons, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using ih (machine.spaceBound_replyStep h bit)

/-- Replay from the initial configuration has linear storage in the input and transcript. -/
private theorem spaceBound_replayConfig (input answers : List Bool) :
    FiniteConfig.SpaceBound input.length answers.length 1 (machine.replayConfig input answers) := by
  simpa only [replayConfig, Nat.zero_add] using
    machine.spaceBound_replayFrom (FiniteConfig.spaceBound_init machine.initial input 1) answers

/-- A pending request contains at most one symbol per elapsed native instruction. -/
private theorem length_pendingRequest_replayConfig_le (input answers : List Bool) :
    (machine.pendingRequest (machine.replayConfig input answers)).length ≤ answers.length :=
  machine.length_pendingRequest_le (machine.spaceBound_replayConfig input answers)

/-- A prefix query has at most `min index answers.length` symbols. -/
theorem length_pendingRequest_replayPrefix_le (input answers : List Bool) (index : ℕ) :
    (machine.pendingRequest (machine.replayPrefix input answers index)).length ≤
      min index answers.length := by
  simpa only [replayPrefix, List.length_take] using
    machine.length_pendingRequest_replayConfig_le input (answers.take index)

section PolyTime

variable [Finite Control] [Fintype Operation]

/-- The next replay instruction is polynomial-time, uniformly in its reply bit. -/
@[fun_prop] theorem replyStep_pt : ComputableTidilyInPolyTime
    (fun p : FiniteConfig k Bool Control Operation × Bool => machine.replyStep p.1 p.2)
    (encPair encFiniteConfig encBool) encFiniteConfig := by
  exact ComputableTidilyInPolyTime.cond
    ((ComputableTidilyInPolyTime.of_finite Option.isSome).comp
      (machine.pendingQuery_pt.comp (.fst encFiniteConfig encBool)))
    machine.receiveBit_pt (machine.localStep_pt.comp (.fst encFiniteConfig encBool))

/-- Deterministic oracle replay is polynomial-time in the encoded input and transcript. -/
@[fun_prop] theorem replayConfig_pt : ComputableTidilyInPolyTime
    (fun p : List Bool × List Bool => machine.replayConfig p.1 p.2)
    (encPair encBits encBits) encFiniteConfig := by
  obtain ⟨c, hc⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Operation)
  have hinit : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => FiniteConfig.init (k := k) (Oracle := Operation)
        machine.initial p.1) (encPair encBits encBits) encFiniteConfig := by fun_prop
  have hin : PolyBounded (fun p : List Bool × List Bool =>
      (encPair encBits encBits p).length) (fun p => p.1.length) :=
    (ComputableTidilyInPolyTime.fst encBits encBits).polyBounded_length
  have hans : PolyBounded (fun p : List Bool × List Bool =>
      (encPair encBits encBits p).length) (fun p => p.2.length) :=
    (ComputableTidilyInPolyTime.snd encBits encBits).polyBounded_length
  have hb := (PolyBounded.const c).mul (((hin.add hans).add (.const 1)).add (.const 1))
  exact ComputableTidilyInPolyTime.foldl' (.snd encBits encBits) hinit machine.replyStep_pt hb
    (fun p i _ => (hc _ _ _ _ (machine.spaceBound_replayConfig p.1 (p.2.take i))).trans
      (Nat.mul_le_mul_left c (by simp only [List.length_take]; omega)))

/-- Prefix replay is jointly polynomial-time in input, transcript and unary instruction index. -/
@[fun_prop] theorem replayPrefix_pt : ComputableTidilyInPolyTime
    (fun p : (List Bool × List Bool) × ℕ => machine.replayPrefix p.1.1 p.1.2 p.2)
    (encPair (encPair encBits encBits) encUnary) encFiniteConfig := by
  exact machine.replayConfig_pt.comp (g := fun p : (List Bool × List Bool) × ℕ =>
    (p.1.1, p.1.2.take p.2)) (by fun_prop)

end PolyTime

section PolyTimeOutput

variable [Finite Control] [Finite Operation]

/-- The replayed output is polynomial-time. -/
@[fun_prop] theorem replayOutput_pt : ComputableTidilyInPolyTime
    (fun p : List Bool × List Bool => machine.replayOutput p.1 p.2)
    (encPair encBits encBits) encBits := by
  let _ := Fintype.ofFinite Operation
  have hout : ComputableTidilyInPolyTime
      (fun cfg : FiniteConfig k Bool Control Operation => cfg.tapes.output)
      encFiniteConfig encBits := by fun_prop
  exact hout.comp machine.replayConfig_pt

/-- The next query in a guessed-reply execution is uniformly polynomial-time. -/
@[fun_prop] theorem replayPrefix_pendingRequest_pt : ComputableTidilyInPolyTime
    (fun p : (List Bool × List Bool) × ℕ =>
      machine.pendingRequest (machine.replayPrefix p.1.1 p.1.2 p.2))
    (encPair (encPair encBits encBits) encUnary) encBits := by
  let _ := Fintype.ofFinite Operation
  exact machine.pendingRequest_pt.comp machine.replayPrefix_pt

/-- Whether the next guessed-reply instruction is a query is uniformly polynomial-time. -/
@[fun_prop] theorem replayPrefix_isQuery_pt : ComputableTidilyInPolyTime
    (fun p : (List Bool × List Bool) × ℕ =>
      (machine.pendingQuery (machine.replayPrefix p.1.1 p.1.2 p.2)).isSome)
    (encPair (encPair encBits encBits) encUnary) encBool := by
  let _ := Fintype.ofFinite Operation
  exact (ComputableTidilyInPolyTime.of_finite Option.isSome).comp
    (machine.pendingQuery_pt.comp machine.replayPrefix_pt)

end PolyTimeOutput

/-- The instruction-indexed transcript of an oracle execution. Local and halted instructions
receive the canonical padding bit `false`. -/
def oracleRepliesFrom (g : List Bool → Bool) :
    FiniteConfig k Bool Control Operation → ℕ → List Bool
  | _, 0 => []
  | cfg, fuel + 1 =>
    (if (machine.pendingQuery cfg).isSome then g (machine.pendingRequest cfg) else false) ::
      oracleRepliesFrom g (machine.answerStep (fun q => [g q.2]) cfg) fuel

/-- The canonical transcript of a clocked execution from the initial configuration. -/
def oracleReplies (g : List Bool → Bool) (fuel : ℕ) (input : List Bool) : List Bool :=
  machine.oracleRepliesFrom g (FiniteConfig.init machine.initial input) fuel

/-- A canonical transcript has exactly one bit per clocked instruction. -/
private theorem length_oracleRepliesFrom (g : List Bool → Bool)
    (cfg : FiniteConfig k Bool Control Operation) (fuel : ℕ) :
    (machine.oracleRepliesFrom g cfg fuel).length = fuel := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih => simp only [oracleRepliesFrom, List.length_cons, ih]

/-- The initial canonical transcript has exactly the clock length. -/
theorem length_oracleReplies (g : List Bool → Bool) (fuel : ℕ) (input : List Bool) :
    (machine.oracleReplies g fuel input).length = fuel :=
  machine.length_oracleRepliesFrom g _ fuel

/-- Canonical transcripts are consistent under truncation of their clock. -/
private theorem take_oracleRepliesFrom (g : List Bool → Bool)
    (cfg : FiniteConfig k Bool Control Operation) (fuel index : ℕ) :
    (machine.oracleRepliesFrom g cfg fuel).take index =
      machine.oracleRepliesFrom g cfg (min index fuel) := by
  induction index generalizing cfg fuel with
  | zero => rfl
  | succ index ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      simp only [oracleRepliesFrom, List.take_succ_cons, Nat.succ_min_succ, ih]

private theorem replyStep_oracleBit (g : List Bool → Bool)
    (cfg : FiniteConfig k Bool Control Operation) :
    machine.replyStep cfg
      (if (machine.pendingQuery cfg).isSome then g (machine.pendingRequest cfg) else false) =
        machine.answerStep (fun q => [g q.2]) cfg := by
  rw [answerStep_bit]
  unfold replyStep
  split <;> rfl

/-- Canonical replay recovers the entire finite configuration, not only its output. -/
private theorem replayFrom_oracleRepliesFrom (g : List Bool → Bool)
    (cfg : FiniteConfig k Bool Control Operation) (fuel : ℕ) :
    machine.replayFrom cfg (machine.oracleRepliesFrom g cfg fuel) =
      (machine.answerStep (fun q => [g q.2]))^[fuel] cfg := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
    change machine.replayFrom (machine.replyStep cfg _)
      (machine.oracleRepliesFrom g (machine.answerStep (fun q => [g q.2]) cfg) fuel) = _
    rw [replyStep_oracleBit, ih, Function.iterate_succ_apply]

/-- The canonical transcript replays the coin-fixed oracle run from its initial configuration. -/
theorem replayConfig_oracleReplies (g : List Bool → Bool) (fuel : ℕ) (input : List Bool) :
    machine.replayConfig input (machine.oracleReplies g fuel input) =
      (machine.answerStep (fun q => [g q.2]))^[fuel]
        (FiniteConfig.init machine.initial input) :=
  machine.replayFrom_oracleRepliesFrom g _ fuel

/-- A canonical prefix recovers the configuration after the corresponding elapsed instructions. -/
private theorem replayPrefix_oracleReplies (g : List Bool → Bool) (fuel : ℕ) (input : List Bool)
    (index : ℕ) :
    machine.replayPrefix input (machine.oracleReplies g fuel input) index =
      (machine.answerStep (fun q => [g q.2]))^[min index fuel]
        (FiniteConfig.init machine.initial input) := by
  unfold replayPrefix oracleReplies
  rw [take_oracleRepliesFrom]
  exact machine.replayFrom_oracleRepliesFrom g _ _

/-- The bit of a canonical transcript at a live clock index is the pending oracle answer, with
`false` at local or halted instructions. -/
private theorem getD_oracleRepliesFrom (g : List Bool → Bool)
    (cfg : FiniteConfig k Bool Control Operation) (fuel index : ℕ) (hindex : index < fuel) :
    (machine.oracleRepliesFrom g cfg fuel).getD index false =
      let current := (machine.answerStep (fun q => [g q.2]))^[index] cfg
      if (machine.pendingQuery current).isSome then g (machine.pendingRequest current)
        else false := by
  induction index generalizing cfg fuel with
  | zero =>
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  | succ index ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [oracleRepliesFrom, List.getD_cons_succ]
      dsimp only
      rw [Function.iterate_succ_apply]
      exact ih (machine.answerStep (fun q => [g q.2]) cfg) fuel (by omega)

/-- Canonical transcript bits agree with the queries seen by replay of their own prefix. -/
theorem getD_oracleReplies (g : List Bool → Bool) (fuel : ℕ) (input : List Bool)
    (index : ℕ) (hindex : index < fuel) :
    (machine.oracleReplies g fuel input).getD index false =
      let current := machine.replayPrefix input (machine.oracleReplies g fuel input) index
      if (machine.pendingQuery current).isSome then g (machine.pendingRequest current)
        else false := by
  rw [replayPrefix_oracleReplies, Nat.min_eq_left hindex.le]
  exact machine.getD_oracleRepliesFrom g _ fuel index hindex

/-- Replayed canonical outputs agree exactly with interpretation of the clocked oracle program. -/
theorem replayOutput_oracleReplies (g : List Bool → Bool) (fuel : ℕ) (input : List Bool) :
    machine.replayOutput input (machine.oracleReplies g fuel input) =
      OracleComp.interpret (m := Id) (fun q => [g q.2])
        (machine.run (pure false) (fun op word => OracleComp.query (op, word)) fuel input) := by
  rw [interpret_run_pure_false, replayOutput, replayConfig_oracleReplies]

end Turing.MultiTapePTM
