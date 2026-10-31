/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Oracle
import Complexity.Computability.Complexity.Classes.Oracle.Deterministic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Oracles given as finite lists

A computation in polynomial time relative to an oracle language `S` asks only words no longer
than its clock, a polynomial `q` in the encoded input length. So any finite list `ℓ` of words
that agrees with `S` on the words of length at most `q n` can replace the oracle, and the run
against `ℓ` is polynomial-time in the input and `ℓ` together
(`Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_listOracle`). This is how a sparse oracle
is replaced by advice, or by a guessed list of its short members.

The proof replays the coin-fixed run of a machine certifying the computation
(`Cslib.Probability.IsOraclePPTOn.exists_fin_run_pure_false`) from its instruction-indexed
transcript of oracle replies (`Turing.MultiTapePTM.oracleReplies`). The transcript against the
list is built one bit at a time (`Turing.MultiTapePTM.listReplyStep`): each step replays the
transcript so far, and if the next instruction makes a query, looks its request up in the list.
The pending request of the instruction at index `i` has at most `i` symbols
(`Turing.MultiTapePTM.length_pendingRequest_replayPrefix_le`), so oracles that agree on the words
no longer than the clock give the same transcript
(`Turing.MultiTapePTM.oracleReplies_congr`).

## Main definitions

* `Turing.MultiTapePTM.listReplyStep`: extend a transcript by the reply of a list oracle.

## Main results

* `Turing.MultiTapePTM.oracleReplies_congr`: transcripts depend only on the replies to words no
  longer than the clock.
* `Turing.MultiTapePTM.iterate_listReplyStep`: iterating the step builds the transcript.
* `Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_listOracle`,
  `Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_listOracle_bool`: polynomial time
  relative to `S` is polynomial time with a list that agrees with `S` on short words.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 3.4.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine MultiTapeTM

variable {k : ℕ} {Control Operation : Type} [DecidableEq Operation]
  (machine : MultiTapePTM k Bool Control Operation)

/-- **Transcripts depend only on short replies.** Oracles that agree on every word of length less
than the clock give the same transcript: the request pending before instruction `i` has at most
`i` symbols. -/
theorem oracleReplies_congr {g g' : List Bool → Bool} {fuel : ℕ} (input : List Bool)
    (h : ∀ w : List Bool, w.length < fuel → g w = g' w) :
    machine.oracleReplies g fuel input = machine.oracleReplies g' fuel input := by
  set t := machine.oracleReplies g fuel input
  set t' := machine.oracleReplies g' fuel input
  have hlen : t.length = fuel := machine.length_oracleReplies g fuel input
  have hlen' : t'.length = fuel := machine.length_oracleReplies g' fuel input
  have htake : ∀ i ≤ fuel, t.take i = t'.take i := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      have hlt : i < fuel := hi
      have ih := ih hlt.le
      have hcfg : machine.replayPrefix input t i = machine.replayPrefix input t' i := by
        simp only [replayPrefix, ih]
      have hreq : (machine.pendingRequest (machine.replayPrefix input t i)).length < fuel :=
        lt_of_le_of_lt ((machine.length_pendingRequest_replayPrefix_le input t i).trans
          (Nat.min_le_left _ _)) hlt
      have hbit : t[i]'(by omega) = t'[i]'(by omega) := by
        rw [← List.getD_eq_getElem t false, ← List.getD_eq_getElem t' false,
          machine.getD_oracleReplies g fuel input i hlt,
          machine.getD_oracleReplies g' fuel input i hlt]
        dsimp only
        rw [← hcfg, h _ hreq]
      rw [List.take_succ_eq_append_getElem (by omega), List.take_succ_eq_append_getElem (by omega),
        ih, hbit]
  simpa only [List.take_of_length_le hlen.le, List.take_of_length_le hlen'.le] using
    htake fuel le_rfl

/-- Extend the transcript `answers` by one bit: replay it, and if the next instruction makes a
query, reply whether its request is in the list `ℓ`; otherwise pad with `false`. -/
def listReplyStep (p : List Bool × List (List Bool)) (answers : List Bool) : List Bool :=
  let cfg := machine.replayConfig p.1 answers
  answers ++ [if (machine.pendingQuery cfg).isSome then decide (machine.pendingRequest cfg ∈ p.2)
    else false]

/-- A canonical transcript one instruction longer extends the shorter one by the reply at its
last instruction. -/
theorem oracleReplies_succ (g : List Bool → Bool) (fuel : ℕ) (input : List Bool) :
    machine.oracleReplies g (fuel + 1) input = machine.oracleReplies g fuel input ++
      [let cfg := machine.replayConfig input (machine.oracleReplies g fuel input)
       if (machine.pendingQuery cfg).isSome then g (machine.pendingRequest cfg) else false] := by
  have hlen := machine.length_oracleReplies g (fuel + 1) input
  have htake : (machine.oracleReplies g (fuel + 1) input).take fuel =
      machine.oracleReplies g fuel input := by
    unfold oracleReplies
    rw [take_oracleRepliesFrom, Nat.min_eq_left (Nat.le_succ fuel)]
  have hbit := machine.getD_oracleReplies g (fuel + 1) input fuel (Nat.lt_succ_self fuel)
  rw [List.getD_eq_getElem _ _ (by omega)] at hbit
  have hcfg : machine.replayPrefix input (machine.oracleReplies g (fuel + 1) input) fuel =
      machine.replayConfig input (machine.oracleReplies g fuel input) := by
    rw [replayPrefix, htake]
  rw [hcfg] at hbit
  calc machine.oracleReplies g (fuel + 1) input
      = (machine.oracleReplies g (fuel + 1) input).take fuel ++
          [(machine.oracleReplies g (fuel + 1) input)[fuel]'(by omega)] := by
        rw [← List.take_succ_eq_append_getElem (by omega), List.take_of_length_le (by omega)]
    _ = _ := by rw [htake, hbit]

/-- **Iterating the step builds the transcript** of the list oracle. -/
theorem iterate_listReplyStep (input : List Bool) (ℓ : List (List Bool)) (fuel : ℕ) :
    (machine.listReplyStep (input, ℓ))^[fuel] [] =
      machine.oracleReplies (fun w => decide (w ∈ ℓ)) fuel input := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply', ih, oracleReplies_succ]
    rfl

section PolyTime

variable [Finite Control] [Finite Operation]

/-- The step is polynomial-time, jointly in the input, the list and the transcript. -/
theorem computableInPolyTime_listReplyStep :
    ComputableInPolyTime (fun x : (List Bool × List (List Bool)) × List Bool =>
      machine.listReplyStep x.1 x.2) (encPair (encPair encBits (encList encBits)) encBits)
      encBits := by
  let _ := Fintype.ofFinite Operation
  have hpair : ComputableInPolyTime
      (fun x : (List Bool × List (List Bool)) × List Bool => (x.1.1, x.2))
      (encPair (encPair encBits (encList encBits)) encBits) (encPair encBits encBits) :=
    (ComputableInPolyTime.fst _ _).fst'.prod (.snd _ _)
  have hcfg : ComputableInPolyTime
      (fun x : (List Bool × List (List Bool)) × List Bool => machine.replayConfig x.1.1 x.2)
      (encPair (encPair encBits (encList encBits)) encBits) encFiniteConfig :=
    machine.replayConfig_pt.comp
      (g := fun x : (List Bool × List (List Bool)) × List Bool => (x.1.1, x.2)) hpair
  have hquery : ComputableInPolyTime
      (fun x : (List Bool × List (List Bool)) × List Bool =>
        (machine.pendingQuery (machine.replayConfig x.1.1 x.2)).isSome)
      (encPair (encPair encBits (encList encBits)) encBits) encBool :=
    (ComputableInPolyTime.of_finite Option.isSome).comp
      (machine.pendingQuery_pt.comp (g := fun x : (List Bool × List (List Bool)) × List Bool =>
        machine.replayConfig x.1.1 x.2) hcfg)
  have hmem : ComputableInPolyTime
      (fun x : (List Bool × List (List Bool)) × List Bool =>
        decide (machine.pendingRequest (machine.replayConfig x.1.1 x.2) ∈ x.1.2))
      (encPair (encPair encBits (encList encBits)) encBits) encBool :=
    ComputableInPolyTime.decide_mem (ComputableInPolyTime.fst _ _).snd'
      (machine.pendingRequest_pt.comp (g := fun x : (List Bool × List (List Bool)) × List Bool =>
        machine.replayConfig x.1.1 x.2) hcfg)
  have hbit : ComputableInPolyTime
      (fun x : (List Bool × List (List Bool)) × List Bool =>
        if (machine.pendingQuery (machine.replayConfig x.1.1 x.2)).isSome then
          decide (machine.pendingRequest (machine.replayConfig x.1.1 x.2) ∈ x.1.2) else false)
      (encPair (encPair encBits (encList encBits)) encBits) encBool :=
    ComputableInPolyTime.ite' hquery hmem (ComputableInPolyTime.const false)
  have hsingle : ComputableInPolyTime (fun b : Bool => [b]) encBool encBits :=
    .of_eq fun _ => rfl
  exact ComputableInPolyTime.bitsAppend (ComputableInPolyTime.snd _ _)
    (hsingle.comp (g := fun x : (List Bool × List (List Bool)) × List Bool =>
      if (machine.pendingQuery (machine.replayConfig x.1.1 x.2)).isSome then
        decide (machine.pendingRequest (machine.replayConfig x.1.1 x.2) ∈ x.1.2) else false) hbit)

end PolyTime

end Turing.MultiTapePTM

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α β : Type} {S : Set (List Bool)} {input : α ↪ List Bool}

open Classical in
/-- **A finite list can replace the oracle.** If `f` is computable in polynomial time relative to
`S`, there are a polynomial `q` and a function `F`, polynomial-time in an instance and a list of
words together, such that `F (a, ℓ)` is the encoded result `output (f a)` whenever `ℓ` agrees with
`S` on every word of length at most `q (input a).length`. -/
theorem ComputableInPolyTimeWithOracle.exists_listOracle {f : α → β} {output : β ↪ List Bool}
    (hf : ComputableInPolyTimeWithOracle S f input output) :
    ∃ (F : α × List (List Bool) → List Bool) (q : Polynomial ℕ),
      ComputableInPolyTime F (encPair input (encList encBits)) encBits ∧
        ∀ a ℓ, (∀ w : List Bool, w.length ≤ q.eval (input a).length → (w ∈ ℓ ↔ w ∈ S)) →
          F (a, ℓ) = output (f a) := by
  obtain ⟨program, hcert, hprogram⟩ := hf
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  let T : α → ℕ := fun a => c * ((input a).length + 1) ^ d
  have hTa : ComputableInPolyTime T input encUnary :=
    ((ComputableInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      (ComputableInPolyTime.encoding_length input)).of_enc_eq fun a => by simp [T]
  have hT : ComputableInPolyTime (fun x : α × List (List Bool) => T x.1)
      (encPair input (encList encBits)) encUnary :=
    hTa.comp (ComputableInPolyTime.fst _ _)
  have hinput : ComputableInPolyTime (fun a : α => input a) input encBits := .of_eq fun _ => rfl
  have hinput' : ComputableInPolyTime (fun x : α × List (List Bool) => input x.1)
      (encPair input (encList encBits)) encBits :=
    hinput.comp (g := fun x : α × List (List Bool) => x.1) (.fst _ _)
  have hpar : ComputableInPolyTime (fun x : α × List (List Bool) => (input x.1, x.2))
      (encPair input (encList encBits)) (encPair encBits (encList encBits)) :=
    hinput'.prod (.snd _ _)
  have hiter : ComputableInPolyTime
      (fun x : α × List (List Bool) => (machine.listReplyStep (input x.1, x.2))^[T x.1] [])
      (encPair input (encList encBits)) encBits :=
    ComputableInPolyTime.iterateWith_of_bounded_growth hpar hT (ComputableInPolyTime.const [])
      machine.computableInPolyTime_listReplyStep (.const 1) fun x answers => by
        simp [Turing.MultiTapePTM.listReplyStep]
  have hout : ComputableInPolyTime
      (fun x : α × List (List Bool) =>
        machine.replayOutput (input x.1) ((machine.listReplyStep (input x.1, x.2))^[T x.1] []))
      (encPair input (encList encBits)) encBits :=
    machine.computableInPolyTime_replayOutput.comp (g := fun x : α × List (List Bool) =>
      (input x.1, (machine.listReplyStep (input x.1, x.2))^[T x.1] [])) (hinput'.prod hiter)
  refine ⟨_, Polynomial.C c * (Polynomial.X + 1) ^ d, hout, fun a ℓ hℓ => ?_⟩
  dsimp only
  rw [machine.iterate_listReplyStep, machine.oracleReplies_congr (g' := fun w => decide (w ∈ S))
    _ fun w hw => ?_, machine.replayOutput_oracleReplies, ← hprogram a, ← hrun a]
  · rfl
  · refine decide_eq_decide.mpr (hℓ w ?_)
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    exact hw.le

/-- **A finite list can replace the oracle of a decision**: the Boolean form of
`Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_listOracle`. -/
theorem ComputableInPolyTimeWithOracle.exists_listOracle_bool {f : α → Bool}
    (hf : ComputableInPolyTimeWithOracle S f input encBool) :
    ∃ (F : α × List (List Bool) → Bool) (q : Polynomial ℕ),
      ComputableInPolyTime F (encPair input (encList encBits)) encBool ∧
        ∀ a ℓ, (∀ w : List Bool, w.length ≤ q.eval (input a).length → (w ∈ ℓ ↔ w ∈ S)) →
          F (a, ℓ) = f a := by
  obtain ⟨F, q, hF, hFS⟩ := hf.exists_listOracle
  refine ⟨fun x => decide (F x = [true]), q,
    ComputableInPolyTime.decide_eq' hF (ComputableInPolyTime.const [true]), fun a ℓ hℓ => ?_⟩
  change decide (F (a, ℓ) = [true]) = f a
  rw [hFS a ℓ hℓ, encBool_apply]
  cases f a <;> rfl

end Cslib.Complexity
