/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Counting.Composition
public import Complexity.Computability.Machines.Turing.MultiTape.Counting.Guess
public import Complexity.Computability.Machines.Turing.MultiTape.Counting.OutputPrefix
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run
import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm

/-!
# Native parsimonious guess-and-verify machines

The witness-length routine, binary scanner, framed input writer and deterministic verifier
are actual finite native machines. Singleton lifting and the shared compilers retain every
occurrence. Polynomial clocks include the unary length computation, framing, buffer preparation
and tidy workspace restoration. The contracts concern encoded instances; no behavior on
words outside the instance encoding is asserted.

## Main results

* `Turing.MultiTapeCTM.exists_guess_machine`: one occurrence per polynomial-length witness.
* `Turing.MultiTapeCTM.exists_framedGuess_machine`: retain the instance in the verifier encoding.
* `Turing.MultiTapeCTM.exists_verifier_machine`: one Boolean result occurrence per witness.

## References

The guess-and-verify construction is standard in counting complexity [Valiant1979]. Native
tidy machines and their calculus are by Christian Reitwiessner and Samuel Schlesinger. The
captured-input construction follows `Computability.Probabilistic.PPT.Capture`, with source
credit recorded there; the present singleton lift retains exact occurrence multiplicity.
-/

@[expose] public section

namespace Turing.MultiTapeCTM

open Cslib MultiTapeTM MultiTapeMachine Polynomial

variable {α : Type}

/-- Compute the witness length in unary and run the actual binary scanner. The finite machine
is fixed before the instance is supplied, and emits each witness once, including the empty word. -/
theorem exists_guess_machine (enc : α ↪ List Bool) (p : Polynomial ℕ) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
      (clock : Polynomial ℕ), machine.Nonblocking ∧ ∀ a,
        machine.HaltsWithin (clock.eval (enc a).length) (machine.initialConfig (enc a)).tapes ∧
        ((machine.runList (clock.eval (enc a).length)
          (machine.initialConfig (enc a)).tapes).map Cfg.output).Perm
          (BitString.enumList (p.eval (enc a).length)) := by
  have hprepare : ComputableTidilyInPolyTime
      (fun a => p.eval (enc a).length) enc encUnary :=
    (ComputableTidilyInPolyTime.unary_eval p).comp
      (ComputableTidilyInPolyTime.encoding_length enc)
  obtain ⟨t, s, ht, _, k, State, hfinite, initializer, hi⟩ := hprepare
  obtain ⟨c, d, ht⟩ := ht.exists_le
  let prepareClock : Polynomial ℕ := C c * (X + 1) ^ d
  let source := ofDeterministic initializer
  let compiled := guessMachine.comp source true
  let clock := prepareClock + (prepareClock + 4 + (p + 1))
  have hnon := (nonblocking_ofDeterministic initializer).comp GuessMachine.nonblocking true
  refine ⟨_, _, inferInstance, compiled, clock, hnon, fun a => ?_⟩
  have hprep : initializer.runFrom (initializer.initCfg (enc a))
      (prepareClock.eval (enc a).length) =
      wordsCfg (enc a) none (fun _ => []) (encUnary (p.eval (enc a).length)) := by
    simpa only [prepareClock, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one,
      encUnary_apply] using ((hi a).mono (ht a) le_rfl).runFrom_initCfg_eq
  have hfirst : source.HaltsWithin (prepareClock.eval (enc a).length)
      (source.initialConfig (enc a)).tapes := by
    rw [haltsWithin_ofDeterministic_iff]
    change (initializer.runFrom (initializer.initCfg (enc a)) _).Halted
    rw [hprep]
    rfl
  have hrun : source.runList (prepareClock.eval (enc a).length)
      (source.initialConfig (enc a)).tapes =
      [wordsCfg (enc a) none (fun _ => []) (encUnary (p.eval (enc a).length))] := by
    rw [runList_ofDeterministic]
    exact congrArg List.singleton hprep
  have hsecond : ∀ result ∈ source.runList (prepareClock.eval (enc a).length)
      (source.initialConfig (enc a)).tapes,
      guessMachine.HaltsWithin (p.eval (enc a).length + 1)
        (guessMachine.initialConfig result.output).tapes := by
    intro result hresult
    have hr : result = wordsCfg (enc a) none (fun _ => [])
        (encUnary (p.eval (enc a).length)) := by simpa [hrun] using hresult
    subst result
    simpa only [wordsCfg, encUnary_apply, List.length_replicate, initialConfig] using
      GuessMachine.haltsWithin (encUnary (p.eval (enc a).length))
  have hhalt := HaltsWithin.comp source guessMachine (nonblocking_ofDeterministic initializer)
    GuessMachine.nonblocking true (enc a) _ _ hfirst hsecond
  constructor
  · simpa only [clock, eval_add, eval_ofNat, eval_one] using hhalt
  · simp only [clock, eval_add, eval_ofNat, eval_one]
    unfold compiled
    rw [runList_comp source guessMachine (nonblocking_ofDeterministic initializer)
      GuessMachine.nonblocking true (enc a) _ _ hfirst hsecond, hrun, List.flatMap_singleton]
    dsimp only [Config.emptyOracleEquiv]
    rw [List.map_map]
    change ((guessMachine.runList (p.eval (enc a).length + 1)
      (guessMachine.initialConfig (encUnary (p.eval (enc a).length))).tapes).map Cfg.output).Perm _
    simpa [runList, GuessMachine.config, Function.comp_def, encUnary_apply, initialConfig] using
      (GuessMachine.interpret_runProgram (encUnary (p.eval (enc a).length))).map Cfg.output

/-- A tidy frame writer surrounds the complete guessing computation, so the scanner still reads
only the unary witness length. Every output is exactly the verifier's framed pair encoding. -/
theorem exists_framedGuess_machine (enc : α ↪ List Bool) (p : Polynomial ℕ) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
      (clock : Polynomial ℕ), machine.Nonblocking ∧ ∀ a,
        machine.HaltsWithin (clock.eval (enc a).length) (machine.initialConfig (enc a)).tapes ∧
        ((machine.runList (clock.eval (enc a).length)
          (machine.initialConfig (enc a)).tapes).map Cfg.output).Perm
          ((BitString.enumList (p.eval (enc a).length)).map
            (fun word => encPair enc encBits (a, word))) := by
  obtain ⟨ks, State, hfinite, source, sourceClock, hnon, hs⟩ := exists_guess_machine enc p
  have hframe : ComputableTidilyInPolyTime (fun a => frame (enc a)) enc encBits :=
    .of_linear (.of_frame fun _ => rfl)
  obtain ⟨t, s, ht, _, ki, InitState, hfinite', initializer, hi⟩ := hframe
  obtain ⟨c, d, ht⟩ := ht.exists_le
  let prepare := initializer.extendTapes (Fin.castAddEmb ks)
  let runner := source.extendTapes (Fin.natAddEmb ki)
  let compiled := (ofDeterministic prepare).seq runner
  let prepareClock : Polynomial ℕ := C c * (X + 1) ^ d
  have hnonrunner : Nonblocking runner := hnon.extendTapes _
  refine ⟨_, _, inferInstance, compiled, prepareClock + sourceClock,
    (nonblocking_ofDeterministic prepare).seq hnonrunner, fun a => ?_⟩
  have hprep : prepare.runFrom (prepare.initCfg (enc a)) (prepareClock.eval (enc a).length) =
      wordsCfg (enc a) none (fun _ => []) (frame (enc a)) := by
    simpa only [prepareClock, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one,
      encBits_apply] using
      (((hi a).mono (ht a) le_rfl).extendTapes (Fin.castAddEmb ks)).runFrom_initCfg_eq
  have hrunner : MultiTapeCTM.HaltsWithin runner (sourceClock.eval (enc a).length)
      (runner.initialConfig (enc a)).tapes := by
    rw [initialConfig_extendTapes]
    exact HaltsWithin.embed hnon _ (source.initialConfig (enc a)) _ _ _ (hs a).1
  constructor
  · simpa only [eval_add] using haltsWithin_seq_prependOutput prepare runner hnonrunner
      (enc a) (frame (enc a)) _ _ hprep hrunner
  · simp only [eval_add]
    rw [runList_seq_prependOutput prepare runner hnonrunner (enc a) (frame (enc a))
      _ _ hprep hrunner, List.map_map]
    change ((runList runner (sourceClock.eval (enc a).length)
      (runner.initialConfig (enc a)).tapes).map (fun final => frame (enc a) ++ final.output)).Perm _
    rw [initialConfig_extendTapes, runList_embed]
    dsimp only [Config.emptyOracleEquiv]
    rw [List.map_map]
    change ((source.runList (sourceClock.eval (enc a).length)
      (source.initialConfig (enc a)).tapes).map (fun final => frame (enc a) ++ final.output)).Perm _
    simpa only [List.map_map, Function.comp_def, encPair_apply, encBits_apply] using
      ((hs a).2).map (frame (enc a) ++ ·)

/-- Run the native verifier once for each witness. Equal Boolean outcomes retain separate List
occurrences; all branches halt at one polynomial clock in the original encoded input length. -/
theorem exists_verifier_machine (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (verifier : α × List Bool → Bool)
    (hverify : ComputableInPolyTime verifier (encPair enc encBits) encBool) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
      (clock : Polynomial ℕ), machine.Nonblocking ∧ ∀ a,
        machine.HaltsWithin (clock.eval (enc a).length) (machine.initialConfig (enc a)).tapes ∧
        ((machine.runList (clock.eval (enc a).length)
          (machine.initialConfig (enc a)).tapes).map Cfg.output).Perm
          ((BitString.enumList (p.eval (enc a).length)).map
            (fun word => encBool (verifier (a, word)))) := by
  obtain ⟨ks, State, hfinite, source, sourceClock, hnon, hs⟩ := exists_framedGuess_machine enc p
  obtain ⟨c, d, kv, VerifyState, hfinite', nativeVerifier, hv⟩ :=
    Internal.NormalForm.polyTime hverify
  let consumer := ofDeterministic nativeVerifier
  let compiled := consumer.comp source true
  let verifyClock : Polynomial ℕ := C c * (2 * X + 1 + p + 1) ^ d
  let clock := sourceClock + (sourceClock + 4 + verifyClock)
  have hnonconsumer := nonblocking_ofDeterministic nativeVerifier
  refine ⟨_, _, inferInstance, compiled, clock, hnon.comp hnonconsumer true, fun a => ?_⟩
  have hnative (word : List Bool) (hword : word.length = p.eval (enc a).length) :
      nativeVerifier.runFrom (nativeVerifier.initCfg (encPair enc encBits (a, word)))
        (verifyClock.eval (enc a).length) =
      wordsCfg (encPair enc encBits (a, word)) none (fun _ => [])
        (encBool (verifier (a, word))) := by
    have htime : c * ((encPair enc encBits (a, word)).length + 1) ^ d ≤
        verifyClock.eval (enc a).length := by
      simp only [verifyClock, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one,
        eval_ofNat, length_encPair, encBits_apply, hword]
      exact le_rfl
    exact ((hv (a, word)).mono htime le_rfl).runFrom_initCfg_eq
  have hsecond : ∀ result ∈ source.runList (sourceClock.eval (enc a).length)
      (source.initialConfig (enc a)).tapes,
      consumer.HaltsWithin (verifyClock.eval (enc a).length)
        (consumer.initialConfig result.output).tapes := by
    intro result hresult
    have hout := (hs a).2.mem_iff.mp (List.mem_map.mpr ⟨result, hresult, rfl⟩)
    obtain ⟨word, hword, heq⟩ := List.mem_map.mp hout
    rw [← heq, haltsWithin_ofDeterministic_iff]
    change (nativeVerifier.runFrom
      (nativeVerifier.initCfg (encPair enc encBits (a, word))) _).Halted
    rw [hnative word (BitString.length_of_mem_enumList hword)]
    rfl
  constructor
  · simpa only [clock, eval_add, eval_ofNat] using
      HaltsWithin.comp source consumer hnon hnonconsumer true (enc a) _ _ (hs a).1 hsecond
  · let finish := fun word : List Bool =>
      (consumer.runList (verifyClock.eval (enc a).length)
        (consumer.initialConfig word).tapes).map Cfg.output
    have hfinish (word : List Bool) (hword : word ∈ BitString.enumList (p.eval (enc a).length)) :
        finish (encPair enc encBits (a, word)) = [encBool (verifier (a, word))] := by
      dsimp only [finish]
      rw [runList_ofDeterministic]
      change [(nativeVerifier.runFrom (nativeVerifier.initCfg (encPair enc encBits (a, word)))
        (verifyClock.eval (enc a).length)).output] = _
      rw [hnative word (BitString.length_of_mem_enumList hword)]
      rfl
    have hout : (compiled.runList (clock.eval (enc a).length)
        (compiled.initialConfig (enc a)).tapes).map Cfg.output =
        ((source.runList (sourceClock.eval (enc a).length)
          (source.initialConfig (enc a)).tapes).map Cfg.output).flatMap finish := by
      simp only [clock, eval_add, eval_ofNat]
      unfold compiled
      rw [runList_comp source consumer hnon hnonconsumer true (enc a) _ _ (hs a).1 hsecond]
      dsimp only [Config.emptyOracleEquiv]
      rw [List.map_flatMap, List.flatMap_map]
      apply List.flatMap_congr
      intro result _
      rw [List.map_map]
      rfl
    rw [hout]
    refine ((hs a).2.flatMap_right finish).trans ?_
    rw [List.flatMap_map]
    conv_rhs => rw [List.map_eq_flatMap]
    exact List.Perm.flatMap_left _ fun word hword => List.Perm.of_eq (hfinish word hword)

end Turing.MultiTapeCTM
