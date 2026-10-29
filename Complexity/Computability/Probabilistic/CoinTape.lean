/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Map
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayInput
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Efficient saved-coin evaluators for typed PPT programs

A strict PPT witness realizes its result from a uniformly sampled polynomial-length tape. Its
deterministic saved-coin evaluator has a genuine TM certificate, including tape preparation and
cleanup. Normalizing arbitrary tapes to the witness budget gives a total typed evaluator whose
every result belongs to the original program's support. No decoder on arbitrary output words is
assumed: supported output words have unique preimages under the declared encoding.

## Main results

* `Cslib.Probability.IsPPTOn.exists_coin_machine`: one finite machine realizes all inputs from
  uniform saved coins.
* `Cslib.Probability.IsPPTOn.exists_polyTime_coin_evaluator`: efficient evaluation on raw words.
* `Cslib.Probability.IsPPTOn.exists_total_seeded_evaluator`: a total efficient typed evaluator,
  supported on every seed and exact under any sufficiently long uniform seed.
* `Cslib.Probability.IsPPTOn.exists_seeded_evaluator`: the exact-budget specialization.
* `Cslib.Probability.IsPPTOn.exists_padded_coin_evaluator`,
  `Cslib.Probability.IsPPTOn.exists_padded_bool_coin_evaluator`: one longer saved tape can be
  reused across inputs of different lengths.

## References

Adapted from Computability/Probabilistic/CoinTape.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common machine, standard pair encoding and
tidy computability calculus.
-/

@[expose] public section

namespace Cslib.Probability

open Turing Turing.MultiTapeTM

variable {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
  {program : α → ProbComp β}

/-- One finite machine and one polynomial budget realize the whole program family from saved
fair bits. Neither witness depends on the input value. -/
theorem IsPPTOn.exists_coin_machine (h : IsPPTOn input output program) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State)
      (c d : ℕ), ∀ a,
      (ProbComp.eval (program a)).map output =
        (BitString.uniformList (c * ((input a).length + 1) ^ d)).map
          (fun coins => machine.runClosedCoins coins (input a)) := by
  obtain ⟨k, State, hfinite, machine, c, d, hm⟩ := h
  exact ⟨k, State, hfinite, machine, c, d, fun a =>
    (hm a).trans (machine.eval_runClosed_eq_map_coins _ _)⟩

/-- The encoded evaluator accepts arbitrary raw input and coin words and is uniformly
polynomial time. Its exact realization law applies to encoded inputs at the stated budget. -/
theorem IsPPTOn.exists_polyTime_coin_evaluator (h : IsPPTOn input output program) :
    ∃ (c d : ℕ) (evaluate : List Bool → List Bool → List Bool),
      ComputableTidilyInPolyTime (fun p : List Bool × List Bool => evaluate p.1 p.2)
        (encPair encBits encBits) encBits ∧
      ∀ a, (ProbComp.eval (program a)).map output =
        (BitString.uniformList (c * ((input a).length + 1) ^ d)).map
          (fun coins => evaluate coins (input a)) := by
  obtain ⟨k, State, _, machine, c, d, hm⟩ := h.exists_coin_machine
  exact ⟨c, d, machine.runClosedCoins, machine.computableInPolyTime_runClosedCoins.tidy, hm⟩

/-- Every typed PPT program has a total deterministic polynomial-time evaluator. Every seed
produces a supported result. Short seeds are padded; longer seeds are truncated to the program's
budget. Every uniform seed at least that long yields exactly the program's distribution.

Computability is relative to the output encoding and requires no decoder for invalid words. -/
theorem IsPPTOn.exists_total_seeded_evaluator (h : IsPPTOn input output program) :
    ∃ (c d : ℕ) (evaluate : α → List Bool → β),
      ComputableTidilyInPolyTime (fun p : α × List Bool => evaluate p.1 p.2)
        (encPair input encBits) output ∧
      (∀ a coins, evaluate a coins ∈ (ProbComp.eval (program a)).support) ∧
      ∀ a length, c * ((input a).length + 1) ^ d ≤ length →
        ProbComp.eval (program a) = (BitString.uniformList length).map (evaluate a) := by
  classical
  obtain ⟨c, d, raw, hraw, hlaw⟩ := h.exists_polyTime_coin_evaluator
  let budget (a : α) := c * ((input a).length + 1) ^ d
  let tape (a : α) (coins : List Bool) := (coins ++ List.replicate (budget a) true).take (budget a)
  have hlength (a : α) (coins : List Bool) : (tape a coins).length = budget a := by
    simp [tape]
  have hvalid (a : α) (coins : List Bool) : ∃ result,
      result ∈ (ProbComp.eval (program a)).support ∧
        output result = raw (tape a coins) (input a) := by
    have hs : raw (tape a coins) (input a) ∈
        ((BitString.uniformList (budget a)).map (fun seed => raw seed (input a))).support :=
      (PMF.mem_support_map_iff _ _ _).mpr
        ⟨tape a coins, BitString.mem_support_uniformList_iff.mpr (hlength a coins), rfl⟩
    rw [← hlaw a] at hs
    exact (PMF.mem_support_map_iff _ _ _).mp hs
  let evaluate (a : α) (coins : List Bool) := (hvalid a coins).choose
  have hencode (a : α) (coins : List Bool) :
      output (evaluate a coins) = raw (tape a coins) (input a) := (hvalid a coins).choose_spec.2
  refine ⟨c, d, evaluate, ?_, fun a coins => (hvalid a coins).choose_spec.1, ?_⟩
  · have hinput : ComputableTidilyInPolyTime input input encBits := .of_eq fun _ => rfl
    have hbudget : ComputableTidilyInPolyTime budget input encUnary := by
      dsimp only [budget]
      fun_prop
    have hpad : ComputableTidilyInPolyTime (fun a => List.replicate (budget a) true)
        input encBits := hbudget.of_enc_eq (fun _ => rfl)
    have ht : ComputableTidilyInPolyTime
        (fun p : α × List Bool => (tape p.1 p.2, input p.1))
        (encPair input encBits) (encPair encBits encBits) := by
      have hfirst := ComputableTidilyInPolyTime.fst input encBits
      have hsecond := ComputableTidilyInPolyTime.snd input encBits
      exact (ComputableTidilyInPolyTime.bitsTakeWithInput
        (hsecond.bitsAppend (hpad.comp hfirst)) (hbudget.comp hfirst)).prod (hinput.comp hfirst)
    exact (hraw.comp ht).of_enc_eq (fun p => hencode p.1 p.2)
  · intro a length hbudget
    apply PMF.map_injective output.injective
    rw [hlaw, PMF.map_comp, ← BitString.uniformList_take hbudget, PMF.map_comp]
    apply PMF.bind_congr_on_support
    intro coins hcoins
    change PMF.pure (raw (coins.take (budget a)) (input a)) =
      PMF.pure (output (evaluate a coins))
    congr 1
    have hcoinsLength := BitString.length_of_mem_support_uniformList hcoins
    simp only [hencode, tape, List.take_append_of_le_length
      (show budget a ≤ coins.length by simpa only [budget, hcoinsLength] using hbudget)]

/-- The exact-budget specialization of the total seeded evaluator. -/
theorem IsPPTOn.exists_seeded_evaluator (h : IsPPTOn input output program) :
    ∃ (c d : ℕ) (evaluate : α → List Bool → β),
      ComputableTidilyInPolyTime (fun p : α × List Bool => evaluate p.1 p.2)
        (encPair input encBits) output ∧
      ∀ a, ProbComp.eval (program a) =
        (BitString.uniformList (c * ((input a).length + 1) ^ d)).map (evaluate a) := by
  obtain ⟨c, d, evaluate, hefficient, _, hlaw⟩ := h.exists_total_seeded_evaluator
  exact ⟨c, d, evaluate, hefficient, fun a => hlaw a _ le_rfl⟩

/-- A typed program can use one larger saved tape across inputs of different lengths. The
raw word evaluator trims to each input's own budget and accepts arbitrary encoded words. -/
theorem IsPPTOn.exists_padded_coin_evaluator (h : IsPPTOn input output program) :
    ∃ (c d : ℕ) (evaluate : List Bool → List Bool → List Bool),
      ComputableTidilyInPolyTime (fun p : List Bool × List Bool => evaluate p.1 p.2)
        (encPair encBits encBits) encBits ∧
      ∀ a length, c * ((input a).length + 1) ^ d ≤ length →
        (ProbComp.eval (program a)).map output = (BitString.uniformList length).map
          (fun coins => evaluate coins (input a)) := by
  obtain ⟨c, d, evaluate, hefficient, hlaw⟩ := h.exists_polyTime_coin_evaluator
  refine ⟨c, d, fun coins input => evaluate (coins.take (c * (input.length + 1) ^ d)) input,
    ?_, ?_⟩
  · exact hefficient.comp (show ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => (p.1.take (c * (p.2.length + 1) ^ d), p.2))
      (encPair encBits encBits) (encPair encBits encBits) by fun_prop)
  · intro a length hlength
    rw [hlaw, ← BitString.uniformList_take hlength, PMF.map_comp]
    rfl

/-- Reading the raw evaluator's first bit preserves a Boolean program's distribution. The
shared tape budget may depend only on a bound on the encoded input size. -/
theorem IsPPTOn.exists_padded_bool_coin_evaluator {program : α → ProbComp Bool}
    (h : IsPPTOn input encBool program) :
    ∃ (c d : ℕ) (evaluate : List Bool → List Bool → List Bool),
      ComputableTidilyInPolyTime (fun p : List Bool × List Bool => evaluate p.1 p.2)
        (encPair encBits encBits) encBits ∧
      ∀ a length, c * ((input a).length + 1) ^ d ≤ length →
        ProbComp.eval (program a) = (BitString.uniformList length).map
          (fun coins => (evaluate coins (input a)).headD false) := by
  obtain ⟨c, d, evaluate, hefficient, hlaw⟩ := h.exists_padded_coin_evaluator
  refine ⟨c, d, evaluate, hefficient, fun a length hlength => ?_⟩
  have heq := congrArg (PMF.map (fun word : List Bool => word.headD false)) (hlaw a length hlength)
  simpa [PMF.map_comp, Function.comp_def, encBool_apply, PMF.map] using heq

end Cslib.Probability
