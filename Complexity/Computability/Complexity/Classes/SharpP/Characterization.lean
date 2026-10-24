/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.Machine
public import Complexity.Computability.Machines.Turing.MultiTape.Counting.Verifier

/-!
# The native counting-machine characterization of #P

Every verifier-defined `#P` function is the accepting count of one fixed finite-control native
List-choice machine, with a polynomial all-branches clock in the encoded instance length.
The converse uses the certified binary replay checker. The reverse construction also preserves
the rejecting count: each unsuccessful witness contributes exactly one rejecting branch.

The machine, number of tapes, finite state type and clock are fixed before the input. For an
arbitrary instance encoding the halting contract is on its image; specializing to `encBits`
covers every binary input. `Classes.SharpP.GapMachine` uses balanced verdict routing to realize
arbitrary #P differences and prove the signed `GapP` characterization.

## Main results

* `Turing.MultiTapeCTM.exists_verifier_counting_machine`: exact accepting and rejecting counts.
* `Cslib.Complexity.mem_SharpP_iff_exists_machine`: the bidirectional #P characterization.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]

The native construction and earlier formalization credits are in `MultiTape.Counting.Verifier`;
the forward certified checker and its source credit are in `Classes.SharpP.Machine`.
-/

@[expose] public section

open Cslib Turing Turing.MultiTapeTM

namespace Turing.MultiTapeCTM

variable {α : Type}

/-- Actual native guess-and-verify has one branch per witness, with both verdict counts exact.
Preparation, framing, buffers and tidy restoration are included in the polynomial clock. -/
theorem exists_verifier_counting_machine (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (verifier : α × List Bool → Bool)
    (hverify : ComputableInPolyTime verifier (encPair enc encBits) encBool) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
      (clock : Polynomial ℕ), machine.Nonblocking ∧ ∀ a,
        machine.HaltsWithin (clock.eval (enc a).length) (Cfg.init machine.initial (enc a)) ∧
        machine.acceptCount (clock.eval (enc a).length) (Cfg.init machine.initial (enc a)) =
          Complexity.acceptCount verifier a (p.eval (enc a).length) ∧
        machine.rejectCount (clock.eval (enc a).length) (Cfg.init machine.initial (enc a)) =
          2 ^ (p.eval (enc a).length) -
            Complexity.acceptCount verifier a (p.eval (enc a).length) := by
  have hverify := hverify.tidy
  obtain ⟨k, State, hfinite, machine, clock, hnon, hm⟩ :=
    exists_verifier_machine enc p verifier hverify
  refine ⟨k, State, hfinite, machine, clock, hnon, fun a => ?_⟩
  have hhalt : machine.HaltsWithin (clock.eval (enc a).length)
      (Cfg.init machine.initial (enc a)) := (hm a).1
  have hp : ((machine.runList (clock.eval (enc a).length)
      (Cfg.init machine.initial (enc a))).map Cfg.output).Perm
      ((BitString.enumList (p.eval (enc a).length)).map
        (fun word => encBool (verifier (a, word)))) := (hm a).2
  have hverdict (verdict : Bool) :
      machine.branchCount (fun out => (out == [true]) == verdict) (clock.eval (enc a).length)
        (Cfg.init machine.initial (enc a)) =
      (Finset.univ.filter fun word : BitString (p.eval (enc a).length) =>
        verifier (a, List.ofFn word) = verdict).card := by
    rw [hhalt.branchCount_eq_countP (fun out => (out == [true]) == verdict)]
    have hcount := hp.countP_eq (fun out => (out == [true]) == verdict)
    simp only [List.countP_map, Function.comp_def] at hcount
    rw [hcount]
    simpa [List.countP_map, Function.comp_def, encBool_apply] using
      BitString.countP_enumList (p.eval (enc a).length) (fun word => verifier (a, word) == verdict)
  refine ⟨hhalt, ?_, ?_⟩
  · simpa [acceptCount, Complexity.acceptCount] using hverdict true
  · have hcount := Complexity.acceptCount_add_card_filter_eq_false
      (V := verifier) (a := a) (n := p.eval (enc a).length)
    have hrejection : machine.rejectCount (clock.eval (enc a).length)
        (Cfg.init machine.initial (enc a)) =
        (Finset.univ.filter fun word : BitString (p.eval (enc a).length) =>
          verifier (a, List.ofFn word) = false).card := by
      simpa [rejectCount] using hverdict false
    rw [hrejection]
    lia

end Turing.MultiTapeCTM

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {f : α → ℕ}

/-- The verifier definition of #P is exactly polynomial-time native accepting-path counting.
All machine parameters are fixed before the encoded instance; every branch halts without
getting stuck. The constructed machines have globally nonblocking transition tables. -/
theorem mem_SharpP_iff_exists_machine :
    f ∈ SharpP enc ↔
      ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
        (clock : Polynomial ℕ), machine.Nonblocking ∧ ∀ a,
          machine.HaltsWithin (clock.eval (enc a).length) (Cfg.init machine.initial (enc a)) ∧
          machine.acceptCount (clock.eval (enc a).length)
            (Cfg.init machine.initial (enc a)) = f a := by
  constructor
  · rintro ⟨p, verifier, hverify, hf⟩
    obtain ⟨k, State, hfinite, machine, clock, hnon, hm⟩ :=
      MultiTapeCTM.exists_verifier_counting_machine enc p verifier hverify
    exact ⟨k, State, hfinite, machine, clock, hnon,
      fun a => ⟨(hm a).1, (hm a).2.1.trans (hf a).symm⟩⟩
  · rintro ⟨k, State, hfinite, machine, clock, _, hm⟩
    have heq : f = fun a => machine.acceptCount (clock.eval (enc a).length)
        (Cfg.init machine.initial (enc a)) := funext fun a => (hm a).2.symm
    rw [heq]
    exact machine.acceptCount_mem_SharpP enc clock

end Cslib.Complexity
