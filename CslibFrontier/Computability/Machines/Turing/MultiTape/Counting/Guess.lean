/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Program
public import CslibFrontier.Foundations.Data.BitString.Enumeration
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup

/-!
# Parsimonious binary guessing

One fixed machine scans its input, choosing and emitting one bit per symbol, then takes a
singleton halting instruction. Its occurrence-labelled terminal traces are in bijection with
Boolean words of the input length. The final instruction makes no discarded binary choice.

## Main definitions

* `Turing.MultiTapeCTM.guessMachine`: the zero-work-tape binary scanner.
* `Turing.MultiTapeCTM.GuessMachine.trace`: the unique occurrence trace for a witness.

## Main results

* `Turing.MultiTapeCTM.GuessMachine.haltsWithin`: every branch halts in `n + 1` steps.
* `Turing.MultiTapeCTM.GuessMachine.runBranch_halted_iff`: exact terminal trace and output.
* `Turing.MultiTapeCTM.GuessMachine.trace_bijOn`: one terminal branch per length-`n` word.
* `Turing.MultiTapeCTM.GuessMachine.branchCount_eq`: preserve every output-predicate count.
* `Turing.MultiTapeCTM.GuessMachine.count_interpret_output`: the shared FreeM/List program
  generates each length-`n` word once.

The scanner is used by the parsimonious guess/verify construction in `MultiTape.Counting.Verifier`
and the #P characterization in `Classes.SharpP.Characterization`. Balanced signed routing in
`Classes.SharpP.GapMachine` gives the reverse GapP construction and characterization.

## References

The witness-guessing construction is standard in counting complexity [Valiant1979]. The scanner
and its configuration invariant adapt `MultiTape.Probabilistic.Sampling`, credited there to the
cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`. Here the List choice interface
and the singleton halt preserve exact branch multiplicity, rather than only the output law.
-/

@[expose] public section

namespace Turing.MultiTapeCTM

namespace GuessMachine

/-- The ordinary instruction for one guessed bit. -/
def emit (bit : Bool) : Turing.Action 0 Bool Unit :=
  { inputTape := 1, workTapes := Fin.elim0, output := some bit, state := some () }

/-- The final instruction emits nothing and halts without moving the input head. -/
def halt : Turing.Action 0 Bool Unit :=
  { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }

end GuessMachine

/-- Emit one independently chosen bit per input symbol, then take a single halting occurrence. -/
def guessMachine : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ symbol _ _ := (if symbol.isSome then
    [GuessMachine.emit false, GuessMachine.emit true] else [GuessMachine.halt]).map
    MultiTapeMachine.Action.emptyOracleEquiv.symm

namespace GuessMachine

/-- Every scanner local view has two bit occurrences or one final halt occurrence. -/
theorem nonblocking : guessMachine.Nonblocking := by
  intro state symbol work
  cases symbol <;> simp [guessMachine]

/-- The scanner at a position in the input, with its current output prefix. -/
def config (input : List Bool) (state : Option Unit) (index : ℕ) (output : List Bool)
    (h : index ≤ input.length) : Cfg 0 Bool Unit input where
  state := state
  inputPos := ⟨index + 1, by lia⟩
  workTapes := Fin.elim0
  workTapePos := Fin.elim0
  output := output

/-- Each bit selects its occurrence index; the last zero selects the singleton halt. -/
def trace (word : List Bool) : List ℕ := word.map Bool.toNat ++ [0]

@[simp] theorem trace_nil : trace [] = [0] := rfl

@[simp] theorem trace_cons (bit : Bool) (word : List Bool) :
    trace (bit :: word) = bit.toNat :: trace word := rfl

@[simp] theorem length_trace (word : List Bool) : (trace word).length = word.length + 1 := by
  simp [trace]

theorem trace_injective : Function.Injective trace := by
  intro first second h
  have hm : first.map Bool.toNat = second.map Bool.toNat := List.append_cancel_right h
  exact List.map_injective_iff.mpr (fun a b hab => by cases a <;> cases b <;> simp_all) hm

private theorem actions_inner {input output : List Bool} {index : ℕ}
    (h : index < input.length) :
    guessMachine.actions (config input (some ()) index output (by lia)) =
      [emit false, emit true] := by
  have hsym := inputSymbolInner (cfg := config input (some ()) index output (by lia))
    index (by simp [config]; lia) h
  simp only [actions, show (config input (some ()) index output (by lia)).state = some ()
    from rfl, guessMachine, hsym, Option.isSome_some, ↓reduceIte, List.map_map]
  rfl

private theorem actions_boundary (input output : List Bool) :
    guessMachine.actions (config input (some ()) input.length output le_rfl) = [halt] := by
  have hsym := inputSymbol_eq_none_of_boundary
    (cfg := config input (some ()) input.length output le_rfl) (Or.inr rfl)
  simp only [actions, show (config input (some ()) input.length output le_rfl).state = some ()
    from rfl, guessMachine, hsym, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.map_map]
  rfl

private theorem apply_emit {input output : List Bool} {index : ℕ}
    (h : index < input.length) (bit : Bool) :
    (emit bit).apply (config input (some ()) index output (by lia)) =
      config input (some ()) (index + 1) (output ++ [bit]) h := by
  refine Cfg.ext_zero_tapes rfl ?_ rfl
  apply Fin.ext
  change (moveInputPos _ .pos).val = index + 1 + 1
  rw [moveInputPos_pos_of_ne_right _ (by simp only [config]; lia)]
  rfl

private theorem apply_halt (input output : List Bool) :
    halt.apply (config input (some ()) input.length output le_rfl) =
      config input none input.length output le_rfl := by
  apply Cfg.ext_zero_tapes <;> simp [Turing.Action.apply, halt, config]

theorem step?_inner {input output : List Bool} {index : ℕ}
    (h : index < input.length) (choice : ℕ) :
    guessMachine.step? (config input (some ()) index output (by lia)) choice =
      if choice < 2 then
        some (config input (some ()) (index + 1) (output ++ [choice == 1]) h)
      else none := by
  rcases choice with _ | (_ | choice)
  · simp [step?, actions_inner h, apply_emit h]
  · simp [step?, actions_inner h, apply_emit h]
  · simp [step?, actions_inner h]

theorem step?_boundary (input output : List Bool) (choice : ℕ) :
    guessMachine.step? (config input (some ()) input.length output le_rfl) choice =
      if choice = 0 then some (config input none input.length output le_rfl) else none := by
  cases choice <;> simp [step?, actions_boundary, apply_halt]

/-- Replaying the bit choices writes that word, without taking the final halting instruction. -/
theorem runBranch_bits (input output word : List Bool) (index : ℕ)
    (h : index + word.length ≤ input.length) :
    guessMachine.runBranch (config input (some ()) index output (by lia))
      (word.map Bool.toNat) =
      some (config input (some ()) (index + word.length) (output ++ word) h) := by
  induction word generalizing index output with
  | nil => simp [config]
  | cons bit word ih =>
    have hi : index < input.length := by simp only [List.length_cons] at h; lia
    have hindex : index + 1 + word.length = index + (word.length + 1) := by lia
    rw [List.map_cons, runBranch_cons, step?_inner hi]
    cases bit <;> simp [ih (output ++ [_]) (index + 1) (by
      simp only [List.length_cons] at h; lia), List.append_assoc, hindex]

/-- A word of the remaining length ends at its output and the right boundary. -/
theorem runBranch_trace (input output word : List Bool) (index : ℕ)
    (h : index + word.length = input.length) :
    guessMachine.runBranch (config input (some ()) index output (by lia)) (trace word) =
      some (config input none input.length (output ++ word) le_rfl) := by
  rw [trace, runBranch_append, runBranch_bits input output word index (by lia)]
  simp only [Option.bind_some, h, runBranch_cons, step?_boundary, ↓reduceIte,
    runBranch_nil]

private theorem haltsWithin_config (input : List Bool) (remaining : ℕ) :
    ∀ (index : ℕ) (output : List Bool) (h : index + remaining = input.length),
      guessMachine.HaltsWithin (remaining + 1)
        (config input (some ()) index output (by lia)) := by
  induction remaining with
  | zero =>
    intro index output h
    have hi : index = input.length := by lia
    subst index
    apply HaltsWithin.step (by rw [actions_boundary]; simp)
    rintro ⟨choice, hchoice⟩
    simp only [actions_boundary, List.length_cons, List.length_nil] at hchoice
    have hi : choice = 0 := by lia
    subst choice
    apply HaltsWithin.halt
    change ((guessMachine.actions _)[0].apply _).Halted
    simp only [actions_boundary, List.getElem_cons_zero, apply_halt]
    rfl
  | succ remaining ih =>
    intro index output h
    have hi : index < input.length := by lia
    apply HaltsWithin.step (by rw [actions_inner hi]; simp)
    rintro ⟨choice, hchoice⟩
    simp only [actions_inner hi, List.length_cons, List.length_nil] at hchoice
    have hc : choice = 0 ∨ choice = 1 := by lia
    change guessMachine.HaltsWithin _ ((guessMachine.actions _)[choice].apply _)
    rcases hc with hc | hc <;>
      simpa [actions_inner hi, hc, apply_emit hi] using
        ih (index + 1) (output ++ [_]) (by lia)

/-- Starting from blank tapes is the zero-position scanner invariant. -/
theorem init_eq_config (input : List Bool) :
    Cfg.init guessMachine.initial input = config input (some ()) 0 [] (Nat.zero_le _) := by
  exact Cfg.ext_zero_tapes rfl rfl rfl

/-- Every branch halts in `n + 1` transitions, with a nonempty choice list at every live node. -/
theorem haltsWithin (input : List Bool) :
    guessMachine.HaltsWithin (input.length + 1) (Cfg.init guessMachine.initial input) := by
  rw [init_eq_config]
  exact haltsWithin_config input input.length 0 [] (by lia)

private theorem word_of_runBranch (input : List Bool) (choices : List ℕ) :
    ∀ (index : ℕ) (output : List Bool) (h : index ≤ input.length)
      (final : Cfg 0 Bool Unit input),
      guessMachine.runBranch (config input (some ()) index output h) choices = some final →
      final.Halted → ∃ word : List Bool, index + word.length = input.length ∧
        choices = trace word ∧ final = config input none input.length (output ++ word) le_rfl := by
  induction choices with
  | nil =>
    intro index output h final hrun hhalt
    cases Option.some.inj hrun
    cases hhalt
  | cons choice rest ih =>
    intro index output h final hrun hhalt
    by_cases hi : index < input.length
    · rw [runBranch_cons, step?_inner hi] at hrun
      split at hrun
      · rename_i hc
        obtain ⟨word, hlen, hrest, rfl⟩ :=
          ih (index + 1) (output ++ [choice == 1]) hi final hrun hhalt
        refine ⟨(choice == 1) :: word, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          lia
        · have hb : (choice == 1).toNat = choice := by
            have : choice = 0 ∨ choice = 1 := by lia
            rcases this with rfl | rfl <;> rfl
          simp [hrest, hb]
        · simp [List.append_assoc]
      · simp at hrun
    · have hi : index = input.length := by lia
      subst index
      rw [runBranch_cons, step?_boundary] at hrun
      split at hrun
      · rename_i hc
        subst choice
        cases rest with
        | nil =>
          have heq : config input none input.length output le_rfl = final :=
            Option.some.inj hrun
          exact ⟨[], by simp, rfl, by simpa using heq.symm⟩
        | cons choice rest =>
          simp [runBranch_cons, guessMachine.step?_of_halted
            (show (config input none input.length output le_rfl).Halted from rfl)] at hrun
      · simp at hrun

/-- Soundness and completeness of terminal replay, including its exact output. -/
theorem runBranch_halted_iff (input : List Bool) (choices : List ℕ)
    (final : Cfg 0 Bool Unit input) :
    guessMachine.runBranch (Cfg.init guessMachine.initial input) choices = some final ∧
      final.Halted ↔
      ∃ word : List Bool, word.length = input.length ∧ choices = trace word ∧
        final = config input none input.length word le_rfl := by
  rw [init_eq_config]
  constructor
  · rintro ⟨hrun, hhalt⟩
    simpa only [Nat.zero_add, List.nil_append] using
      word_of_runBranch input choices 0 [] (Nat.zero_le _) final hrun hhalt
  · rintro ⟨word, hlen, rfl, rfl⟩
    exact ⟨by simpa only [List.nil_append] using
      runBranch_trace input [] word 0 (by lia), rfl⟩

/-- Every terminal branch has exactly one instruction per input symbol and one final halt. -/
theorem length_of_terminal {input : List Bool} {choices : List ℕ}
    {final : Cfg 0 Bool Unit input}
    (hrun : guessMachine.runBranch (Cfg.init guessMachine.initial input) choices = some final)
    (hhalt : final.Halted) : choices.length = input.length + 1 := by
  obtain ⟨word, hlen, rfl, _⟩ := (runBranch_halted_iff input choices final).mp ⟨hrun, hhalt⟩
  simp [hlen]

/-- The bounded terminal traces are exactly the encoded witnesses, with the exact clock exposed. -/
theorem mem_branches_iff (input : List Bool) (fuel : ℕ) (choices : List ℕ) :
    choices ∈ guessMachine.branches fuel (Cfg.init guessMachine.initial input) ↔
      input.length + 1 ≤ fuel ∧
        ∃ word : List Bool, word.length = input.length ∧ choices = trace word := by
  rw [MultiTapeCTM.mem_branches_iff]
  simp only [runBranch_halted_iff]
  constructor
  · rintro ⟨hlen, final, word, hword, rfl, _⟩
    exact ⟨by simpa [hword] using hlen, word, hword, rfl⟩
  · rintro ⟨hlen, word, hword, rfl⟩
    exact ⟨by simpa [hword] using hlen, _, word, hword, rfl, rfl⟩

/-- Witness words and first-halting occurrence traces are in bijection. -/
theorem trace_bijOn (input : List Bool) :
    Set.BijOn trace {word | word.length = input.length}
      (guessMachine.branches (input.length + 1) (Cfg.init guessMachine.initial input)) := by
  refine ⟨?_, trace_injective.injOn, ?_⟩
  · intro word hword
    exact (mem_branches_iff input _ _).mpr ⟨le_rfl, word, hword, rfl⟩
  · intro choices hchoices
    obtain ⟨_, word, hword, heq⟩ := (mem_branches_iff input _ _).mp hchoices
    exact ⟨word, hword, heq.symm⟩

/-- The same bijection, enumerated by the existing fixed-width bit-string type. -/
theorem branches_eq_image (input : List Bool) :
    guessMachine.branches (input.length + 1) (Cfg.init guessMachine.initial input) =
      Finset.univ.image (fun word : Cslib.BitString input.length => trace (List.ofFn word)) := by
  ext choices
  simp only [mem_branches_iff, le_refl, true_and, Finset.mem_image, Finset.mem_univ]
  constructor
  · rintro ⟨word, hword, rfl⟩
    refine ⟨fun i => word[i.val]'(by lia), ?_⟩
    congr 1
    apply List.ext_getElem <;> simp [hword]
  · rintro ⟨word, rfl⟩
    exact ⟨List.ofFn word, by simp, rfl⟩

/-- There are exactly `2 ^ n` terminal branches, including one when the input is empty. -/
theorem card_branches (input : List Bool) :
    (guessMachine.branches (input.length + 1) (Cfg.init guessMachine.initial input)).card =
      2 ^ input.length := by
  rw [branches_eq_image]
  calc
    _ = (Finset.univ : Finset (Cslib.BitString input.length)).card :=
      Finset.card_image_of_injective _ (trace_injective.comp List.ofFn_injective)
    _ = 2 ^ input.length := by simp [Cslib.BitString]

/-- Counting any output predicate is exactly counting witnesses satisfying that predicate. -/
theorem branchCount_eq (input : List Bool) (verdict : List Bool → Bool) :
    guessMachine.branchCount verdict (input.length + 1) (Cfg.init guessMachine.initial input) =
      (Finset.univ.filter fun word : Cslib.BitString input.length =>
        verdict (List.ofFn word)).card := by
  have hrun (word : Cslib.BitString input.length) :
      guessMachine.runBranch (Cfg.init guessMachine.initial input) (trace (List.ofFn word)) =
        some (config input none input.length (List.ofFn word) le_rfl) := by
    rw [init_eq_config]
    simpa only [List.nil_append] using runBranch_trace input [] (List.ofFn word) 0 (by simp)
  simp only [branchCount, branches_eq_image, Finset.filter_image, hrun, Option.any_some]
  exact Finset.card_image_of_injective _ (trace_injective.comp List.ofFn_injective)

open Cslib

private theorem interpret_runProgram_config (input : List Bool) (remaining : ℕ) :
    ∀ (index : ℕ) (output : List Bool) (h : index + remaining = input.length),
      (OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
        (guessMachine.runProgram (remaining + 1)
          (config input (some ()) index output (by lia)))).Perm
        ((BitString.enumList remaining).map
          (fun word => config input none input.length (output ++ word) le_rfl)) := by
  induction remaining with
  | zero =>
    intro index output h
    have hi : index = input.length := by lia
    subst index
    rw [interpret_runProgram_succ guessMachine _ 0 () rfl, actions_boundary]
    simp [runProgram_zero, apply_halt]
  | succ remaining ih =>
    intro index output h
    have hi : index < input.length := by lia
    rw [interpret_runProgram_succ guessMachine _ (remaining + 1) () rfl, actions_inner hi]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, apply_emit hi]
    refine ((ih (index + 1) (output ++ [false]) (by lia)).append
      (ih (index + 1) (output ++ [true]) (by lia))).trans ?_
    simp only [BitString.enumList_succ, List.map_flatMap, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append]
    simpa only [← List.map_eq_flatMap, List.singleton_append] using
      (List.flatMap_append_perm (BitString.enumList remaining)
        (fun word => [config input none input.length (output ++ false :: word) le_rfl])
        (fun word => [config input none input.length (output ++ true :: word) le_rfl]))

/-- List interpretation of the shared program returns each word once, in scanner enumeration order.
The existing bit-string enumeration can use a different order, so the result is a permutation. -/
theorem interpret_runProgram (input : List Bool) :
    (OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
      (guessMachine.runProgram (input.length + 1) (Cfg.init guessMachine.initial input))).Perm
      ((BitString.enumList input.length).map
        (fun word => config input none input.length word le_rfl)) := by
  rw [init_eq_config]
  simpa only [List.nil_append] using
    interpret_runProgram_config input input.length 0 [] (by lia)

/-- The shared FreeM program generates each word of the input length with multiplicity one. -/
theorem count_interpret_output (input word : List Bool) :
    (OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
      (Cfg.output <$> guessMachine.runProgram (input.length + 1)
        (Cfg.init guessMachine.initial input))).count word =
      if word.length = input.length then 1 else 0 := by
  have hp : (List.map Cfg.output (OracleComp.interpret
      (fun n => List.ofFn (id : Fin n → Fin n))
      (guessMachine.runProgram (input.length + 1) (Cfg.init guessMachine.initial input)))).Perm
      (BitString.enumList input.length) := by
    simpa [config, Function.comp_def] using (interpret_runProgram input).map Cfg.output
  rw [OracleComp.interpret_map]
  change (List.map Cfg.output (OracleComp.interpret
    (fun n => List.ofFn (id : Fin n → Fin n))
    (guessMachine.runProgram (input.length + 1)
      (Cfg.init guessMachine.initial input)))).count word = _
  rw [hp.count_eq]
  have hn : (BitString.enumList input.length).Nodup :=
    (BitString.nodup_enum _).map List.ofFn_injective
  by_cases h : word.length = input.length
  · rw [ite_eq_left h]
    exact List.count_eq_one_of_mem hn (BitString.mem_enumList.mpr h)
  · simp [h, List.count_eq_zero]

end GuessMachine

end Turing.MultiTapeCTM
