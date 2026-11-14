/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Prepend
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.CopyToOrigin
import Mathlib.Tactic.FinCases

/-!
# Dispatching a counting terminal to its actual alternating evaluator

A terminal word is `[query, carry, claimOrAnswer] ++ index`. Three native transitions read the
flags. A constant terminal emits its answer and halts. A query copies the remaining index to a
blank root-index tape, then enters the selected carry/save evaluator with its actual tapes.
The original terminal word is preserved. No transition receives a semantic oracle answer.
-/

public section

namespace Turing.MultiTapeATM.CountingTerminalDispatch

/-- Finite control for three flag reads and the chosen native continuation. -/
inductive State (S : Type) where
  | query
  | carry (query : Bool)
  | answer (query carry : Bool)
  | continuation (carry answer : Bool) (state : S)

instance {S : Type} [Finite S] : Finite (State S) :=
  Finite.of_injective (fun q : State S => match q with
    | .query => (Sum.inl none : Option (Bool ⊕ Bool × Bool) ⊕ Bool × Bool × S)
    | .carry query => .inl (some (.inl query))
    | .answer query carry => .inl (some (.inr (query, carry)))
    | .continuation carry answer state => .inr (carry, answer, state)) (by
      intro a b h
      cases a <;> cases b <;> simp_all)

variable {k : ℕ} {S : Type}

private def readAction (flags : Fin k) (state : Option (State S)) (output : Option Bool) :
    Turing.Action k Bool (State S) :=
  ⟨0, Function.update (fun _ => (none, 0)) flags (none, 1), output, state⟩

private noncomputable def transition (flags : Fin k)
    (family : Bool → Bool → MultiTapeATM k Bool S) (bit : Bool) :
    State S → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool (State S)
  | .query, _, work => readAction flags (some (.carry ((work flags).getD false))) none
  | .carry query, _, work =>
    readAction flags (some (.answer query ((work flags).getD false))) none
  | .answer query carry, _, work =>
    let answer := (work flags).getD false
    if query then
      readAction flags (some (.continuation carry answer (family carry answer).toPTM.initial)) none
    else readAction flags none (some answer)
  | .continuation carry answer state, input, work =>
    let action := (family carry answer).action state input work bit
    { action with state := action.state.map (.continuation carry answer) }

private def universal (family : Bool → Bool → MultiTapeATM k Bool S) : State S → Bool
  | .continuation carry answer state => (family carry answer).universal state
  | _ => false

private noncomputable def reader (flags : Fin k)
    (family : Bool → Bool → MultiTapeATM k Bool S) : MultiTapeATM k Bool (State S) :=
  ofTMs (fun bit => MultiTapeTM.ofTr .query (transition flags family bit)) (universal family)

private def atHead {input : List Bool} (flags : Fin k) (position : ℕ)
    (storage : Cfg k Bool Unit input) : Cfg k Bool Unit input :=
  { storage.withState none with
    workTapePos := Function.update storage.workTapePos flags (position : ℤ) }

private theorem atHead_zero {input : List Bool} (flags : Fin k)
    (storage : Cfg k Bool Unit input) (h : storage.workTapePos flags = 0) :
    (atHead flags 0 storage).withState (some (State.query (S := S))) =
      storage.withState (some (State.query (S := S))) := by
  simp [atHead, ← h, Cfg.withState]

private theorem apply_readAction {input : List Bool} (flags : Fin k) (position : ℕ)
    (storage : Cfg k Bool Unit input) (state next : Option (State S)) (output : Option Bool) :
    (readAction flags next output).apply ((atHead flags position storage).withState state) =
      (atHead flags (position + 1)
        { storage with output := storage.output ++ output.toList }).withState next := by
  apply Cfg.ext <;> try rfl
  · simp [readAction, Turing.Action.apply, atHead, moveInputPos_zero]
  · funext i
    by_cases hi : i = flags <;> simp [readAction, Turing.Action.apply, atHead, Cfg.withState, hi]
  · funext i
    by_cases hi : i = flags <;> simp [readAction, Turing.Action.apply, atHead, Cfg.withState, hi]

private theorem next_query {input : List Bool} (flags : Fin k)
    (family : Bool → Bool → MultiTapeATM k Bool S) (storage : Cfg k Bool Unit input)
    (query carry answer bit : Bool) (index : List Bool)
    (hw : storage.workTapes flags = tapeOfList ([query, carry, answer] ++ index)) :
    (reader flags family).next bit ((atHead flags 0 storage).withState (some .query)) =
      (atHead flags 1 storage).withState (some (.carry query)) := by
  rw [reader, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have hr : ((atHead flags 0 storage).withState (some (State.query (S := S)))).workTapeSymbols
      flags = some query := by
    simp only [Cfg.workTapeSymbols, atHead, hw, Cfg.withState, Function.update_self]
    rfl
  simp only [MultiTapeTM.tr_ofTr, transition, hr, Option.getD_some, apply_readAction,
    Option.toList_none, List.append_nil]

private theorem next_carry {input : List Bool} (flags : Fin k)
    (family : Bool → Bool → MultiTapeATM k Bool S) (storage : Cfg k Bool Unit input)
    (query carry answer bit : Bool) (index : List Bool)
    (hw : storage.workTapes flags = tapeOfList ([query, carry, answer] ++ index)) :
    (reader flags family).next bit ((atHead flags 1 storage).withState (some (.carry query))) =
      (atHead flags 2 storage).withState (some (.answer query carry)) := by
  rw [reader, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have hr : ((atHead flags 1 storage).withState (some (State.carry (S := S) query))).workTapeSymbols
      flags = some carry := by
    simp only [Cfg.workTapeSymbols, atHead, Cfg.withState, Function.update_self, hw]
    rfl
  simp only [MultiTapeTM.tr_ofTr, transition, hr, Option.getD_some, apply_readAction,
    Option.toList_none, List.append_nil]

private theorem next_answer_query {input : List Bool} (flags : Fin k)
    (family : Bool → Bool → MultiTapeATM k Bool S) (storage : Cfg k Bool Unit input)
    (carry answer bit : Bool) (index : List Bool)
    (hw : storage.workTapes flags = tapeOfList ([true, carry, answer] ++ index)) :
    (reader flags family).next bit
        ((atHead flags 2 storage).withState (some (.answer true carry))) =
      ((atHead flags 3 storage).withState (some (family carry answer).toPTM.initial)).mapState
        (Option.map (.continuation carry answer)) := by
  rw [reader, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have hr : ((atHead flags 2 storage).withState
      (some (State.answer (S := S) true carry))).workTapeSymbols flags = some answer := by
    simp only [Cfg.workTapeSymbols, atHead, Cfg.withState, Function.update_self, hw]
    rfl
  simp only [MultiTapeTM.tr_ofTr, transition, hr, Option.getD_some,
    ite_true, apply_readAction, Option.toList_none, List.append_nil]
  rfl

private theorem next_answer_constant {input : List Bool} (flags : Fin k)
    (family : Bool → Bool → MultiTapeATM k Bool S) (storage : Cfg k Bool Unit input)
    (carry answer bit : Bool) (index : List Bool)
    (hw : storage.workTapes flags = tapeOfList ([false, carry, answer] ++ index)) :
    (reader flags family).next bit
        ((atHead flags 2 storage).withState (some (.answer false carry))) =
      (atHead flags 3 { storage with output := storage.output ++ [answer] }).withState none := by
  rw [reader, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have hr : ((atHead flags 2 storage).withState
      (some (State.answer (S := S) false carry))).workTapeSymbols flags = some answer := by
    simp only [Cfg.workTapeSymbols, atHead, Cfg.withState, Function.update_self, hw]
    rfl
  simp only [MultiTapeTM.tr_ofTr, transition, hr, Option.getD_some, Bool.false_eq_true,
    ite_false, apply_readAction, Option.toList_some]

private noncomputable def continuationSimulation (flags : Fin k)
    (family : Bool → Bool → MultiTapeATM k Bool S) (carry answer : Bool) :
    StateSimulation (family carry answer) (reader flags family) where
  stateMap := .continuation carry answer
  universal_eq _ := rfl
  next_eq c bit := by
    cases hs : c.state with
    | none =>
      rw [next_of_halted _ (by simp [Cfg.mapState, hs]), next_of_halted _ hs]
    | some q =>
      have hstate : (c.mapState (Option.map (State.continuation carry answer))).state =
          some (State.continuation carry answer q) := by simp [Cfg.mapState, hs]
      rw [reader, next_ofTMs, MultiTapeTM.step_of_state hstate, next_of_state _ hs]
      simp only [MultiTapeTM.tr_ofTr, transition]
      rfl

private def copyEmb (flags root : Fin k) (h : flags ≠ root) : Fin 2 ↪ Fin k :=
  ⟨![flags, root], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

private noncomputable def prepare (flags root : Fin k) (h : flags ≠ root) :=
  MultiTapeTM.CopyToOrigin.machine.extendTapes (copyEmb flags root h)

/-- Read a terminal and either halt with its constant answer or copy its index and enter the
selected actual carry/save machine. -/
noncomputable def machine (flags root : Fin k) (h : flags ≠ root)
    (family : Bool → Bool → MultiTapeATM k Bool S) :=
  reader flags (fun carry answer => prependTM (prepare flags root h) (family carry answer))

/-- Actual query storage after copying: flags intact at their right blank, root index at zero,
and every other tape, input position and output unchanged. -/
@[expose] def copied {input : List Bool} (flags root : Fin k) (index : List Bool)
    (storage : Cfg k Bool Unit input) : Cfg k Bool Unit input :=
  { storage.withState none with
    workTapes := Function.update storage.workTapes root (tapeOfList index)
    workTapePos := Function.update
      (Function.update storage.workTapePos flags (3 + index.length : ℕ)) root 0 }

private theorem run_prepare {input : List Bool} (flags root : Fin k) (hne : flags ≠ root)
    (storage : Cfg k Bool Unit input) (carry answer : Bool) (index : List Bool)
    (hw : storage.workTapes flags = tapeOfList ([true, carry, answer] ++ index))
    (hr : storage.workTapes root = tapeOfList []) (hp : storage.workTapePos root = 0)
    (hi : storage.inputPos = 0) :
    (prepare flags root hne).runFrom
        ((atHead flags 3 storage).withState (some (prepare flags root hne).q₀))
        (2 * index.length + 5) = (copied flags root index storage).withState none := by
  let e := copyEmb flags root hne
  have hv : MultiTapeTM.viewCfg e (atHead flags 3 storage) =
      MultiTapeTM.CopyToOrigin.initial input [true, carry, answer] index storage.output := by
    apply Cfg.ext
    · rfl
    · exact hi
    · funext j z
      fin_cases j
      · change storage.workTapes flags z = _
        rw [hw]
        simp [MultiTapeTM.CopyToOrigin.initial, MultiTapeTM.AppendWord.config, tapesCfg]
      · change storage.workTapes root z = _
        rw [hr]
        simp [MultiTapeTM.CopyToOrigin.initial, MultiTapeTM.AppendWord.config, tapesCfg]
    · funext j
      fin_cases j
      · change Function.update storage.workTapePos flags (3 : ℤ) flags = 3
        rw [Function.update_self]
      · change Function.update storage.workTapePos flags (3 : ℤ) root = 0
        rw [Function.update_of_ne (Ne.symm hne), hp]
    · rfl
  have ht := MultiTapeTM.CopyToOrigin.runsBetween input [true, carry, answer] index storage.output
  rw [← hv] at ht
  have he : MultiTapeTM.embed e
      (MultiTapeTM.CopyToOrigin.final input [true, carry, answer] index storage.output)
      (atHead flags 3 storage).workTapes (atHead flags 3 storage).workTapePos =
      copied flags root index storage := by
    apply Cfg.ext
    · rfl
    · exact hi.symm
    · funext j
      by_cases hjf : j = flags
      · subst j
        change (MultiTapeTM.embed e _ _ _).workTapes (e 0) = _
        rw [MultiTapeTM.embed_workTapes_embed]
        simpa [copied, MultiTapeTM.CopyToOrigin.final, tapesCfg, Cfg.withState, hne] using hw.symm
      · by_cases hjr : j = root
        · subst j
          change (MultiTapeTM.embed e _ _ _).workTapes (e 1) = _
          rw [MultiTapeTM.embed_workTapes_embed]
          simp [copied, MultiTapeTM.CopyToOrigin.final, tapesCfg, Cfg.withState]
        · have hn : j ∉ Set.range e := by
            rintro ⟨i, rfl⟩
            fin_cases i <;> contradiction
          simp [MultiTapeTM.embed, MultiTapeTM.partialInv_eq_none e hn, copied, atHead,
            Cfg.withState, hjr]
    · funext j
      by_cases hjf : j = flags
      · subst j
        change (MultiTapeTM.embed e _ _ _).workTapePos (e 0) = _
        rw [MultiTapeTM.embed_workTapePos_embed]
        simp [copied, MultiTapeTM.CopyToOrigin.final, tapesCfg, Cfg.withState, hne]
        omega
      · by_cases hjr : j = root
        · subst j
          change (MultiTapeTM.embed e _ _ _).workTapePos (e 1) = _
          rw [MultiTapeTM.embed_workTapePos_embed]
          simp [copied, MultiTapeTM.CopyToOrigin.final, tapesCfg, Cfg.withState]
        · have hn : j ∉ Set.range e := by
            rintro ⟨i, rfl⟩
            fin_cases i <;> contradiction
          simp [MultiTapeTM.embed, MultiTapeTM.partialInv_eq_none e hn, copied, atHead,
            Cfg.withState, hjf, hjr]
    · rfl
  have h := (ht.extendTapes e).1
  rw [he] at h
  exact h

private theorem reader_query_spec {input : List Bool} (flags : Fin k)
    (family : Bool → Bool → MultiTapeATM k Bool S) (storage : Cfg k Bool Unit input)
    (carry answer : Bool) (index : List Bool) (n : ℕ)
    (hw : storage.workTapes flags = tapeOfList ([true, carry, answer] ++ index))
    (hh : (family carry answer).HaltsWithin n
      ((atHead flags 3 storage).withState (some (family carry answer).toPTM.initial))) :
    (reader flags family).HaltsWithin (n + 3)
        ((atHead flags 0 storage).withState (some .query)) ∧
      ((reader flags family).AcceptsWithin (n + 3)
        ((atHead flags 0 storage).withState (some .query)) ↔
        (family carry answer).AcceptsWithin n
          ((atHead flags 3 storage).withState (some (family carry answer).toPTM.initial))) := by
  have h₀ := fun bit => next_query flags family storage true carry answer bit index hw
  have h₁ := fun bit => next_carry flags family storage true carry answer bit index hw
  have h₂ := fun bit => next_answer_query flags family storage carry answer bit index hw
  constructor
  · rw [show n + 3 = (n + 1 + 1) + 1 by omega, haltsWithin_succ]
    intro b
    rw [h₀ b, haltsWithin_succ]
    intro b
    rw [h₁ b, haltsWithin_succ]
    intro b
    rw [h₂ b]
    exact ((continuationSimulation flags family carry answer).haltsWithin_iff n _).mpr hh
  · rw [show n + 3 = (n + 1 + 1) + 1 by omega,
      acceptsWithin_succ_of_next_eq h₀, acceptsWithin_succ_of_next_eq h₁,
      acceptsWithin_succ_of_next_eq h₂]
    exact (continuationSimulation flags family carry answer).acceptsWithin_iff n _

/-- A query reads its three flags, copies only its encoded index, and enters the selected native
family. Acceptance and all-branch halting include both the copy and the family clock. -/
theorem query_spec {input : List Bool} (flags root : Fin k) (hne : flags ≠ root)
    (family : Bool → Bool → MultiTapeATM k Bool S) (storage : Cfg k Bool Unit input)
    (carry claim : Bool) (index : List Bool) (n : ℕ)
    (hw : storage.workTapes flags = tapeOfList ([true, carry, claim] ++ index))
    (hf : storage.workTapePos flags = 0)
    (hr : storage.workTapes root = tapeOfList []) (hp : storage.workTapePos root = 0)
    (hi : storage.inputPos = 0)
    (hh : (family carry claim).HaltsWithin n
      ((copied flags root index storage).withState (some (family carry claim).toPTM.initial))) :
    (machine flags root hne family).HaltsWithin (2 * index.length + 8 + n)
        (storage.withState (some (machine flags root hne family).toPTM.initial)) ∧
      ((machine flags root hne family).AcceptsWithin (2 * index.length + 8 + n)
        (storage.withState (some (machine flags root hne family).toPTM.initial)) ↔
        (family carry claim).AcceptsWithin n
          ((copied flags root index storage).withState
            (some (family carry claim).toPTM.initial))) := by
  have hc := prependTM_spec (prepare flags root hne) (family carry claim)
    (atHead flags 3 storage) (copied flags root index storage) (2 * index.length + 5) n
    (run_prepare flags root hne storage carry claim index hw hr hp hi) hh
  have hd := reader_query_spec flags
    (fun carry claim => prependTM (prepare flags root hne) (family carry claim))
    storage carry claim index (2 * index.length + 5 + n) hw hc.1
  rw [atHead_zero flags storage hf] at hd
  have hclock : 2 * index.length + 5 + n + 3 = 2 * index.length + 8 + n := by omega
  rw [hclock] at hd
  exact ⟨hd.1, hd.2.trans hc.2⟩

/-- A constant terminal reads three flags and emits its answer. An initially empty output is
required for the standard alternating acceptance convention `output = [true]`. -/
theorem constant_spec {input : List Bool} (flags root : Fin k) (hne : flags ≠ root)
    (family : Bool → Bool → MultiTapeATM k Bool S) (storage : Cfg k Bool Unit input)
    (carry answer : Bool) (index : List Bool)
    (hw : storage.workTapes flags = tapeOfList ([false, carry, answer] ++ index))
    (hf : storage.workTapePos flags = 0) (ho : storage.output = []) :
    (machine flags root hne family).HaltsWithin 3
        (storage.withState (some (machine flags root hne family).toPTM.initial)) ∧
      ((machine flags root hne family).AcceptsWithin 3
        (storage.withState (some (machine flags root hne family).toPTM.initial)) ↔
        answer = true) := by
  let continuation := fun carry answer =>
    prependTM (prepare flags root hne) (family carry answer)
  have h₀ := fun bit => next_query flags continuation storage false carry answer bit index hw
  have h₁ := fun bit => next_carry flags continuation storage false carry answer bit index hw
  have h₂ := fun bit => next_answer_constant flags continuation storage carry answer bit index hw
  change (reader flags continuation).HaltsWithin (0 + 1 + 1 + 1)
    (storage.withState (some .query)) ∧
    ((reader flags continuation).AcceptsWithin (0 + 1 + 1 + 1)
      (storage.withState (some .query)) ↔ answer = true)
  rw [← atHead_zero flags storage hf]
  constructor
  · rw [haltsWithin_succ]
    intro b
    rw [h₀ b, haltsWithin_succ]
    intro b
    rw [h₁ b, haltsWithin_succ]
    intro b
    rw [h₂ b]
    exact haltsWithin_of_halted rfl
  · rw [acceptsWithin_succ_of_next_eq h₀, acceptsWithin_succ_of_next_eq h₁,
      acceptsWithin_succ_of_next_eq h₂, acceptsWithin_of_halted _ rfl]
    simp [atHead, ho, Cfg.withState]

end Turing.MultiTapeATM.CountingTerminalDispatch
