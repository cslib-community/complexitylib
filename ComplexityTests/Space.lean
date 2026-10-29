/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Space
import Complexity.Computability.Machines.Turing.MultiTape.Machine.Space
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Space
import Complexity.Computability.Complexity.Classes.Space.Savitch

/-! Polynomial-space classes and finite views of space-bounded nondeterministic machines:
inhabitants, a branch running forever, a stuck branch, repeated output, empty inputs, malformed
codes, and the codes of views. -/

namespace ComplexityTests.Space

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### Inhabitants -/

example :
    (∅ : Set (List Bool)) ∈ PSPACE encBits ∧
    (Set.univ : Set (List Bool)) ∈ NPSPACE encBits :=
  ⟨P_subset_PSPACE ⟨fun _ => false, ComputableInPolyTime.const false, fun _ => by simp⟩,
   PSPACE_subset_NPSPACE (P_subset_PSPACE
     ⟨fun _ => true, ComputableInPolyTime.const true, fun _ => by simp⟩)⟩

/-! ### A branch running forever -/

/-- Halt with output `[true]`. -/
private def acceptAction : Action 0 Bool Bool :=
  { inputTape := 0, workTapes := Fin.elim0, output := some true, state := none }

/-- Stay in the initial state, emitting nothing. -/
private def loopAction : Action 0 Bool Bool :=
  { inputTape := 0, workTapes := Fin.elim0, output := none, state := some false }

/-- From its only running state, either accept or loop forever. -/
private def loopOrAccept : MultiTapeNTM 0 Bool Bool where
  q₀ := false
  Tr q _ _ action := q = false ∧ (action = acceptAction ∨ action = loopAction)

/-- A computation path of one step accepts. -/
private theorem accepts_loopOrAccept (input : List Bool) : loopOrAccept.Accepts input := by
  have hstep : loopOrAccept.Step (loopOrAccept.initCfg input)
      (acceptAction.apply (loopOrAccept.initCfg input)) := ⟨acceptAction, ⟨rfl, .inl rfl⟩, rfl⟩
  refine ⟨⟨(RelSeries.singleton _ _).cons (loopOrAccept.initCfg input) hstep, rfl⟩, ?_, ?_⟩ <;>
    simp [acceptAction]

/-- The looping machine recognizes every word within no space: its looping branch does not
accept. -/
private theorem recognizesInSpace_loopOrAccept :
    loopOrAccept.RecognizesInSpace encBits Set.univ fun _ => 0 :=
  fun a => ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _, by simpa using accepts_loopOrAccept a⟩

/-- The looping branch stays at the initial configuration. -/
private theorem step_loop (input : List Bool) :
    loopOrAccept.Step (loopOrAccept.initCfg input) (loopOrAccept.initCfg input) := by
  refine ⟨loopAction, ⟨rfl, .inr rfl⟩, ?_⟩
  apply Cfg.ext_zero_tapes <;> simp [loopAction, Action.apply, loopOrAccept]

/-- The looping branch runs for any number of steps without leaving the initial configuration. -/
private theorem exists_path_loop (input : List Bool) (n : ℕ) :
    ∃ p : loopOrAccept.ComputationPath input, p.time = n ∧ p.last = loopOrAccept.initCfg input := by
  induction n with
  | zero => exact ⟨⟨RelSeries.singleton _ (loopOrAccept.initCfg input), rfl⟩, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨p, hp, hlast⟩ := ih
    obtain ⟨q, hq, hqlast⟩ := p.exists_snoc (c := loopOrAccept.initCfg input)
      (by rw [hlast]; exact step_loop input)
    exact ⟨q, by rw [hq, hp], hqlast⟩

/-- **Deciders halt.** The looping machine decides no problem within any space: no number of
steps bounds its looping branch, so the halting requirement of `NPSPACE` is not vacuous. -/
example (A : Set (List Bool)) (s : List Bool → ℕ) :
    ¬loopOrAccept.DecidesInSpace encBits A s := by
  rintro ⟨-, h⟩
  obtain ⟨t, ht⟩ := h []
  obtain ⟨p, hp, hlast⟩ := exists_path_loop (encBits []) t
  have hhalt := ht p hp.ge
  rw [hlast] at hhalt
  simp [MultiTapeNTM.initCfg, Cfg.init, Cfg.Halted, loopOrAccept] at hhalt

/-- Halt with output `[false]`. -/
private def rejectAction : Action 0 Bool Bool :=
  { inputTape := 0, workTapes := Fin.elim0, output := some false, state := none }

/-- From its only running state, either accept or reject: two halting branches. -/
private def rejectOrAccept : MultiTapeNTM 0 Bool Bool where
  q₀ := false
  Tr q _ _ action := q = false ∧ (action = acceptAction ∨ action = rejectAction)

/-- A computation path of one step accepts. -/
private theorem accepts_rejectOrAccept (input : List Bool) : rejectOrAccept.Accepts input := by
  have hstep : rejectOrAccept.Step (rejectOrAccept.initCfg input)
      (acceptAction.apply (rejectOrAccept.initCfg input)) := ⟨acceptAction, ⟨rfl, .inl rfl⟩, rfl⟩
  refine ⟨⟨(RelSeries.singleton _ _).cons (rejectOrAccept.initCfg input) hstep, rfl⟩, ?_, ?_⟩ <;>
    simp [acceptAction]

/-- **A branching decider.** Both branches halt after one step and one of them accepts, so the
machine decides every word within no space. -/
example : rejectOrAccept.DecidesInSpace encBits Set.univ fun _ => 0 :=
  ⟨fun a => ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _, by simpa using accepts_rejectOrAccept a⟩,
    fun _ => ⟨1, MultiTapeNTM.runsInTime_one_of_forall_step_initCfg fun c hc => by
      simp only [MultiTapeNTM.Step, MultiTapeNTM.initCfg, Cfg.init] at hc
      obtain ⟨action, ⟨-, rfl | rfl⟩, rfl⟩ := hc <;>
        simp [Cfg.Halted, Action.apply, acceptAction, rejectAction]⟩⟩

/-- Run paths of every length stay at the initial configuration. -/
private theorem exists_loop_path (input : List Bool) (n : ℕ) :
    ∃ p : loopOrAccept.RunPath input, p.head = loopOrAccept.initCfg input ∧ p.length = n ∧
      p.last = loopOrAccept.initCfg input := by
  induction n with
  | zero => exact ⟨RelSeries.singleton _ _, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨p, hhead, hlen, hlast⟩ := ih
    have hstep : loopOrAccept.Step p.last (loopOrAccept.initCfg input) :=
      hlast ▸ step_loop input
    exact ⟨p.snoc _ hstep, by simpa using hhead, by simp [hlen], by simp⟩

/-- The looping branch has computation paths of every length that have not halted. -/
example (input : List Bool) (n : ℕ) : ∃ p : loopOrAccept.ComputationPath input,
    p.time = n ∧ ¬p.last.Halted := by
  obtain ⟨p, hhead, hlen, hlast⟩ := exists_loop_path input n
  refine ⟨⟨p, hhead⟩, hlen, ?_⟩
  change ¬(RelSeries.last p).Halted
  rw [hlast]
  simp [loopOrAccept]

/-! ### Views -/

/-- Repeated output is not acceptance: `[true, true]` is summarized as `[false]`, while `[true]`
and `[false]` are preserved. -/
example :
    MultiTapeNTM.outputClass [true, true] = [false] ∧
    MultiTapeNTM.outputClass [true] = [true] ∧
    MultiTapeNTM.outputClass [false] = [false] :=
  ⟨rfl, rfl, rfl⟩

/-- Acceptance of the looping machine is witnessed by a reachable halted view with output
`[true]`, on the empty input. -/
example : ∃ finite, Relation.ReflTransGen loopOrAccept.ViewStep (loopOrAccept.initView [])
    finite ∧ finite.state = none ∧ finite.output = [true] :=
  MultiTapeNTM.accepts_iff_reflTransGen_viewStep.mp (accepts_loopOrAccept [])

/-! ### A stuck branch -/

/-- A machine permitting no action: its initial configuration is stuck. -/
private def stuck : MultiTapeNTM 0 Bool Bool where
  q₀ := false
  Tr _ _ _ _ := False

/-- The initial view of the stuck machine has no successor, even itself. -/
private theorem not_viewStep_stuck (input : List Bool) (next : FiniteCfg 0 Bool Bool) :
    ¬stuck.ViewStep (stuck.initView input) next := by
  simp [MultiTapeNTM.ViewStep, MultiTapeNTM.initView, FiniteCfg.init, stuck]

/-- A stuck branch does not accept: no halted view is reachable. -/
private theorem not_accepts_stuck (input : List Bool) : ¬stuck.Accepts input := by
  rw [MultiTapeNTM.accepts_iff_reflTransGen_viewStep]
  rintro ⟨finite, hreach, hstate, -⟩
  rcases Relation.ReflTransGen.cases_head hreach with rfl | ⟨next, hstep, -⟩
  · simp [MultiTapeNTM.initView, FiniteCfg.init] at hstate
  · exact not_viewStep_stuck input next hstep

/-- A stuck branch halts nowhere, yet bounds the computation: the stuck machine decides the empty
problem, its only path ending stuck before one step. -/
example : (∅ : Set (List Bool)) ∈ NPSPACE encBits :=
  ⟨0, Bool, inferInstance, stuck, fun _ => 0, .const 0, ⟨fun a =>
    ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _, iff_of_false id (not_accepts_stuck a)⟩,
    fun _ => ⟨1, MultiTapeNTM.runsInTime_one_of_forall_step_initCfg fun _ hc => by
      simp [MultiTapeNTM.Step, MultiTapeNTM.initCfg, Cfg.init, stuck] at hc⟩⟩⟩

/-- The step test rejects every successor of the stuck initial view. -/
example (input : List Bool) (next : FiniteCfg 0 Bool Bool) :
    stuck.viewStepB (stuck.initView input, next) = false := by
  rw [Bool.eq_false_iff, Ne, MultiTapeNTM.viewStepB_iff]
  exact not_viewStep_stuck input next

/-- A halted view steps to itself, and only to itself. -/
example (finite next : FiniteCfg 0 Bool Bool) (h : finite.state = none) :
    loopOrAccept.ViewStep finite next ↔ next = finite := by
  simp [MultiTapeNTM.ViewStep, h]

/-! ### Codes of views -/

/-- Malformed words decode to some configuration: the empty word to one on the empty input. -/
example : (decodeFiniteCfg (k := 0) (State := Bool) []).input = [] := rfl

/-- A malformed stack tape ending in blank cells decodes to the canonical tape without them. -/
example : (decodeStackTape (encList (encOption encBool) [some true, none, none])).toList =
    [some true] := by
  rw [decodeStackTape_encList]
  rfl

example : (decodeFiniteCfg (k := 0) (State := Bool)
    (encFiniteCfg (stuck.initView [true, false]))).input = [true, false] := by
  rw [decodeFiniteCfg_encFiniteCfg]
  rfl

/-- The accepting code is no view's code. -/
example : MultiTapeNTM.decodeView (k := 0) (State := Bool) (MultiTapeNTM.acceptCode 3) = none :=
  rfl

/-- The width bounding every reachable view of the looping machine on the empty input. -/
private noncomputable abbrev loopWidth : ℕ :=
  (10 + 2 * Nat.card (Option Bool) + 200 * 0) * (0 + 0 + 1)

/-- Acceptance on the empty input reaches the accepting code from the initial code. -/
example : Relation.ReflTransGen (loopOrAccept.CodeStep loopWidth)
    (MultiTapeNTM.viewCode loopWidth (loopOrAccept.initView []))
    (MultiTapeNTM.acceptCode loopWidth) :=
  (MultiTapeNTM.accepts_iff_reflTransGen_codeStep fun _ h =>
    MultiTapeNTM.length_encFiniteCfg_le (MultiTapeNTM.runsInSpace_zero_tapes _ _ 0) h).mp
    (accepts_loopOrAccept [])

/-- The stuck machine never reaches the accepting code. -/
example : ¬Relation.ReflTransGen (stuck.CodeStep loopWidth)
    (MultiTapeNTM.viewCode loopWidth (stuck.initView [])) (MultiTapeNTM.acceptCode loopWidth) :=
  (MultiTapeNTM.accepts_iff_reflTransGen_codeStep fun _ h =>
    MultiTapeNTM.length_encFiniteCfg_le (MultiTapeNTM.runsInSpace_zero_tapes _ _ 0) h).not.mp
    (not_accepts_stuck [])

/-- The edge test is polynomial-time on pairs of words. -/
example : ComputableInPolyTime
    (fun p : List Bool × List Bool => loopOrAccept.codeEdge p.1 p.2) (encPair encBits encBits)
      encBool :=
  loopOrAccept.computableInPolyTime_codeEdge (by fun_prop) (by fun_prop)

/-! ### Savitch's theorem -/

/-- Nondeterministic polynomial-space membership transfers to deterministic polynomial-space
decidability (`NPSPACE = PSPACE`). -/
example {A : Set (List Bool)} (hA : A ∈ NPSPACE encBits) :
    ∃ t s, PolyBounded (fun a => (encBits a).length) s ∧ DecidableInTimeAndSpace A encBits t s :=
  mem_PSPACE_iff.mp (NPSPACE_eq_PSPACE (enc := encBits) ▸ hA)

/-- A machine with a forever-looping branch is decided deterministically: Savitch's theorem needs
no time bound, so the problem it recognizes, every word, is in `PSPACE`. -/
example : (Set.univ : Set (List Bool)) ∈ PSPACE encBits :=
  mem_PSPACE_of_recognizesInSpace (.const 0) recognizesInSpace_loopOrAccept

/-- Savitch's decider for the looping machine accepts every input, the branch running forever
notwithstanding. -/
example (input : List Bool) : loopOrAccept.savitchDecide 0 0 input = true :=
  (MultiTapeNTM.savitchDecide_eq_true_iff (MultiTapeNTM.runsInSpace_zero_tapes _ _ 0)
    (Nat.zero_le _)).mpr (accepts_loopOrAccept input)

/-- Savitch's decider for the stuck machine rejects, here the empty input. -/
example : stuck.savitchDecide 0 0 [] = false := by
  rw [Bool.eq_false_iff, Ne, MultiTapeNTM.savitchDecide_eq_true_iff
    (MultiTapeNTM.runsInSpace_zero_tapes _ _ 0) (Nat.zero_le _)]
  exact not_accepts_stuck []

/-- The decider of a fixed machine is an actual polynomial-space computation. -/
example : ∃ t s, PolyBounded (fun word : List Bool => (encBits word).length) s ∧
    ComputableInTimeAndSpace (fun word => loopOrAccept.savitchDecide 0 0 (encBits word))
      encBits encBool t s :=
  loopOrAccept.exists_polyBounded_space_savitchDecide encBits 0 0

end ComplexityTests.Space
