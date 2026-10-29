/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Space.Savitch

/-! Space-bounded machines at the boundaries of the polynomial-space development: output written
twice is not acceptance, a work tape that is actually written is within its space bound, a head
running right forever is within no space bound, and malformed codes have no edges. -/

namespace ComplexityTests.SpaceMachines

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Turing.MultiTapeNTM

/-! ### Output written twice -/

/-- Write `true` to the output, then halt or move on. -/
private def emitAction (halt : Bool) : Action 0 Bool Bool :=
  { inputTape := 0, workTapes := Fin.elim0, output := some true,
    state := if halt then none else some true }

/-- Write `true` to the output twice, then halt. -/
private def twiceTrue : MultiTapeNTM 0 Bool Bool where
  q₀ := false
  Tr q _ _ action := action = emitAction q

/-- The reachable views of `twiceTrue`: before any output, after one `true`, or halted with output
summarized as `[false]`. -/
private theorem twiceTrue_reachable {input : List Bool} {finite : FiniteCfg 0 Bool Bool}
    (h : Relation.ReflTransGen twiceTrue.ViewStep (twiceTrue.initView input) finite) :
    (finite.state = some false ∧ finite.output = []) ∨
      (finite.state = some true ∧ finite.output = [true]) ∨
      (finite.state = none ∧ finite.output = [false]) := by
  induction h with
  | refl => exact .inl ⟨rfl, rfl⟩
  | @tail view next _ hstep ih =>
    rcases ih with ⟨hs, ho⟩ | ⟨hs, ho⟩ | ⟨hs, ho⟩
    · simp only [ViewStep, hs] at hstep
      obtain ⟨action, rfl, rfl⟩ := hstep
      exact .inr (.inl ⟨rfl, by simp [FiniteCfg.summarizeOutput, FiniteCfg.step, emitAction, ho,
        outputClass]⟩)
    · simp only [ViewStep, hs] at hstep
      obtain ⟨action, rfl, rfl⟩ := hstep
      exact .inr (.inr ⟨rfl, by simp [FiniteCfg.summarizeOutput, FiniteCfg.step, emitAction, ho,
        outputClass]⟩)
    · simp only [ViewStep, hs] at hstep
      subst hstep
      exact .inr (.inr ⟨hs, ho⟩)

/-- Halting with output `[true, true]` is not acceptance. -/
private theorem not_accepts_twiceTrue (input : List Bool) : ¬twiceTrue.Accepts input := by
  rw [accepts_iff_reflTransGen_viewStep]
  rintro ⟨finite, hreach, hstate, hout⟩
  rcases twiceTrue_reachable hreach with ⟨hs, -⟩ | ⟨hs, -⟩ | ⟨-, ho⟩
  · simp [hs] at hstate
  · simp [hs] at hstate
  · simp [ho] at hout

/-- Savitch's decider rejects output written twice. -/
example (input : List Bool) : twiceTrue.savitchDecide 0 0 input = false := by
  rw [Bool.eq_false_iff, Ne, savitchDecide_eq_true_iff (runsInSpace_zero_tapes _ _ 0)
    (Nat.zero_le _)]
  exact not_accepts_twiceTrue input

/-! ### A written work tape -/

/-- Write `true` on the work tape and to the output without moving, and halt. -/
private def writeAction : Action 1 Bool Unit :=
  { inputTape := 0, workTapes := fun _ => (some (some true), 0), output := some true,
    state := none }

/-- Write `true` on the work tape and to the output, and halt. -/
private def writeAccept : MultiTapeNTM 1 Bool Unit where
  q₀ := ()
  Tr _ _ _ action := action = writeAction

/-- Every computation path of `writeAccept` keeps its work head at `0`. -/
private theorem visitedByTapeHead_writeAccept {input : List Bool} (p : writeAccept.RunPath input)
    (hp : p.head = writeAccept.initCfg input) : p.visitedByTapeHead 0 ⊆ {0} := by
  induction p using RelSeries.inductionOn' with
  | singleton c =>
    simp only [RelSeries.head_singleton] at hp
    subst hp
    rw [RunPath.visitedByTapeHead_singleton]
    rfl
  | snoc p c hc ih =>
    have ih := ih (by simpa using hp)
    have hlast : p.last.workTapePos 0 = 0 := Finset.mem_singleton.mp
      (ih ((RunPath.mem_visitedByTapeHead _).mpr ⟨p.last, RelSeries.last_mem _, rfl⟩))
    have hc' : c.workTapePos 0 = 0 := by
      change writeAccept.Step p.last c at hc
      rcases hs : p.last.state with _ | _
      · rw [(MultiTapeNTM.step_of_halt hs).mp hc]
        exact hlast
      · simp only [Step, hs] at hc
        obtain ⟨action, rfl, rfl⟩ := hc
        simp [Action.apply, writeAction, hlast]
    rw [RunPath.visitedByTapeHead_snoc]
    exact Finset.insert_subset (by simp [hc']) ih

/-- Every computation path of `writeAccept` visits one work cell. -/
private theorem runsInSpace_writeAccept (input : List Bool) : writeAccept.RunsInSpace input 1 := by
  intro p
  have := Finset.card_le_card (visitedByTapeHead_writeAccept p.toRunPath p.head_eq)
  simpa [ComputationPath.space, RunPath.space, RunPath.spaceUsedByTape] using this

/-- `writeAccept` accepts in one step. -/
private theorem accepts_writeAccept (input : List Bool) : writeAccept.Accepts input := by
  have hstep : writeAccept.Step (writeAccept.initCfg input)
      (writeAction.apply (writeAccept.initCfg input)) := ⟨writeAction, rfl, rfl⟩
  refine ⟨⟨(RelSeries.singleton _ _).cons (writeAccept.initCfg input) hstep, rfl⟩, ?_, ?_⟩ <;>
    simp [writeAction]

/-- `writeAccept` halts after its first step. -/
private theorem runsInTime_writeAccept (input : List Bool) : writeAccept.RunsInTime input 1 :=
  MultiTapeNTM.runsInTime_one_of_forall_step_initCfg fun c hc => by
    simp only [Step, MultiTapeNTM.initCfg, Cfg.init] at hc
    obtain ⟨action, rfl, rfl⟩ := hc
    simp [Action.apply, writeAction]

/-- With a work tape that is actually written, the problem of all words is in `NPSPACE` within
one cell, and Savitch's decider accepts. -/
example (input : List Bool) :
    (Set.univ : Set (List Bool)) ∈ NPSPACE encBits ∧
    writeAccept.savitchDecide 1 0 input = true :=
  ⟨⟨1, Unit, inferInstance, writeAccept, fun _ => 1, .const 1, ⟨fun a =>
    ⟨runsInSpace_writeAccept a, by simpa using accepts_writeAccept a⟩,
    fun a => ⟨1, runsInTime_writeAccept a⟩⟩⟩,
    (savitchDecide_eq_true_iff (runsInSpace_writeAccept input) (by simp)).mpr
      (accepts_writeAccept input)⟩

/-! ### A head running right forever -/

/-- Move the work head right and stay in the same state. -/
private def rightAction : Action 1 Bool Unit :=
  { inputTape := 0, workTapes := fun _ => (none, 1), output := none, state := some () }

/-- Move the work head right forever. -/
private def runRight : MultiTapeNTM 1 Bool Unit where
  q₀ := ()
  Tr _ _ _ action := action = rightAction

/-- `runRight` has run paths of every length `n`, visiting the cells `0, …, n`. -/
private theorem exists_runRight_path (input : List Bool) (n : ℕ) :
    ∃ p : runRight.RunPath input, p.head = runRight.initCfg input ∧ p.last.state = some () ∧
      p.last.workTapePos 0 = n ∧ ∀ m ≤ n, (m : ℤ) ∈ p.visitedByTapeHead 0 := by
  induction n with
  | zero =>
    refine ⟨RelSeries.singleton _ _, rfl, rfl, rfl, fun m hm => ?_⟩
    obtain rfl : m = 0 := by omega
    rw [RunPath.visitedByTapeHead_singleton]
    simp
  | succ n ih =>
    obtain ⟨p, hhead, hstate, hpos, hvisited⟩ := ih
    have hstep : (p.last, rightAction.apply p.last) ∈ runRight.stepRel input := by
      change runRight.Step p.last _
      simp only [Step, hstate]
      exact ⟨rightAction, rfl, rfl⟩
    refine ⟨p.snoc _ hstep, by simpa using hhead, by simp [rightAction, Action.apply],
      by simp [rightAction, Action.apply, hpos], fun m hm => ?_⟩
    rw [RunPath.visitedByTapeHead_snoc]
    rcases Nat.lt_or_ge m (n + 1) with h | h
    · exact Finset.mem_insert_of_mem (hvisited m (by omega))
    · obtain rfl : m = n + 1 := by omega
      simp [rightAction, Action.apply, hpos]

/-- **No space bound holds** for a head running right forever: every bound is exceeded by a
prefix of its only branch. -/
example (input : List Bool) (s : ℕ) : ¬runRight.RunsInSpace input s := by
  intro hs
  obtain ⟨p, hhead, -, -, hvisited⟩ := exists_runRight_path input s
  have hsub : (Finset.range (s + 1)).image (fun m : ℕ => (m : ℤ)) ⊆ p.visitedByTapeHead 0 := by
    intro z hz
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
    exact hvisited m (by simpa [Nat.lt_succ_iff] using hm)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range] at hcard
  have := hs ⟨p, hhead⟩
  simp only [ComputationPath.space, RunPath.space, RunPath.spaceUsedByTape,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at this
  omega

/-! ### Malformed codes -/

/-- Neither the empty word nor a word with tag one (including the accepting code) has outgoing
edges. -/
example (code next : List Bool) :
    writeAccept.codeEdge [] next = false ∧
    writeAccept.codeEdge (true :: code) next = false :=
  ⟨rfl, rfl⟩

end ComplexityTests.SpaceMachines
