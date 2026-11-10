/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Nondeterministic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Space

/-!
# Descriptions of nondeterministic machines

A machine without work tapes that emits either bit and halts. Its description lists both
transitions, so from the initial configuration it can step to either output; a halted
configuration takes no step; and the machine accepts every input, read off its description, also
within the space bound for no cells.

A machine with one work tape that marks its first cell and accepts runs within one cell, and its
description accepts within the space bound for one work tape and one cell.
-/

@[expose] public section

namespace CslibFrontierTests.UniversalNondeterministic

open Turing Turing.MultiTapeTM.Universal

/-- Emit either bit and halt. -/
def coin : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ a := ∃ b, a = ⟨0, Fin.elim0, some b, none⟩

/-- The single state, as a number. -/
def eUnit : Unit ↪ ℕ := ⟨fun _ => 0, fun _ _ _ => rfl⟩

/-- From the initial configuration, the description of `coin` can emit either bit and halt. -/
theorem nStep_init (input : List Bool) (b : Bool) :
    NStep (descN eUnit eBit coin) (input.map eBit) (init (descN eUnit eBit coin), [])
      (⟨none, 1, []⟩, [eBit b]) := by
  refine ⟨eUnit (), by simp [init], _, (mem_descN eUnit eBit coin).mpr
    ⟨(), input.head?, Fin.elim0, ⟨0, Fin.elim0, some b, none⟩, ⟨b, rfl⟩, rfl⟩, ?_, ?_⟩
  · simp [init, key, SCfg.key, inputSymbol, List.head?_map]
  · simp only [init, descN_tapes, descN_q₀, List.replicate_zero]
    rfl

/-- A halted configuration takes no step. -/
example (x : List ℕ) (o : List ℕ) (p : SCfg × List ℕ) :
    ¬NStep (descN eUnit eBit coin) x (⟨none, 1, []⟩, o) p := by
  rintro ⟨q, hq, -⟩
  cases hq

/-- Both outputs are reachable. -/
example (input : List Bool) (b : Bool) :
    Relation.ReflTransGen (NStep (descN eUnit eBit coin) (input.map eBit))
      (init (descN eUnit eBit coin), []) (⟨none, 1, []⟩, [eBit b]) :=
  .single (nStep_init input b)

/-- `coin` accepts every input, read off its description. -/
theorem coin_accepts (input : List Bool) : coin.Accepts input :=
  (accepts_iff_reflTransGen_nStep eUnit coin input).mpr ⟨_, rfl, .single (nStep_init input true)⟩

/-- Without work tapes `coin` runs within no cells, so its description accepts within the bound
for `S = 0`. -/
example (input : List Bool) :
    ∃ s, s.state = none ∧
      Relation.ReflTransGen (fun p p' => NStep (descN eUnit eBit coin) (input.map eBit) p p' ∧
          (eCfg p'.1).length ≤ cfgSpaceBound (descLen (descN eUnit eBit coin)) input.length 0 0)
        (init (descN eUnit eBit coin), []) (s, [eBit true]) :=
  (accepts_iff_reflTransGen_nStep_fits eUnit coin input (by simp)).mp (coin_accepts input)

/-! ### A written work tape -/

/-- Write `true` on the work tape and to the output without moving, and halt. -/
def markAction : Action 1 Bool Unit :=
  { inputTape := 0, workTapes := fun _ => (some (some true), 0), output := some true,
    state := none }

/-- A machine with one work tape that marks its first cell and accepts. -/
def mark : MultiTapeNTM 1 Bool Unit where
  q₀ := ()
  Tr _ _ _ a := a = markAction

/-- Every computation path of `mark` keeps its work head at `0`. -/
theorem visitedByTapeHead_mark {input : List Bool} (p : mark.RunPath input)
    (hp : p.head = mark.initCfg input) : p.visitedByTapeHead 0 ⊆ {0} := by
  induction p using RelSeries.inductionOn' with
  | singleton c =>
    simp only [RelSeries.head_singleton] at hp
    subst hp
    rw [MultiTapeNTM.RunPath.visitedByTapeHead_singleton]
    rfl
  | snoc p c hc ih =>
    have ih := ih (by simpa using hp)
    have hlast : p.last.workTapePos 0 = 0 := Finset.mem_singleton.mp
      (ih ((MultiTapeNTM.RunPath.mem_visitedByTapeHead _).mpr ⟨p.last, RelSeries.last_mem _, rfl⟩))
    have hc' : c.workTapePos 0 = 0 := by
      change mark.Step p.last c at hc
      rcases hs : p.last.state with _ | _
      · rw [(MultiTapeNTM.step_of_halt hs).mp hc]
        exact hlast
      · simp only [MultiTapeNTM.Step, hs] at hc
        obtain ⟨a, rfl, rfl⟩ := hc
        simp [Action.apply, markAction, hlast]
    rw [MultiTapeNTM.RunPath.visitedByTapeHead_snoc]
    exact Finset.insert_subset (by simp [hc']) ih

/-- `mark` runs within one cell. -/
theorem runsInSpace_mark (input : List Bool) : mark.RunsInSpace input 1 := by
  intro p
  have := Finset.card_le_card (visitedByTapeHead_mark p.toRunPath p.head_eq)
  simpa [MultiTapeNTM.ComputationPath.space, MultiTapeNTM.RunPath.space,
    MultiTapeNTM.RunPath.spaceUsedByTape] using this

/-- `mark` accepts in one step. -/
theorem mark_accepts (input : List Bool) : mark.Accepts input := by
  have hstep : mark.Step (mark.initCfg input) (markAction.apply (mark.initCfg input)) :=
    ⟨markAction, rfl, rfl⟩
  refine ⟨⟨(RelSeries.singleton _ _).cons (mark.initCfg input) hstep, rfl⟩, ?_, ?_⟩ <;>
    simp [markAction]

/-- The description of `mark` accepts within the bound for one work tape and one cell, so the
covering invariant is used on a written cell. -/
example (input : List Bool) :
    ∃ s, s.state = none ∧
      Relation.ReflTransGen (fun p p' => NStep (descN eUnit eBit mark) (input.map eBit) p p' ∧
          (eCfg p'.1).length ≤ cfgSpaceBound (descLen (descN eUnit eBit mark)) input.length 1 1)
        (init (descN eUnit eBit mark), []) (s, [eBit true]) :=
  (accepts_iff_reflTransGen_nStep_fits eUnit mark input (runsInSpace_mark input)).mp
    (mark_accepts input)

end CslibFrontierTests.UniversalNondeterministic
