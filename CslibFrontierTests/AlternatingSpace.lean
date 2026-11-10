/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.Alternation.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Marking

/-!
# Tests: alternating space, `APSPACE ⊆ EXP` and `AL ⊆ P`

A one-state machine that emits its move and halts decides `Set.univ` (existential) and `∅`
(universal) within space `0`, so both are in `AL`, `APSPACE`, `P` and `EXP` through the explicit
machines and the inclusions. A variant with one work tape, which writes a cell before halting,
exercises a nonzero space bound. A one-state machine whose move `false` loops and whose move `true`
halts with output `[true]` separates the least fixed point from the greatest. Existential, it
accepts every input. Universal, every finite strategy fails, because the move `false` never halts,
so it accepts no input: it recognizes `∅` within space `0` but decides nothing, since it has an
infinite branch. The recognizer theorems still put `∅` in `P` and `EXP`, and marking its views
rejects, while marking the existential machine's views accepts.
-/

namespace CslibFrontierTests.AlternatingSpace

open Cslib Cslib.Complexity Turing
open Turing.MultiTapeTM (encBits PolyBounded)

/-! ### A machine emitting its move -/

/-- The machine with one state that emits its move and halts; its state is universal when `u`
is `true`. -/
private def emitMove (u : Bool) : MultiTapeATM 0 Bool Unit where
  toPTM :=
    { initial := ()
      tr := fun _ _ _ _ b => .step ⟨0, Fin.elim0, some b, none⟩ Empty.elim Empty.elim }
  universal _ := u

/-- The move `b` halts with output `[b]`. -/
private theorem next_emitMove (u b : Bool) (input : List Bool) :
    ((emitMove u).next b ((emitMove u).toPTM.toNTM.initCfg input)).state = none ∧
      ((emitMove u).next b ((emitMove u).toPTM.toNTM.initCfg input)).output = [b] := by
  rw [MultiTapeATM.next_of_state _ (q := ()) rfl]
  exact ⟨rfl, rfl⟩

/-- Every list of one move halts. -/
private theorem runsInTime_emitMove (u : Bool) (input : List Bool) :
    (emitMove u).toPTM.toNTM.RunsInTime input 1 := by
  refine MultiTapeATM.runsInTime_iff_stepCoins.mpr fun coins hlen => ?_
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hlen
  exact (next_emitMove u b input).1

/-- The existential machine decides `Set.univ` within one step. -/
private theorem decidesInTime_univ :
    (emitMove false).DecidesInTime encBits Set.univ fun _ => 1 := fun a =>
  ⟨runsInTime_emitMove false a, iff_of_true trivial
    ⟨1, ((emitMove false).acceptsWithin_succ_of_existential (q := ()) rfl rfl).mpr
      ⟨true, (next_emitMove false true a).1, (next_emitMove false true a).2⟩⟩⟩

/-- The universal machine decides `∅` within one step. -/
private theorem decidesInTime_empty :
    (emitMove true).DecidesInTime encBits ∅ fun _ => 1 := fun a => by
  refine ⟨runsInTime_emitMove true a, iff_of_false (Set.notMem_empty a) ?_⟩
  rw [MultiTapeATM.accepts_iff_acceptsWithin (runsInTime_emitMove true (encBits a)),
    (emitMove true).acceptsWithin_succ_of_universal (q := ()) rfl rfl]
  intro h
  have := (h false).2
  rw [(next_emitMove true false (encBits a)).2] at this
  simp at this

/-- The existential machine decides `Set.univ` within logarithmic space with constant `0`. -/
private theorem decidesInSpace_univ :
    (emitMove false).DecidesInSpace encBits Set.univ
      fun a => 0 * (Nat.log2 (encBits a).length + 1) :=
  decidesInTime_univ.decidesInSpace.mono fun _ => by simp

/-- The universal machine decides `∅` within logarithmic space with constant `0`. -/
private theorem decidesInSpace_empty :
    (emitMove true).DecidesInSpace encBits ∅ fun a => 0 * (Nat.log2 (encBits a).length + 1) :=
  decidesInTime_empty.decidesInSpace.mono fun _ => by simp

/-- `Set.univ` and `∅` are in `AL` by explicit machines, hence in `APSPACE`, `P` and `EXP`. -/
example :
    (Set.univ : Set (List Bool)) ∈ AL encBits ∧ (∅ : Set (List Bool)) ∈ AL encBits ∧
    (Set.univ : Set (List Bool)) ∈ APSPACE encBits ∧ (∅ : Set (List Bool)) ∈ P encBits ∧
    (Set.univ : Set (List Bool)) ∈ EXP encBits :=
  have huniv : (Set.univ : Set (List Bool)) ∈ AL encBits :=
    ⟨0, Unit, inferInstance, emitMove false, 0, decidesInSpace_univ⟩
  have hempty : (∅ : Set (List Bool)) ∈ AL encBits :=
    ⟨0, Unit, inferInstance, emitMove true, 0, decidesInSpace_empty⟩
  ⟨huniv, hempty, AL_subset_APSPACE huniv, AL_subset_P hempty,
    APSPACE_subset_EXP (AL_subset_APSPACE huniv)⟩

/-- `AP ⊆ APSPACE` on an explicit machine and time bound. -/
example : (Set.univ : Set (List Bool)) ∈ APSPACE encBits :=
  AP_subset_APSPACE ⟨_, PolyBounded.const 1, 0, Unit, inferInstance, emitMove false,
    decidesInTime_univ⟩

/-! ### A machine with one work tape -/

/-- The existential machine with one state and one work tape that writes `true` on its work tape,
moves its work head right, emits its move and halts. -/
private def writeEmit : MultiTapeATM 1 Bool Unit where
  toPTM :=
    { initial := ()
      tr := fun _ _ _ _ b =>
        .step ⟨0, fun _ => (some (some true), 1), some b, none⟩ Empty.elim Empty.elim }
  universal _ := false

/-- The move `b` halts with output `[b]`. -/
private theorem next_writeEmit (b : Bool) (input : List Bool) :
    (writeEmit.next b (writeEmit.toPTM.toNTM.initCfg input)).state = none ∧
      (writeEmit.next b (writeEmit.toPTM.toNTM.initCfg input)).output = [b] := by
  rw [MultiTapeATM.next_of_state _ (q := ()) rfl]
  exact ⟨rfl, rfl⟩

/-- The machine decides `Set.univ` within one step. -/
private theorem decidesInTime_writeEmit :
    writeEmit.DecidesInTime encBits Set.univ fun _ => 1 := fun a => by
  refine ⟨MultiTapeATM.runsInTime_iff_stepCoins.mpr fun coins hlen => ?_, iff_of_true trivial
    ⟨1, (writeEmit.acceptsWithin_succ_of_existential (q := ()) rfl rfl).mpr
      ⟨true, (next_writeEmit true a).1, (next_writeEmit true a).2⟩⟩⟩
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hlen
  exact (next_writeEmit b a).1

/-- With one work tape the space bound is not trivial: one step gives space `1 * (1 + 1)`, which is
within `2 * (log₂ n + 1)`, so `Set.univ ∈ AL` through this machine, and in `APSPACE` through the
constant bound. -/
example : (Set.univ : Set (List Bool)) ∈ AL encBits ∧
    (Set.univ : Set (List Bool)) ∈ APSPACE encBits :=
  ⟨⟨1, Unit, inferInstance, writeEmit, 2,
      decidesInTime_writeEmit.decidesInSpace.mono fun _ => by omega⟩,
    ⟨1, Unit, inferInstance, writeEmit, _, PolyBounded.const _,
      decidesInTime_writeEmit.decidesInSpace⟩⟩

/-- `AL` is `ASPACE (log₂ n)` and `APSPACE` the union of the classes `ASPACE (n ^ k)`: the
universal logspace decider gives `∅ ∈ ASPACE log₂`, and the one-tape machine, within space `2`,
gives `Set.univ ∈ ASPACE (n ^ 0)`, hence `Set.univ ∈ APSPACE`. -/
example : (∅ : Set (List Bool)) ∈ ASPACE encBits Nat.log2 ∧
    (Set.univ : Set (List Bool)) ∈ ASPACE encBits (· ^ 0) ∧
    (Set.univ : Set (List Bool)) ∈ APSPACE encBits := by
  have hempty : (∅ : Set (List Bool)) ∈ AL encBits :=
    ⟨0, Unit, inferInstance, emitMove true, 0, decidesInSpace_empty⟩
  have huniv : (Set.univ : Set (List Bool)) ∈ ASPACE encBits (· ^ 0) :=
    ⟨1, Unit, inferInstance, writeEmit, 2, 0,
      decidesInTime_writeEmit.decidesInSpace.mono fun _ => by simp⟩
  rw [← AL_eq_ASPACE]
  exact ⟨hempty, huniv, mem_APSPACE_iff_exists_mem_ASPACE.mpr ⟨0, huniv⟩⟩

/-! ### A machine whose move `false` loops -/

/-- The machine with one state whose move `false` loops back to it and whose move `true` halts
with output `[true]`; its state is universal when `u` is `true`. -/
private def loopOrAccept (u : Bool) : MultiTapeATM 0 Bool Unit where
  toPTM :=
    { initial := ()
      tr := fun _ _ _ _ b =>
        .step ⟨0, Fin.elim0, if b then some true else none, if b then none else some ()⟩
          Empty.elim Empty.elim }
  universal _ := u

/-- The move `false` keeps the machine running. -/
private theorem state_next_false (u : Bool) {input : List Bool} {c : Cfg 0 Bool Unit input}
    (h : c.state = some ()) : ((loopOrAccept u).next false c).state = some () := by
  rw [MultiTapeATM.next_of_state _ h]
  rfl

/-- The move `true` halts with output `[true]` from the initial configuration. -/
private theorem next_true (u : Bool) (input : List Bool) :
    ((loopOrAccept u).next true ((loopOrAccept u).toPTM.toNTM.initCfg input)).state = none ∧
      ((loopOrAccept u).next true ((loopOrAccept u).toPTM.toNTM.initCfg input)).output =
        [true] := by
  rw [MultiTapeATM.next_of_state _ (q := ()) rfl]
  exact ⟨rfl, rfl⟩

/-- Universal, no running configuration accepts within any number of moves: the move `false`
keeps it running. -/
private theorem not_acceptsWithin_loop {input : List Bool} (n : ℕ) {c : Cfg 0 Bool Unit input}
    (h : c.state = some ()) : ¬(loopOrAccept true).AcceptsWithin n c := by
  induction n generalizing c with
  | zero => exact MultiTapeATM.not_acceptsWithin_zero _ h
  | succ n ih =>
    rw [(loopOrAccept true).acceptsWithin_succ_of_universal h rfl]
    exact fun hall => ih (state_next_false true h) (hall false)

/-- Universal, the machine accepts no input: the least fixed point ignores the infinite branch of
moves `false`. -/
private theorem not_accepts_loop (input : List Bool) : ¬(loopOrAccept true).Accepts input :=
  fun ⟨n, h⟩ => not_acceptsWithin_loop n rfl h

/-- Existential, the machine accepts every input by the move `true`. -/
private theorem accepts_loop (input : List Bool) : (loopOrAccept false).Accepts input :=
  ⟨1, ((loopOrAccept false).acceptsWithin_succ_of_existential (q := ()) rfl rfl).mpr
    ⟨true, (next_true false input).1, (next_true false input).2⟩⟩

/-- The universal machine recognizes `∅` within space `0`. -/
private theorem recognizesInSpace_empty :
    (loopOrAccept true).RecognizesInSpace encBits ∅
      fun a => 0 * (Nat.log2 (encBits a).length + 1) := fun a =>
  ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _,
    iff_of_false (Set.notMem_empty a) (not_accepts_loop _)⟩

/-- The existential machine recognizes `Set.univ` within space `0`. -/
private theorem recognizesInSpace_univ :
    (loopOrAccept false).RecognizesInSpace encBits Set.univ fun _ => 0 := fun _ =>
  ⟨MultiTapeNTM.runsInSpace_zero_tapes _ _ _, iff_of_true trivial (accepts_loop _)⟩

/-- The list of `n` moves `false` keeps the machine running. -/
private theorem state_stepCoins_false (u : Bool) (input : List Bool) (n : ℕ) :
    ((loopOrAccept u).toPTM.stepCoins (List.replicate n false)
      ((loopOrAccept u).toPTM.toNTM.initCfg input)).state = some () := by
  suffices ∀ (n : ℕ) (c : Cfg 0 Bool Unit input), c.state = some () →
      ((loopOrAccept u).toPTM.stepCoins (List.replicate n false) c).state = some () from
    this n _ rfl
  intro n
  induction n with
  | zero => exact fun _ h => h
  | succ n ih =>
    intro c h
    rw [List.replicate_succ, MultiTapeATM.stepCoins_cons]
    exact ih _ (state_next_false u h)

/-- The machine has an infinite branch, so it decides nothing: no number of steps bounds its
computation paths, although it recognizes `∅` within space `0`. -/
example (s : List Bool → ℕ) (A : Set (List Bool)) :
    ¬(loopOrAccept true).DecidesInSpace encBits A s := by
  rintro ⟨-, h⟩
  obtain ⟨t, ht⟩ := h []
  have := MultiTapeATM.runsInTime_iff_stepCoins.mp ht (List.replicate t false)
    (List.length_replicate ..)
  rw [state_stepCoins_false] at this
  exact Option.some_ne_none _ this

/-- The recognizer theorems apply to machines with infinite branches. -/
example : (∅ : Set (List Bool)) ∈ P encBits ∧ (Set.univ : Set (List Bool)) ∈ EXP encBits :=
  ⟨recognizesInSpace_empty.mem_P, recognizesInSpace_univ.mem_EXP (PolyBounded.const 0)⟩

/-! ### Marking -/

/-- Marking the views of the universal machine rejects: the infinite branch of moves `false` is
never marked. -/
example (input : List Bool) :
    (loopOrAccept true).boundedAccepts input
      (2 ^ (2 * MultiTapeNTM.coreLengthBound 0 Unit input.length 0 + 1)) = false := by
  rw [← Bool.not_eq_true, MultiTapeATM.boundedAccepts_iff
    (MultiTapeNTM.runsInSpace_zero_tapes _ _ _) le_rfl]
  exact not_accepts_loop input

/-- Marking the views of the existential machine accepts. -/
example (input : List Bool) :
    (loopOrAccept false).boundedAccepts input
      (2 ^ (2 * MultiTapeNTM.coreLengthBound 0 Unit input.length 0 + 1)) = true :=
  (MultiTapeATM.boundedAccepts_iff (MultiTapeNTM.runsInSpace_zero_tapes _ _ _) le_rfl).mpr
    (accepts_loop input)

end CslibFrontierTests.AlternatingSpace
