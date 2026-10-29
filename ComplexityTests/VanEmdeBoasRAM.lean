/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.VanEmdeBoas.Call
public import Complexity.Algorithms.Lean.VanEmdeBoas.Insert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
Native membership boundary, adversarial-memory and calling-convention regressions.
Fixture installation below is test-harness code, not a charged initializer. Generic correctness
comes from the execution theorems, not these finite evaluations.
-/

@[expose] public section

namespace ComplexityTests.VanEmdeBoasRAM

open Cslib
open Cslib.WordRAM
open Cslib.Algorithms.Lean.VanEmdeBoas
open Cslib.Algorithms.WordRAM.VanEmdeBoas

/-- The test tree represents exactly the three keys zero, one and three. -/
def fixtureTree : Tree 1 := (((Tree.empty 1).insert 0).insert 1).insert 3

/-- Concrete headers for the represented test tree. -/
def fixtureWords : List ℕ :=
  [1, 0, 3, 2, 5, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0]

-- A fake occupied leaf immediately beyond the tree would make the old unguarded program
-- report key 4 as present. All other unowned cells are deliberately nonzero/stale.
/-- The fixture's tree region, a hostile fake leaf, and nonzero unowned memory. -/
def poisonedMemory (a : ℕ) : ℕ :=
  if 8 ≤ a ∧ a < 28 then fixtureWords[a - 8]!
  else if a = 28 then 1 else if a ∈ [29, 30, 31, 32] then 0 else 173

/-- A fully fitting eight-bit caller with nonzero stale scratch registers. -/
def caller (query : ℕ) : Data 32 where
  regs i := if i = root then 8 else if i = arg then query else if i = tag then 1 else 173
  mem := poisonedMemory

/-- A concrete valid represented instance, including deliberately hostile outside memory. -/
theorem fixture_valid : fixtureTree.Valid := by
  unfold fixtureTree
  iterate 3 apply Tree.valid_insert (hx := by decide)
  exact Tree.valid_empty 1

/-- The recursive memory hypothesis is inhabited by the finite nonzero-background fixture. -/
theorem fixture_represented : Rep fixtureTree 8 poisonedMemory := by
  refine ⟨?_, ?_, ?_⟩
  · change Header 1 (some (0, 3)) 8 poisonedMemory
    unfold Header
    decide
  · change Header 0 (some (0, 1)) 13 poisonedMemory
    unfold Header
    decide
  · intro i
    fin_cases i <;> change Header 0 (some (1, 1)) _ poisonedMemory <;>
      unfold Header <;> decide

/-- The represented fixture satisfies the machine's global bounded-memory hypothesis. -/
theorem caller_bounded (query : ℕ) (hq : Fits 8 query) : (caller query).Bounded 8 := by
  constructor
  · intro i
    simp only [caller]
    split_ifs <;> first | exact hq | decide
  · intro a
    simp only [caller, poisonedMemory]
    split_ifs with htree
    · obtain ⟨hlo, hhi⟩ := htree
      interval_cases a <;> decide
    · decide
    · decide
    · decide

/-- The complete flat-call theorem applies to every fitting query on hostile outside memory. -/
theorem fixture_call (query : ℕ) (hq : Fits 8 query) :
    ∃ n ≤ 74, Executes 8 (program.program out) ⟨0, caller query⟩
      (if fixtureTree.member query then 1 else 0) n :=
  member_executes (caller_bounded query hq) fixture_valid fixture_represented
    (by decide) (by simp +decide [caller]) (by simp +decide [caller])
    (by simp +decide [caller])

private def structuredAnswer (query : ℕ) : Option (ℕ × ℕ) :=
  (program.eval 8 3 (caller query)).map fun yn => (yn.1.regs out, yn.2 + 1)

private def flatAnswer (query : ℕ) : Option (ℕ × ℕ) :=
  Cslib.WordRAM.run 8 (program.program out) 1024 ⟨0, caller query⟩

-- Every fitting query word, including all 252 queries outside the four-key universe.
private def queriesAgree (start : ℕ) : Bool :=
  (List.range 64).all (fun offset =>
    let query := start + offset
    (structuredAnswer query).map Prod.fst == some (if query ∈ [0, 1, 3] then 1 else 0)) =
    true

example :
    (queriesAgree 0 ∧ queriesAgree 64 ∧ queriesAgree 128 ∧ queriesAgree 192) ∧
    (flatAnswer 4 = structuredAnswer 4 ∧
      flatAnswer 255 = structuredAnswer 255 ∧
      flatAnswer 0 = structuredAnswer 0 ∧
      flatAnswer 1 = structuredAnswer 1 ∧
      flatAnswer 2 = structuredAnswer 2 ∧
      flatAnswer 3 = structuredAnswer 3) ∧
    (poisonedMemory 28 = 1 ∧ poisonedMemory 29 = 0 ∧ poisonedMemory 1000 = 173) := by
  decide

private def adaptiveAnswers : Option (List ℕ) := do
  let (a, _) ← program.eval 8 3 (caller 1)
  let q := if a.regs out = 1 then 4 else 0
  let (b, _) ← program.eval 8 3 (a.set arg q)
  let q' := if b.regs out = 0 then 3 else 2
  let (c, _) ← program.eval 8 3 (b.set arg q')
  pure [a.regs out, b.regs out, c.regs out]

-- Empty extrema may be stale even inside the represented interval.
private def staleEmptyMemory (a : ℕ) : ℕ :=
  if a ∈ [8, 13, 18, 23, 16, 17, 21, 22, 26, 27] then 0
  else if a = 11 then 2 else if a = 12 then 5 else 173

example :
    adaptiveAnswers = some [1, 0, 1] ∧
    Rep (Tree.empty 1) 8 staleEmptyMemory ∧
    ((program.eval 8 3 ⟨(caller 255).regs, staleEmptyMemory⟩).map
      (fun yn => yn.1.regs out)) = some 0 := by
  refine ⟨by decide, ⟨?_, ?_, ?_⟩, by decide⟩
  · change Header 1 none 8 staleEmptyMemory
    unfold Header
    decide
  · change Header 0 none 13 staleEmptyMemory
    unfold Header
    decide
  · intro i
    fin_cases i <;> change Header 0 none _ staleEmptyMemory <;> unfold Header <;> decide

/-- Initial state for depth-1 initialization at base 8 on hostile nonzero memory (`173`). -/
def initStart : Data 32 where
  regs i := if i = root then 8 else if i = depth then 1 else 173
  mem _ := 173

theorem initStart_bounded : initStart.Bounded 8 := by
  refine ⟨fun i => ?_, fun a => ?_⟩
  · simp only [initStart]
    split_ifs <;> decide
  · change Fits 8 173
    decide

/-- Non-vacuous instantiation of `init_executes` on hostile nonzero memory. -/
theorem fixture_init_executes :
    ∃ n ≤ 205, Executes 8 (initProgram.program out) ⟨0, initStart⟩ 28 n :=
  init_executes (base := 8) (d := 1) initStart_bounded (by decide) rfl rfl

private theorem bounded_set {x : Data 32} (hx : x.Bounded 8) (r : Fin 32) {v : ℕ}
    (hv : Fits 8 v) : (x.set r v).Bounded 8 := by
  refine ⟨fun i => ?_, hx.2⟩
  simp only [Data.set_regs, Function.update_apply]
  split_ifs
  · exact hv
  · exact hx.1 i

/-- Non-vacuous instantiation of `insert_executes` on the fixture tree. -/
theorem fixture_insert_executes :
    ∃ n ≤ 94, Executes 8 (program.program out)
      ⟨0, ((caller 2).set tag 0)⟩ 0 n :=
  insert_executes (key := 2)
    (bounded_set (caller_bounded 2 (by decide)) tag (by decide))
    fixture_valid fixture_represented (by decide) (by decide) rfl rfl rfl

/-- Non-vacuous instantiation of `successor_executes` on the fixture tree. -/
theorem fixture_successor_executes (query : ℕ) (hq : Fits 8 query) :
    ∃ (z : Data 32) (n : ℕ), n ≤ 152 ∧
      Executes 8 (program.program out)
        ⟨0, ((caller query).set stackBase 28).set tag 2⟩ (z.regs out) n ∧
      (if z.regs found = 0 then none else some (z.regs out)) =
        fixtureTree.successor query ∧
      Rep fixtureTree 8 z.mem ∧
      (∀ a, a < 28 ∨ 32 ≤ a → z.mem a = poisonedMemory a) :=
  successor_executes (d := 1) (w := 8) (base := 8) (stackBase₀ := 28) (query := query)
    (bounded_set (bounded_set (caller_bounded query hq) stackBase (by decide)) tag (by decide))
    fixture_valid fixture_represented (by decide) (by decide) rfl rfl rfl rfl

/-- Initial state for depth-0 initialization at base 8 on hostile nonzero memory (`173`). -/
private def initStart0 : Data 32 where
  regs i := if i = root then 8 else if i = depth then 0 else 173
  mem _ := 173

/-- Concrete evaluation of `initProgram` from nonzero memory (`173`) at depth `0`, checking that
`out = 13` (`base + span 0`), stale extrema (`mem 9`, `mem 10`) remain `173`, and memory outside
`[8, 17)` (`mem 7`, `mem 17`) remains `173`. -/
private def initZeroCheck : Option (ℕ × Bool) := do
  let (s0, _) ← initProgram.eval 8 10 initStart0
  let ok := s0.mem 8 == 0 && s0.mem 9 == 173 && s0.mem 10 == 173 &&
    s0.mem 11 == 0 && s0.mem 12 == 0 && s0.mem 7 == 173 && s0.mem 17 == 173
  pure (s0.regs out, ok)

/-- Concrete evaluation of native `insert 3` at depth `1` on `staleEmptyMemory` (with nonzero stale
extrema and `173` outside), checking that the root header becomes `(1, 3, 3)` and outside memory
remains `173`. -/
private def insertStaleCheck : Option Bool := do
  let s0 : Data 32 := ⟨(caller 0).regs, staleEmptyMemory⟩
  let (s1, _) ← program.eval 8 3 ((s0.set tag 0).set arg 3)
  pure (s1.mem 8 == 1 && s1.mem 9 == 3 && s1.mem 10 == 3 && s1.mem 7 == 173 && s1.mem 28 == 173)

/-- Native strict-successor query on the represented `fixtureTree` (`{0, 1, 3}`), covering
in-cluster successor (`0 ↦ some 1`), summary-backed cross-cluster successor (`1 ↦ some 3`),
gap successor (`2 ↦ some 3`), maximum (`3 ↦ none`), and out-of-universe query (`255 ↦ none`). -/
private def askFixtureSuccessor (q : ℕ) : Option (Option ℕ × Bool) := do
  let (r, _) ← program.eval 8 3 (((caller q).set stackBase 28).set tag 2)
  let ans := if r.regs found = 0 then none else some (r.regs out)
  pure (ans, r.mem 7 == 173 && r.mem 32 == 0)

example :
    initZeroCheck = some (13, true) ∧
    insertStaleCheck = some true ∧
    askFixtureSuccessor 0 = some (some 1, true) ∧
    askFixtureSuccessor 1 = some (some 3, true) ∧
    askFixtureSuccessor 2 = some (some 3, true) ∧
    askFixtureSuccessor 3 = some (none, true) ∧
    askFixtureSuccessor 255 = some (none, true) := by
  decide

/-- Adaptive client that inserts `1` and `3`, queries `successor 0`, and branches on the answer
before inserting a third key and querying `successor 1`. -/
def sampleAdaptiveClient : (spec 1 8).Client (Option ℕ) :=
  .liftBind (.insert 1) fun _ =>
    .liftBind (.insert 3) fun _ =>
      .liftBind (.successor 0) fun s0 =>
        let nextKey := match s0 with
          | some 1 => 2
          | _ => 0
        .liftBind (.insert nextKey) fun _ =>
          .liftBind (.successor 1) fun s1 =>
            .pure s1

/-- Non-vacuous instantiation of `run_initialized` combining `initProgram` with the adaptive
client `sampleAdaptiveClient` on hostile initial memory. -/
theorem sampleAdaptiveClient_run_initialized :
    ∃ x₀ n_init y traces,
      n_init + 1 ≤ 205 ∧
      Exec 8 initProgram initStart x₀ n_init ∧
      SetRep 1 8 28 8 (∅ : Finset ℕ) x₀ ∧
      Stateful.Executes ((dynamicProgram 1 8).ExecOp 8) sampleAdaptiveClient x₀
        ((spec 1 8).runClient (∅ : Finset ℕ) sampleAdaptiveClient).1 y traces ∧
      SetRep 1 8 28 8 ((spec 1 8).runClient (∅ : Finset ℕ) sampleAdaptiveClient).2.1 y ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces ≤
        ((spec 1 8).runClient (∅ : Finset ℕ) sampleAdaptiveClient).2.2.length * 152 ∧
      (∀ j, j < 8 ∨ 36 ≤ j → y.mem j = initStart.mem j) :=
  run_initialized (d := 1) (w := 8) (base := 8)
    initStart_bounded (by decide) rfl rfl sampleAdaptiveClient
    (by
      dsimp only [spec, Stateful.Spec.runClient, Stateful.Spec.ValidHistory,
        sampleAdaptiveClient, OrderedSet.least]
      refine ⟨by decide, by decide, ?_, by decide, ?_, trivial⟩
      · change 0 < 2 ^ 8; decide
      · change 1 < 2 ^ 8; decide)

end ComplexityTests.VanEmdeBoasRAM
