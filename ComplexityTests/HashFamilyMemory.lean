/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.HashFamily.Memory

/-!
# A random table over the memory oracle, on concrete parameters

A table of two one-bit cells at word size `8`. The tests evaluate a lookup on concrete memory,
check that the general theorems apply (room in empty memory, admissibility of every memory call,
the transcript law `evalOps`, call counts for a concrete operation list), and instantiate the
expected amortized certificate and the identical-until-bad step, so that none of their hypotheses
is vacuous here.
-/

@[expose] public section

namespace ComplexityTests.HashFamilyMemory

open Cslib Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.HashFamily
  Cslib.DataStructure.HashFamily.RandomTable

/-- Empty memory with nothing allocated. -/
def empty : Memory.State := ⟨fun _ => 0, 0⟩

/-- A table of two cells at address `0`, holding `0` and `1`. -/
def stored : Memory.State := ⟨fun a => if a = 1 then 1 else 0, 2⟩

/-- Looking up cell `1` answers the stored bit and leaves memory unchanged. -/
example : (Memory.spec 8).toRandomized.withCoins.run (methods ⟨0, 2⟩ 1 2 (.eval 1)) stored =
    PMF.pure (1, stored) := by
  rw [run_methods_eval]
  rfl

/-- Empty memory has room for the table at this word size. -/
theorem room : Fits 8 (empty.frontier + 2) := by decide

/-- An operation list: two lookups around a resample. -/
def ops : List (HashFamily.Op 2) := [.eval 0, .resample, .eval 0, .eval 1]

/-- Every memory call of the run is admissible. -/
example : (Memory.spec 8).toRandomized.withCoins.toSpec.DemonicValid empty
    (run 1 2 ((tableSpec 2 1).obliviousClient ops)) :=
  demonicValid_run (by omega) _ room

/-- The transcript law of the run from allocation is `evalOps` of the random function. -/
example : ((Memory.spec 8).toRandomized.withCoins.run
      (run 1 2 ((tableSpec 2 1).obliviousClient ops)) empty).map Prod.fst =
    evalOps (Probability.PMF.uniformOfFintype (Fin 2 → Fin (2 ^ 1))) (fun θ u => θ u) ops :=
  run_obliviousClient (w := 8) (by omega) ops empty

/-- The run makes at most `1 + 4 + 7 = 12` calls: one allocation, a fill of two cells, and the
operations, at one call per lookup and four per resample. -/
example : OracleComp.IsQueryBounded (run 1 2 ((tableSpec 2 1).obliviousClient ops)) 12 :=
  isQueryBounded_run ((tableSpec 2 1).isCostBounded_obliviousClient (budget 2) ops)

/-- The refinement and its expected amortized certificate exist on these parameters. -/
example : (refinement (w := 8) ⟨0, 2⟩ 1 rfl (by omega)).ExpectedAmortized (fun _ _ => 1)
    (fun _ o => budget 2 o) fun _ => 0 :=
  expectedAmortized rfl (by omega)

/-- The identical-until-bad step applies to the table: with no bad state, an experiment on the
real run accepts at most as often as on the specification. -/
example {β : Type} (next : List (Sigma (HashFamily.Result (U := 2) (2 ^ 1))) ×
      (Fin 2 → Fin (2 ^ 1)) → PMF β) (b : β) :
    let M := refinement (w := 8) ⟨0, 2⟩ 1 rfl (by omega)
    ((Memory.spec 8).toRandomized.withCoins.run
        (link M.methods ((tableSpec 2 1).obliviousClient ops)) ⟨empty.mem, 2⟩).bind
        (fun (a, e') => next (a, M.abs e')) b ≤
      ((tableSpec 2 1).run ((tableSpec 2 1).obliviousClient ops)
        (M.abs ⟨empty.mem, 2⟩)).bind next b +
      ((Memory.spec 8).toRandomized.withCoins.run
        (link M.methods ((tableSpec 2 1).obliviousClient ops)) ⟨empty.mem, 2⟩).toOuterMeasure
        ∅ := by
  intro M
  exact M.bind_apply_le_of_identicalUntilBad M.methods (bad := fun _ => False)
    ⟨fun _ _ _ _ _ _ => rfl, fun _ _ h => h.elim, fun _ _ h => h.elim⟩ _ le_rfl
    ((tableSpec 2 1).toSpec.demonicValid_of_forall_valid (fun _ _ => trivial) _ _) next b

end ComplexityTests.HashFamilyMemory
