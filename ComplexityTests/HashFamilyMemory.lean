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
the transcript law `evalOps` and the `kWiseSpec` contract, call counts for a concrete operation
list), and instantiate the expected amortized certificate and the identical-until-bad step, so
that none of their hypotheses is vacuous here. A small upper hop with coins of its own is stacked
on the table with `compCoins`, and the stacked law and expected costs are instantiated.
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

/-- The operation list has at most two keys per epoch. -/
theorem bounded : BoundedEpochKeys 2 ops := by
  rw [BoundedEpochKeys]
  refine ⟨by decide, ?_⟩
  change BoundedEpochKeys 2 [.eval 0, .eval 1]
  rw [BoundedEpochKeys]
  exact ⟨by decide, trivial⟩

/-- The run from allocation meets the `kWiseSpec` contract on the operation list. -/
example : (kWiseSpec 2 2 (2 ^ 1)).Contract ops
    (((Memory.spec 8).toRandomized.withCoins.run
      (run 1 2 ((tableSpec 2 1).obliviousClient ops)) empty).map Prod.fst) :=
  kWiseSpec_contract_run (by omega) bounded empty

/-! ## A coin-using hop over a coin-using hop -/

/-- An upper hop with coins of its own: before each resample it draws a bit and ignores it. -/
noncomputable def wastefulMethods :
    Methods (tableSpec 2 1).toSpec (tableSpec 2 1).withCoins.toSpec
  | .resample => ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun _ =>
      ProbOracleComp.query (spec := HashFamily.Result (U := 2) (2 ^ 1)) .resample
  | .eval u => ProbOracleComp.query (spec := HashFamily.Result (U := 2) (2 ^ 1)) (.eval u)

/-- The wasteful hop refines the random function, since the ignored bit changes no law. -/
noncomputable def wasteful : RandomizedRefinement (tableSpec 2 1) (tableSpec 2 1).withCoins :=
  .ofLaw wastefulMethods (fun _ => True) id
    (fun _ _ _ => (tableSpec 2 1).withCoins.toSpec.demonicValid_of_forall_valid
      (fun _ o => by cases o <;> trivial) _ _)
    (fun _ _ _ _ _ _ => trivial)
    (fun {θ} o _ _ => by
      cases o with
      | resample =>
        have h : (tableSpec 2 1).withCoins.run (wastefulMethods .resample) θ =
            (tableSpec 2 1).law .resample θ := by
          rw [wastefulMethods, RandomizedSpec.run_bind, RandomizedSpec.withCoins_run_sample,
            PMF.bind_map]
          change ((ProbComp.unifFin 1).eval.bind fun _ => (tableSpec 2 1).withCoins.run
            (OracleComp.query (spec := probOracleSpec _)
              (.inr (.resample : HashFamily.Op 2))) θ) = _
          rw [PMF.bind_const, RandomizedSpec.run_query]
          rfl
        rw [h]
        exact PMF.map_id _
      | eval u =>
        rw [wastefulMethods]
        exact (congrArg (PMF.map _) (RandomizedSpec.run_query _ _ _)).trans (PMF.map_id _))

/-- The wasteful hop composed over the random table: one stream of coins over memory. -/
noncomputable def stacked :
    RandomizedRefinement (tableSpec 2 1) (Memory.spec 8).toRandomized.withCoins :=
  wasteful.compCoins (refinement ⟨0, 2⟩ 1 rfl (by omega))

/-- The law of a client through both coin-using hops is its law on the random function. -/
example : ((Memory.spec 8).toRandomized.withCoins.run
      (link stacked.methods ((tableSpec 2 1).obliviousClient ops)) ⟨empty.mem, 2⟩).map
        (fun (a, e') => (a, stacked.abs e')) =
    (tableSpec 2 1).run ((tableSpec 2 1).obliviousClient ops)
      (stacked.abs ⟨empty.mem, 2⟩) :=
  stacked.run_link _ ((RandomizedRefinement.compCoins_inv _ _ _).mpr ⟨le_rfl, trivial⟩)
    ((tableSpec 2 1).toSpec.demonicValid_of_forall_valid (fun _ _ => trivial) _ _)

/-- Expected costs stack across both hops: one unit per memory call or coin, against one more
unit per operation than the table's budget. -/
example : stacked.ExpectedAmortized (fun _ _ => 1) (fun _ o => budget 2 o + 1) fun _ => 0 := by
  have hlower : (tableSpec 2 1).coinCharge (fun _ => 1) (fun _ o => budget 2 o) =
      fun _ q => Sum.elim (fun _ => 1) (budget 2) q := by
    funext _ q
    cases q <;> rfl
  have A : wasteful.ExpectedAmortized (fun _ q => Sum.elim (fun _ => 1) (budget 2) q)
      (fun _ o => budget 2 o + 1) fun _ => 0 :=
    .of_isCostBounded fun o => by
      cases o with
      | resample =>
        exact OracleComp.IsCostBounded.liftBind_iff.mpr
          ⟨by decide, fun _ => (OracleComp.IsCostBounded.query _).mono (by decide)⟩
      | eval u => exact (OracleComp.IsCostBounded.query _).mono (Nat.le_succ _)
  rw [← hlower] at A
  have B := expectedAmortized (w := 8) (table := ⟨0, 2⟩) (b := 1) rfl (by omega)
  rw [← RandomizedSpec.coinCharge_const (D := (Memory.spec 8).toRandomized) 1] at B
  unfold stacked
  simpa using A.compCoins B

end ComplexityTests.HashFamilyMemory
