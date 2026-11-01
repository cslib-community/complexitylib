/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.HashFamily.Randomized
public import Complexity.DataStructure.Memory.Field
import Complexity.Probability.Product

/-!
# A random table over the memory oracle

A uniformly random function `Fin U → Fin (2 ^ b)` is the simplest resamplable hash family: its
seed is the whole table. Here it is stored in a field array `table` of `U` cells, behind the
memory oracle with private coins, `(Memory.spec w).toRandomized.withCoins`. `resample` refills the
table with one uniform `b`-bit draw and one write per cell (`fill`), and `eval u` reads cell `u`.

The abstraction function reads the table as a function (`tableOf`). The implementation is a
`RandomizedRefinement` of the seed-level specification `tableSpec U b` (`refinement`): the only
probabilistic fact is that independent uniform draws fill a uniform table (`run_fill`,
`tableOf_writeFrom`). The generic hop then gives the law of every adaptive client, and the run
from allocation (`run`) has the transcript law `HashFamily.evalOps` on every operation list
(`run_obliviousClient`). This is the memory-level counterpart of
`HashFamily.WordRAM.Impl.evalOps_execSteps`, with no register, instruction count or `ExecSteps`
bookkeeping. Every operation makes at most `2 * U` calls, and `eval` exactly one
(`isCostBounded_methods`, `expectedAmortized`, `isQueryBounded_run`).

## Main definitions

* `Cslib.DataStructure.HashFamily.RandomTable.tableSpec`: the random function as a seed-level
  specification.
* `Cslib.DataStructure.HashFamily.RandomTable.fill`, `methods`: the operations over memory with
  coins.
* `Cslib.DataStructure.HashFamily.RandomTable.tableOf`, `writeFrom`: the abstraction function, and
  the memory after a fill.
* `Cslib.DataStructure.HashFamily.RandomTable.refinement`: the distributional refinement.
* `Cslib.DataStructure.HashFamily.RandomTable.run`: allocate, fill, then serve a client.

## Main results

* `Cslib.DataStructure.HashFamily.RandomTable.run_fill`: a fill writes a uniform table.
* `Cslib.DataStructure.HashFamily.RandomTable.run_eq`: the law of a client run from allocation.
* `Cslib.DataStructure.HashFamily.RandomTable.run_obliviousClient`: its oblivious transcripts are
  `evalOps`.
* `Cslib.DataStructure.HashFamily.RandomTable.demonicValid_run`: every memory call is admissible.
* `Cslib.DataStructure.HashFamily.RandomTable.expectedAmortized`,
  `Cslib.DataStructure.HashFamily.RandomTable.isQueryBounded_run`: call counts.

## References

* [J. L. Carter, M. N. Wegman, *Universal classes of hash functions*][CarterWegman1979]
-/

@[expose] public section

namespace Cslib.DataStructure.HashFamily.RandomTable

open Cslib.WordRAM Cslib.DataStructure

/-- The uniformly random function `Fin U → Fin (2 ^ b)` as a resamplable hash family. -/
noncomputable abbrev tableSpec (U b : ℕ) : RandomizedSpec :=
  seedSpec (Probability.PMF.uniformOfFintype (Fin U → Fin (2 ^ b))) fun θ u => θ u

variable (table : Block) (b : ℕ)

/-- The table stored in the field `table`: cell `u` read as a `b`-bit word. -/
def tableOf (U : ℕ) (s : Memory.State) : Fin U → Fin (2 ^ b) :=
  fun u => Fin.ofNat (2 ^ b) (s.mem (table.base + u))

/-- Fill cells `i, …, i + n - 1` of the table with independent uniform `b`-bit words, one draw and
one write per cell. -/
noncomputable def fill : ℕ → ℕ → ProbOracleComp Memory.Op.Result Unit
  | _, 0 => pure ()
  | i, n + 1 => do
    let x ← ProbOracleComp.sample (ProbComp.uniform (Fin (2 ^ b)))
    OracleComp.liftRight (table.set i x.val)
    fill (i + 1) n

/-- The operations: `resample` refills the table, and `eval u` reads cell `u`. -/
noncomputable def methods (U : ℕ) :
    (o : HashFamily.Op U) → ProbOracleComp Memory.Op.Result (HashFamily.Result (2 ^ b) o)
  | .resample => fill table b 0 U
  | .eval u => OracleComp.liftRight (Fin.ofNat (2 ^ b) <$> table.get u)

/-- The memory after writing `θ j` to cell `i + j` of the table for each `j < n`, in order. -/
def writeFrom : (i n : ℕ) → (Fin n → Fin (2 ^ b)) → Memory.State → Memory.State
  | _, 0, _, s => s
  | i, n + 1, θ, s =>
    writeFrom (i + 1) n (Fin.tail θ) ⟨Function.update s.mem (table.base + i) (θ 0), s.frontier⟩

/-! ## The memory after a fill -/

variable {table b}

@[simp] theorem frontier_writeFrom (i n : ℕ) (θ : Fin n → Fin (2 ^ b)) (s : Memory.State) :
    (writeFrom table b i n θ s).frontier = s.frontier := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih => exact ih _ _ _

/-- Cells below the first written cell are unchanged. -/
theorem mem_writeFrom_of_lt (i n : ℕ) (θ : Fin n → Fin (2 ^ b)) (s : Memory.State) {a : ℕ}
    (ha : a < table.base + i) : (writeFrom table b i n θ s).mem a = s.mem a := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih =>
    rw [writeFrom, ih _ _ _ (by omega)]
    exact Function.update_of_ne (by omega) _ _

/-- Cell `i + j` holds the `j`-th written word. -/
theorem mem_writeFrom (i n : ℕ) (θ : Fin n → Fin (2 ^ b)) (s : Memory.State) (j : Fin n) :
    (writeFrom table b i n θ s).mem (table.base + (i + j)) = θ j := by
  induction n generalizing i s with
  | zero => exact j.elim0
  | succ n ih =>
    rw [writeFrom]
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [mem_writeFrom_of_lt _ _ _ _ (by simp)]
      simp
    · rw [show table.base + (i + (j.succ : ℕ)) = table.base + (i + 1 + j) by simp; omega, ih]
      rfl

/-- A full fill stores the written table. -/
theorem tableOf_writeFrom {U : ℕ} (θ : Fin U → Fin (2 ^ b)) (s : Memory.State) :
    tableOf table b U (writeFrom table b 0 U θ s) = θ := by
  funext u
  have h := mem_writeFrom (table := table) 0 U θ s u
  rw [Nat.zero_add] at h
  simp [tableOf, h]

/-! ## Evaluation -/

variable {w : ℕ}

/-- **A fill writes a uniform table.** -/
theorem run_fill (i n : ℕ) (s : Memory.State) :
    ((Memory.spec w).toRandomized.withCoins.run (fill table b i n) s).map Prod.snd =
      (Probability.PMF.uniformOfFintype (Fin n → Fin (2 ^ b))).map fun θ =>
        writeFrom table b i n θ s := by
  induction n generalizing i s with
  | zero =>
    change (PMF.pure ((), s)).map Prod.snd = _
    rw [PMF.pure_map]
    exact (PMF.map_const _ _).symm
  | succ n ih =>
    change ((Memory.spec w).toRandomized.withCoins.run
      (ProbOracleComp.sample (ProbComp.uniform (Fin (2 ^ b))) >>= fun x =>
        OracleComp.liftRight (table.set i x.val) >>= fun _ => fill table b (i + 1) n) s).map
          Prod.snd = _
    rw [RandomizedSpec.run_bind, RandomizedSpec.withCoins_run_sample, ProbComp.eval_uniform,
      PMF.bind_map, PMF.map_bind,
      ← Probability.PMF.pi_uniformOfFintype (α := fun _ : Fin (n + 1) => Fin (2 ^ b)),
      Probability.PMF.pi_fin_succ, Probability.PMF.pi_uniformOfFintype, PMF.map_bind]
    refine congrArg (Probability.PMF.uniformOfFintype (Fin (2 ^ b))).bind (funext fun x => ?_)
    rw [Function.comp_apply]
    dsimp only
    rw [RandomizedSpec.run_bind, RandomizedSpec.withCoins_run_liftRight,
      StateTransitionSpec.run_toRandomized, PMF.pure_bind, ih, PMF.map_comp]
    rfl

/-- Reading a cell answers the stored word and leaves memory unchanged. -/
theorem run_methods_eval {U : ℕ} (u : Fin U) (s : Memory.State) :
    (Memory.spec w).toRandomized.withCoins.run (methods table b U (.eval u)) s =
      PMF.pure (tableOf table b U s u, s) := by
  rw [methods, RandomizedSpec.withCoins_run_liftRight, StateTransitionSpec.run_toRandomized]
  rfl

/-! ## Admissibility -/

/-- Every call of a fill within an allocated table is admissible when `b`-bit words fit. -/
theorem demonicValid_fill (hb : b ≤ w) {i n : ℕ} (hn : i + n ≤ table.length)
    {s : Memory.State} (hs : table.Allocated s) :
    (Memory.spec w).toRandomized.withCoins.toSpec.DemonicValid s (fill table b i n) := by
  induction n generalizing i s with
  | zero => exact StateTransitionSpec.DemonicValid.pure _ _
  | succ n ih =>
    refine RandomizedSpec.demonicValid_sample_bind fun x => ?_
    have hfit : Fits w x.val :=
      fits_iff.mpr (lt_of_lt_of_le x.2 (Nat.pow_le_pow_right (by omega) hb))
    refine StateTransitionSpec.DemonicValid.liftBind
      (D := (Memory.spec w).toRandomized.withCoins.toSpec)
      (Sum.inr (Memory.Op.write (table.base + i) x.val)) (fun _ => fill table b (i + 1) n)
      ⟨hs.lt_frontier (by omega), hfit⟩ fun s' a hstep => ?_
    obtain ⟨-, rfl⟩ := Prod.ext_iff.mp ((PMF.mem_support_pure_iff _ _).mp hstep)
    exact ih (by omega) hs

/-! ## The refinement -/

variable (table b) in
/-- **The random table refines the random function.** From an allocated table of `U` cells,
`resample` draws a uniform table and `eval u` answers its entry `u`. -/
noncomputable def refinement {U : ℕ} (hlen : table.length = U) (hb : b ≤ w) :
    RandomizedRefinement (tableSpec U b) (Memory.spec w).toRandomized.withCoins :=
  .ofLaw (methods table b U) table.Allocated (tableOf table b U)
    (fun {s} o hs _ => by
      cases o with
      | resample => exact demonicValid_fill hb (by omega) hs
      | eval u =>
        exact RandomizedSpec.demonicValid_liftRight
          (StateTransitionSpec.toRandomized_demonicValid_of_validHistory
            ⟨hs.lt_frontier (by omega), trivial⟩))
    (fun {s} o hs _ a s' h => by
      cases o with
      | resample =>
        have h' : s' ∈ (((Memory.spec w).toRandomized.withCoins.run
            (fill table b 0 U) s).map Prod.snd).support :=
          (PMF.mem_support_map_iff _ _ _).mpr ⟨(a, s'), h, rfl⟩
        rw [run_fill] at h'
        obtain ⟨θ, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h'
        exact hs.mono (le_of_eq (frontier_writeFrom _ _ _ _).symm)
      | eval u =>
        rw [run_methods_eval, PMF.mem_support_pure_iff] at h
        obtain ⟨-, rfl⟩ := Prod.ext_iff.mp h
        exact hs)
    (fun {s} o _ _ => by
      cases o with
      | resample =>
        calc _ = (((Memory.spec w).toRandomized.withCoins.run (fill table b 0 U) s).map
                Prod.snd).map fun s' => (PUnit.unit, tableOf table b U s') := by
              rw [PMF.map_comp]
              rfl
          _ = _ := by
              rw [run_fill, PMF.map_comp]
              simp only [Function.comp_def, tableOf_writeFrom]
      | eval u =>
        rw [run_methods_eval, PMF.pure_map])

/-! ## Costs -/

variable (U : ℕ) in
/-- One unit per call: `resample` makes one draw and one write per cell, `eval` one read. -/
def budget : HashFamily.Op U → ℕ
  | .resample => 2 * U
  | .eval _ => 1

/-- A fill of `n` cells makes `2 * n` calls. -/
theorem isQueryBounded_fill (i n : ℕ) : OracleComp.IsQueryBounded (fill table b i n) (2 * n) := by
  induction n generalizing i with
  | zero => exact .pure _ _
  | succ n ih =>
    have hsample : OracleComp.IsQueryBounded
        (ProbOracleComp.sample (spec := Memory.Op.Result) (ProbComp.uniform (Fin (2 ^ b)))) 1 := by
      rw [ProbComp.uniform, ProbOracleComp.sample_map]
      exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
    have hwrite (x : ℕ) : OracleComp.IsQueryBounded
        (OracleComp.liftRight (spec₁ := unifSpec) (table.set i x)) 1 :=
      OracleComp.IsCostBounded.query (spec := probOracleSpec Memory.Op.Result) _
    have h := hsample.bind fun x => (hwrite x.val).bind fun _ => ih (i + 1)
    exact h.mono (by omega)

/-- Every operation makes at most its budget of calls. -/
theorem isCostBounded_methods {U : ℕ} (o : HashFamily.Op U) :
    OracleComp.IsQueryBounded (methods table b U o) (budget U o) := by
  cases o with
  | resample => exact isQueryBounded_fill 0 U
  | eval u =>
    change OracleComp.IsQueryBounded
      (PFunctor.FreeM.liftBind (P := ⟨ℕ ⊕ Memory.Op, probOracleSpec Memory.Op.Result⟩)
        (Sum.inr (Memory.Op.read _)) fun v => pure (Fin.ofNat (2 ^ b) v)) 1
    exact OracleComp.IsCostBounded.liftBind_iff.mpr ⟨le_rfl, fun _ => .pure _ _⟩

/-- In expectation as well, every operation costs at most its budget of calls. -/
theorem expectedAmortized {U : ℕ} (hlen : table.length = U) (hb : b ≤ w) :
    (refinement table b hlen hb).ExpectedAmortized (fun _ _ => 1) (fun _ o => budget U o)
      fun _ => 0 :=
  .of_isCostBounded isCostBounded_methods

/-! ## The run from allocation -/

variable (b) in
/-- Allocate a table of `U` cells, fill it, then serve the client `p`. -/
noncomputable def run (U : ℕ) {α : Type} (p : OracleComp (HashFamily.Result (U := U) (2 ^ b)) α) :
    ProbOracleComp Memory.Op.Result α := do
  let table ← OracleComp.liftRight (Memory.allocBlockDirty U)
  OracleComp.interpret (methods table b U)
    (OracleComp.query (.resample : HashFamily.Op U) >>= fun _ => p)

theorem run_eq_link {U : ℕ} {α : Type} (p : OracleComp (HashFamily.Result (U := U) (2 ^ b)) α)
    (s : Memory.State) (hlen : (⟨s.frontier, U⟩ : Block).length = U) (hb : b ≤ w) :
    (Memory.spec w).toRandomized.withCoins.run (run b U p) s =
      (Memory.spec w).toRandomized.withCoins.run
        (link (refinement ⟨s.frontier, U⟩ b hlen hb).methods
          (OracleComp.query (.resample : HashFamily.Op U) >>= fun _ => p))
        ⟨s.mem, s.frontier + U⟩ := by
  rw [run, RandomizedSpec.run_bind, RandomizedSpec.withCoins_run_liftRight,
    StateTransitionSpec.run_toRandomized, PMF.pure_bind]
  rfl

/-- **The law of a client run from allocation**: a uniform table, then the client against the
random function. -/
theorem run_eq (hb : b ≤ w) {U : ℕ} {α : Type}
    (p : OracleComp (HashFamily.Result (U := U) (2 ^ b)) α) (s : Memory.State) :
    ((Memory.spec w).toRandomized.withCoins.run (run b U p) s).map Prod.fst =
      (Probability.PMF.uniformOfFintype (Fin U → Fin (2 ^ b))).bind fun θ =>
        ((tableSpec U b).run p θ).map Prod.fst := by
  have hlen : (⟨s.frontier, U⟩ : Block).length = U := rfl
  let M := refinement ⟨s.frontier, U⟩ b hlen hb
  have hlaw := M.run_link (OracleComp.query (.resample : HashFamily.Op U) >>= fun _ => p)
    (e := ⟨s.mem, s.frontier + U⟩) le_rfl
    ((tableSpec U b).toSpec.demonicValid_of_forall_valid (fun _ _ => trivial) _ _)
  rw [run_eq_link p s hlen hb]
  calc _ = (((Memory.spec w).toRandomized.withCoins.run
          (link M.methods (OracleComp.query (.resample : HashFamily.Op U) >>= fun _ => p))
          ⟨s.mem, s.frontier + U⟩).map fun (a, e') => (a, M.abs e')).map Prod.fst := by
        rw [PMF.map_comp]
        rfl
    _ = _ := by rw [hlaw, run_resample_bind_seedSpec, PMF.map_bind]

/-- **The memory-level `evalOps` theorem.** From any memory state, the transcript law of the
oblivious client of `ops`, run after allocating and filling the table, is
`HashFamily.evalOps` of the random function. -/
theorem run_obliviousClient (hb : b ≤ w) {U : ℕ} (ops : List (HashFamily.Op U))
    (s : Memory.State) :
    ((Memory.spec w).toRandomized.withCoins.run
        (run b U ((tableSpec U b).obliviousClient ops)) s).map Prod.fst =
      HashFamily.evalOps (Probability.PMF.uniformOfFintype (Fin U → Fin (2 ^ b)))
        (fun θ u => θ u) ops := by
  rw [run_eq hb, HashFamily.evalOps]
  exact congrArg _ (funext fun θ => run_obliviousClient_seedSpec _ _ θ ops)

/-- Every memory call of the run is admissible when the table and `b`-bit words fit. -/
theorem demonicValid_run (hb : b ≤ w) {U : ℕ} {α : Type}
    (p : OracleComp (HashFamily.Result (U := U) (2 ^ b)) α) {s : Memory.State}
    (hfit : Fits w (s.frontier + U)) :
    (Memory.spec w).toRandomized.withCoins.toSpec.DemonicValid s (run b U p) := by
  have hlen : (⟨s.frontier, U⟩ : Block).length = U := rfl
  let M := refinement ⟨s.frontier, U⟩ b hlen hb
  refine StateTransitionSpec.DemonicValid.liftBind
    (D := (Memory.spec w).toRandomized.withCoins.toSpec)
    (Sum.inr (Memory.Op.allocDirty U)) _ hfit fun s' a hstep => ?_
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp ((PMF.mem_support_pure_iff _ _).mp hstep)
  exact (M.toRefinement.simulates_demonic _ (e := ⟨s.mem, s.frontier + U⟩) le_rfl
    ((tableSpec U b).toSpec.demonicValid_of_forall_valid (fun _ _ => trivial) _ _)).1

/-- A client whose operations cost at most `n` in total, with `budget U`, runs from allocation
with at most `1 + 2 * U + n` calls. -/
theorem isQueryBounded_run {U : ℕ} {α : Type}
    {p : OracleComp (HashFamily.Result (U := U) (2 ^ b)) α} {n : ℕ}
    (hp : OracleComp.IsCostBounded (budget U) p n) :
    OracleComp.IsQueryBounded (run b U p) (1 + 2 * U + n) := by
  have halloc : OracleComp.IsQueryBounded
      (OracleComp.liftRight (spec₁ := unifSpec) (Memory.allocBlockDirty U)) 1 := by
    change OracleComp.IsQueryBounded
      (PFunctor.FreeM.liftBind (P := ⟨ℕ ⊕ Memory.Op, probOracleSpec Memory.Op.Result⟩)
        (Sum.inr (Memory.Op.allocDirty U)) fun base => pure (⟨base, U⟩ : Block)) 1
    exact OracleComp.IsCostBounded.liftBind_iff.mpr ⟨le_rfl, fun _ => .pure _ _⟩
  have h := halloc.bind fun table => OracleComp.IsCostBounded.interpret
    (isCostBounded_methods (table := table) (b := b))
    ((OracleComp.IsCostBounded.query (cost := budget U) .resample).bind fun _ => hp)
  simpa [run, budget, Nat.add_assoc] using h

end Cslib.DataStructure.HashFamily.RandomTable
