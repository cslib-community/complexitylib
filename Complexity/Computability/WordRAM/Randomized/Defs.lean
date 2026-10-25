/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.MapOp
public import Complexity.Languages.Probabilistic.Semantics
public import Complexity.Languages.Probabilistic.QueryCount

/-!
# Randomized word RAMs

A *randomized word RAM* executes a `Cslib.WordRAM.Program B r` at word size `w`, interpreting
`Instr.rand dst src` as drawing a uniform integer in `[0, regs src]` (`ProbComp.unifFin`) when
`regs src < 2 ^ w` (`Fits w (regs src)`), writing the sample to `dst`, advancing `pc` by `1`, and
charging one instruction and one `rand` call. When `regs src ≥ 2 ^ w` on an unbounded raw state,
`Instr.rand` faults; on any word-bounded state (`Data.Bounded w`), `regs src < 2 ^ w` holds
automatically and `Instr.rand` preserves `Data.Bounded w`. Note that `rand(0)` succeeds without
faulting, writes `0`, and still charges one instruction and one `rand` call (`unifBitCost 0 = 0`
entropy bits).

Following `Cslib.OracleComp`, clocked `T`-step execution `runRand` is defined as a terminating
program in `ProbComp (Cfg r)` (`= OracleComp unifSpec (Cfg r)`), and its configuration distribution
`evalRand` in `PMF (Cfg r)` is obtained via the monad morphism `ProbComp.eval`. Unlike deterministic
`Outcome.halt` (which carries only the scalar output), the absorbing randomized configuration
`Cfg r` records the final `Data r` alongside the scalar output (`Cfg.halted v data`) so flat-program
theorems can assert in-place memory postconditions directly.

On `rand`-free programs (`Program.IsRandFree`), `runRand` makes zero oracle calls and agrees in
both directions with deterministic `Runs`/`Executes` (`runRand_eq_pure_halted_iff_of_isRandFree`,
`exists_data_runRand_eq_pure_halted_iff_executes_of_isRandFree`). Conversely, any deterministic
halting run lifts unconditionally to `runRand` without `IsRandFree` because a deterministic run
never executes `Instr.rand` (`runRand_eq_pure_halted_of_runs_halt`).

## Main definitions

* `Cslib.WordRAM.Cfg`, `Cslib.WordRAM.Cfg.ofOutcome`: absorbing randomized machine configuration
  (`running`, `halted v data`, `faulted`) and lifting from deterministic `Outcome`.
* `Cslib.WordRAM.stepRand`, `Cslib.WordRAM.runRand`, `Cslib.WordRAM.evalRand`: single-step and
  clocked `T`-step randomized execution in `ProbComp` and `PMF`.
* `Cslib.WordRAM.FaultFree`, `Cslib.WordRAM.HaltsWithin`: zero-fault invariant and worst-case
  step bound.
* `Cslib.WordRAM.RandCallsBounded`, `Cslib.WordRAM.unifBitCost`,
  `Cslib.WordRAM.RandBitsBounded`: worst-case `rand`-call and entropy-bit budgets via
  `OracleComp.IsQueryBounded` and `OracleComp.IsCostBounded`.

## Main results

* `Cslib.WordRAM.runRand_add`: clocked runs compose additively in `ProbComp`.
* `Cslib.WordRAM.runRand_bounded_init`: from an input that fits `w`, every supported configuration
  remains word-bounded.
* `Cslib.WordRAM.runRand_eq_pure_halted_of_runs_halt`: deterministic halting runs lift
  unconditionally to `runRand` with the halting state's `Data r`.
* `Cslib.WordRAM.runRand_isQueryBounded_zero_of_isRandFree`: `rand`-free programs issue zero
  queries.
* `Cslib.WordRAM.runRand_eq_pure_halted_iff_of_isRandFree`,
  `Cslib.WordRAM.exists_data_runRand_eq_pure_halted_iff_executes_of_isRandFree`: two-way agreement
  with deterministic semantics on `rand`-free programs.
* `Cslib.WordRAM.RandCallsBounded.randBitsBounded`: `R` `rand` calls at word size `w` use at most
  `R * w` entropy bits.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

@[expose] public section

namespace Cslib

/-! ## General `OracleComp` and `ProbComp` helpers -/

namespace OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α β : Type v}

/-- Two continuations that agree on every possible output of `program` have identical `>>=` in
`OracleComp`. -/
theorem bind_congr_on_support {program : OracleComp spec α}
    {f g : α → OracleComp spec β} (h : ∀ a ∈ program.support, f a = g a) :
    program >>= f = program >>= g := by
  induction program using OracleComp.induction with
  | pure a =>
    simpa only [pure_bind] using h a rfl
  | query_bind q cont ih =>
    simp only [bind_assoc]
    exact congrArg (query q >>= ·) (funext fun r => ih r fun a ha =>
      h a (mem_supportWith_bind_iff.mpr ⟨r, by simp, ha⟩))

/-- Query cost budgets add under sequencing when the continuation is bounded on every possible
first-stage output. -/
theorem IsCostBounded.bind_on_support {cost : ι → ℕ} {program : OracleComp spec α}
    {next : α → OracleComp spec β} {n m : ℕ}
    (h : IsCostBounded cost program n)
    (hnext : ∀ a ∈ program.support, IsCostBounded cost (next a) m) :
    IsCostBounded cost (program >>= next) (n + m) := by
  induction h with
  | pure a n => exact (hnext a rfl).mono (by omega)
  | liftBind q cont n _ ih =>
    rw [show n + cost q + m = n + m + cost q by omega]
    exact .liftBind q _ (n + m) fun r =>
      ih r fun a ha => hnext a (mem_supportWith_bind_iff.mpr ⟨r, by simp, ha⟩)

/-- A computation with query budget `0` is `pure`. -/
theorem eq_pure_of_isQueryBounded_zero {program : OracleComp spec α}
    (h : program.IsQueryBounded 0) : ∃ a, program = pure a := by
  cases h with
  | pure a _ => exact ⟨a, rfl⟩

end OracleComp

namespace ProbComp

/-- Every `ProbComp` computation has at least one possible result. -/
theorem support_nonempty {α : Type} (program : ProbComp α) : program.support.Nonempty := by
  rw [← support_eval]
  exact (eval program).support_nonempty

/-- `unifFin n` makes one oracle query. -/
theorem isQueryBounded_unifFin (n : ℕ) : (unifFin n).IsQueryBounded 1 :=
  OracleComp.IsCostBounded.query (spec := unifSpec) (cost := fun _ => 1) n

/-- Every value in `Fin (n + 1)` is a possible output of `unifFin n`. -/
@[simp]
theorem mem_support_unifFin (n : ℕ) (k : Fin (n + 1)) : k ∈ (unifFin n).support := by
  simp [unifFin, OracleComp.support]

end ProbComp

namespace WordRAM

variable {B B' : Basis} {r : ℕ}

/-! ## Randomized configurations and single step -/

/-- Absorbing machine configuration for clocked randomized execution.
Retains the halting `Data r` alongside the scalar output `v` so flat-program specifications can
inspect final memory without changing deterministic `Outcome.halt`. -/
inductive Cfg (r : ℕ) where
  /-- Active execution at machine state `s`. -/
  | running (s : State r)
  /-- Halted with output word `v` and final machine data `data`. -/
  | halted (v : ℕ) (data : Data r)
  /-- Faulted on an invalid operation, out-of-range constant/sample, or out-of-bounds `pc`. -/
  | faulted

namespace Cfg

/-- Lift a deterministic `Outcome` from pre-step data `x` (`halt i` does not mutate `x`). -/
def ofOutcome (x : Data r) : Outcome r → Cfg r
  | .next s => .running s
  | .halt v => .halted v x
  | .fault => .faulted

/-- Whether a configuration is still actively running. -/
def isRunning : Cfg r → Prop
  | .running _ => True
  | _ => False

/-- Decidability of `Cfg.isRunning`. -/
instance (cfg : Cfg r) : Decidable cfg.isRunning :=
  match cfg with
  | .running _ => isTrue trivial
  | .halted _ _ | .faulted => isFalse id

/-- Whether a configuration has halted cleanly. -/
def isHalted : Cfg r → Prop
  | .halted _ _ => True
  | _ => False

/-- Decidability of `Cfg.isHalted`. -/
instance (cfg : Cfg r) : Decidable cfg.isHalted :=
  match cfg with
  | .halted _ _ => isTrue trivial
  | .running _ | .faulted => isFalse id

/-- Word-boundedness lifted to randomized configurations. -/
def Bounded (w : ℕ) : Cfg r → Prop
  | .running s => s.data.Bounded w
  | .halted v d => Fits w v ∧ d.Bounded w
  | .faulted => True

end Cfg

/-- One step of randomized execution at word size `w`. Halted and faulted configurations are
absorbing (`pure`, issuing zero queries). Never mark `@[simp]`. -/
def stepRand (w : ℕ) (p : Program B r) : Cfg r → ProbComp (Cfg r)
  | .halted v d => pure (.halted v d)
  | .faulted => pure .faulted
  | .running s =>
    match p[s.pc]? with
    | none => pure .faulted
    | some (.op o) =>
      match o.eval w s.data with
      | some x => pure (.running ⟨s.pc + 1, x⟩)
      | none => pure .faulted
    | some (.jump t) => pure (.running ⟨t, s.data⟩)
    | some (.branch c t) =>
      pure (.running ⟨if c.Holds s.data then t else s.pc + 1, s.data⟩)
    | some (.halt i) => pure (.halted (s.data.regs i) s.data)
    | some (.rand dst src) =>
      let n := s.data.regs src
      if Fits w n then do
        let k ← ProbComp.unifFin n
        pure (.running ⟨s.pc + 1, s.data.set dst k.val⟩)
      else
        pure .faulted

section StepRand

variable {w : ℕ} {p : Program B r} {s : State r}

theorem stepRand_halted (v : ℕ) (d : Data r) :
    stepRand w p (.halted v d) = pure (.halted v d) := rfl

theorem stepRand_faulted : stepRand w p .faulted = pure .faulted := rfl

theorem stepRand_none (hp : p[s.pc]? = none) :
    stepRand w p (.running s) = pure .faulted := by
  simp only [stepRand, hp]

theorem stepRand_op {o : Op B r} {x : Data r} (hp : p[s.pc]? = some (.op o))
    (h : o.eval w s.data = some x) :
    stepRand w p (.running s) = pure (.running ⟨s.pc + 1, x⟩) := by
  simp only [stepRand, hp, h]

theorem stepRand_op_fault {o : Op B r} (hp : p[s.pc]? = some (.op o))
    (h : o.eval w s.data = none) :
    stepRand w p (.running s) = pure .faulted := by
  simp only [stepRand, hp, h]

theorem stepRand_jump {t : ℕ} (hp : p[s.pc]? = some (.jump t)) :
    stepRand w p (.running s) = pure (.running ⟨t, s.data⟩) := by
  simp only [stepRand, hp]

theorem stepRand_branch {c : Cond r} {t : ℕ} (hp : p[s.pc]? = some (.branch c t)) :
    stepRand w p (.running s) =
      pure (.running ⟨if c.Holds s.data then t else s.pc + 1, s.data⟩) := by
  simp only [stepRand, hp]

theorem stepRand_halt {i : Fin r} (hp : p[s.pc]? = some (.halt i)) :
    stepRand w p (.running s) = pure (.halted (s.data.regs i) s.data) := by
  simp only [stepRand, hp]

theorem stepRand_rand_of_fits {dst src : Fin r} (hp : p[s.pc]? = some (.rand dst src))
    (hfit : Fits w (s.data.regs src)) :
    stepRand w p (.running s) = (do
      let k ← ProbComp.unifFin (s.data.regs src)
      pure (.running ⟨s.pc + 1, s.data.set dst k.val⟩)) := by
  simp only [stepRand, hp, hfit, ↓reduceIte]

theorem stepRand_rand_of_not_fits {dst src : Fin r} (hp : p[s.pc]? = some (.rand dst src))
    (hfit : ¬Fits w (s.data.regs src)) :
    stepRand w p (.running s) = pure .faulted := by
  simp only [stepRand, hp, hfit, ↓reduceIte]

/-- A deterministic step (any non-faulting outcome of `WordRAM.step`) agrees unconditionally with
`stepRand`. -/
theorem stepRand_of_step_eq_next {t : State r} (h : step w p s = .next t) :
    stepRand w p (.running s) = pure (.running t) := by
  cases hpc : p[s.pc]? with
  | none => simp [step, hpc] at h
  | some instr =>
    cases instr with
    | op o =>
      cases ho : o.eval w s.data with
      | none => simp [step, hpc, ho] at h
      | some x =>
        rw [step_op hpc ho] at h
        cases h
        exact stepRand_op hpc ho
    | jump tgt =>
      rw [step_jump hpc] at h
      cases h
      exact stepRand_jump hpc
    | branch c tgt =>
      rw [step_branch hpc] at h
      cases h
      exact stepRand_branch hpc
    | halt i => simp [step, hpc] at h
    | rand dst src => simp [step, hpc] at h

/-- A deterministic `halt` step agrees unconditionally with `stepRand`, retaining `s.data`. -/
theorem stepRand_of_step_eq_halt {v : ℕ} (h : step w p s = .halt v) :
    stepRand w p (.running s) = pure (.halted v s.data) := by
  cases hpc : p[s.pc]? with
  | none => simp [step, hpc] at h
  | some instr =>
    cases instr with
    | op o =>
      simp only [step, hpc] at h
      split at h <;> cases h
    | jump _ | branch _ _ | rand _ _ => simp [step, hpc] at h
    | halt i =>
      rw [step_halt hpc] at h
      cases h
      exact stepRand_halt hpc

end StepRand

/-! ## Clocked randomized runs and output distribution -/

/-- Clocked `T`-step randomized execution from configuration `cfg`. -/
def runRand (w : ℕ) (p : Program B r) : ℕ → Cfg r → ProbComp (Cfg r)
  | 0, cfg => pure cfg
  | T + 1, cfg => do
    let cfg' ← stepRand w p cfg
    runRand w p T cfg'

/-- `T`-step configuration distribution from initial machine state `s`. -/
noncomputable def evalRand (w : ℕ) (p : Program B r) (T : ℕ) (s : State r) : PMF (Cfg r) :=
  (runRand w p T (.running s)).eval

@[simp]
theorem runRand_zero (w : ℕ) (p : Program B r) (cfg : Cfg r) :
    runRand w p 0 cfg = pure cfg := rfl

theorem runRand_succ (w : ℕ) (p : Program B r) (T : ℕ) (cfg : Cfg r) :
    runRand w p (T + 1) cfg = (do
      let cfg' ← stepRand w p cfg
      runRand w p T cfg') := rfl

@[simp]
theorem runRand_halted (w : ℕ) (p : Program B r) (T : ℕ) (v : ℕ) (d : Data r) :
    runRand w p T (.halted v d) = pure (.halted v d) := by
  induction T with
  | zero => rfl
  | succ T ih => simp only [runRand_succ, stepRand_halted, pure_bind, ih]

@[simp]
theorem runRand_faulted (w : ℕ) (p : Program B r) (T : ℕ) :
    runRand w p T .faulted = pure .faulted := by
  induction T with
  | zero => rfl
  | succ T ih => simp only [runRand_succ, stepRand_faulted, pure_bind, ih]

/-- Clocked runs compose additively in `ProbComp`. -/
theorem runRand_add (w : ℕ) (p : Program B r) (T₁ T₂ : ℕ) (cfg : Cfg r) :
    runRand w p (T₁ + T₂) cfg = (do
      let cfg' ← runRand w p T₁ cfg
      runRand w p T₂ cfg') := by
  induction T₁ generalizing cfg with
  | zero => simp only [Nat.zero_add, runRand_zero, pure_bind]
  | succ T₁ ih =>
    rw [Nat.succ_add, runRand_succ, runRand_succ, bind_assoc]
    exact congrArg (stepRand w p cfg >>= ·) (funext ih)

@[simp]
theorem evalRand_zero (w : ℕ) (p : Program B r) (s : State r) :
    evalRand w p 0 s = PMF.pure (.running s) := rfl

theorem evalRand_succ (w : ℕ) (p : Program B r) (T : ℕ) (s : State r) :
    evalRand w p (T + 1) s =
      (stepRand w p (.running s)).eval.bind fun cfg => (runRand w p T cfg).eval := by
  simp only [evalRand, runRand_succ, ProbComp.eval_bind]

theorem support_evalRand (w : ℕ) (p : Program B r) (T : ℕ) (s : State r) :
    (evalRand w p T s).support = (runRand w p T (.running s)).support :=
  ProbComp.support_eval _

/-! ## Translation along basis homomorphisms -/

@[simp]
theorem stepRand_mapOp (φ : B.Hom B') (w : ℕ) (p : Program B r) (cfg : Cfg r) :
    stepRand w (p.mapOp φ) cfg = stepRand w p cfg := by
  cases cfg with
  | halted _ _ | faulted => rfl
  | running s =>
    dsimp only [stepRand, Program.mapOp]
    rw [List.getElem?_map]
    cases p[s.pc]? with
    | none => rfl
    | some i =>
      cases i with
      | op o => simp only [Option.map_some, Instr.mapOp, Op.eval_mapOp]
      | _ => rfl

@[simp]
theorem runRand_mapOp (φ : B.Hom B') (w : ℕ) (p : Program B r) (T : ℕ) (cfg : Cfg r) :
    runRand w (p.mapOp φ) T cfg = runRand w p T cfg := by
  induction T generalizing cfg with
  | zero => rfl
  | succ T ih => simp only [runRand_succ, stepRand_mapOp, ih]

@[simp]
theorem evalRand_mapOp (φ : B.Hom B') (w : ℕ) (p : Program B r) (T : ℕ) (s : State r) :
    evalRand w (p.mapOp φ) T s = evalRand w p T s := by
  simp only [evalRand, runRand_mapOp]

/-! ## Word-bound preservation -/

/-- One randomized step preserves `Cfg.Bounded w`. -/
theorem stepRand_bounded {w : ℕ} {p : Program B r} {cfg cfg' : Cfg r}
    (hcfg : cfg.Bounded w) (hmem : cfg' ∈ (stepRand w p cfg).support) :
    cfg'.Bounded w := by
  cases cfg with
  | halted v d =>
    cases OracleComp.eq_of_mem_supportWith_pure hmem
    exact hcfg
  | faulted =>
    cases OracleComp.eq_of_mem_supportWith_pure hmem
    trivial
  | running s =>
    have hs : s.data.Bounded w := hcfg
    cases hpc : p[s.pc]? with
    | none =>
      rw [stepRand_none hpc] at hmem
      cases OracleComp.eq_of_mem_supportWith_pure hmem
      trivial
    | some instr =>
      cases instr with
      | op o =>
        cases ho : o.eval w s.data with
        | none =>
          rw [stepRand_op_fault hpc ho] at hmem
          cases OracleComp.eq_of_mem_supportWith_pure hmem
          trivial
        | some x =>
          rw [stepRand_op hpc ho] at hmem
          cases OracleComp.eq_of_mem_supportWith_pure hmem
          exact hs.op ho
      | jump t =>
        rw [stepRand_jump hpc] at hmem
        cases OracleComp.eq_of_mem_supportWith_pure hmem
        exact hs
      | branch c t =>
        rw [stepRand_branch hpc] at hmem
        cases OracleComp.eq_of_mem_supportWith_pure hmem
        exact hs
      | halt i =>
        rw [stepRand_halt hpc] at hmem
        cases OracleComp.eq_of_mem_supportWith_pure hmem
        exact ⟨hs.1 i, hs⟩
      | rand dst src =>
        by_cases hfit : Fits w (s.data.regs src)
        · rw [stepRand_rand_of_fits hpc hfit] at hmem
          obtain ⟨k, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hmem
          cases OracleComp.eq_of_mem_supportWith_pure hk
          exact hs.set (hfit.of_le (Nat.le_of_lt_succ k.isLt))
        · rw [stepRand_rand_of_not_fits hpc hfit] at hmem
          cases OracleComp.eq_of_mem_supportWith_pure hmem
          trivial

/-- Clocked randomized execution preserves `Cfg.Bounded w`. -/
theorem runRand_bounded {w : ℕ} {p : Program B r} {T : ℕ} {cfg cfg' : Cfg r}
    (hcfg : cfg.Bounded w) (hmem : cfg' ∈ (runRand w p T cfg).support) :
    cfg'.Bounded w := by
  induction T generalizing cfg with
  | zero =>
    cases OracleComp.eq_of_mem_supportWith_pure hmem
    exact hcfg
  | succ T ih =>
    obtain ⟨mid, hmid, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hmem
    exact ih (stepRand_bounded hcfg hmid) hrest

/-- Every configuration reachable under `runRand` from an input that fits `w` holds only `w`-bit
words. -/
theorem runRand_bounded_init {w : ℕ} {p : Program B r} {input : List ℕ} {T : ℕ} {cfg : Cfg r}
    (hi : InputFits w input) (hmem : cfg ∈ (runRand w p T (.running (.init input))).support) :
    cfg.Bounded w :=
  runRand_bounded (cfg := .running (.init input)) (Data.Bounded.init hi) hmem

/-! ## Agreement with deterministic semantics -/

/-- On a `rand`-free program, `stepRand` agrees with deterministic `WordRAM.step`. -/
theorem stepRand_eq_of_isRandFree {w : ℕ} {p : Program B r} (hp : p.IsRandFree) (s : State r) :
    stepRand w p (.running s) = pure (Cfg.ofOutcome s.data (step w p s)) := by
  cases hpc : p[s.pc]? with
  | none => simp only [stepRand, step, hpc, Cfg.ofOutcome]
  | some instr =>
    have hrf : instr.IsRandFree := hp instr (List.mem_of_getElem? hpc)
    cases instr with
    | op o =>
      cases ho : o.eval w s.data <;> simp only [stepRand, step, hpc, ho, Cfg.ofOutcome]
    | jump t => simp only [stepRand, step, hpc, Cfg.ofOutcome]
    | branch c t => simp only [stepRand, step, hpc, Cfg.ofOutcome]
    | halt i => simp only [stepRand, step, hpc, Cfg.ofOutcome]
    | rand _ _ => exact hrf.elim

/-- Injectivity of `pure` in `OracleComp` via its singleton support. -/
private theorem pure_injective {α : Type} {a b : α}
    (h : (pure a : ProbComp α) = pure b) : a = b := by
  have hmem : a ∈ (pure a : ProbComp α).support := rfl
  rw [h] at hmem
  exact OracleComp.eq_of_mem_supportWith_pure hmem

/-- A deterministic `m`-step `Runs` lifts unconditionally to `runRand` (no `IsRandFree` needed, as
`Runs` never visits `Instr.rand`). -/
theorem runRand_eq_pure_running_of_runs {w m : ℕ} {p : Program B r} {s t : State r}
    (hrun : Runs w p s t m) :
    runRand w p m (.running s) = pure (.running t) := by
  induction hrun using Relation.RelatesInSteps.head_induction_on with
  | hrefl => rfl
  | hhead hsc _ ih =>
    simp only [runRand_succ, stepRand_of_step_eq_next hsc, pure_bind, ih]

/-- Unconditional lifting (no `IsRandFree` needed): a deterministic `Runs` followed by `halt` gives
`pure (.halted v t.data)` at every fuel `T ≥ m + 1`. -/
theorem runRand_eq_pure_halted_of_runs_halt {w m T : ℕ} {p : Program B r} {s t : State r} {v : ℕ}
    (hrun : Runs w p s t m) (hhalt : step w p t = .halt v) (hT : m + 1 ≤ T) :
    runRand w p T (.running s) = pure (.halted v t.data) := by
  obtain ⟨k, rfl⟩ : ∃ k, T = m + (1 + k) := ⟨T - (m + 1), by omega⟩
  rw [runRand_add, runRand_eq_pure_running_of_runs hrun, pure_bind, Nat.one_add, runRand_succ,
    stepRand_of_step_eq_halt hhalt, pure_bind, runRand_halted]

/-- On a `rand`-free program, a single step makes zero oracle calls. -/
theorem stepRand_isQueryBounded_zero_of_isRandFree {w : ℕ} {p : Program B r}
    (hp : p.IsRandFree) (cfg : Cfg r) :
    OracleComp.IsQueryBounded (stepRand w p cfg) 0 := by
  cases cfg with
  | halted v d => exact .pure _ 0
  | faulted => exact .pure _ 0
  | running s =>
    rw [stepRand_eq_of_isRandFree hp s]
    exact .pure _ 0

/-- On a `rand`-free program, clocked execution makes zero oracle calls. -/
theorem runRand_isQueryBounded_zero_of_isRandFree {w T : ℕ} {p : Program B r}
    (hp : p.IsRandFree) (cfg : Cfg r) :
    OracleComp.IsQueryBounded (runRand w p T cfg) 0 := by
  induction T generalizing cfg with
  | zero => exact .pure _ 0
  | succ T ih =>
    simpa only [runRand_succ, Nat.add_zero] using
      (stepRand_isQueryBounded_zero_of_isRandFree hp cfg).bind ih

/-- Full state-and-memory agreement on `IsRandFree` programs, matching `Executes`. -/
theorem runRand_eq_pure_halted_iff_of_isRandFree {w T : ℕ} {p : Program B r}
    (hp : p.IsRandFree) {s : State r} {v : ℕ} {d : Data r} :
    runRand w p T (.running s) = pure (.halted v d) ↔
      ∃ t m, m + 1 ≤ T ∧ Runs w p s t m ∧ step w p t = .halt v ∧ t.data = d := by
  constructor
  · intro h
    induction T generalizing s with
    | zero => cases pure_injective h
    | succ T ih =>
      rw [runRand_succ, stepRand_eq_of_isRandFree hp s, pure_bind] at h
      cases hstep : step w p s with
      | next u =>
        rw [hstep, Cfg.ofOutcome] at h
        obtain ⟨t, m, hmT, hrun, hhalt, hd⟩ := ih h
        exact ⟨t, m + 1, by omega, hrun.head s u t m hstep, hhalt, hd⟩
      | halt v' =>
        rw [hstep, Cfg.ofOutcome, runRand_halted] at h
        cases pure_injective h
        exact ⟨s, 0, by omega, .refl s, hstep, rfl⟩
      | fault =>
        rw [hstep, Cfg.ofOutcome, runRand_faulted] at h
        cases pure_injective h
  · rintro ⟨t, m, hmT, hrun, hhalt, rfl⟩
    exact runRand_eq_pure_halted_of_runs_halt hrun hhalt hmT

/-- Scalar projection corollary matching `Executes` on `IsRandFree` programs. -/
theorem exists_data_runRand_eq_pure_halted_iff_executes_of_isRandFree
    {w T : ℕ} {p : Program B r} (hp : p.IsRandFree) {s : State r} {v : ℕ} :
    (∃ d, runRand w p T (.running s) = pure (.halted v d)) ↔ ∃ n ≤ T, Executes w p s v n := by
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨t, m, hmT, hrun, hhalt, -⟩ := (runRand_eq_pure_halted_iff_of_isRandFree hp).mp hd
    exact ⟨m + 1, hmT, t, m, hrun, hhalt, rfl⟩
  · rintro ⟨n, hnT, t, m, hrun, hhalt, rfl⟩
    exact ⟨t.data, runRand_eq_pure_halted_of_runs_halt hrun hhalt hnT⟩

/-! ## Worst-case safety, step bounds, and randomness budgets -/

/-- Starting from `s`, `p` never reaches `.faulted` at any horizon `T`. -/
def FaultFree (w : ℕ) (p : Program B r) (s : State r) : Prop :=
  ∀ T, .faulted ∉ (runRand w p T (.running s)).support

/-- Under `FaultFree`, the fault probability vanishes at every horizon `T`. -/
theorem FaultFree.evalRand_faulted_eq_zero {w : ℕ} {p : Program B r} {s : State r}
    (h : FaultFree w p s) (T : ℕ) :
    evalRand w p T s .faulted = 0 := by
  rw [PMF.apply_eq_zero_iff, support_evalRand]
  exact h T

/-- Every supported execution path from `s` has halted cleanly within `T` steps. -/
def HaltsWithin (w : ℕ) (p : Program B r) (s : State r) (T : ℕ) : Prop :=
  ∀ cfg ∈ (runRand w p T (.running s)).support, ∃ v d, cfg = .halted v d

/-- Once `HaltsWithin w p s T` holds, increasing the step budget `T' ≥ T` leaves the `ProbComp`
computation identically unchanged (and charges zero additional oracle queries). -/
theorem runRand_eq_of_haltsWithin {w T T' : ℕ} {p : Program B r} {s : State r}
    (h : HaltsWithin w p s T) (hT : T ≤ T') :
    runRand w p T' (.running s) = runRand w p T (.running s) := by
  obtain ⟨k, rfl⟩ : ∃ k, T' = T + k := ⟨T' - T, by omega⟩
  rw [runRand_add]
  have hcongr : (runRand w p T (.running s) >>= runRand w p k) =
      (runRand w p T (.running s) >>= pure) := by
    refine OracleComp.bind_congr_on_support fun cfg hmem => ?_
    obtain ⟨v, d, rfl⟩ := h cfg hmem
    exact runRand_halted w p k v d
  rw [bind_pure] at hcongr
  exact hcongr

/-- Increasing fuel preserves the output distribution once `HaltsWithin` holds. -/
theorem evalRand_eq_of_haltsWithin {w T T' : ℕ} {p : Program B r} {s : State r}
    (h : HaltsWithin w p s T) (hT : T ≤ T') :
    evalRand w p T' s = evalRand w p T s := by
  simp only [evalRand, runRand_eq_of_haltsWithin h hT]

/-- `HaltsWithin` is monotone in the step bound. -/
theorem HaltsWithin.mono {w T T' : ℕ} {p : Program B r} {s : State r}
    (h : HaltsWithin w p s T) (hT : T ≤ T') :
    HaltsWithin w p s T' := by
  intro cfg hmem
  rw [runRand_eq_of_haltsWithin h hT] at hmem
  exact h cfg hmem

/-- Any program that halts within `T` steps is fault-free at all horizons. -/
theorem HaltsWithin.faultFree {w T : ℕ} {p : Program B r} {s : State r}
    (h : HaltsWithin w p s T) :
    FaultFree w p s := by
  intro t hmem
  have hmem_max : Cfg.faulted ∈ (runRand w p (max t T) (.running s)).support := by
    have heq : max t T = t + (max t T - t) := by omega
    rw [heq, runRand_add]
    exact OracleComp.mem_supportWith_bind_iff.mpr
      ⟨.faulted, hmem, by simp only [runRand_faulted]; rfl⟩
  rw [runRand_eq_of_haltsWithin h (le_max_right t T)] at hmem_max
  obtain ⟨v, d, hvd⟩ := h Cfg.faulted hmem_max
  cases hvd

/-- Worst-case `rand`-call budget: at most `R` `rand` instructions are executed on every path within
`T` steps (including `rand(0)`). -/
def RandCallsBounded (w : ℕ) (p : Program B r) (s : State r) (T R : ℕ) : Prop :=
  (runRand w p T (.running s)).IsQueryBounded R

/-- `RandCallsBounded` is monotone in the call budget `R`. -/
theorem RandCallsBounded.mono {w T R R' : ℕ} {p : Program B r} {s : State r}
    (h : RandCallsBounded w p s T R) (hR : R ≤ R') :
    RandCallsBounded w p s T R' :=
  OracleComp.IsCostBounded.mono h hR

/-- Once `HaltsWithin w p s T` holds, running for `T' ≥ T` steps charges zero additional `rand`
calls. -/
theorem RandCallsBounded.of_haltsWithin {w T T' R : ℕ} {p : Program B r} {s : State r}
    (hhalt : HaltsWithin w p s T) (hr : RandCallsBounded w p s T R) (hT : T ≤ T') :
    RandCallsBounded w p s T' R := by
  rw [RandCallsBounded, runRand_eq_of_haltsWithin hhalt hT]
  exact hr

/-- Information-theoretic bit cost of a single `ProbComp.unifFin n` draw: `⌈log₂(n + 1)⌉`.
`rand(0)` costs `0` bits; `rand(2 ^ w - 1)` costs `w` bits. -/
def unifBitCost (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

@[simp]
theorem unifBitCost_zero : unifBitCost 0 = 0 := by
  simp [unifBitCost]

@[simp]
theorem unifBitCost_two_pow_sub_one (w : ℕ) : unifBitCost (2 ^ w - 1) = w := by
  cases w with
  | zero => rfl
  | succ w =>
    have hpos : 1 ≤ 2 ^ (w + 1) := Nat.one_le_two_pow
    simp only [unifBitCost, Nat.sub_add_cancel hpos]
    exact Nat.clog_pow 2 (w + 1) (by decide)

theorem unifBitCost_le_of_fits {w n : ℕ} (h : Fits w n) : unifBitCost n ≤ w :=
  (Nat.clog_le_iff_le_pow (by decide)).mpr (Nat.succ_le_of_lt h)

/-- Worst-case entropy-bit budget over `T` steps. -/
def RandBitsBounded (w : ℕ) (p : Program B r) (s : State r) (T B_bits : ℕ) : Prop :=
  OracleComp.IsCostBounded unifBitCost (runRand w p T (.running s)) B_bits

/-- Every `ProbComp.unifFin n` query issued by `stepRand` satisfies `Fits w n`. -/
theorem stepRand_queriesSatisfy_fits (w : ℕ) (p : Program B r) (cfg : Cfg r) :
    OracleComp.QueriesSatisfy (Fits w) (stepRand w p cfg) := by
  cases cfg with
  | halted _ _ | faulted => exact .pure _
  | running s =>
    cases hpc : p[s.pc]? with
    | none =>
      rw [stepRand_none hpc]
      exact .pure _
    | some instr =>
      cases instr with
      | op o =>
        cases ho : o.eval w s.data with
        | none =>
          rw [stepRand_op_fault hpc ho]
          exact .pure _
        | some x =>
          rw [stepRand_op hpc ho]
          exact .pure _
      | jump _ =>
        rw [stepRand_jump hpc]
        exact .pure _
      | branch _ _ =>
        rw [stepRand_branch hpc]
        exact .pure _
      | halt _ =>
        rw [stepRand_halt hpc]
        exact .pure _
      | rand dst src =>
        by_cases hfit : Fits w (s.data.regs src)
        · rw [stepRand_rand_of_fits hpc hfit]
          exact (OracleComp.QueriesSatisfy.query hfit).bind fun _ => .pure _
        · rw [stepRand_rand_of_not_fits hpc hfit]
          exact .pure _

/-- Every `ProbComp.unifFin n` query issued by `runRand` satisfies `Fits w n`. -/
theorem runRand_queriesSatisfy_fits (w : ℕ) (p : Program B r) (T : ℕ) (cfg : Cfg r) :
    OracleComp.QueriesSatisfy (Fits w) (runRand w p T cfg) := by
  induction T generalizing cfg with
  | zero => exact .pure _
  | succ T ih => exact (stepRand_queriesSatisfy_fits w p cfg).bind ih

private theorem isCostBounded_of_queriesSatisfy_mul {α : Type} {pred : ℕ → Prop} {cost : ℕ → ℕ}
    {c R : ℕ} {program : ProbComp α}
    (hsat : OracleComp.QueriesSatisfy pred program)
    (hq : program.IsQueryBounded R)
    (hc : ∀ q, pred q → cost q ≤ c) :
    OracleComp.IsCostBounded cost program (R * c) := by
  induction hq with
  | pure a n => exact .pure a (n * c)
  | liftBind q cont n _ ih =>
    obtain ⟨hq_pred, hcont_sat⟩ := OracleComp.QueriesSatisfy.liftBind_iff.mp hsat
    have hstep : OracleComp.IsCostBounded cost (OracleComp.query q >>= cont) (n * c + cost q) :=
      .liftBind q cont (n * c) fun a => ih a (hcont_sat a)
    exact hstep.mono (by
      have := hc q hq_pred
      calc
        n * c + cost q ≤ n * c + c := Nat.add_le_add_left this _
        _ = (n + 1) * c := (Nat.succ_mul n c).symm)

/-- At word size `w`, `R` `rand` calls cost at most `R * w` entropy bits. -/
theorem RandCallsBounded.randBitsBounded {w T R : ℕ} {p : Program B r} {s : State r}
    (h : RandCallsBounded w p s T R) :
    RandBitsBounded w p s T (R * w) :=
  isCostBounded_of_queriesSatisfy_mul
    (runRand_queriesSatisfy_fits w p T (.running s))
    h
    fun _ hfit => unifBitCost_le_of_fits hfit

-- Keep `runRand` irreducible for downstream clients so `whnf` (and linters inspecting `Set.Mem`
-- on `(runRand w p T cfg).support`) does not symbolically unfold `T` machine steps on large
-- concrete step bounds `T`. Rewrite via `runRand_zero`, `runRand_succ`, and `runRand_add`.
attribute [irreducible] runRand

end WordRAM

end Cslib
