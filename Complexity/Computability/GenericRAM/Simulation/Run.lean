/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Simulation.Turing

/-!
# Clocked multi-step execution and whole-run native transport for generic RAMs

Iterating `FiniteState.step` yields a clocked multi-step finite-state semantics `FiniteState.run`
whose halting outputs agree with `GenericRAM.run` and `GenericRAM.Executes`. Each continuing step
adds at most one distinct address to the sparse store.

On the native multitape Turing-machine side, applying `NativeCertificate.iterate` to
`FiniteState.stepCertificate` yields `FiniteState.runCertificate` and `FiniteState.evalCertificate`,
together with automatic whole-run algorithm transport (`FiniteState.transportCertificate`,
`FiniteState.transport_inO`, `FiniteState.transport_polyTime`, and
`FiniteState.transport_polyTime_of_le_const`).

## Main definitions

* `FiniteState.init`, `FiniteState.initConst`: finite initial configurations at instruction `0`.
* `FiniteState.stepResult`, `FiniteState.run`, `FiniteState.eval`: clocked multi-step execution
  and halting output extraction.
* `FiniteState.initCertificate`, `FiniteState.initConstCertificate`: native initialization
  certificates.
* `FiniteState.runCertificate`, `FiniteState.evalCertificate`, `FiniteState.runTime`,
  `FiniteState.runSpace`: native clocked whole-run certificates and parameterized resource bounds.
* `FiniteState.transportCertificate`: automatic whole-run transport of `GenericRAM.Executes`
  certificates to native multitape Turing machines.

## Main results

* `FiniteState.length_entries_run_le`: `n` steps add at most `n` stored sparse-memory cells.
* `FiniteState.denote_run`, `FiniteState.executes_iff_exists_run`: exact multi-step refinement.
* `FiniteState.run_inO`, `FiniteState.eval_inO`: one finite native machine implements clocked
  multi-step execution uniformly across runtime configurations, step budgets, and states.
* `FiniteState.le_runTime_of_run_eq_inl`, `FiniteState.le_runSpace_of_run_eq_inl`: retention of
  per-step primitive and sparse-memory bounds along the run.
* `FiniteState.step_polyTime`, `FiniteState.transport_inO`, `FiniteState.transport_polyTime`,
  `FiniteState.transport_polyTime_of_le_const`: parameterized and polynomial-time whole-run
  transport theorems.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.GenericRAM.FiniteState

variable {M : Model.{0, 0, 0, 0}} {r : ℕ}

/-! ## Multi-step finite-state execution and refinement -/

/-- Extract the continuing finite state from a step outcome, if any. -/
def continuing : Result M r → Option (FiniteState M r)
  | some (.inl s) => some s
  | _ => none

@[simp] theorem continuing_none : continuing (M := M) (r := r) none = none := rfl
@[simp] theorem continuing_inl (s : FiniteState M r) :
    continuing (some (.inl s)) = some s := rfl
@[simp] theorem continuing_inr (v : M.Value) :
    continuing (M := M) (r := r) (some (.inr v)) = none := rfl

theorem continuing_eq_elim (res : Result M r) :
    continuing res = res.elim none Sum.getLeft? := by
  cases res with
  | none => rfl
  | some u => cases u <;> rfl

/-- Extract the halting output value from a step outcome, if any. -/
def output : Result M r → Option M.Value
  | some (.inr v) => some v
  | _ => none

@[simp] theorem output_none : output (M := M) (r := r) none = none := rfl
@[simp] theorem output_inl (s : FiniteState M r) :
    output (some (.inl s)) = none := rfl
@[simp] theorem output_inr (v : M.Value) :
    output (M := M) (r := r) (some (.inr v)) = some v := rfl

theorem output_eq_elim (res : Result M r) :
    output res = res.elim none Sum.getRight? := by
  cases res with
  | none => rfl
  | some u => cases u <;> rfl

/-- Initial finite configuration at control label `0`. -/
def init (regs : Fin r → M.Value) (default : M.Value)
    (memory : SparseMemory M.Address M.Value) : FiniteState M r :=
  ⟨0, regs, default, memory⟩

/-- Initial finite configuration at control label `0` with a uniform initial register value. -/
def initConst (initReg default : M.Value)
    (memory : SparseMemory M.Address M.Value) : FiniteState M r :=
  init (fun _ => initReg) default memory

@[simp] theorem denote_init_empty (initReg default : M.Value) :
    (initConst (M := M) (r := r) initReg default ∅).denote =
      ⟨0, Data.init initReg (fun _ => default)⟩ := rfl

/-- Advance a continuing finite state by one step; halting and faulting outcomes are absorbing. -/
def stepResult (k : M.Config) (p : Program M r) : Result M r → Result M r
  | some (.inl s) => step k p s
  | out => out

@[simp] theorem stepResult_none (k : M.Config) (p : Program M r) :
    stepResult k p none = none := rfl

@[simp] theorem stepResult_inl (k : M.Config) (p : Program M r) (s : FiniteState M r) :
    stepResult k p (some (.inl s)) = step k p s := rfl

@[simp] theorem stepResult_inr (k : M.Config) (p : Program M r) (v : M.Value) :
    stepResult k p (some (.inr v)) = some (.inr v) := rfl

theorem stepResult_eq (k : M.Config) (p : Program M r) (res : Result M r) :
    stepResult k p res = (continuing res).elim res (fun s => step k p s) := by
  cases res with
  | none => rfl
  | some u => cases u <;> rfl

@[simp] theorem iterate_stepResult_none (k : M.Config) (p : Program M r) (n : ℕ) :
    (stepResult k p)^[n] none = none := by
  induction n <;> simp [*]

@[simp] theorem iterate_stepResult_inr (k : M.Config) (p : Program M r) (n : ℕ) (v : M.Value) :
    (stepResult k p)^[n] (some (.inr v)) = some (.inr v) := by
  induction n <;> simp [*]

/-- Execute a fixed program for at most `n` steps from `s`, stopping early on halt or fault. -/
def run (k : M.Config) (p : Program M r) : ℕ → FiniteState M r → Result M r
  | 0, s => some (.inl s)
  | n + 1, s =>
    match step k p s with
    | some (.inl t) => run k p n t
    | out => out

@[simp] theorem run_zero (k : M.Config) (p : Program M r) (s : FiniteState M r) :
    run k p 0 s = some (.inl s) := rfl

theorem run_succ (k : M.Config) (p : Program M r) (n : ℕ) (s : FiniteState M r) :
    run k p (n + 1) s =
      match step k p s with
      | some (.inl t) => run k p n t
      | out => out := rfl

/-- Multi-step execution is exact iteration of `stepResult` from `some (.inl s)`. -/
theorem run_eq_iterate_stepResult (k : M.Config) (p : Program M r) (n : ℕ)
    (s : FiniteState M r) :
    run k p n s = (stepResult k p)^[n] (some (.inl s)) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, run_succ, stepResult_inl]
    cases hs : step k p s with
    | none => simp
    | some u =>
      cases u with
      | inl t => exact ih t
      | inr v => simp

theorem run_add (k : M.Config) (p : Program M r) (m n : ℕ) (s : FiniteState M r) :
    run k p (m + n) s =
      match run k p m s with
      | some (.inl t) => run k p n t
      | out => out := by
  rw [Nat.add_comm, run_eq_iterate_stepResult, Function.iterate_add_apply,
    ← run_eq_iterate_stepResult]
  cases hr : run k p m s with
  | none => simp
  | some u =>
    cases u with
    | inl t => exact (run_eq_iterate_stepResult k p n t).symm
    | inr v => simp

/-- Halting output after at most `n` finite steps (`none` on fault or unhalted continuation). -/
def eval (k : M.Config) (p : Program M r) (n : ℕ) (s : FiniteState M r) : Option M.Value :=
  output (run k p n s)

/-! ### Memory-growth and default-preservation invariants -/

theorem default_move {k : M.Config} {s t : FiniteState M r} {d : Fin r} {v : M.Value}
    (h : s.move k d v = some t) : t.default = s.default := by
  unfold move at h
  split at h
  · injection h with h; subst h; rfl
  · contradiction

theorem length_entries_move_eq {k : M.Config} {s t : FiniteState M r} {d : Fin r} {v : M.Value}
    (h : s.move k d v = some t) :
    (SparseMemory.entries t.memory).length = (SparseMemory.entries s.memory).length := by
  unfold move at h
  split at h
  · injection h with h; subst h; rfl
  · contradiction

theorem default_evalOp {k : M.Config} {o : Op M r} {s t : FiniteState M r}
    (h : evalOp k o s = some t) : t.default = s.default := by
  cases o with
  | const d c =>
    simp only [evalOp, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl
  | copy d src => exact default_move h
  | alu f d args =>
    simp only [evalOp, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl
  | load d a =>
    simp only [evalOp, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, hm⟩ := h
    exact default_move hm
  | store a src =>
    simp only [evalOp, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, hm⟩ := h
    split at hm
    · injection hm with hm; subst hm; rfl
    · contradiction

/-- A single data operation adds at most one stored address to sparse memory. -/
theorem length_entries_evalOp_le {k : M.Config} {o : Op M r} {s t : FiniteState M r}
    (h : evalOp k o s = some t) :
    (SparseMemory.entries t.memory).length ≤ (SparseMemory.entries s.memory).length + 1 := by
  cases o with
  | const d c =>
    simp only [evalOp, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    exact Nat.le_add_right _ _
  | copy d src =>
    rw [length_entries_move_eq h]
    exact Nat.le_add_right _ _
  | alu f d args =>
    simp only [evalOp, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    exact Nat.le_add_right _ _
  | load d a =>
    simp only [evalOp, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, hm⟩ := h
    rw [length_entries_move_eq hm]
    exact Nat.le_add_right _ _
  | store a src =>
    simp only [evalOp, bind, Option.bind_eq_some_iff] at h
    obtain ⟨addr, _, hm⟩ := h
    split at hm
    · injection hm with hm
      subst hm
      exact SparseMemory.length_insert_le addr (s.regs src) s.memory
    · contradiction

theorem default_resume {k : M.Config} {pc : ℕ} {s t : FiniteState M r}
    (h : resume k pc s = some (.inl t)) : t.default = s.default := by
  unfold resume at h
  split at h
  · simp only [Option.some.injEq, Sum.inl.injEq] at h
    subst h; rfl
  · contradiction

theorem memory_resume {k : M.Config} {pc : ℕ} {s t : FiniteState M r}
    (h : resume k pc s = some (.inl t)) : t.memory = s.memory := by
  unfold resume at h
  split at h
  · simp only [Option.some.injEq, Sum.inl.injEq] at h
    subst h; rfl
  · contradiction

theorem default_evalInstr {k : M.Config} {nextPC : ℕ} {i : Instr M r} {s t : FiniteState M r}
    (h : evalInstr k nextPC i s = some (.inl t)) : t.default = s.default := by
  cases i with
  | op o =>
    simp only [evalInstr, bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, ho, hr⟩ := h
    exact (default_resume hr).trans (default_evalOp ho)
  | jump target => exact default_resume h
  | branch c target =>
    cases c with
    | test f args =>
      simp only [evalInstr, bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, hr⟩ := h
      exact default_resume hr
  | halt idx =>
    simp only [evalInstr] at h
    split at h <;> simp at h

theorem length_entries_evalInstr_le {k : M.Config} {nextPC : ℕ} {i : Instr M r}
    {s t : FiniteState M r} (h : evalInstr k nextPC i s = some (.inl t)) :
    (SparseMemory.entries t.memory).length ≤ (SparseMemory.entries s.memory).length + 1 := by
  cases i with
  | op o =>
    simp only [evalInstr, bind, Option.bind_eq_some_iff] at h
    obtain ⟨u, ho, hr⟩ := h
    rw [memory_resume hr]
    exact length_entries_evalOp_le ho
  | jump target =>
    rw [memory_resume h]
    exact Nat.le_add_right _ _
  | branch c target =>
    cases c with
    | test f args =>
      simp only [evalInstr, bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, hr⟩ := h
      rw [memory_resume hr]
      exact Nat.le_add_right _ _
  | halt idx =>
    simp only [evalInstr] at h
    split at h <;> simp at h

/-- A continuing finite step preserves the memory default. -/
theorem default_step {k : M.Config} {p : Program M r} {s t : FiniteState M r}
    (h : step k p s = some (.inl t)) : t.default = s.default := by
  unfold step at h
  split at h
  · rw [dispatch_eq_getElem? k p 0 s (Nat.zero_le _), Nat.sub_zero] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨i, _, hi⟩ := h
    exact default_evalInstr hi
  · simp at h

/-- A continuing finite step adds at most one stored address to sparse memory. -/
theorem length_entries_step_le {k : M.Config} {p : Program M r} {s t : FiniteState M r}
    (h : step k p s = some (.inl t)) :
    (SparseMemory.entries t.memory).length ≤ (SparseMemory.entries s.memory).length + 1 := by
  unfold step at h
  split at h
  · rw [dispatch_eq_getElem? k p 0 s (Nat.zero_le _), Nat.sub_zero] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨i, _, hi⟩ := h
    exact length_entries_evalInstr_le hi
  · simp at h

/-- Multi-step execution preserves the memory default on all continuing states. -/
theorem default_run {k : M.Config} {p : Program M r} {n : ℕ} {s t : FiniteState M r}
    (h : run k p n s = some (.inl t)) : t.default = s.default := by
  induction n generalizing s with
  | zero =>
    simp only [run_zero, Option.some.injEq, Sum.inl.injEq] at h
    exact h ▸ rfl
  | succ n ih =>
    rw [run_succ] at h
    cases hs : step k p s with
    | none => simp [hs] at h
    | some u =>
      cases u with
      | inl u =>
        simp only [hs] at h
        exact (ih h).trans (default_step hs)
      | inr v => simp [hs] at h

/-- Across `n` finite steps, sparse memory grows by at most `n` stored cells. -/
theorem length_entries_run_le {k : M.Config} {p : Program M r} {n : ℕ} {s t : FiniteState M r}
    (h : run k p n s = some (.inl t)) :
    (SparseMemory.entries t.memory).length ≤ (SparseMemory.entries s.memory).length + n := by
  induction n generalizing s with
  | zero =>
    simp only [run_zero, Option.some.injEq, Sum.inl.injEq] at h
    subst h
    simp
  | succ n ih =>
    rw [run_succ] at h
    cases hs : step k p s with
    | none => simp [hs] at h
    | some u =>
      cases u with
      | inl u =>
        simp only [hs] at h
        have hstep := length_entries_step_le hs
        have hrun := ih h
        omega
      | inr v => simp [hs] at h

/-! ### Multi-step denotation and `Executes` correspondence -/

/-- Continuing for `n` finite steps refines an `n`-step `GenericRAM.Runs` trace. -/
theorem runs_of_run_eq_inl {k : M.Config} {p : Program M r} {n : ℕ} {s t : FiniteState M r}
    (h : run k p n s = some (.inl t)) : GenericRAM.Runs k p s.denote t.denote n := by
  induction n generalizing s with
  | zero =>
    simp only [run_zero, Option.some.injEq, Sum.inl.injEq] at h
    subst h
    exact .refl _
  | succ n ih =>
    rw [run_succ] at h
    cases hs : step k p s with
    | none => simp [hs] at h
    | some u =>
      cases u with
      | inl u =>
        simp only [hs] at h
        have hnext : GenericRAM.Next k p s.denote u.denote := by
          rw [GenericRAM.Next, ← denote_step, hs, denoteResult]
        exact (ih h).head _ _ _ _ hnext
      | inr v => simp [hs] at h

private theorem exists_run_eq_inl_of_runs_aux {k : M.Config} {p : Program M r} {n : ℕ}
    {s₀ u : State M r} (h : GenericRAM.Runs k p s₀ u n) :
    ∀ s : FiniteState M r, s.denote = s₀ →
      ∃ t, run k p n s = some (.inl t) ∧ t.denote = u := by
  induction h using Relation.RelatesInSteps.head_induction_on with
  | hrefl =>
    intro s hd
    exact ⟨s, rfl, hd⟩
  | hhead hab _ ih =>
    intro s hd
    subst hd
    have hstep := denote_step k p s
    rw [GenericRAM.Next] at hab
    rw [hab] at hstep
    cases hs : step k p s with
    | none => simp [hs, denoteResult] at hstep
    | some out =>
      cases out with
      | inl s' =>
        simp only [hs, denoteResult, Outcome.next.injEq] at hstep
        obtain ⟨t, hrun, hden⟩ := ih s' hstep
        refine ⟨t, ?_, hden⟩
        simp [run_succ, hs, hrun]
      | inr v => simp [hs, denoteResult] at hstep

/-- Every `n`-step `GenericRAM.Runs` trace from `s.denote` lifts to a continuing finite state. -/
theorem exists_run_eq_inl_of_runs {k : M.Config} {p : Program M r} {n : ℕ}
    {s : FiniteState M r} {u : State M r} (h : GenericRAM.Runs k p s.denote u n) :
    ∃ t, run k p n s = some (.inl t) ∧ t.denote = u :=
  exists_run_eq_inl_of_runs_aux h s rfl

/-- **Exact multi-step output refinement**: at every step budget `n`, the finite-state evaluator
agrees with the fuel-bounded generic RAM interpreter. -/
theorem denote_run (k : M.Config) (p : Program M r) (n : ℕ) (s : FiniteState M r) :
    eval k p n s = (GenericRAM.run k p n s.denote).map Prod.fst := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [eval, run_succ, GenericRAM.run_succ, ← denote_step]
    cases hs : step k p s with
    | none => rfl
    | some u =>
      cases u with
      | inl t =>
        simp only [denoteResult, Option.map_map]
        exact ih t
      | inr v => rfl

/-- A halting execution of `m ≤ n` instructions halts with the same output in `n` finite steps. -/
theorem run_eq_inr_of_executes {k : M.Config} {p : Program M r} {s : FiniteState M r}
    {v : M.Value} {m n : ℕ} (h : GenericRAM.Executes k p s.denote v m) (hmn : m ≤ n) :
    run k p n s = some (.inr v) := by
  have hrun := GenericRAM.run_mono h.run_eq hmn
  have hden := denote_run k p n s
  rw [hrun, Option.map_some, eval] at hden
  cases hr : run k p n s with
  | none => simp [hr] at hden
  | some u =>
    cases u with
    | inl t => simp [hr] at hden
    | inr w =>
      simp only [hr, output_inr, Option.some.injEq] at hden
      exact congrArg (some ∘ Sum.inr) hden

/-- A halting execution of `m ≤ n` instructions produces `some v` under `eval`. -/
theorem eval_eq_some_of_executes {k : M.Config} {p : Program M r} {s : FiniteState M r}
    {v : M.Value} {m n : ℕ} (h : GenericRAM.Executes k p s.denote v m) (hmn : m ≤ n) :
    eval k p n s = some v := by
  rw [eval, run_eq_inr_of_executes h hmn, output_inr]

/-- Every halting finite-state run within `n` steps witnesses a halting `GenericRAM.Executes` run
of at most `n` instructions. -/
theorem executes_of_run_eq_inr {k : M.Config} {p : Program M r} {n : ℕ}
    {s : FiniteState M r} {v : M.Value} (h : run k p n s = some (.inr v)) :
    ∃ m ≤ n, GenericRAM.Executes k p s.denote v m := by
  induction n generalizing s with
  | zero => simp [run_zero] at h
  | succ n ih =>
    rw [run_succ] at h
    cases hs : step k p s with
    | none => simp [hs] at h
    | some u =>
      cases u with
      | inl t =>
        simp only [hs] at h
        obtain ⟨m, hmn, hex⟩ := ih h
        have hnext : GenericRAM.Next k p s.denote t.denote := by
          rw [GenericRAM.Next, ← denote_step, hs, denoteResult]
        exact ⟨m + 1, Nat.add_le_add_right hmn 1, hex.head hnext⟩
      | inr w =>
        simp only [hs, Option.some.injEq, Sum.inr.injEq] at h
        cases h
        have hhalt : GenericRAM.step k p s.denote = .halt v := by
          rw [← denote_step, hs, denoteResult]
        exact ⟨1, Nat.succ_le_succ (Nat.zero_le _), .halt hhalt⟩

/-- Halting generic-RAM executions from `s.denote` correspond to halting finite-state runs. -/
theorem executes_iff_exists_run (k : M.Config) (p : Program M r) (s : FiniteState M r)
    (v : M.Value) :
    (∃ m, GenericRAM.Executes k p s.denote v m) ↔ ∃ n, run k p n s = some (.inr v) :=
  ⟨fun ⟨m, h⟩ => ⟨m, run_eq_inr_of_executes h le_rfl⟩,
   fun ⟨_, h⟩ => let ⟨m, _, hex⟩ := executes_of_run_eq_inr h; ⟨m, hex⟩⟩

end Cslib.GenericRAM.FiniteState

/-! ## Native certificates for initialization, clocked execution, and transport -/

noncomputable section

namespace Cslib.GenericRAM

open Turing.MultiTapeTM
open NativeCertificate

namespace FiniteState

variable {M : Model.{0, 0, 0, 0}} {r : ℕ}
variable {α : Type} {ei : α ↪ List Bool}

/-- Framed encoding of initialization arguments `(regs, default, memory)`. -/
abbrev initEncoding (enc : M.Encoding) :
    ((Fin r → M.Value) × M.Value × SparseMemory M.Address M.Value) ↪ List Bool :=
  encPair (encPi enc.value) (encPair enc.value (SparseMemory.encoding enc.address enc.value))

/-- Construct an initial finite configuration at `pc = 0` from certificates for its fields. -/
def initCertificate (enc : M.Encoding)
    {regsFn : α → Fin r → M.Value} {defaultFn : α → M.Value}
    {memoryFn : α → SparseMemory M.Address M.Value}
    (regs : NativeCertificate regsFn ei (encPi enc.value))
    (default : NativeCertificate defaultFn ei enc.value)
    (memory : NativeCertificate memoryFn ei (SparseMemory.encoding enc.address enc.value)) :
    NativeCertificate (fun a => init (regsFn a) (defaultFn a) (memoryFn a)) ei (encoding enc) :=
  post (prod (const 0) (prod regs (prod default memory))) (Native.pack enc).computes

@[simp] theorem initCertificate_time (enc : M.Encoding)
    {regsFn : α → Fin r → M.Value} {defaultFn : α → M.Value}
    {memoryFn : α → SparseMemory M.Address M.Value}
    (regs : NativeCertificate regsFn ei (encPi enc.value))
    (default : NativeCertificate defaultFn ei enc.value)
    (memory : NativeCertificate memoryFn ei (SparseMemory.encoding enc.address enc.value))
    (a : α) :
    (initCertificate enc regs default memory).time a =
      (ei a).length + (regs.time a + (default.time a + memory.time a)) := rfl

@[simp] theorem initCertificate_space (enc : M.Encoding)
    {regsFn : α → Fin r → M.Value} {defaultFn : α → M.Value}
    {memoryFn : α → SparseMemory M.Address M.Value}
    (regs : NativeCertificate regsFn ei (encPi enc.value))
    (default : NativeCertificate defaultFn ei enc.value)
    (memory : NativeCertificate memoryFn ei (SparseMemory.encoding enc.address enc.value))
    (a : α) :
    (initCertificate enc regs default memory).space a =
      (ei a).length + (regs.space a + (default.space a + memory.space a)) := rfl

/-- Copy a certified value into every fixed register, retaining the original summed bounds. -/
def constRegsCertificate (enc : M.Encoding) {initRegFn : α → M.Value}
    (initReg : NativeCertificate initRegFn ei enc.value) :
    NativeCertificate (fun a : α => fun _ : Fin r => initRegFn a) ei (encPi enc.value) where
  time a := (ei a).length + ∑ _i : Fin r, initReg.time a
  space a := (ei a).length + ∑ _i : Fin r, initReg.space a
  computes := by
    cases r with
    | zero =>
      have hc := ComputableInO.const (encIn := ei)
        (encMid := encPi (Index := Fin 0) enc.value) (fun i : Fin 0 => Fin.elim0 i)
      have heq : (fun a : α => fun _ : Fin 0 => initRegFn a) =
          (fun _ : α => fun i : Fin 0 => (Fin.elim0 i : M.Value)) :=
        funext fun _ => funext fun i => Fin.elim0 i
      simpa only [heq, Fin.sum_univ_zero, Nat.add_zero] using hc
    | succ r =>
      have hone : ComputableInO (fun v : M.Value => fun _ : Unit => v)
          enc.value (encPi enc.value) (fun v => (enc.value v).length)
          (fun v => (enc.value v).length) := .of_linear (.of_frame fun v => by
            change frame (enc.value v) ++ [] = frame (enc.value v)
            exact List.append_nil _)
      have hgather := ComputableInO.pi_gather enc.value (fun _ : Fin (r + 1) => ())
      have h := (hgather.comp_linear hone).comp_linear initReg.computes
      exact h.mono_le (fun a => by simp only [Fin.sum_univ_succ]; omega)
        (fun a => by simp only [Fin.sum_univ_succ]; omega)

/-- Construct an initial finite configuration at `pc = 0` with constant registers `initReg`. -/
def initConstCertificate (enc : M.Encoding)
    {initRegFn defaultFn : α → M.Value}
    {memoryFn : α → SparseMemory M.Address M.Value}
    (initReg : NativeCertificate initRegFn ei enc.value)
    (default : NativeCertificate defaultFn ei enc.value)
    (memory : NativeCertificate memoryFn ei (SparseMemory.encoding enc.address enc.value)) :
    NativeCertificate (fun a => initConst (r := r) (initRegFn a) (defaultFn a) (memoryFn a))
      ei (encoding enc) :=
  initCertificate enc (constRegsCertificate enc initReg) default memory

/-- Top-level native certificate for `init` on `(regs, default, memory)`. -/
theorem init_inO (enc : M.Encoding) :
    ComputableInO
      (fun q : (Fin r → M.Value) × M.Value × SparseMemory M.Address M.Value =>
        init q.1 q.2.1 q.2.2)
      (initEncoding (r := r) enc) (encoding enc)
      (fun q => 4 * (initEncoding (r := r) enc q).length)
      (fun q => 4 * (initEncoding (r := r) enc q).length) := by
  let idInit : NativeCertificate
      (id : (Fin r → M.Value) × M.Value × SparseMemory M.Address M.Value →
        (Fin r → M.Value) × M.Value × SparseMemory M.Address M.Value)
      (initEncoding (r := r) enc) (initEncoding (r := r) enc) :=
    linear (ComputableInO.of_eq (f := fun x => x) fun _ => rfl)
  have h := (initCertificate enc (fst idInit) (fst (snd idInit)) (snd (snd idInit))).computes
  exact h.mono_le (T' := fun q => 4 * (initEncoding (r := r) enc q).length)
    (S' := fun q => 4 * (initEncoding (r := r) enc q).length)
    (fun _ => by simp [idInit, initCertificate_time]; omega)
    (fun _ => by simp [idInit, initCertificate_space]; omega)

/-! ### Outcome projection certificates -/

/-- Extract a continuing finite state from `Result M r` in linear time and space. -/
def continuingCertificate (enc : M.Encoding) :
    NativeCertificate (continuing (M := M) (r := r))
      (resultEncoding enc) (encOption (encoding enc)) := by
  let hid : NativeCertificate (id : Result M r → Result M r)
      (resultEncoding enc) (resultEncoding enc) :=
    linear (ComputableInO.of_eq (f := fun x => x) fun _ => rfl)
  let hleft : NativeCertificate
      (fun p : Result M r × (FiniteState M r ⊕ M.Value) => Sum.getLeft? p.2)
      (encPair (resultEncoding enc) (encSum (encoding enc) enc.value))
      (encOption (encoding enc)) :=
    post (payload (resultEncoding enc) (encSum (encoding enc) enc.value))
      (ComputableInO.getLeft? (encoding enc) enc.value)
  let hopt := option hid (const none) hleft
  refine ⟨fun res => (resultEncoding enc res).length,
    fun res => (resultEncoding enc res).length, ?_⟩
  refine (hopt.computes.mono 6 (fun res => ?_) (fun res => ?_)).of_enc_eq fun res => ?_
  · cases res <;> simp [hopt, hid, hleft]; omega
  · cases res <;> simp [hopt, hid, hleft]; omega
  · exact congrArg (encOption (encoding enc)) (continuing_eq_elim res)

@[simp] theorem continuingCertificate_time (enc : M.Encoding) (res : Result M r) :
    (continuingCertificate enc).time res = (resultEncoding enc res).length := rfl

@[simp] theorem continuingCertificate_space (enc : M.Encoding) (res : Result M r) :
    (continuingCertificate enc).space res = (resultEncoding enc res).length := rfl

/-- Extract a halting output value from `Result M r` in linear time and space. -/
def outputCertificate (enc : M.Encoding) :
    NativeCertificate (output (M := M) (r := r))
      (resultEncoding enc) (encOption enc.value) := by
  let hid : NativeCertificate (id : Result M r → Result M r)
      (resultEncoding enc) (resultEncoding enc) :=
    linear (ComputableInO.of_eq (f := fun x => x) fun _ => rfl)
  let hright : NativeCertificate
      (fun p : Result M r × (FiniteState M r ⊕ M.Value) => Sum.getRight? p.2)
      (encPair (resultEncoding enc) (encSum (encoding enc) enc.value))
      (encOption enc.value) :=
    post (payload (resultEncoding enc) (encSum (encoding enc) enc.value))
      (ComputableInO.getRight? (encoding enc) enc.value)
  let hopt := option hid (const none) hright
  refine ⟨fun res => (resultEncoding enc res).length,
    fun res => (resultEncoding enc res).length, ?_⟩
  refine (hopt.computes.mono 6 (fun res => ?_) (fun res => ?_)).of_enc_eq fun res => ?_
  · cases res <;> simp [hopt, hid, hright]; omega
  · cases res <;> simp [hopt, hid, hright]; omega
  · exact congrArg (encOption enc.value) (output_eq_elim res)

@[simp] theorem outputCertificate_time (enc : M.Encoding) (res : Result M r) :
    (outputCertificate enc).time res = (resultEncoding enc res).length := rfl

@[simp] theorem outputCertificate_space (enc : M.Encoding) (res : Result M r) :
    (outputCertificate enc).space res = (resultEncoding enc res).length := rfl

/-! ### Clocked multi-step simulation certificates -/

/-- Encoding of the loop state `(k, res) : M.Config × Result M r`. -/
abbrev loopEncoding (enc : M.Encoding) :
    (M.Config × Result M r) ↪ List Bool :=
  encPair enc.config (resultEncoding enc)

/-- Encoding of a clocked simulation input `(n, (k, s)) : ℕ × (M.Config × FiniteState M r)`. -/
abbrev runInputEncoding (enc : M.Encoding) :
    (ℕ × (M.Config × FiniteState M r)) ↪ List Bool :=
  encPair encNat (inputEncoding enc)

/-- One round of the clocked simulator, preserving the runtime configuration. -/
def round (p : Program M r) (q : M.Config × Result M r) : M.Config × Result M r :=
  (q.1, stepResult q.1 p q.2)

theorem iterate_round (p : Program M r) (n : ℕ) (k : M.Config) (res : Result M r) :
    (round p)^[n] (k, res) = (k, (stepResult k p)^[n] res) := by
  induction n generalizing res with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, round, ih, ← Function.iterate_succ_apply]

theorem iterate_round_inl (p : Program M r) (n : ℕ) (k : M.Config) (s : FiniteState M r) :
    (round p)^[n] (k, Option.some (.inl s)) = (k, run k p n s) := by
  rw [iterate_round, run_eq_iterate_stepResult]

/-- Native certificate for `stepResult`, charging `stepCertificate` only on continuing states. -/
def stepResultCertificate (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) :
    NativeCertificate (fun q : M.Config × Result M r => stepResult q.1 p q.2)
      (loopEncoding enc) (resultEncoding enc) :=
  let idLoop := linear (ei := loopEncoding enc) (ComputableInO.of_eq (f := fun x => x) fun _ => rfl)
  let idBody := linear
    (ei := encPair (loopEncoding enc) (encoding enc))
    (ComputableInO.of_eq (f := fun x => x) fun _ => rfl)
  congr
    (option ((continuingCertificate enc).comp (snd idLoop))
      (snd idLoop)
      ((stepCertificate enc N p).comp (prod (fst (fst idBody)) (snd idBody))))
    (fun q => (stepResult_eq q.1 p q.2).symm)

/-- Native certificate for one clocked simulation round on `M.Config × Result M r`. -/
def roundCertificate (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) :
    NativeCertificate (round p) (loopEncoding enc) (loopEncoding enc) :=
  let idLoop := linear (ei := loopEncoding enc) (ComputableInO.of_eq (f := fun x => x) fun _ => rfl)
  prod (fst idLoop) (stepResultCertificate enc N p)

/-- Prepare the initial loop state `(k, some (.inl s))` from `(n, (k, s))`. -/
def initLoopCertificate (enc : M.Encoding) :
    NativeCertificate
      (fun q : ℕ × (M.Config × FiniteState M r) =>
        (q.2.1, (Option.some (.inl q.2.2) : Result M r)))
      (runInputEncoding enc) (loopEncoding enc) :=
  let idIn := linear (ei := runInputEncoding enc)
    (ComputableInO.of_eq (f := fun x => x) fun _ => rfl)
  prod (fst (snd idIn)) (some (inl (snd (snd idIn)) enc.value))

/-- Native certificate for clocked multi-step execution `run q.2.1 p q.1 q.2.2`. -/
def runCertificate (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) :
    NativeCertificate (fun q : ℕ × (M.Config × FiniteState M r) => run q.2.1 p q.1 q.2.2)
      (runInputEncoding enc) (resultEncoding enc) :=
  let idIn := linear (ei := runInputEncoding enc)
    (ComputableInO.of_eq (f := fun x => x) fun _ => rfl)
  congr
    (snd (iterate (fst idIn) (initLoopCertificate enc) (roundCertificate enc N p)))
    (fun q => by simp [iterate_round_inl])

/-- Parameterized time bound for clocked multi-step execution. -/
def runTime (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) :
    ℕ × (M.Config × FiniteState M r) → ℕ :=
  (runCertificate enc N p).time

/-- Parameterized space bound for clocked multi-step execution. -/
def runSpace (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) :
    ℕ × (M.Config × FiniteState M r) → ℕ :=
  (runCertificate enc N p).space

/-- One finite native machine implements clocked multi-step execution uniformly across step
budgets, runtime configurations, and finite states. -/
theorem run_inO (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) :
    ComputableInO (fun q : ℕ × (M.Config × FiniteState M r) => run q.2.1 p q.1 q.2.2)
      (runInputEncoding enc) (resultEncoding enc)
      (runTime enc N p) (runSpace enc N p) :=
  (runCertificate enc N p).computes

/-- Native certificate for clocked output evaluation `eval q.2.1 p q.1 q.2.2`. -/
def evalCertificate (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) :
    NativeCertificate (fun q : ℕ × (M.Config × FiniteState M r) => eval q.2.1 p q.1 q.2.2)
      (runInputEncoding enc) (encOption enc.value) :=
  post (runCertificate enc N p) (outputCertificate enc).computes

@[simp] theorem evalCertificate_time (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) : (evalCertificate enc N p).time = runTime enc N p := rfl

@[simp] theorem evalCertificate_space (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) : (evalCertificate enc N p).space = runSpace enc N p := rfl

/-- Native `ComputableInO` theorem for clocked output evaluation. -/
theorem eval_inO (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) :
    ComputableInO (fun q : ℕ × (M.Config × FiniteState M r) => eval q.2.1 p q.1 q.2.2)
      (runInputEncoding enc) (encOption enc.value)
      (runTime enc N p) (runSpace enc N p) :=
  (evalCertificate enc N p).computes

/-! ### Retention of per-step resource bounds in `runTime` and `runSpace` -/

theorem le_roundCertificate_time_inl (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) (k : M.Config) (s : FiniteState M r) :
    stepTime enc N p (k, s) ≤ (roundCertificate enc N p).time (k, Option.some (.inl s)) := by
  simp only [stepTime, roundCertificate, stepResultCertificate, prod_time, congr_time,
    option_time, comp_time, continuing_inl, Option.elim_some, Function.comp_apply,
    fst_time, snd_time, linear_time]
  omega

theorem le_roundCertificate_space_inl (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) (k : M.Config) (s : FiniteState M r) :
    stepSpace enc N p (k, s) ≤ (roundCertificate enc N p).space (k, Option.some (.inl s)) := by
  simp only [stepSpace, roundCertificate, stepResultCertificate, prod_space, congr_space,
    option_space, comp_space, continuing_inl, Option.elim_some, Function.comp_apply,
    fst_space, snd_space, linear_space]
  omega

/-- Every continuing state reached within `j ≤ n` steps has its single-step time bound retained
in `runTime`. -/
theorem le_runTime_of_run_eq_inl (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) {n j : ℕ} {k : M.Config} {s t : FiniteState M r}
    (hj : j ≤ n) (hrun : run k p j s = Option.some (.inl t)) :
    stepTime enc N p (k, t) ≤ runTime enc N p (n, (k, s)) := by
  have h1 := le_roundCertificate_time_inl enc N p k t
  have h2 := le_maxRoundTime (roundCertificate enc N p) hj (k, Option.some (.inl s))
  rw [iterate_round_inl, hrun] at h2
  have h3 := le_trans h1 h2
  have h4 : maxRoundTime (roundCertificate enc N p) n (k, Option.some (.inl s)) ≤
      (n + 1) * (maxRoundTime (roundCertificate enc N p) n (k, Option.some (.inl s)) +
        maxStateLength (encPair enc.config (resultEncoding enc))
          (round p) n (k, Option.some (.inl s)) +
        ((encNat n).length + 1) ^ 2) :=
    le_trans (Nat.le_add_right _ _)
      (le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_left _ (Nat.succ_pos n)))
  simp only [runTime, runCertificate, congr_time, snd_time, iterate_time]
  omega

/-- Every continuing state reached within `j ≤ n` steps has its single-step space bound retained
in `runSpace`. -/
theorem le_runSpace_of_run_eq_inl (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) {n j : ℕ} {k : M.Config} {s t : FiniteState M r}
    (hj : j ≤ n) (hrun : run k p j s = Option.some (.inl t)) :
    stepSpace enc N p (k, t) ≤ runSpace enc N p (n, (k, s)) := by
  have h1 := le_roundCertificate_space_inl enc N p k t
  have h2 := le_maxRoundSpace (roundCertificate enc N p) hj (k, Option.some (.inl s))
  rw [iterate_round_inl, hrun] at h2
  have h3 := le_trans h1 h2
  simp only [runSpace, runCertificate, congr_space, snd_space, iterate_space]
  omega

/-! ### Automatic whole-run algorithm transport -/

theorem unoption_inO (ev : M.Value ↪ List Bool) :
    ComputableInO (fun o : Option M.Value => (encOption ev o).tail)
      (encOption ev) encBits
      (fun o => (encOption ev o).length) (fun o => (encOption ev o).length) := by
  have hraw : ComputableInDegree (fun o : Option M.Value => encOption ev o)
      (encOption ev) encBits 1 1 := .of_eq fun _ => rfl
  exact ((ComputableInDegree.tail (enc₁ := encBool) (enc := encBits)).comp hraw).inO_one

/-- Transport a halting generic-RAM execution certificate (`GenericRAM.Executes`) within `steps a`
instructions to a native multitape Turing-machine certificate for `f : α → M.Value`.
No `[Inhabited M.Value]` or polynomiality assumption is required. -/
def transportCertificate (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r)
    {f : α → M.Value} {cfg : α → M.Config} {initState : α → FiniteState M r}
    {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (encoding enc))
    (hExec : ∀ a, ∃ m ≤ steps a,
      GenericRAM.Executes (cfg a) p (initState a).denote (f a) m) :
    NativeCertificate f ei enc.value :=
  let cEval := (evalCertificate enc N p).comp (prod cSteps (prod cCfg cInit))
  let cTail := post cEval (unoption_inO enc.value)
  ⟨cTail.time, cTail.space, cTail.computes.of_enc_eq fun a => by
    obtain ⟨m, hm, hex⟩ := hExec a
    have hev := eval_eq_some_of_executes hex hm
    simp [Function.comp_apply, hev]⟩

@[simp] theorem transportCertificate_time (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) {f : α → M.Value} {cfg : α → M.Config}
    {initState : α → FiniteState M r} {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (encoding enc))
    (hExec : ∀ a, ∃ m ≤ steps a,
      GenericRAM.Executes (cfg a) p (initState a).denote (f a) m) (a : α) :
    (transportCertificate enc N p cSteps cCfg cInit hExec).time a =
      cSteps.time a + (cCfg.time a + cInit.time a) +
        runTime enc N p (steps a, (cfg a, initState a)) := rfl

@[simp] theorem transportCertificate_space (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) {f : α → M.Value} {cfg : α → M.Config}
    {initState : α → FiniteState M r} {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (encoding enc))
    (hExec : ∀ a, ∃ m ≤ steps a,
      GenericRAM.Executes (cfg a) p (initState a).denote (f a) m) (a : α) :
    (transportCertificate enc N p cSteps cCfg cInit hExec).space a =
      cSteps.space a + (cCfg.space a + cInit.space a) +
        runSpace enc N p (steps a, (cfg a, initState a)) := rfl

/-- Parameterized `ComputableInO` transport theorem from `GenericRAM.Executes`. -/
theorem transport_inO (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r)
    {f : α → M.Value} {cfg : α → M.Config} {initState : α → FiniteState M r}
    {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (encoding enc))
    (hExec : ∀ a, ∃ m ≤ steps a,
      GenericRAM.Executes (cfg a) p (initState a).denote (f a) m) :
    ComputableInO f ei enc.value
      (fun a => cSteps.time a + (cCfg.time a + cInit.time a) +
        runTime enc N p (steps a, (cfg a, initState a)))
      (fun a => cSteps.space a + (cCfg.space a + cInit.space a) +
        runSpace enc N p (steps a, (cfg a, initState a))) :=
  (transportCertificate enc N p cSteps cCfg cInit hExec).computes

/-! ### Polynomiality of single steps, rounds, and whole runs -/

namespace Native

variable {s : α → FiniteState M r} {k : α → M.Config} {v : α → M.Value}

theorem fields_isPolynomial (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    (hc : c.IsPolynomial) : (fields enc c).IsPolynomial := hc

theorem register_isPolynomial (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    (i : Fin r) (hc : c.IsPolynomial) : (register enc c i).IsPolynomial := hc

theorem operands_isPolynomial (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    {n : ℕ} (args : Fin n → Fin r) (hc : c.IsPolynomial) :
    (operands enc c args).IsPolynomial := hc

theorem setCertificate_isPolynomial (enc : M.Encoding)
    (c : NativeCertificate s ei (encoding enc)) (d : Fin r)
    (value : NativeCertificate v ei enc.value)
    (hc : c.IsPolynomial) (hv : value.IsPolynomial) :
    (setCertificate enc c d value).IsPolynomial :=
  prod_isPolynomial _ _ hc (prod_isPolynomial _ _ (prod_isPolynomial _ _ hc hv) hc)

theorem moveCertificate_isPolynomial (enc : M.Encoding) (N : M.NativePrimitives enc)
    (config : NativeCertificate k ei enc.config) (c : NativeCertificate s ei (encoding enc))
    (d : Fin r) (value : NativeCertificate v ei enc.value)
    (hN : N.IsPolynomial) (hk : config.IsPolynomial) (hc : c.IsPolynomial)
    (hv : value.IsPolynomial) :
    (moveCertificate enc N config c d value).IsPolynomial :=
  branch_isPolynomial _ _ _
    (comp_isPolynomial N.validMove (prod config value) hN.validMove (prod_isPolynomial _ _ hk hv))
    (setCertificate_isPolynomial enc c d value hc hv)
    (const_isPolynomial none)

theorem readCertificate_isPolynomial (enc : M.Encoding)
    (c : NativeCertificate s ei (encoding enc))
    {a : α → M.Address} (address : NativeCertificate a ei enc.address)
    (hc : c.IsPolynomial) (ha : address.IsPolynomial) :
    (readCertificate enc c address).IsPolynomial := by
  have hread : (⟨SparseMemory.readTime enc.address enc.value,
      SparseMemory.readSpace enc.address enc.value,
      SparseMemory.read_inO enc.address enc.value⟩ :
        NativeCertificate _ _ _).IsPolynomial := by
    refine ⟨.of_forall_le 32 3 fun q => ?_, .of_forall_le 32 1 fun q => ?_⟩
    · have hq : (SparseMemory.queryEncoding enc.address enc.value q.1).length ≤
          (SparseMemory.readEncoding enc.address enc.value q).length := by
        simp only [SparseMemory.readEncoding, length_encPair]; omega
      have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 3
      have ht := SparseMemory.scanTime_le_cube enc.address enc.value q.1
      have he : (SparseMemory.readEncoding enc.address enc.value q).length ≤
          ((SparseMemory.readEncoding enc.address enc.value q).length + 1) ^ 3 := by
        ring_nf; omega
      unfold SparseMemory.readTime
      nlinarith
    · have hs := SparseMemory.scanSpace_le_linear enc.address enc.value q.1
      simp only [SparseMemory.readSpace, SparseMemory.readEncoding,
        length_encPair, pow_one] at hs ⊢
      omega
  exact comp_isPolynomial _
    (prod (prod address (snd (snd (snd (fields enc c))))) (fst (snd (snd (fields enc c)))))
    hread (prod_isPolynomial _ _ (prod_isPolynomial _ _ ha hc) hc)

theorem writeCertificate_isPolynomial (enc : M.Encoding)
    (c : NativeCertificate s ei (encoding enc))
    {a : α → M.Address} (address : NativeCertificate a ei enc.address)
    (value : NativeCertificate v ei enc.value)
    (hc : c.IsPolynomial) (ha : address.IsPolynomial) (hv : value.IsPolynomial) :
    (writeCertificate enc c address value).IsPolynomial := by
  have hwrite : (⟨SparseMemory.writeTime enc.address enc.value,
      SparseMemory.writeSpace enc.address enc.value,
      SparseMemory.insert_inO enc.address enc.value⟩ :
        NativeCertificate _ _ _).IsPolynomial := by
    refine ⟨.of_forall_le 33 3 fun q => ?_, .of_forall_le 33 1 fun q => ?_⟩
    · have hq : (SparseMemory.queryEncoding enc.address enc.value (q.1.1, q.2)).length ≤
          (SparseMemory.writeEncoding enc.address enc.value q).length := by
        simp only [SparseMemory.queryEncoding, SparseMemory.writeEncoding, length_encPair]
        omega
      have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 3
      have ht := SparseMemory.scanTime_le_cube enc.address enc.value (q.1.1, q.2)
      have he : (SparseMemory.writeEncoding enc.address enc.value q).length ≤
          ((SparseMemory.writeEncoding enc.address enc.value q).length + 1) ^ 3 := by
        ring_nf; omega
      unfold SparseMemory.writeTime
      nlinarith
    · have hs := SparseMemory.scanSpace_le_linear enc.address enc.value (q.1.1, q.2)
      simp only [SparseMemory.writeSpace, SparseMemory.queryEncoding,
        SparseMemory.writeEncoding, length_encPair, pow_one] at hs ⊢
      omega
  have hmem := comp_isPolynomial _
    (prod (prod address value) (snd (snd (snd (fields enc c)))))
    hwrite (prod_isPolynomial _ _ (prod_isPolynomial _ _ ha hv) hc)
  exact prod_isPolynomial (fst (fields enc c)) _ hc
    (prod_isPolynomial (fst (snd (fields enc c))) _ hc
      (prod_isPolynomial (fst (snd (snd (fields enc c)))) _ hc hmem))

theorem evalOpCertificate_isPolynomial (enc : M.Encoding)
    (N : M.NativePrimitives enc) (config : NativeCertificate k ei enc.config)
    (c : NativeCertificate s ei (encoding enc)) (o : Op M r)
    (hN : N.IsPolynomial) (hk : config.IsPolynomial) (hc : c.IsPolynomial) :
    (evalOpCertificate enc N config c o).IsPolynomial := by
  cases o with
  | const d literal =>
    exact option_isPolynomial _ _ _
      (comp_isPolynomial _ _ (hN.constant literal) hk)
      (const_isPolynomial none)
      (setCertificate_isPolynomial enc _ d _
        (pull_isPolynomial c enc.value hc) (payload_isPolynomial ei enc.value))
  | copy d src =>
    exact moveCertificate_isPolynomial enc N config c d (register enc c src) hN hk hc hc
  | alu op d args =>
    exact option_isPolynomial _ _ _
      (comp_isPolynomial _ _ (hN.operation op) (prod_isPolynomial _ _ hk hc))
      (const_isPolynomial none)
      (setCertificate_isPolynomial enc _ d _
        (pull_isPolynomial c enc.value hc) (payload_isPolynomial ei enc.value))
  | load d a =>
    have hpullC := pull_isPolynomial c enc.address hc
    have hpullK := pull_isPolynomial config enc.address hk
    have hpay := payload_isPolynomial ei enc.address
    exact option_isPolynomial _ _ _
      (comp_isPolynomial _ _ hN.address (prod_isPolynomial _ _ hk hc))
      (const_isPolynomial none)
      (moveCertificate_isPolynomial enc N _ _ d _ hN hpullK hpullC
        (readCertificate_isPolynomial enc _ _ hpullC hpay))
  | store a src =>
    have hpullC := pull_isPolynomial c enc.address hc
    have hpullK := pull_isPolynomial config enc.address hk
    have hpay := payload_isPolynomial ei enc.address
    exact option_isPolynomial _ _ _
      (comp_isPolynomial _ _ hN.address (prod_isPolynomial _ _ hk hc))
      (const_isPolynomial none)
      (branch_isPolynomial _ _ _
        (comp_isPolynomial _ _ hN.validMove (prod_isPolynomial _ _ hpullK hpullC))
        (writeCertificate_isPolynomial enc _ _ _ hpullC hpay hpullC)
        (const_isPolynomial none))

theorem resumeCertificate_isPolynomial (enc : M.Encoding) (N : M.NativePrimitives enc)
    (config : NativeCertificate k ei enc.config) (c : NativeCertificate s ei (encoding enc))
    (pc : ℕ) (hN : N.IsPolynomial) (hk : config.IsPolynomial) (hc : c.IsPolynomial) :
    (resumeCertificate enc N config c pc).IsPolynomial :=
  branch_isPolynomial _ _ _
    (comp_isPolynomial _ _ hN.validPC (prod_isPolynomial _ _ hk (const_isPolynomial pc)))
    (prod_isPolynomial _ _ (const_isPolynomial pc) hc)
    (const_isPolynomial none)

theorem evalInstrCertificate_isPolynomial (enc : M.Encoding)
    (N : M.NativePrimitives enc) (config : NativeCertificate k ei enc.config)
    (c : NativeCertificate s ei (encoding enc)) (nextPC : ℕ) (i : Instr M r)
    (hN : N.IsPolynomial) (hk : config.IsPolynomial) (hc : c.IsPolynomial) :
    (evalInstrCertificate enc N config c nextPC i).IsPolynomial := by
  cases i with
  | op o =>
    exact option_isPolynomial _ _ _
      (evalOpCertificate_isPolynomial enc N config c o hN hk hc)
      (const_isPolynomial none)
      (resumeCertificate_isPolynomial enc N _ _ nextPC hN
        (pull_isPolynomial config (encoding enc) hk)
        (payload_isPolynomial ei (encoding enc)))
  | jump target =>
    exact resumeCertificate_isPolynomial enc N config c target hN hk hc
  | branch test target =>
    cases test with
    | test f args =>
      have hpullK := pull_isPolynomial config encBool hk
      have hpullC := pull_isPolynomial c encBool hc
      exact option_isPolynomial _ _ _
        (comp_isPolynomial _ _ (hN.test f) (prod_isPolynomial _ _ hk hc))
        (const_isPolynomial none)
        (branch_isPolynomial _ _ _
          (payload_isPolynomial ei encBool)
          (resumeCertificate_isPolynomial enc N _ _ target hN hpullK hpullC)
          (resumeCertificate_isPolynomial enc N _ _ nextPC hN hpullK hpullC))
  | halt idx =>
    exact branch_isPolynomial _ _ _
      (comp_isPolynomial _ _ hN.validMove (prod_isPolynomial _ _ hk hc))
      hc
      (const_isPolynomial none)

theorem pcEquals_isPolynomial (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    (pc : ℕ) (hc : c.IsPolynomial) :
    (pcEquals enc c pc).IsPolynomial := by
  have heq : (⟨fun p : ℕ × ℕ => ((encNat p.1).length + 1) *
      ((encNat p.1).length + (encNat p.2).length + 1),
    fun p : ℕ × ℕ => (encPair encNat encNat p).length,
    ComputableInO.eq encNat⟩ : NativeCertificate _ _ _).IsPolynomial := by
    refine ⟨.of_forall_le 1 2 fun p => ?_, .self⟩
    simp only [length_encPair]
    nlinarith
  exact comp_isPolynomial _ _ heq (prod_isPolynomial _ _ hc (const_isPolynomial pc))

theorem dispatchCertificate_isPolynomial (enc : M.Encoding)
    (N : M.NativePrimitives enc) (config : NativeCertificate k ei enc.config)
    (c : NativeCertificate s ei (encoding enc)) (p : Program M r) (pc : ℕ)
    (hN : N.IsPolynomial) (hk : config.IsPolynomial) (hc : c.IsPolynomial) :
    (dispatchCertificate enc N config c p pc).IsPolynomial := by
  induction p generalizing pc with
  | nil => exact const_isPolynomial none
  | cons i p ih =>
    exact branch_isPolynomial _ _ _
      (pcEquals_isPolynomial enc c pc hc)
      (evalInstrCertificate_isPolynomial enc N config c (pc + 1) i hN hk hc)
      (ih (pc + 1))

end Native

/-- When all scalar primitive certificates are polynomial, `stepCertificate` is polynomial. -/
theorem stepCertificate_isPolynomial (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) (hN : N.IsPolynomial) :
    (stepCertificate enc N p).IsPolynomial :=
  branch_isPolynomial _ _ _
    (comp_isPolynomial _ _ hN.validPC
      (prod_isPolynomial _ _ ⟨.self, .self⟩ ⟨.self, .self⟩))
    (Native.dispatchCertificate_isPolynomial enc N _ _ p 0 hN ⟨.self, .self⟩ ⟨.self, .self⟩)
    (const_isPolynomial none)

/-- When all scalar primitive certificates are polynomial, the encoded single-step transition of
any fixed program is computable in polynomial time. -/
theorem step_polyTime (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) (hN : N.IsPolynomial) :
    ComputableInPolyTime (fun q : M.Config × FiniteState M r => step q.1 p q.2)
      (inputEncoding enc) (resultEncoding enc) :=
  (stepCertificate enc N p).polyTime (stepCertificate_isPolynomial enc N p hN)

/-- When all scalar primitive certificates are polynomial, `roundCertificate` is polynomial. -/
theorem roundCertificate_isPolynomial (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) (hN : N.IsPolynomial) :
    (roundCertificate enc N p).IsPolynomial := by
  have hstep := stepCertificate_isPolynomial enc N p hN
  have hres : (stepResultCertificate enc N p).IsPolynomial :=
    option_isPolynomial _ _ _
      (comp_isPolynomial _ _ ⟨.self, .self⟩ ⟨.self, .self⟩)
      ⟨.self, .self⟩
      (comp_isPolynomial _ _ hstep (prod_isPolynomial _ _ ⟨.self, .self⟩ ⟨.self, .self⟩))
  exact prod_isPolynomial _ _ ⟨.self, .self⟩ hres

theorem initCertificate_isPolynomial (enc : M.Encoding)
    {regsFn : α → Fin r → M.Value} {defaultFn : α → M.Value}
    {memoryFn : α → SparseMemory M.Address M.Value}
    (regs : NativeCertificate regsFn ei (encPi enc.value))
    (default : NativeCertificate defaultFn ei enc.value)
    (memory : NativeCertificate memoryFn ei (SparseMemory.encoding enc.address enc.value))
    (hregs : regs.IsPolynomial) (hdef : default.IsPolynomial) (hmem : memory.IsPolynomial) :
    (initCertificate enc regs default memory).IsPolynomial :=
  prod_isPolynomial _ _ (const_isPolynomial 0)
    (prod_isPolynomial _ _ hregs (prod_isPolynomial _ _ hdef hmem))

theorem constRegsCertificate_isPolynomial (enc : M.Encoding) {initRegFn : α → M.Value}
    (initReg : NativeCertificate initRegFn ei enc.value) (hreg : initReg.IsPolynomial) :
    (constRegsCertificate (r := r) enc initReg).IsPolynomial := by
  refine ⟨.add .self ?_, .add .self ?_⟩
  · simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using
      (PolyBounded.const r).mul hreg.1
  · simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using
      (PolyBounded.const r).mul hreg.2

theorem initConstCertificate_isPolynomial (enc : M.Encoding)
    {initRegFn defaultFn : α → M.Value}
    {memoryFn : α → SparseMemory M.Address M.Value}
    (initReg : NativeCertificate initRegFn ei enc.value)
    (default : NativeCertificate defaultFn ei enc.value)
    (memory : NativeCertificate memoryFn ei (SparseMemory.encoding enc.address enc.value))
    (hreg : initReg.IsPolynomial) (hdef : default.IsPolynomial) (hmem : memory.IsPolynomial) :
    (initConstCertificate (r := r) enc initReg default memory).IsPolynomial :=
  initCertificate_isPolynomial enc _ default memory
    (constRegsCertificate_isPolynomial enc initReg hreg) hdef hmem

/-- Polynomial-time whole-run transport: if scalar primitives, step-budget certificate,
configuration certificate, and initial-state certificate are polynomial, the step budget `steps a`
is polynomially bounded, and the encoded outcomes along `0 ≤ j ≤ steps a` are bounded by a
polynomially bounded function `B`, then the transported certificate is polynomial. -/
theorem transportCertificate_isPolynomial (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) {f : α → M.Value} {cfg : α → M.Config}
    {initState : α → FiniteState M r} {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (encoding enc))
    (hExec : ∀ a, ∃ m ≤ steps a,
      GenericRAM.Executes (cfg a) p (initState a).denote (f a) m)
    (hN : N.IsPolynomial)
    (hSteps : cSteps.IsPolynomial) (hCfg : cCfg.IsPolynomial) (hInit : cInit.IsPolynomial)
    (hStepsBound : PolyBounded (fun a => (ei a).length) steps)
    {B : α → ℕ} (hB : PolyBounded (fun a => (ei a).length) B)
    (hOutLen : ∀ a, ∀ j ≤ steps a,
      (resultEncoding enc (run (cfg a) p j (initState a))).length ≤ B a) :
    (transportCertificate enc N p cSteps cCfg cInit hExec).IsPolynomial := by
  have hIter : (iterate cSteps (prod cCfg (some (inl cInit enc.value)))
      (roundCertificate enc N p)).IsPolynomial :=
    iterate_isPolynomial cSteps _ (roundCertificate enc N p)
      hSteps (prod_isPolynomial _ _ hCfg (some_isPolynomial _ (inl_isPolynomial _ _ hInit)))
      (roundCertificate_isPolynomial enc N p hN) hStepsBound
      ((((PolyBounded.const 2).mul (cCfg.polyTime hCfg).polyBounded_length).add (.const 1)).add hB)
      fun a j hj => by
        rw [iterate_round_inl]
        have := hOutLen a j hj
        simp only [loopEncoding, length_encPair]
        omega
  have hInLen : PolyBounded (fun a => (ei a).length)
      (fun a => (runInputEncoding enc (steps a, (cfg a, initState a))).length) :=
    ((prod cSteps (prod cCfg cInit)).polyTime
      (prod_isPolynomial _ _ hSteps (prod_isPolynomial _ _ hCfg hInit))).polyBounded_length
  refine ⟨(hIter.1.add ((PolyBounded.const 3).mul hInLen)).mono fun a => ?_,
    (hIter.2.add ((PolyBounded.const 3).mul hInLen)).mono fun a => ?_⟩
  · simp only [transportCertificate_time, runTime, runCertificate, congr_time, snd_time,
      iterate_time, initLoopCertificate, prod_time, fst_time, snd_time, some_time, inl_time,
      linear_time, resultEncoding]
    omega
  · simp only [transportCertificate_space, runSpace, runCertificate, congr_space, snd_space,
      iterate_space, initLoopCertificate, prod_space, fst_space, snd_space, some_space, inl_space,
      linear_space, resultEncoding]
    omega

/-- Automatic `ComputableInPolyTime` transport corollary from `GenericRAM.Executes`. -/
theorem transport_polyTime (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) {f : α → M.Value} {cfg : α → M.Config}
    {initState : α → FiniteState M r} {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (encoding enc))
    (hExec : ∀ a, ∃ m ≤ steps a,
      GenericRAM.Executes (cfg a) p (initState a).denote (f a) m)
    (hN : N.IsPolynomial)
    (hSteps : cSteps.IsPolynomial) (hCfg : cCfg.IsPolynomial) (hInit : cInit.IsPolynomial)
    (hStepsBound : PolyBounded (fun a => (ei a).length) steps)
    {B : α → ℕ} (hB : PolyBounded (fun a => (ei a).length) B)
    (hOutLen : ∀ a, ∀ j ≤ steps a,
      (resultEncoding enc (run (cfg a) p j (initState a))).length ≤ B a) :
    ComputableInPolyTime f ei enc.value :=
  (transportCertificate enc N p cSteps cCfg cInit hExec).polyTime
    (transportCertificate_isPolynomial enc N p cSteps cCfg cInit hExec
      hN hSteps hCfg hInit hStepsBound hB hOutLen)

/-- Iterating `roundCertificate` a fixed number of rounds `j` yields a certificate for the `j`-th
loop state. -/
def roundIterCertificate (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r)
    {cfg : α → M.Config} {initState : α → FiniteState M r}
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (encoding enc)) : (j : ℕ) →
    NativeCertificate
      (fun a => (round p)^[j] (cfg a, Option.some (.inl (initState a))))
      ei (loopEncoding enc)
  | 0 => prod cCfg (some (inl cInit enc.value))
  | j + 1 =>
    ((roundCertificate enc N p).comp
      (roundIterCertificate enc N p cCfg cInit j)).congr fun _ =>
        (Function.iterate_succ_apply' _ _ _).symm

theorem roundIterCertificate_isPolynomial (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) {cfg : α → M.Config} {initState : α → FiniteState M r}
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (encoding enc))
    (hN : N.IsPolynomial) (hCfg : cCfg.IsPolynomial) (hInit : cInit.IsPolynomial) :
    ∀ j : ℕ, (roundIterCertificate enc N p cCfg cInit j).IsPolynomial
  | 0 => prod_isPolynomial _ _ hCfg (some_isPolynomial _ (inl_isPolynomial _ _ hInit))
  | j + 1 =>
    congr_isPolynomial _ _
      (comp_isPolynomial _ _ (roundCertificate_isPolynomial enc N p hN)
        (roundIterCertificate_isPolynomial enc N p cCfg cInit hN hCfg hInit j))

theorem polyBounded_length_run (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) {cfg : α → M.Config} {initState : α → FiniteState M r}
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (encoding enc))
    (hN : N.IsPolynomial) (hCfg : cCfg.IsPolynomial) (hInit : cInit.IsPolynomial) (j : ℕ) :
    PolyBounded (fun a => (ei a).length)
      (fun a => (resultEncoding enc (run (cfg a) p j (initState a))).length) := by
  have hloop := ((roundIterCertificate enc N p cCfg cInit j).polyTime
    (roundIterCertificate_isPolynomial enc N p cCfg cInit hN hCfg hInit j)).polyBounded_length
  refine hloop.mono fun a => ?_
  rw [iterate_round_inl]
  simp only [loopEncoding, length_encPair]
  omega

/-- Automatic `ComputableInPolyTime` transport for a constant step-budget bound
`∀ a, steps a ≤ K`: the intermediate outcome lengths along `0 ≤ j ≤ K` are bounded by induction on
`K` using `roundCertificate_isPolynomial`. -/
theorem transport_polyTime_of_le_const (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) {f : α → M.Value} {cfg : α → M.Config}
    {initState : α → FiniteState M r} {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (encoding enc))
    (hExec : ∀ a, ∃ m ≤ steps a,
      GenericRAM.Executes (cfg a) p (initState a).denote (f a) m)
    (hN : N.IsPolynomial)
    (hSteps : cSteps.IsPolynomial) (hCfg : cCfg.IsPolynomial) (hInit : cInit.IsPolynomial)
    (K : ℕ) (hStepsLe : ∀ a, steps a ≤ K) :
    ComputableInPolyTime f ei enc.value := by
  have hSum : ∀ n : ℕ, PolyBounded (fun a => (ei a).length)
      (fun a => ∑ j ∈ Finset.range n,
        (resultEncoding enc (run (cfg a) p j (initState a))).length) := by
    intro n
    induction n with
    | zero =>
      simpa only [Finset.range_zero, Finset.sum_empty] using PolyBounded.const 0
    | succ n ih =>
      simpa only [Finset.sum_range_succ] using
        ih.add (polyBounded_length_run enc N p cCfg cInit hN hCfg hInit n)
  exact transport_polyTime enc N p cSteps cCfg cInit hExec hN hSteps hCfg hInit
    ((PolyBounded.const K).mono hStepsLe) (hSum (K + 1)) fun a j hj =>
      Finset.single_le_sum
        (f := fun i => (resultEncoding enc (run (cfg a) p i (initState a))).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by have := hStepsLe a; omega))

end FiniteState
end Cslib.GenericRAM

end
