/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Abstract

/-!
# Renaming pointer-machine data

A sortwise permutation commuting with the chosen primitives preserves execution.
Protected-symbol instances permit every permutation of symbols while fixing numerical data.
References and allocation identities are unchanged by this data renaming.
-/

public section

namespace Cslib.PointerMachine

variable {k : ℕ} {M : Model k} {L : Layout k}

/-- Permutations of data which preserve the fixed operation and predicate interpretations. -/
structure Model.Renaming (M : Model k) where
  /-- Permute values within each sort. -/
  value : (t : Fin k) → M.Value t ≃ M.Value t
  /-- Primitive operations commute with the permutations, including failure. -/
  operation : ∀ {a b c} (f : M.Op a b c) (va : M.Value a) (vb : M.Value b),
    M.evalOp f (value a va) (value b vb) = (M.evalOp f va vb).map (value c)
  /-- Primitive predicates cannot observe the permutation. -/
  test : ∀ {a b} (f : M.Test a b) (va : M.Value a) (vb : M.Value b),
    M.evalTest f (value a va) (value b vb) = M.evalTest f va vb

/-- Rename data fields, retaining all pointers. -/
@[expose] def Node.rename (ρ : M.Renaming) (x : Node M L) : Node M L :=
  { x with data := Pi.map (fun t bank => Option.map (ρ.value t) ∘ bank) x.data }

/-- Rename all data without changing control, allocation, or pointers. -/
@[expose] def State.rename (ρ : M.Renaming) (x : State M L) : State M L :=
  { x with data := Pi.map (fun t bank => Option.map (ρ.value t) ∘ bank) x.data
           heap := Node.rename ρ ∘ x.heap }

/-- Renaming commutes with writing a typed register. -/
theorem State.rename_setData (ρ : M.Renaming) (x : State M L) {t : Fin k}
    (dst : Fin (L.dataRegs t)) (v : M.Value t) :
    (x.setData dst v).rename ρ = (x.rename ρ).setData dst (ρ.value t v) := by
  simp [State.setData, State.rename, Pi.map_update, Function.comp_update]

/-- Renaming commutes with writing a typed field. -/
theorem Node.rename_setData (ρ : M.Renaming) (x : Node M L) {t : Fin k}
    (f : Fin (L.dataFields t)) (v : M.Value t) :
    (x.setData f v).rename ρ = (x.rename ρ).setData f (ρ.value t v) := by
  simp [Node.setData, Node.rename, Pi.map_update, Function.comp_update]

/-- Renaming does not change a record's reference fields. -/
@[simp] theorem Node.rename_ptr (ρ : M.Renaming) (x : Node M L) :
    (x.rename ρ).ptr = x.ptr := rfl

/-- Data fields are renamed within their declared sorts. -/
@[simp] theorem Node.rename_data (ρ : M.Renaming) (x : Node M L) (t : Fin k)
    (f : Fin (L.dataFields t)) :
    (x.rename ρ).data t f = (x.data t f).map (ρ.value t) := rfl

/-- Undefined fields remain undefined under renaming. -/
@[simp] theorem Node.rename_empty (ρ : M.Renaming) :
    (Node.empty : Node M L).rename ρ = .empty := rfl

/-- Instructions commute with data renaming, including undefined operands and failure. -/
theorem Instr.eval_rename (ρ : M.Renaming) (i : Instr M L) (x : State M L) :
    i.eval (x.rename ρ) = (i.eval x).map (State.rename ρ) := by
  cases i <;>
    simp only [bind, pure, Option.map_some, Option.map_none,
      Equiv.apply_eq_iff_eq, Instr.eval, State.access, State.address, State.rename,
      State.setData, State.fresh, Node.rename_ptr, Node.rename_data,
      Node.rename_empty, Option.bind_map, Option.map_bind,
      Pi.map_update, Function.comp_update, Function.comp_apply, Pi.map_apply,
      ρ.operation, ρ.test]
  all_goals congr 1
  all_goals funext a
  all_goals cases a <;>
    simp only [State.rename, Option.map_bind, Option.map_some,
      Pi.map_update, Function.comp_update, Function.comp_apply, Node.rename_setData]
  all_goals rfl

/-- Renaming preserves the control label. -/
@[simp] theorem State.rename_pc (ρ : M.Renaming) (x : State M L) :
    (x.rename ρ).pc = x.pc := rfl

/-- Renaming preserves allocated space. -/
@[simp] theorem State.rename_size (ρ : M.Renaming) (x : State M L) :
    (x.rename ρ).size = x.size := rfl

/-- Rename a continuing state; halting and failure are unchanged. -/
@[expose] def Outcome.rename (ρ : M.Renaming) : Outcome M L → Outcome M L
  | .next x => .next (x.rename ρ)
  | .halt => .halt
  | .fault => .fault

/-- Every program step commutes with data renaming. -/
theorem step_rename (ρ : M.Renaming) (code : List (Instr M L)) (x : State M L) :
    step code (x.rename ρ) = (step code x).rename ρ := by
  unfold step
  simp only [State.rename_pc]
  split
  · rfl
  · rfl
  · next i _ _ =>
      rw [Instr.eval_rename]
      cases i.eval x <;> rfl

/-- Renaming changes neither a run's control flow nor its instruction count. -/
theorem Runs.rename (ρ : M.Renaming) {code : List (Instr M L)}
    {x y : State M L} {n : ℕ} (h : Runs code x y n) :
    Runs code (x.rename ρ) (y.rename ρ) n := by
  induction h with
  | refl => exact .refl _
  | tail _ _ _ _ hxy ih =>
    apply Relation.RelatesInSteps.tail _ _ _ _ ih
    rw [step_rename, hxy]
    rfl

/-- Successful executions are invariant under compatible data renamings, with the same cost. -/
theorem Executes.rename (ρ : M.Renaming) {code : List (Instr M L)}
    {x y : State M L} {n : ℕ} (h : Executes code x y n) :
    Executes code (x.rename ρ) (y.rename ρ) n := by
  obtain ⟨m, hr, hh, hn⟩ := h
  refine ⟨m, hr.rename ρ, ?_, hn⟩
  rw [step_rename, hh]
  rfl

end Cslib.PointerMachine
