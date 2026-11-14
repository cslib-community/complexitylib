/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Abstract

/-!
# Pointer-machine invariants

Validity, pointer provenance, allocation freshness, determinism and the space bound.
The model itself is defined in `Abstract`.
-/

public section

namespace Cslib.PointerMachine

variable {k : ℕ} {M : Model k} {L : Layout k}

/-- Empty states satisfy allocated-pointer validity. -/
theorem State.empty_valid : (State.empty : State M L).Valid := by
  simp [State.Valid, State.empty, Node.empty]

/-- A resolved nonnull address comes from the base register and is allocated. -/
theorem State.address_eq_some {x : State M L} {i : Fin L.ptrRegs} {a : NodeId} :
    x.address i = some (some a) ↔ x.ptr i = some (.node a) ∧ x.Allocated a := by
  simp only [State.address, State.Allocated]
  split <;> simp_all [and_comm]

/-- Instructions preserve validity for every data interpretation. -/
theorem Instr.eval_valid {i : Instr M L} {x y : State M L}
    (hx : x.Valid) (h : i.eval x = some y) : y.Valid := by
  cases i <;> simp only [Instr.eval, State.access] at h
  all_goals repeat' first
    | simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    | obtain ⟨v, hv, h⟩ := h
    | split at h
    | cases h
  all_goals simp only [State.Valid, State.Allocated, State.setData, Node.setData] at hx ⊢
  all_goals try exact hx
  all_goals constructor
  all_goals first
    | (intro dst a ha
       try simp only [Function.update_apply] at ha
       try split_ifs at ha
       all_goals grind [State.address_eq_some, State.Allocated, State.fresh,
         NodeId.below_ofIndex, NodeId.below_succ])
    | (intro a ha f b hb
       try simp only [Function.update_apply] at hb
       try split_ifs at hb
       all_goals try simp only [Function.update_apply, Node.empty] at hb
       all_goals grind [State.address_eq_some, State.Allocated, State.fresh,
         NodeId.below_ofIndex, NodeId.below_succ])

/-- A continuing instruction allocates at most one record and never deallocates. -/
theorem Instr.eval_size {i : Instr M L} {x y : State M L}
    (h : i.eval x = some y) : x.size ≤ y.size ∧ y.size ≤ x.size + 1 := by
  cases i <;> simp only [Instr.eval, State.access] at h
  all_goals repeat' first
    | simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    | obtain ⟨v, hv, h⟩ := h
    | split at h
    | cases h
  all_goals dsimp only [State.setData]
  all_goals exact ⟨by omega, by omega⟩

/-- Every resulting register pointer comes from a register, a single existing edge from a
register, or fresh allocation, independently of the data basis. -/
theorem Instr.eval_provenance {i : Instr M L} {x y : State M L}
    (h : i.eval x = some y) {dst : Fin L.ptrRegs} {a : NodeId}
    (ha : y.ptr dst = some (.node a)) :
    (∃ src, x.ptr src = some (.node a)) ∨
    (∃ base b f, x.ptr base = some (.node b) ∧ x.Allocated b ∧
      (x.heap b).ptr f = some (.node a)) ∨
    (a = x.fresh ∧ y.size = x.size + 1) := by
  cases i <;> simp only [Instr.eval, State.access] at h
  all_goals repeat' first
    | simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    | obtain ⟨v, hv, h⟩ := h
    | split at h
    | cases h
  all_goals simp only [State.setData, Function.update_apply] at ha ⊢
  all_goals grind [State.address_eq_some, State.Allocated]

/-- The allocator returns a pointer outside the previous allocated pool. -/
theorem Instr.alloc_fresh {x y : State M L} {dst : Fin L.ptrRegs}
    (h : (Instr.alloc dst).eval x = some y) :
    y.ptr dst = some (.node x.fresh) ∧ ¬x.Allocated x.fresh := by
  simp only [Instr.eval, Option.some.injEq] at h
  subst y
  simp [Function.update_self, State.Allocated, State.fresh]

/-- A continuing program step is exactly evaluation of its current instruction. -/
theorem step_eq_next_iff {code : List (Instr M L)} {x y : State M L} :
    step code x = .next y ↔ ∃ i, code[x.pc]? = some i ∧ i.eval x = some y := by
  unfold step
  split
  · simp_all
  · simp_all [Instr.eval]
  · split <;> simp_all

/-- Program steps preserve allocated-pointer validity. -/
theorem step_valid {code : List (Instr M L)} {x y : State M L}
    (hx : x.Valid) (h : step code x = .next y) : y.Valid := by
  obtain ⟨i, _, hi⟩ := step_eq_next_iff.mp h
  exact i.eval_valid hx hi

/-- A program step allocates at most one record and never deallocates. -/
theorem step_size {code : List (Instr M L)} {x y : State M L}
    (h : step code x = .next y) : x.size ≤ y.size ∧ y.size ≤ x.size + 1 := by
  obtain ⟨i, _, hi⟩ := step_eq_next_iff.mp h
  exact i.eval_size hi

/-- All states of a run from a valid input have allocated pointers. -/
theorem Runs.valid {code : List (Instr M L)} {x y : State M L} {n : ℕ}
    (h : Runs code x y n) (hx : x.Valid) : y.Valid := by
  induction h with
  | refl => exact hx
  | tail _ _ _ _ hxy ih => exact step_valid ih hxy

/-- Space counts input records plus at most one new record per continuing instruction. -/
theorem Runs.size_le {code : List (Instr M L)} {x y : State M L} {n : ℕ}
    (h : Runs code x y n) : y.size ≤ x.size + n :=
  h.apply_le_apply_add State.size (fun _ _ hxy => (step_size hxy).2)

/-- Continuing execution is deterministic. -/
theorem step_deterministic {code : List (Instr M L)} {x y z : State M L}
    (hy : step code x = .next y) (hz : step code x = .next z) : y = z :=
  Outcome.next.inj (hy.symm.trans hz)


end Cslib.PointerMachine
