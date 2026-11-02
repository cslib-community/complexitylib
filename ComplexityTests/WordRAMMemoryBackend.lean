/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: candidate

import Complexity.Computability.WordRAM.Realization.MemoryBackend

/-! The operation-level backend composes through the existing generic semantics. These examples
exercise reply-dependent addresses, full-memory retention, body-only costs and zero-width empty
allocation. Argument delivery and client control are not charged by this backend. -/

open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

namespace ComplexityTests.WordRAMMemoryBackend

open MemoryBackend

-- The backend plugs into the existing semantic module projection without changing that API.
noncomputable example {D : StateTransitionSpec} (w : ℕ)
    (M : DataStructure.Module D (Memory.spec w)) :
    StateTransitionImpl D (fun x o a y ts => DataStructure.Executes (exec w)
      (M.methods o) x a y ts) := M.realize (implementation w)

-- Every actual native execution from the prepared state has the specified typed result and
-- full-memory post-state, even when that execution was not obtained from `total`.
example {w n : ℕ} {s : Memory.State} {x y : Data registers} {o : Memory.Op}
    (hr : memoryState frontier x = s ∧ x.Bounded w) (hv : Memory.valid w s o)
    (he : Exec w (body o) (prepare o x) y n) :
    result o y = (Memory.step s o).2 ∧ memoryState frontier y = (Memory.step s o).1 ∧
      n ≤ factor * (Memory.charge s o + 1) := by
  have hr' := (rep_iff w s x).mpr hr
  have he' := (exec_iff w x y o (result o y) n).mpr ⟨he, rfl⟩
  obtain ⟨ha, hs⟩ := (implementation w).correct_ofFn hr' hv he'
  exact ⟨ha, ((rep_iff w _ _).mp hs).1, instruction_bound w hr' hv he'⟩

private def client : Memory.Prog ℕ := do
  let base ← Memory.alloc 2
  Memory.write base 7
  Memory.read base

private noncomputable def initial : Data registers := ⟨fun _ => 3, fun _ => 9⟩

private theorem initial_bounded : initial.Bounded 4 := by
  constructor
  · intro i; change Fits 4 3; decide
  · intro a; change Fits 4 9; decide

private theorem initial_valid :
    (Memory.spec 4).ValidHistory (memoryState frontier initial)
      ((Memory.spec 4).clientHistory (memoryState frontier initial) client) := by
  change Fits 4 (3 + 2) ∧ (3 < 3 + 2 ∧ Fits 4 7) ∧ 3 < 3 + 2 ∧ True
  decide

-- Allocation's answer determines both later query addresses. The backend retains inaccessible
-- cells as well as the frontier, and exposes the actual three native instruction-count traces.
example : ∃ y ts, DataStructure.Executes (exec 4) client initial 7 y ts ∧
    (memoryState frontier y).frontier = 5 ∧ y.mem 3 = 7 ∧ y.mem 10 = 9 ∧
    DataStructure.total id ts ≤ factor * 8 := by
  have hr := (rep_iff 4 _ initial).mpr ⟨rfl, initial_bounded⟩
  obtain ⟨y, ts, he, hy⟩ := (implementation 4).exists_executes client hr initial_valid
  have hb := DataStructure.Bound.client (instruction_bound 4) hr initial_valid he
  obtain ⟨hm, _⟩ := (rep_iff 4 _ y).mp hy
  refine ⟨y, ts, he, ?_, ?_, ?_, ?_⟩
  · exact congrArg Memory.State.frontier hm
  · exact congrArg (fun s : Memory.State => s.mem 3) hm
  · change (memoryState frontier y).mem 10 = 9
    have hc := congrArg (fun s : Memory.State => s.mem 10) hm
    simpa [StateTransitionSpec.clientState, StateTransitionSpec.runClient, client,
      Memory.step, memoryState, initial, clear, Block.Owns] using hc
  · change DataStructure.total id ts ≤ factor * 4 + (factor * 2 + (factor * 2 + 0)) at hb
    omega

private noncomputable def zeroState : Data registers := ⟨fun _ => 0, fun _ => 0⟩

private theorem zero_rep :
    (implementation 0).rep (memoryState frontier zeroState) zeroState := by
  apply (rep_iff 0 _ _).mpr
  refine ⟨rfl, ?_, ?_⟩ <;> intro i <;> exact fits_zero 0

-- Empty allocations remain valid at width zero, for both static allocation bodies.
example : ∃ y n, exec 0 zeroState (.alloc 0) 0 y n ∧
    memoryState frontier y = memoryState frontier zeroState := by
  obtain ⟨a, y, n, he⟩ := (implementation 0).total (.alloc 0) zero_rep (fits_zero 0)
  obtain ⟨ha, hr⟩ := (implementation 0).correct_ofFn (o := .alloc 0) zero_rep (fits_zero 0) he
  change a = 0 at ha
  subst a
  refine ⟨y, n, he, ?_⟩
  exact ((rep_iff 0 _ _).mp hr).1.trans (by
    apply Memory.State.ext
    · simp [Memory.step]
    · rfl)

example : ∃ y n, exec 0 zeroState (.allocDirty 0) 0 y n ∧
    memoryState frontier y = memoryState frontier zeroState := by
  obtain ⟨a, y, n, he⟩ := (implementation 0).total (.allocDirty 0) zero_rep (fits_zero 0)
  obtain ⟨ha, hr⟩ := (implementation 0).correct_ofFn (o := .allocDirty 0) zero_rep (fits_zero 0) he
  change a = 0 at ha
  subst a
  exact ⟨y, n, he, ((rep_iff 0 _ _).mp hr).1⟩

-- The four bodies are invariant under delivered argument values.
example (a v b u : ℕ) : body (.write a v) = body (.write b u) := body_write_eq a v b u

end ComplexityTests.WordRAMMemoryBackend
