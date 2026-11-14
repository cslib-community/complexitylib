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

@[expose] public section

namespace Cslib.PointerMachine

variable {M : Model} {L : Layout}

/-- No records, null pointer registers and undefined data registers. -/
def State.empty : State M L := ⟨0, fun _ => none, fun _ => M.undefined, []⟩

/-- The empty state is valid. -/
theorem State.empty_valid : (State.empty : State M L).Valid := by
  simp [State.Valid, State.empty]

/-- A register specifies a record exactly when it holds the position of that record. -/
theorem State.deref_eq_some {x : State M L} {r : Fin L.ptrRegs} {n : Record M L} :
    x.deref r = some n ↔ ∃ a, x.ptr r = some a ∧ x.heap[a]? = some n := by
  simp [State.deref, Option.bind_eq_some_iff]

/-- A record of a modified heap is an old record or the image of one. -/
theorem State.mem_heap_modify {x : State M L} {r : Fin L.ptrRegs} {g : Record M L → Record M L}
    {n : Record M L} (h : n ∈ (x.modify r g).heap) : n ∈ x.heap ∨ ∃ m ∈ x.heap, n = g m := by
  unfold State.modify at h
  split at h
  · exact .inl h
  · next a _ =>
    simp only [List.modify_eq_set_getElem?] at h
    cases hm : x.heap[a]? with
    | none => simp_all
    | some m =>
      rw [hm] at h
      rcases List.mem_or_eq_of_mem_set h with h | h
      · exact .inl h
      · exact .inr ⟨m, List.mem_of_getElem? hm, h⟩

/-- Modifying a record keeps the number of records. -/
@[simp] theorem State.length_heap_modify {x : State M L} {r : Fin L.ptrRegs}
    {g : Record M L → Record M L} : (x.modify r g).heap.length = x.heap.length := by
  unfold State.modify
  split <;> simp

/-- Modifying a record keeps the pointer registers. -/
@[simp] theorem State.ptr_modify {x : State M L} {r : Fin L.ptrRegs}
    {g : Record M L → Record M L} : (x.modify r g).ptr = x.ptr := by
  unfold State.modify
  split <;> rfl

/-- Modifying a record keeps the data registers. -/
@[simp] theorem State.data_modify {x : State M L} {r : Fin L.ptrRegs}
    {g : Record M L → Record M L} : (x.modify r g).data = x.data := by
  unfold State.modify
  split <;> rfl

/-- Instructions preserve validity. -/
theorem Instr.effect_valid {i : Instr M L} {x : State M L} (hx : x.Valid) :
    (i.effect x).Valid := by
  obtain ⟨hr, hh⟩ := hx
  cases i <;> simp only [Instr.effect]
  case loadPtr r f base =>
    cases hn : x.deref base with
    | none => exact ⟨hr, hh⟩
    | some n =>
      obtain ⟨a, -, ha⟩ := State.deref_eq_some.mp hn
      have := hh n (List.mem_of_getElem? ha) f
      refine ⟨fun r' b hb => ?_, hh⟩
      simp only [Option.elim, State.setPtr, Function.update_apply] at hb ⊢
      grind
  case loadData s f base =>
    cases hn : x.deref base with
    | none => exact ⟨hr, hh⟩
    | some n => exact ⟨hr, hh⟩
  case storePtr f base r =>
    refine ⟨by simpa using hr, fun n hn f' b hb => ?_⟩
    rw [State.length_heap_modify]
    rcases State.mem_heap_modify hn with hn | ⟨m, hm, rfl⟩
    · exact hh n hn f' b hb
    · simp only [Function.update_apply] at hb
      grind
  case storeData f base s =>
    refine ⟨by simpa using hr, fun n hn f' b hb => ?_⟩
    rw [State.length_heap_modify]
    rcases State.mem_heap_modify hn with hn | ⟨m, hm, rfl⟩
    · exact hh n hn f' b hb
    · exact hh m hm f' b hb
  case create r =>
    refine ⟨fun r' b hb => ?_, fun n hn f b hb => ?_⟩
    · simp only [State.setPtr, Function.update_apply] at hb
      simp only [List.length_append, List.length_singleton]
      grind
    · simp only [List.length_append, List.length_singleton]
      rcases List.mem_append.mp hn with hn | hn
      · exact Nat.lt_succ_of_lt (hh n hn f b hb)
      · rw [List.mem_singleton.mp hn] at hb
        cases hb
  all_goals first
    | exact ⟨hr, hh⟩
    | (refine ⟨fun r' b hb => ?_, hh⟩
       simp only [State.setPtr, Function.update_apply] at hb ⊢
       grind)

/-- An instruction creates at most one record and removes none. -/
theorem Instr.effect_length {i : Instr M L} {x : State M L} :
    x.heap.length ≤ (i.effect x).heap.length ∧
      (i.effect x).heap.length ≤ x.heap.length + 1 := by
  cases i <;> simp only [Instr.effect, State.setPtr, State.setData]
  all_goals first
    | (cases x.deref ‹_› <;> simp)
    | simp

/-- A pointer in a register after an instruction was in a register before it, or in a field of
a record specified by a register, or specifies the record just created. -/
theorem Instr.effect_provenance {i : Instr M L} {x : State M L} {r : Fin L.ptrRegs} {a : ℕ}
    (ha : (i.effect x).ptr r = some a) :
    (∃ r', x.ptr r' = some a) ∨
    (∃ base n f, x.deref base = some n ∧ n.ptr f = some a) ∨
    (a = x.heap.length ∧ (i.effect x).heap.length = x.heap.length + 1) := by
  cases i <;> simp only [Instr.effect, State.setPtr, State.setData] at ha ⊢
  case loadPtr r' f base =>
    cases hn : x.deref base with
    | none => exact .inl ⟨r, by simpa [hn] using ha⟩
    | some n =>
      simp only [hn, Option.elim, Function.update_apply] at ha
      split_ifs at ha
      · exact .inr (.inl ⟨base, n, f, hn, ha⟩)
      · exact .inl ⟨r, ha⟩
  case loadData s f base =>
    cases hn : x.deref base <;> exact .inl ⟨r, by simpa [hn] using ha⟩
  case storePtr | storeData => exact .inl ⟨r, by simpa using ha⟩
  all_goals
    try simp only [Function.update_apply] at ha
    grind

/-- In a valid state, `create` returns a pointer that no register or record held. -/
theorem Instr.create_fresh {x : State M L} (hx : x.Valid) {r : Fin L.ptrRegs} :
    ((Instr.create r).effect x).ptr r = some x.heap.length ∧
      (∀ r', x.ptr r' ≠ some x.heap.length) ∧
      ∀ n ∈ x.heap, ∀ f, n.ptr f ≠ some x.heap.length :=
  ⟨by simp [Instr.effect, State.setPtr], fun r' h => lt_irrefl _ (hx.1 r' _ h),
    fun n hn f h => lt_irrefl _ (hx.2 n hn f _ h)⟩

/-- A step executes the current instruction, which is not a `halt`. -/
theorem step_eq_some_iff {code : List (Instr M L)} {x y : State M L} :
    step code x = some y ↔
      ∃ i, code[x.pc]? = some i ∧ i ≠ .halt ∧ y = { i.effect x with pc := i.next x } := by
  unfold step
  split
  · simp_all
  · simp_all
  · next i hne hi => exact ⟨fun h => ⟨i, hi, by simpa using hne, (Option.some.inj h).symm⟩, by
      rintro ⟨j, hj, -, rfl⟩
      cases hi.symm.trans hj
      rfl⟩

/-- Program steps preserve validity. -/
theorem step_valid {code : List (Instr M L)} {x y : State M L}
    (hx : x.Valid) (h : step code x = some y) : y.Valid := by
  obtain ⟨i, -, -, rfl⟩ := step_eq_some_iff.mp h
  exact i.effect_valid hx

/-- A program step creates at most one record and removes none. -/
theorem step_length {code : List (Instr M L)} {x y : State M L} (h : step code x = some y) :
    x.heap.length ≤ y.heap.length ∧ y.heap.length ≤ x.heap.length + 1 := by
  obtain ⟨i, -, -, rfl⟩ := step_eq_some_iff.mp h
  exact i.effect_length

/-- Every state of a run from a valid state is valid. -/
theorem Runs.valid {code : List (Instr M L)} {x y : State M L} {n : ℕ}
    (h : Runs code x y n) (hx : x.Valid) : y.Valid := by
  induction h with
  | refl => exact hx
  | tail _ _ _ _ hxy ih => exact step_valid ih hxy

/-- Space is at most the initial number of records plus the number of instructions executed. -/
theorem Runs.length_le {code : List (Instr M L)} {x y : State M L} {n : ℕ}
    (h : Runs code x y n) : y.heap.length ≤ x.heap.length + n :=
  h.apply_le_apply_add (fun x => x.heap.length) (fun _ _ hxy => (step_length hxy).2)

/-- Execution is deterministic. -/
theorem step_deterministic {code : List (Instr M L)} {x y z : State M L}
    (hy : step code x = some y) (hz : step code x = some z) : y = z :=
  Option.some.inj (hy.symm.trans hz)

end Cslib.PointerMachine
