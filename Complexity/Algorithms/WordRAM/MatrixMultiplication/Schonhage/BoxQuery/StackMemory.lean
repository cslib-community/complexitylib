/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Stack
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Prefixes

/-!
# Readback of the actual native query frontier

Each pending prefix is represented by its five computed scalar fields. List heads
occupy the top physical record, so the existing native push prepends a task and pop
removes that head. These are memory predicates, not supplied execution or layout certificates.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The five real words of one prefix task at its occupied native record index. -/
structure TaskReadback {L : ℕ} (η : OutStr L) (F n : ℕ) (xs : List Term)
    (μ : ℕ → ℕ) : Prop where
  /-- Prefix depth. -/
  depth : μ (F + n * 5) = xs.length
  /-- Existing little-endian prefix code. -/
  code : μ (F + n * 5 + 1) = prefixCode xs
  /-- Number of used indexed inner terms. -/
  used : μ (F + n * 5 + 2) = usedFrom η 0 xs
  /-- Initial inner P0 count. -/
  stars : μ (F + n * 5 + 3) = starsFrom η 0 xs
  /-- Actual decimal power. -/
  power : μ (F + n * 5 + 4) = 10 ^ xs.length

/-- Pending logical prefixes in top-first order, with no initial-zero-memory premise. -/
@[expose] def StackMemory {L : ℕ} (η : OutStr L) (F : ℕ) :
    List (List Term) → (ℕ → ℕ) → Prop
  | [], _ => True
  | xs :: rest, μ => TaskReadback η F rest.length xs μ ∧ StackMemory η F rest μ

/-- Transport a real record across equality of its occupied five-word interval. -/
theorem TaskReadback.transport {L F n : ℕ} {η : OutStr L} {xs : List Term}
    {μ ν : ℕ → ℕ} (h : TaskReadback η F n xs μ)
    (hf : ∀ q, F + n * 5 ≤ q → q < F + n * 5 + 5 → ν q = μ q) :
    TaskReadback η F n xs ν := by
  constructor
  · rw [hf _ (by omega) (by omega)]; exact h.depth
  · rw [hf _ (by omega) (by omega)]; exact h.code
  · rw [hf _ (by omega) (by omega)]; exact h.used
  · rw [hf _ (by omega) (by omega)]; exact h.stars
  · rw [hf _ (by omega) (by omega)]; exact h.power

/-- Changes outside the occupied stack prefix preserve every pending task. -/
theorem StackMemory.transport {L F : ℕ} {η : OutStr L} {tasks : List (List Term)}
    {μ ν : ℕ → ℕ} (h : StackMemory η F tasks μ)
    (hf : ∀ q, F ≤ q → q < F + 5 * tasks.length → ν q = μ q) :
    StackMemory η F tasks ν := by
  induction tasks with
  | nil => trivial
  | cons xs rest ih =>
    refine ⟨h.1.transport (fun q hq hq' => hf q (by omega) (by
      simp only [List.length_cons]; omega)), ?_⟩
    exact ih h.2 (fun q hq hq' => hf q hq (by simp only [List.length_cons]; omega))

/-- Appending the actual five computed fields prepends precisely that logical task. -/
theorem StackMemory.push {L F : ℕ} {η : OutStr L} {tasks : List (List Term)}
    {μ : ℕ → ℕ} (h : StackMemory η F tasks μ) (xs : List Term) :
    StackMemory η F (xs :: tasks)
      (writeTask F tasks.length xs.length (prefixCode xs) (usedFrom η 0 xs)
        (starsFrom η 0 xs) (10 ^ xs.length) μ) := by
  refine ⟨?_, h.transport (fun q hq hq' => writeTask_frame _ _ _ _ _ _ _ _ q (by omega))⟩
  obtain ⟨hd, hc, hu, he, hp⟩ := writeTask_read F tasks.length xs.length
    (prefixCode xs) (usedFrom η 0 xs) (starsFrom η 0 xs) (10 ^ xs.length) μ
  exact ⟨hd, hc, hu, he, hp⟩

/-- A nonempty stack exposes its real top record and preserves every deeper pending task. -/
theorem StackMemory.pop {L F : ℕ} {η : OutStr L} {tasks : List (List Term)}
    {xs : List Term} {μ : ℕ → ℕ} (h : StackMemory η F (xs :: tasks) μ) :
    TaskReadback η F tasks.length xs μ ∧ StackMemory η F tasks μ := h

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
