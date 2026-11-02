/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Karger.Memory.Contract
public import Complexity.Computability.WordRAM.Realization.While

/-!
# Canonical loop equations for the contraction structure

The existing memory programs `scan`, `mergeLoop` and `compactLoop` are finite recursions.
Their equations below express exactly the same memory clients using `boundedWhile` and
`iterate`. Equality is of the free programs, so it retains the queries, their order, replies and
all interpreter and admissibility contracts. No native execution theorem is asserted here.

The scan carries remaining fuel, the current index and the residual offset. A successful entry
sets the remaining fuel to zero, so the next guard exits without another read. The matrix loops
carry their current index, including iterations that skip a row or column. Their local control
work must still be charged by a later realization certificate.

## Main results

* `scan_eq_boundedWhile`: the prefix scan is an early-exit loop.
* `mergeLoop_eq_iterate`, `compactLoop_eq_iterate`: matrix scans are bounded iterations.

## References

* [KargerStein1996]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Karger.Memory

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

/-- The prefix scan as an early-exit loop. A zero cutoff reads nothing, and finding an entry
exits immediately, preserving the original remaining offset and index. -/
theorem scan_eq_boundedWhile (b : Block) (n i r : ℕ) :
    scan b n i r = (do
      let (_, i, r) ← boundedWhile
        (fun (_ : Block) (s : ℕ × ℕ × ℕ) => let (left, _, _) := s; 0 < left)
        (fun (b, (left, i, r)) => do
          let x ← b.get i
          if r < x then pure (0, i, r) else pure (left - 1, i + 1, r - x))
        b n (n, i, r)
      pure (i, r)) := by
  induction n generalizing i r with
  | zero => simp only [scan, boundedWhile, pure_bind]
  | succ n ih =>
    simp only [scan, boundedWhile, Nat.succ_pos, ↓reduceIte, bind_assoc]
    congr 1
    funext x
    by_cases h : r < x
    · simp only [h, ↓reduceIte, pure_bind]
      rw [boundedWhile_of_not _ _ b n (0, i, r) (by simp)]
      rfl
    · simpa only [h, ↓reduceIte, pure_bind, Nat.add_sub_cancel] using ih (i + 1) (r - x)

/-- The merge scan as an iteration over its current column. Skipping either contracted vertex
issues exactly the same empty client as before; it still advances the index. -/
theorem mergeLoop_eq_iterate (L : Layout) (u v n c : ℕ) :
    mergeLoop L u v n c = (do
      let _ ← iterate (fun ((L, u, v), c) => do
        (if c = u then pure () else if c = v then pure () else mergeStep L u v c)
        pure (c + 1)) (L, u, v) n c
      pure ()) := by
  induction n generalizing c with
  | zero => simp only [mergeLoop, iterate, pure_bind]
  | succ n ih =>
    have hskip :
        (if c = u ∨ c = v then (pure () : Memory.Prog Unit) else mergeStep L u v c) =
          (if c = u then pure () else if c = v then pure () else mergeStep L u v c) := by
      by_cases hu : c = u <;> by_cases hv : c = v <;> simp [hu, hv]
    simp only [mergeLoop, iterate, bind_assoc, pure_bind, hskip]
    congr 1
    funext a
    exact ih (c + 1)

/-- The compaction scan as an iteration over its current column, retaining the skipped target
and the exact order of all memory queries. -/
theorem compactLoop_eq_iterate (L : Layout) (v m n c : ℕ) :
    compactLoop L v m n c = (do
      let _ ← iterate (fun ((L, v, m), c) => do
        (if c = v then pure () else compactStep L v m c)
        pure (c + 1)) (L, v, m) n c
      pure ()) := by
  induction n generalizing c with
  | zero => simp only [compactLoop, iterate, pure_bind]
  | succ n ih =>
    simp only [compactLoop, iterate, bind_assoc, pure_bind]
    congr 1
    funext a
    exact ih (c + 1)

end Cslib.Algorithms.Lean.Karger.Memory
