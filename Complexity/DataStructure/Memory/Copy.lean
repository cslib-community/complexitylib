/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Copy
public import Complexity.DataStructure.Memory.Spec

/-!
# Copying cells over the memory oracle

`Memory.copy src dst n` copies the `n` cells from `src` to the `n` cells from `dst`, one read and
one write per cell, in increasing order. A structure that grows into a larger block, such as a
doubling array or a resizing hash table, moves its contents this way. When the two ranges do not
overlap, the copy leaves memory as `Cslib.WordRAM.ArrayCopy.copyPrefix` describes, the same
function that specifies the word RAM's copy routine. It costs `2 n` memory units, and its
operations are admissible when both ranges are allocated and the copied cells hold words.

## Main definitions

* `Memory.copy`: copy `n` cells.

## Main results

* `Memory.clientState_copy`: the memory after the copy.
* `Memory.totalCost_copy`: its cost.
* `Memory.validHistory_copy`: its admissibility.
-/

@[expose] public section

namespace Cslib.DataStructure.Memory

open Cslib.WordRAM Cslib.WordRAM.ArrayCopy

variable {w : ℕ}

/-- Copy the `n` cells from `src` to the `n` cells from `dst`, in increasing order. -/
def copy (src dst : ℕ) : ℕ → Prog Unit
  | 0 => pure ()
  | n + 1 => do
    copy src dst n
    let v ← read (src + n)
    write (dst + n) v

/-- The last cell of a copy: a read and a write after the shorter copy. -/
theorem copy_succ (src dst n : ℕ) :
    copy src dst (n + 1) = copy src dst n >>= fun _ => read (src + n) >>= write (dst + n) := rfl

/-- **The memory after a copy** between non-overlapping ranges: the destination holds the source,
and the frontier is unchanged. -/
theorem clientState_copy (src dst n : ℕ) (s : State) (h : src + n ≤ dst ∨ dst + n ≤ src) :
    (spec w).clientState s (copy src dst n) = ⟨copyPrefix s.mem src dst n, s.frontier⟩ := by
  induction n with
  | zero =>
    rw [copyPrefix_zero]
    rfl
  | succ n ih =>
    rw [copy_succ, (spec w).clientState_bind, ih (by omega)]
    change State.mk (Function.update (copyPrefix s.mem src dst n) (dst + n)
      (copyPrefix s.mem src dst n (src + n))) s.frontier = _
    rw [copyPrefix_outside (by omega), copyPrefix_succ]

/-- A copy of `n` cells costs `2 n` memory units. -/
theorem totalCost_copy (src dst n : ℕ) (s : State) :
    (spec w).totalCost charge s ((spec w).clientHistory s (copy src dst n)) = 2 * n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [copy_succ, (spec w).clientHistory_bind, StateTransitionSpec.totalCost_append, ih]
    change 2 * n + 2 = 2 * (n + 1)
    omega

/-- **A copy is admissible** when both ranges are allocated, they do not overlap, and the copied
cells hold words. -/
theorem validHistory_copy (src dst n : ℕ) (s : State) (h : src + n ≤ dst ∨ dst + n ≤ src)
    (hsrc : src + n ≤ s.frontier) (hdst : dst + n ≤ s.frontier)
    (hfit : ∀ i < n, Fits w (s.mem (src + i))) :
    (spec w).ValidHistory s ((spec w).clientHistory s (copy src dst n)) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [copy_succ, (spec w).clientHistory_bind, StateTransitionSpec.validHistory_append,
      StateTransitionSpec.run_runClient, clientState_copy src dst n s (by omega)]
    refine ⟨ih (by omega) (by omega) (by omega) fun i hi => hfit i (by omega), ?_⟩
    change src + n < s.frontier ∧
      (dst + n < s.frontier ∧ Fits w (copyPrefix s.mem src dst n (src + n))) ∧ True
    rw [copyPrefix_outside (by omega)]
    exact ⟨by omega, ⟨by omega, hfit n (by omega)⟩, trivial⟩

end Cslib.DataStructure.Memory
