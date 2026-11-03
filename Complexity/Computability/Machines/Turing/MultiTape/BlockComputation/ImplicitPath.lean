/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadSearch

/-!
# Implicit block-tree addresses

A path is followed by retaining one interval index. Child zero selects the preceding interval;
other children select the last earlier window provider. Missing providers and the padded source
stay at index zero. Out-of-range child numbers and intervals also return zero.

Provider selection uses a fixed family indexed by the simulated machine's work tapes and three
ports. Thus each head offset in a schedule reader is fixed, rather than an unchecked runtime
exponent. No tree, interval list or table is constructed.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ImplicitPath

/-- Read one fixed work-head/port provider, using zero for the initial source. -/
@[expose] def provider (k : ℕ) (a : ℕ × ℕ) (p : Fin (k * 3)) : ℕ :=
  let (σ, n) := a
  let (h, δ) : Fin k × Fin 3 := finProdFinEquiv.symm p
  ((ScheduleRead.search k (h + 1) (σ, n, δ)).map fun j => j + 1).getD 0

/-- The fixed finite family of providers for one interval. -/
@[expose] def providers (k : ℕ) (a : ℕ × ℕ) : List ℕ :=
  List.ofFn fun p : Fin (k * 3) => provider k a p

/-- Schedule, horizon, current interval index and child number. -/
abbrev Args := ℕ × ℕ × ℕ × ℕ

/-- Follow one child without constructing the unfolded tree. -/
@[expose] def child (k : ℕ) : Args → ℕ := fun (σ, q, index, j) =>
  match index with
  | 0 => 0
  | n + 1 =>
    if n < q ∧ j < k * 3 + 1 then
      if j = 0 then n else (providers k (σ, n)).getD (j - 1) 0
    else 0

/-- Binary schedule and horizon, followed by an explicitly stored sequence of child numbers. -/
abbrev WalkArgs := ℕ × ℕ × List ℕ

/-- Fold a path from the root index, retaining one current interval. -/
@[expose] def walk (k : ℕ) : WalkArgs → ℕ := fun (σ, q, path) =>
  path.foldl (fun index j => child k (σ, q, index, j)) q

end Turing.MultiTapePTM.BlockComputation.ImplicitPath
