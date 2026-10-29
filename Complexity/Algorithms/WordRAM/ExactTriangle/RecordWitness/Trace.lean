/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Count
public import Mathlib.Data.List.Range

/-!
# The actual witness controller's short-circuit scan trace

`foundBefore` specifies the cached native flag after an input prefix. It is not a witness
oracle or an extra runtime computation: the execution invariant derives it from the actual
loads and verifier calls. Scan and failure counts use Mathlib's `Nat.count` directly.

The argument follows the scan-accounting portion of pinned `ScanPairs.lean`,
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. This controller starts
with a false flag; the source's optional already-successful incoming flag is not needed.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

/-- Pure value of the cached flag: an earlier accepted pair has a genuine original witness. -/
@[expose] def foundBefore (accept hit : ℕ → Bool) (i : ℕ) : Bool :=
  (List.range i).any fun j => accept j && hit j

/-- Before reading any answer, the native success flag is false. -/
theorem foundBefore_zero (accept hit : ℕ → Bool) : foundBefore accept hit 0 = false := rfl

/-- One actual query extends the previous success flag by its own accepted witness result. -/
theorem foundBefore_succ (accept hit : ℕ → Bool) (i : ℕ) :
    foundBefore accept hit (i + 1) = (foundBefore accept hit i || (accept i && hit i)) := by
  simp [foundBefore, List.range_succ]

/-- The cached success flag records an actually accepted earlier query. -/
theorem foundBefore_eq_true (accept hit : ℕ → Bool) (i : ℕ) :
    foundBefore accept hit i = true ↔ ∃ j < i, accept j = true ∧ hit j = true := by
  simp [foundBefore, List.any_eq_true, List.mem_range]

/-- Every actual scan except at most the successful one is a failed accepted candidate.
The functions describe original input values; no such function is an algorithm argument. -/
theorem scan_count_le (accept hit : ℕ → Bool) (Q : ℕ) :
    Nat.count (fun i => (accept i && !foundBefore accept hit i) = true) Q ≤
      Nat.count (fun i => (accept i && !hit i) = true) Q +
        (foundBefore accept hit Q).toNat := by
  induction Q with
  | zero => simp [foundBefore]
  | succ Q ih =>
    rw [Nat.count_succ, Nat.count_succ, foundBefore_succ]
    rcases ha : accept Q <;> rcases hh : hit Q <;> rcases hf : foundBefore accept hit Q <;>
      simp_all only [Bool.not_false, Bool.not_true, Bool.and_false, Bool.and_true,
        Bool.or_false, Bool.or_true, Bool.toNat_false, Bool.toNat_true,
        Bool.false_eq_true, ↓reduceIte] <;> omega

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
