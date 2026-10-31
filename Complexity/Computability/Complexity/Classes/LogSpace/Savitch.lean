/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace.Randomized
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Savitch

/-!
# Savitch's theorem for logarithmic space: `NL ⊆ DSPACE(log² n)`

A problem in `Cslib.Complexity.NL` is decided by a deterministic machine within space
`O((log₂ n) ^ 2)` [Savitch1970]: Savitch's midpoint recursion on the compact configuration graph
of the nondeterministic machine, which never copies the input
(`Turing.MultiTapeNTM.exists_decidableInTimeAndSpace_log_sq`). The simulation uses only the space
bound and acceptance, so it also applies to logspace recognizers, whose branches may run forever.
Since one-sided-error randomized logspace is within `NL` (`Cslib.Complexity.RL_subset_NL`), the
same bound holds for `Cslib.Complexity.RL` [Hoza, Section 4.3][Hoza2022].

The space classes are `Cslib.Complexity.DSPACE enc fun n => Nat.log2 n ^ 2`, the problems decided
within space `c₁ * (log₂ n) ^ 2 + c₂` on encoded instances of length `n`.

The source statement for sublinear space is the extension in the final paragraph of Sipser's
Section 8.4 (3rd edition, p. 351), "We can extend Savitch's theorem to hold for sublinear space
bounds down to f(n) ≥ log n"; Sipser's Theorem 8.5 assumes `f(n) ≥ n`. The source is about
deciders on strings; the statements here also cover nonhalting recognizers and arbitrary encoded
instances.

## Main results

* `Cslib.Complexity.mem_DSPACE_log2_sq_of_recognizesInSpace`: a logspace recognizer, whose
  branches need not halt, places its problem in `DSPACE(log² n)`.
* `Cslib.Complexity.NL_subset_DSPACE_log2_sq`: `NL ⊆ DSPACE(log² n)`.
* `Cslib.Complexity.RL_subset_DSPACE_log2_sq`: `RL ⊆ DSPACE(log² n)`.

## References

* [W. J. Savitch, *Relationships between nondeterministic and deterministic tape
  complexities*][Savitch1970]
* [W. M. Hoza, *Recent Progress on Derandomizing Space-Bounded Computation*, Section 4.3][Hoza2022]
* [M. Sipser, *Introduction to the Theory of Computation*, 3rd edition, Section 8.4, final
  paragraph (p. 351)][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- **Savitch's theorem for logspace recognizers**: a problem recognized by a nondeterministic
machine within space `c * (log₂ n + 1)`, whose branches need not halt, is in `DSPACE(log² n)`
[Savitch1970]. -/
theorem mem_DSPACE_log2_sq_of_recognizesInSpace {k : ℕ} {State : Type} [Finite State]
    {ntm : MultiTapeNTM k Bool State} {c : ℕ}
    (hA : ntm.RecognizesInSpace enc A fun a => c * (Nat.log2 (enc a).length + 1)) :
    A ∈ DSPACE enc fun n => Nat.log2 n ^ 2 := by
  obtain ⟨t, c', h⟩ := MultiTapeNTM.exists_decidableInTimeAndSpace_log_sq hA
  refine mem_DSPACE_iff.mpr ⟨2 * c', 2 * c', t,
    ComputableInTimeAndSpace.mono h (fun _ => le_rfl) fun a => ?_⟩
  have : (Nat.log2 (enc a).length + 1) ^ 2 ≤ 2 * Nat.log2 (enc a).length ^ 2 + 2 := by nlinarith
  have := Nat.mul_le_mul_left c' this
  nlinarith

/-- **Savitch's theorem for logarithmic space**: `NL ⊆ DSPACE(log² n)` [Savitch1970]. -/
theorem NL_subset_DSPACE_log2_sq : NL enc ⊆ DSPACE enc fun n => Nat.log2 n ^ 2 := by
  rintro A ⟨k, State, hfinite, ntm, c, h⟩
  exact mem_DSPACE_log2_sq_of_recognizesInSpace h.recognizesInSpace

/-- **`RL ⊆ DSPACE(log² n)`**, through `RL ⊆ NL` [Hoza, Section 4.3][Hoza2022]. -/
theorem RL_subset_DSPACE_log2_sq : RL enc ⊆ DSPACE enc fun n => Nat.log2 n ^ 2 :=
  fun _ h => NL_subset_DSPACE_log2_sq (RL_subset_NL h)

end Cslib.Complexity
