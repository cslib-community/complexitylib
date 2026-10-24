/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.LineCode.Basic
public import Complexity.Computability.Circuit.Boolean.MassProduction.Point
public import Cslib.Computability.Circuit.Boolean.Basic

/-!
# Recovery schedules

A scheduler circuit reads `t` target points and writes, for every request in its original
position, the points of a punctured line through that request's target, such that the lines of
distinct requests are disjoint (`IsScheduler`). Targets may repeat, and `t` may be zero. The
directions are existential; only the listed points are outputs.

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.IsScheduler`: the scheduler specification.

## References

* Adapted from the scheduler contracts of MassProduction/Nonuniform/SchedulerCircuit.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction

open BitString LineCode

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ b s t : ℕ}

/-- A scheduler maps every batch of `t` targets to listed punctured lines through them, with
nonzero directions and pairwise disjoint lines, keeping every request in its original
position. The lines are listed in the order of the bijection `scalar` onto the nonzero
scalars. -/
def IsScheduler (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    (c : Circuit Boolean.signature (t * (ℓ * b)) (t * (s * (ℓ * b)))) : Prop :=
  ∀ targets : Fin t → Fin ℓ → K, ∃ directions : Fin t → Fin ℓ → K,
    (∀ i, directions i ≠ 0) ∧
      (∀ i j, i ≠ j →
        Disjoint (puncturedLine (targets i) (directions i))
          (puncturedLine (targets j) (directions j))) ∧
      c.eval Boolean.interpretation (targetBits bits targets) =
        lineBits bits (fun j => (scalar j : K)) targets directions

end Cslib.Circuits.Boolean.MassProduction
