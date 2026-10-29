/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.LogSpace.USTCON
import Complexity.Computability.Complexity.Problems.STCON.Completeness
import Complexity.Computability.Complexity.Problems.STCON.Search

/-!
# Directed connectivity tests

The language `Cslib.Complexity.STCON` is neither empty nor everything, and its arcs are directed:
the path `0 → 1 → 2` connects `0` to `2`, while the single arc `1 → 0` does not connect `0` to
`1`. The encoding of the path is pinned bit by bit, and the nondeterministic search accepts the
first instance and rejects the second (`Cslib.Complexity.STCON.accepts_searchProgram_iff`).

The hardness hypothesis is satisfiable: undirected connectivity, which is in `L`, reduces to
`STCON` through the configuration graph of its logarithmic-space decider.
-/

namespace ComplexityTests.STCON

open Cslib Cslib.Complexity

/-- The path `0 → 1 → 2`, from `0` to `2`. -/
def pathInstance : STCONInstance where
  n := 3
  adj a b := decide ((a : ℕ) + 1 = b)
  s := 0
  t := 2

/-- The single arc `1 → 0`, from `0` to `1`. -/
def backInstance : STCONInstance where
  n := 2
  adj a b := decide ((a : ℕ) = 1 ∧ (b : ℕ) = 0)
  s := 0
  t := 1

-- The encoding of the path: `1^3 0`, `1^0 0`, `1^2 0`, then the matrix row by row.
example : pathInstance.encode =
    [true, true, true, false, false, true, true, false,
      false, true, false, false, false, true, false, false, false] := by
  decide

/-- The path `0 → 1 → 2` connects `0` to `2`. -/
theorem pathInstance_mem : pathInstance ∈ STCON :=
  (Relation.ReflTransGen.single (show pathInstance.Adj ⟨0, by decide⟩ ⟨1, by decide⟩ from rfl)).tail
    (show pathInstance.Adj ⟨1, by decide⟩ ⟨2, by decide⟩ from rfl)

/-- The arc `1 → 0` reaches nothing from `0` but `0` itself. -/
theorem backInstance_notMem : backInstance ∉ STCON := by
  have key : ∀ x, Relation.ReflTransGen backInstance.Adj backInstance.s x → (x : ℕ) = 0 := by
    intro x hx
    induction hx with
    | refl => rfl
    | @tail y z _ hyz ih =>
      have hz := z.isLt
      change decide ((y : ℕ) = 1 ∧ (z : ℕ) = 0) = true at hyz
      simp only [decide_eq_true_eq] at hyz
      omega
  intro h
  exact absurd (key _ h) (by decide)

-- The search accepts the path and rejects the backward arc.
example : STCON.searchProgram.toNondeterministicQueryMachine.Accepts pathInstance.encode :=
  (STCON.accepts_searchProgram_iff _).mpr pathInstance_mem

example : ¬ STCON.searchProgram.toNondeterministicQueryMachine.Accepts backInstance.encode :=
  fun h => backInstance_notMem ((STCON.accepts_searchProgram_iff _).mp h)

-- The matrix row by row.
example : pathInstance.matrix = (List.range 3).flatMap fun u =>
    (List.range 3).map fun v => decide (u + 1 = v) :=
  pathInstance.matrix_eq_flatMap _ fun _ _ => rfl

-- Each of `STCON` and `STCONᶜ` reduces in logarithmic space to the other via `NL`-completeness.
example : LogSpaceReducible encSTCON encSTCON STCONᶜ STCON :=
  STCON.logSpaceComplete.2 encSTCON STCONᶜ STCON.compl_mem_NL

example : LogSpaceReducible encSTCON encSTCON STCON STCONᶜ :=
  STCON.compl_logSpaceComplete.2 encSTCON STCON STCON.mem_NL

-- The hardness hypothesis is satisfiable: undirected connectivity reduces to `STCON`.
example : LogSpaceReducible encUSTCON encSTCON USTCON STCON :=
  STCON.logSpaceReducible_of_mem_NL (L_subset_NL USTCON_mem_L)

example (h : STCON ∈ L encSTCON) : STCONᶜ ∈ L encSTCON :=
  (STCON.mem_L_iff_forall_NL_eq_L.mp h encSTCON) ▸ STCON.compl_mem_NL

end ComplexityTests.STCON
