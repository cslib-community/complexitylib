/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Synthesis

/-!
# Finding available circuit wires

`synthesis_available` proves membership and inclusion of wire families by following unions,
indexed bundles, and local availability hypotheses. It also finds the wires retained by a
`Synthesis.Builder`. Semantic rewrites and bounds on indices remain ordinary local lemmas.
The tactic never adds a gate or invokes a synthesis theorem.

## Main definitions

* `synthesis_available`: close an available-wire obligation by structural proof search.
* `synthesis_step b using rule`: append a certified construction to `b`, finding its input wires.
-/

public section

/-- Find already available wires, without synthesizing new functions. -/
syntax (name := synthesisAvailable) "synthesis_available" : tactic
macro_rules | `(tactic| synthesis_available) => `(tactic|
  first
  | assumption
  | exact Set.mem_range_self _
  | rfl
  | (solve | apply Set.mem_union_right; synthesis_available)
  | (solve | apply Set.mem_union_left; synthesis_available)
  | (solve |
      change _ ∈ Set.iUnion _
      rw [Set.mem_iUnion]
      refine ⟨?_, ?_⟩
      rotate_left
      synthesis_available)
  | (solve | apply Set.range_subset_iff.mpr; intro i; synthesis_available)
  | (solve | apply Set.iUnion_subset; intro i; synthesis_available)
  | solve_by_elim (maxDepth := 3) (symm := false) (exfalso := false)
      (constructor := false) (intro := false) [Set.mem_range_self]
  | (solve | intro i; synthesis_available))

/-- Append a synthesis rule to the named builder, solving its available-wire premises. -/
syntax (name := synthesisStep) "synthesis_step " ident " using " term : tactic
macro_rules
  | `(tactic| synthesis_step $b:ident using $rule:term) =>
    `(tactic| let $b := ($b).add (by apply $rule <;> synthesis_available))

end
