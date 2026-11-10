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

It first tries `synthesis_union`, which matches syntactic members of a union
`A₀ ∪ T₁ ∪ ⋯ ∪ Tₖ` at reducible transparency. This is the shape that a chain of
`Synthesis.extend` steps produces. Only if that fails does it run the general search, which
compares wire functions at default transparency. On wire families of equal width, such as the
bits of `BitVec` words, those comparisons unfold the word operations before they fail.
On a fifteen-step chain they exhaust the default heartbeat budget.

## Main definitions

* `synthesis_available`: close an available-wire obligation by structural proof search.
* `synthesis_union`: close it when the wires are syntactically a member of a union, or are
  in one by a local hypothesis, without unfolding any definition.
* `synthesis_step b using rule`: append a certified construction to `b`, finding its input wires.
-/

public section

/-- Close `X ⊆ A₀ ∪ T₁ ∪ ⋯ ∪ Tₖ` when `X` is syntactically `A₀` or some `Tᵢ`, or is contained in
one of them by a local hypothesis, and close `f ∈ A₀ ∪ T₁ ∪ ⋯ ∪ Tₖ` from a local hypothesis
`f ∈ A₀` or `f ∈ Tᵢ`. Matching is at reducible transparency and never looks inside a wire family.
Each step uses `refine`, which unifies the goal before recursing, so the search ends after one
step per union in the goal and fails quickly on any other goal. -/
syntax (name := synthesisUnion) "synthesis_union" : tactic
macro_rules | `(tactic| synthesis_union) => `(tactic| first
  | with_reducible assumption
  | with_reducible exact Set.Subset.rfl
  | with_reducible exact Set.subset_union_right
  | (with_reducible refine Set.subset_union_of_subset_left ?_ _); synthesis_union
  | (with_reducible refine Set.mem_union_right _ ?_); synthesis_union
  | (with_reducible refine Set.mem_union_left _ ?_); synthesis_union)

/-- The recursive search behind `synthesis_available`. Its failures are discarded by the
alternatives that call it, so only `synthesis_available` reports one. -/
syntax (name := synthesisAvailableSearch) "synthesis_available_search" : tactic
macro_rules | `(tactic| synthesis_available_search) => `(tactic|
  first
  | assumption
  | exact Set.mem_range_self _
  | rfl
  | (solve | apply Set.mem_union_right; synthesis_available_search)
  | (solve | apply Set.mem_union_left; synthesis_available_search)
  | (solve |
      change _ ∈ Set.iUnion _
      rw [Set.mem_iUnion]
      refine ⟨?_, ?_⟩
      rotate_left
      synthesis_available_search)
  | (solve | apply Set.range_subset_iff.mpr; intro i; synthesis_available_search)
  | (solve | apply Set.iUnion_subset; intro i; synthesis_available_search)
  | solve_by_elim (maxDepth := 3) (symm := false) (exfalso := false)
      (constructor := false) (intro := false) [Set.mem_range_self]
  | (solve | intro i; synthesis_available_search))

/-- Find already available wires, without synthesizing new functions. Tries the syntactic
`synthesis_union` first, then the general search. -/
syntax (name := synthesisAvailable) "synthesis_available" : tactic
macro_rules | `(tactic| synthesis_available) => `(tactic|
  first
  | synthesis_union
  | synthesis_available_search
  | fail "synthesis_available could not find these wires among the available ones. It follows \
      unions, indexed families, the wires of a `Synthesis.Builder` and local hypotheses, but \
      never adds a gate: append the missing construction first, with `synthesis_step` or \
      `Builder.add`.")

/-- Append a synthesis rule to the named builder, solving its available-wire premises. -/
syntax (name := synthesisStep) "synthesis_step " ident " using " term : tactic
macro_rules
  | `(tactic| synthesis_step $b:ident using $rule:term) =>
    `(tactic| let $b := ($b).add (by apply $rule <;> synthesis_available))

end
