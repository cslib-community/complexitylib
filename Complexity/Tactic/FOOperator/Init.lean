/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Tactic.FirstOrder.Init

/-!
# Rule set for certified formula synthesis

`FODefinable` contains compositional certificates that synthesize a single well-formed formula
from a Lean predicate across a family of structures. Logical extensions can register their own
semantic operations in this rule set. The tactic is defined in `Complexity.Tactic.FOOperator`.
-/

public section

declare_aesop_rule_sets [FODefinable]
