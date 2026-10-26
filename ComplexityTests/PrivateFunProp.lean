/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests)

public import Complexity.Computability.Circuit.Rational.Runtime.Determinant
public import Complexity.Computability.Complexity.Classes.IP.GraphNonIsomorphism
public import Complexity.Computability.Complexity.Classes.TFNP.Subclasses
public import Complexity.Computability.Complexity.FineGrained.PermutationIndependentSet
public import Complexity.Computability.Complexity.Problems.CountingSAT
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Complexity

/-!
# Private automation rules stay in their defining modules

An ordinary module import must not export a `fun_prop` rule referring to an unavailable private
theorem. Such a rule crashes proof search with an unknown-constant error when it is selected.
Inspect this library's private declarations in all four imported rule registries, including lazy
discrimination-tree entries, and check that public polynomial-time certificates remain usable in
composed goals.
-/

open Lean Mathlib.Meta.FunProp in
run_meta do
  let env ← getEnv
  let check (name : Name) : MetaM Unit := do
    -- Dependency-owned rules are outside this library's regression.
    if (`_private.Complexity).isPrefixOf name then
      unless (env.find? name).isSome do
        logError m!"imported fun_prop rule is unavailable: {name}"
  for (_, rules) in (lambdaTheoremsExt.getState env).theorems do
    for rule in rules do
      check rule.thmName
  for (_, properties) in (functionTheoremsExt.getState env).theorems do
    for (_, rules) in properties do
      for rule in rules do
        if let .decl name := rule.thmOrigin then
          check name
  for state in #[transitionTheoremsExt.getState env, morTheoremsExt.getState env] do
    for trie in state.theorems.tries do
      for rule in trie.values do
        check rule.thmName
      for (_, rule) in trie.pending do
        check rule.thmName

open Turing.MultiTapeTM Cslib.Complexity Cslib.Logic.PL

namespace ComplexityTests.PrivateFunProp

/-- The public padding certificate remains usable in composed plain polynomial-time goals. -/
public theorem padMajority_composition :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => padMajority p.1 (p.2 + 1))
    (encPair encCNF encUnary) encCNF := by
  fun_prop

/-- The public search-width certificate remains usable after an ordinary module import. -/
public theorem searchBits_composition : ComputableInPolyTime
    (fun n : ℕ => BipartitePermutationIndependentSet.searchBits (n + 1))
    encUnary encUnary := by
  fun_prop

end ComplexityTests.PrivateFunProp
