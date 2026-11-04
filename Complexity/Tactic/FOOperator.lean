/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Operator.Definability
public import Complexity.Tactic.FOOperator.Init

/-!
# Certified synthesis of formulas with logical operators

`fo_definable` proves uniform definability of an ordinary Lean predicate by constructing a
well-formed formula, using the extensible Aesop rule set `FODefinable`. Its witness is a single
formula for the whole family of structures, rather than a formula chosen separately for each
structure. The built-in rules cover first-order atoms, Boolean connectives, and quantification.

To add a semantic operation, prove a theorem whose conclusion is `Operator.Definable` and
register it with `@[aesop safe apply (rule_sets := [FODefinable])]`. The theorem must supply a
well-formed formula and prove its meaning; `Definable.of_formula` provides the explicit-witness
entry point. Free-variable renaming and equivalent semantic presentations are also available
through `Definable.relabel` and `Definable.congr`.

Synthesis does not unfold fixed points or search over arbitrary formulas. Semantic reasoning
about an explicit formula continues to use the existing `fo_realize` simp set. In particular,
fixed-point unfolding is not a global simplification rule.

## Main definitions

* `fo_definable`: synthesize a uniformly defining, well-formed formula from registered rules.
* `fo_wf`: check formation conditions of explicit syntax, with optional simplification lemmas.
-/

public section

open Cslib.Logic.FO.Operator
open Lean Parser.Tactic

attribute [aesop safe apply (rule_sets := [FODefinable])]
  Definable.ofFO Definable.neg Definable.conj Definable.disj Definable.imp
  Definable.ex Definable.all Definable.truth Definable.falsity
  Definable.var_eq Definable.equal Definable.relation Definable.relation_vars Definable.rel
  Definable.relation₁ Definable.relation₂ Definable.rel_vars Definable.rel₁ Definable.rel₂

/-- Construct a well-formed defining formula by composing registered semantic certificates. -/
macro (name := foDefinable) "fo_definable" : tactic =>
  `(tactic| aesop (rule_sets := [FODefinable])
    (config := { terminal := true, enableSimp := false }))

/-- Prove the formation conditions of explicit formula syntax. `fo_wf [φ, policy]` unfolds
named formulas and formation policies in addition to the structural checks. The tactic fails
unless it closes the goal; it never assumes positivity of a recursive relation. -/
syntax (name := foWf) "fo_wf" (simpArgs)? : tactic

macro_rules
  | `(tactic| fo_wf $[[$args,*]]?) =>
    let args := args.map (·.getElems) |>.getD #[]
    `(tactic| solve
      | decide
      | simp [Formula.wellFormed, Formula.checkPolarity, Formula.disj, Formula.all,
          Marking.inner, Marking.outer, RelVar.split, $args,*])
