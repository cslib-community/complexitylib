/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import VersoManual
import Complexity.Logics.FirstOrder.Operator.LeastFixedPoint.Definability
import Complexity.Logics.FirstOrder.Operator.Relabel
import Complexity.Logics.FirstOrder.Operator.TransitiveClosure.Definability
import Complexity.Tactic.FOOperator

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 80

#doc (Manual) "First-Order Logic with Operators" =>
%%%
tag := "first-order-operators"
%%%

First-order formulas often describe a local step: two vertices share an edge, a tuple satisfies
a constraint, or a relation gains a new tuple. Logical operators turn those steps into paths or
least fixed points. The library provides a shared syntax for these extensions, concrete FO(LFP)
and FO(TC) interpretations, and certificates that construct formulas from ordinary Lean predicates.

```lean -show
open FirstOrder Language Cslib.Logic.FO
```

# Binding and Interpretation
%%%
tag := "operator-binding"
%%%

{name}`Cslib.Logic.FO.Operator.Shape` records the number of term arguments, the number of formula
bodies, and the local binders of each body. Each binder lists its relation arities and its number
of first-order variables. A body keeps ambient parameters under `Sum.inl` and sees its new tuple
variables under `Sum.inr`.

{name}`Cslib.Logic.FO.Operator.Formula` uses Mathlib's native first-order terms and formulas for
its base language. A relation context is a list of arities: `RelVar.here` denotes the nearest
relation binder, and `RelVar.there` passes an inner binder to reach an outer variable. An
interpretation supplies the meaning of each operator; binding itself is independent of that meaning.

Reusable formulas can move beneath a new relation binder with
`(φ.weakenRel [k]).relabel Sum.inl`. The first operation shifts outer relation variables; the
second shifts the free first-order parameters. Local binders inside `φ` remain local. The
{name}`Cslib.Logic.FO.Operator.Formula.realize_weakenRel` theorem shows that the new relation's
value cannot affect the weakened formula, and both operations preserve formation checks.

# Least Fixed Points
%%%
tag := "operator-lfp"
%%%

{name}`Cslib.Logic.FO.LFP.RawFormula` is syntax whose formation conditions have not yet been
checked. {name}`Cslib.Logic.FO.LFP.Formula` packages that syntax with a proof of well-formedness.
The `lfp` constructor binds a relation and a tuple of the same arity; its body must contain its
own relation positively. Ordinary negation outside that recursion is allowed, as are nested
fixed points and free parameters.

Raw semantics is total: it intersects all pre-fixed relations. The fixed-point unfolding and
leastness laws require the positivity certificate. This distinction prevents a negative recursive
body from silently acquiring the laws of a monotone least fixed point. `fo_wf [definitions]`
checks formation of explicit syntax by unfolding its named formulas and the syntactic checks.

For a finite structure with `n` elements and an arity-`k` relation, iteration starts at the empty
relation and reaches the least fixed point by stage `n ^ k`. The theorem proves equality at that
stage, including empty domains and arity zero; it counts possible tuples, rather than all possible
relations. {name}`OrderHom.iterate_card_bot_eq_lfp` provides the underlying general powerset bound.
This is a semantic iteration theorem. A native polynomial-time evaluator and the ordered
Immerman–Vardi capture theorem remain separate work.

# Tuple Reachability
%%%
tag := "operator-tc"
%%%

{name}`Cslib.Logic.FO.TC.tc` binds two `k`-tuples in its body and takes two endpoint tuples as
arguments. Its semantics is {name}`Relation.ReflTransGen`: a path of zero or more body edges.
The zero-length path makes a tuple reachable from itself even when the body is false.
Parameters stay fixed along the path. Width-zero closure is meaningful on an empty domain,
because there is still one empty tuple.

{name}`Cslib.Logic.FO.TC.pair` concatenates the endpoints; `TC.left` and `TC.right` recover them.
The semantic API proves reflexivity, inclusion of body edges, and composition of paths. It does
not yet certify an FO(TC) model-checking machine or a capture theorem for NL.

# Constructing Formulas from Predicates
%%%
tag := "operator-synthesis"
%%%

{name}`Cslib.Logic.FO.Operator.Definable` asserts that one well-formed formula defines a predicate
throughout an indexed family of structures. The formula is chosen before the family index and
the variable assignment. A certificate therefore cannot select a different formula for each size.

The `fo_definable` tactic composes certified construction rules. Here it builds a formula from an
ordinary predicate using existential quantification, conjunction, and equality:

```lean
example {L : Language} {ι : Type} {M : ι → Type}
    [∀ i, L.Structure (M i)] {α : Type} (a b : α) :
    Operator.Definable (L := L) LFP.policy M
      (fun _ => LFP.interpretation) (fun _ => Operator.RelEnv.empty)
      (fun i v => ∃ x : M i, x = v a ∧ x = v b) := by
  fo_definable
```

The LFP rule also starts from an ordinary Lean relation transformer. This step includes the
starting vertex and extends the current relation by one edge. The final `fo_definable` constructs
the fixed-point formula and certifies its positive, existential body:

```lean
def exampleReachStep {L : Language} {A : Type} [L.Structure A]
    (edge : L.Relations 2) (start : A) :
    Set (Fin 1 → A) →o Set (Fin 1 → A) where
  toFun R := {ys | ys 0 = start ∨ ∃ x,
    (fun _ : Fin 1 => x) ∈ R ∧ Structure.RelMap edge ![x, ys 0]}
  monotone' := by
    intro R S h ys hy
    rcases hy with hstart | ⟨x, hx, hedge⟩
    · exact Or.inl hstart
    · exact Or.inr ⟨x, h hx, hedge⟩

example {L : Language} {ι : Type} {M : ι → Type}
    [∀ i, L.Structure (M i)] {α : Type}
    (edge : L.Relations 2) (a b : α) :
    Operator.Definable (L := L) LFP.policy M
      (fun _ => LFP.interpretation) (fun _ => Operator.RelEnv.empty)
      (fun _ v => ![v b] ∈ (exampleReachStep edge (v a)).lfp) := by
  fo_definable
```

Importing the TC synthesis module registers the closure rule as well. This example starts with
semantic reachability for an arbitrary binary relation symbol; the tactic constructs the closure
formula and its correctness proof:

```lean
example {L : Language} {ι : Type} {M : ι → Type}
    [∀ i, L.Structure (M i)] {α : Type}
    (r : L.Relations 2) (xs ys : Fin 1 → L.Term α) :
    Operator.Definable (L := L) TC.policy M
      (fun _ => TC.interpretation) (fun _ => Operator.RelEnv.empty)
      (fun i v => Relation.ReflTransGen
        (fun us vs : Fin 1 → M i => Structure.RelMap r ![us 0, vs 0])
        (fun j => (xs j).realize v) (fun j => (ys j).realize v)) := by
  fo_definable
```

An extension rule concludes `Operator.Definable`, supplies a well-formed formula witness, and
proves its semantics uniformly across the family. Register it with
`@[aesop safe apply (rule_sets := [FODefinable])]`. Rules for recursive bodies must also preserve
their syntactic polarity certificate. The current LFP synthesis rules cover first-order bodies;
nested LFP syntax is supported, but an automatic rule for nested fixed-point bodies is not supplied.

# Adding Other Operators
%%%
tag := "operator-extensions"
%%%

{name}`Cslib.Logic.FO.Operator.Policy` declares each body's variance and its locally positive
relation variables. An interpretation proves {name}`Cslib.Logic.FO.Operator.Interpretation.Respects`
for that variance. Positive slots preserve implication; negative slots reverse it; arbitrary
slots require equivalence. The polarity checker propagates these requirements through nesting.

A regular-language quantifier can use this binding interface and declare arbitrary variance for
a body whose changes are not monotone. In a recursive context, that declaration requires both
polarity checks and conservatively excludes dependence on the recursive relation. The interface
supports such an extension; no REG interpretation or FO(REG) capture theorem is implemented here.

The [checked regression examples][examples] exercise nesting, rejected negative recursion,
finite iteration, relation weakening, empty domains, and formula synthesis.

[examples]: https://github.com/cslib-community/complexitylib/blob/main/ComplexityTests/FOOperators.lean
