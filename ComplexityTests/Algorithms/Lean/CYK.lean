/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.CYK.Basic

/-!
# The Cocke–Younger–Kasami algorithm: worked examples

Kernel-checked examples (no `native_decide`) for two grammars in Chomsky normal form: `{aⁿbⁿ}`
without `ε`, whose start symbol occurs on a right-hand side, and the balanced-parenthesis
language with the rule `S → ε`. Each grammar gets accepted and rejected words, including the
empty word, through `cyk` and through the `Decidable` instance on language membership. The file
also checks exact tick counts, and that the bundled invariant is not vacuous.
-/

public section

namespace ComplexityTests.CYK

open Cslib Cslib.Algorithms.Lean.CYK ChomskyNormalFormRule

/-! ### `{aⁿbⁿ | n ≥ 1}` -/

/-- Nonterminals for `{aⁿbⁿ}`. -/
inductive N
  | S | X | A | B
  deriving DecidableEq, Repr

/-- `{aⁿbⁿ | n ≥ 1}`: `S → AB | AX`, `X → SB`, `A → a`, `B → b`. The start symbol `S` occurs on
the right-hand side of `X → SB`, which is allowed since there is no rule `S → ε`. -/
@[expose] def anbn : ChomskyNormalFormGrammar Char where
  NT := N
  initial := .S
  rules := [node .S .A .B, node .S .A .X, node .X .S .B, leaf .A 'a', leaf .B 'b']
  nilRule := false
  initial_notMem_output := by simp

instance : DecidableEq anbn.NT := inferInstanceAs (DecidableEq N)

example : cyk anbn ['a', 'b'] = true := by decide
example : cyk anbn ['a', 'a', 'b', 'b'] = true := by decide
example : cyk anbn ['a', 'a', 'a', 'b', 'b', 'b'] = true := by decide
example : cyk anbn ['a', 'b', 'a', 'b'] = false := by decide
example : cyk anbn ['a', 'a', 'b'] = false := by decide
example : cyk anbn ['b', 'a'] = false := by decide
example : cyk anbn ['a'] = false := by decide
example : cyk anbn [] = false := by decide

example : ['a', 'a', 'b', 'b'] ∈ anbn.toCFG.language := by decide
example : ['a', 'b', 'b'] ∉ anbn.toCFG.language := by decide
example : [] ∉ anbn.toCFG.language := by decide

/-- Reading derivations off the table: `X` derives `abb` (the cell of length `3` at position `1`
of `aabb`), and `S` does not derive `abab`. The nonterminals are given type `anbn.NT`, so that
`decide` finds the `DecidableEq anbn.NT` instance. -/
example : anbn.toCFG.Derives [.nonterminal N.X] ((['a', 'b', 'b'] : List Char).map .terminal) :=
  (mem_table_iff (G := anbn) (w := ['a', 'a', 'b', 'b']) (L := 3) (i := 1) (l := 3) (by decide)
    (by decide) (by decide) (show anbn.NT from N.X)).mp (by decide)

example : ¬ anbn.toCFG.Derives [.nonterminal anbn.initial]
    ((['a', 'b', 'a', 'b'] : List Char).map .terminal) :=
  fun h => absurd ((mem_table_iff (G := anbn) (w := ['a', 'b', 'a', 'b']) (L := 4) (i := 0)
    (l := 4) (by decide) (by decide) (by decide) anbn.initial).mpr h) (by decide)

/-- Exact tick count on `aabb`: `(5 + 1) (4 + C(5, 3)) = 84`, from `time_cykM` and by evaluation. -/
example : (cykM anbn ['a', 'a', 'b', 'b']).time = 84 := by
  rw [time_cykM]
  rfl

example : (cykM anbn ['a', 'a', 'b', 'b']).time = 84 := by decide

example : (cykM anbn ['a', 'a', 'b', 'b']).ret = true := by decide

/-! ### Balanced parentheses, with `ε` -/

/-- Nonterminals for the balanced-parenthesis language. -/
inductive D
  | Z | S | Y | L | R
  deriving DecidableEq, Repr

/-- Balanced parentheses, including `ε`: `Z → ε | LR | LY | SS`, `S → LR | LY | SS`, `Y → SR`,
`L → (`, `R → )`. The start symbol `Z` occurs on no right-hand side, as the rule `Z → ε`
requires. -/
@[expose] def dyck : ChomskyNormalFormGrammar Char where
  NT := D
  initial := .Z
  rules := [node .Z .L .R, node .Z .L .Y, node .Z .S .S,
    node .S .L .R, node .S .L .Y, node .S .S .S, node .Y .S .R, leaf .L '(', leaf .R ')']
  nilRule := true
  initial_notMem_output := by simp [output]

instance : DecidableEq dyck.NT := inferInstanceAs (DecidableEq D)

example : [] ∈ dyck.toCFG.language := by decide
example : ['(', ')'] ∈ dyck.toCFG.language := by decide
example : ['(', '(', ')', ')'] ∈ dyck.toCFG.language := by decide
example : ['(', '(', ')', ')', '(', ')'] ∈ dyck.toCFG.language := by decide
example : ['(', ')', ')', '('] ∉ dyck.toCFG.language := by decide
example : ['('] ∉ dyck.toCFG.language := by decide
example : [')', '('] ∉ dyck.toCFG.language := by decide

/-- Insertion skips repeats: the cell of `()()` holds `S` and `Z` once each, although each is
found at two split points. (`S` is given type `dyck.NT` so that `decide` finds the
`DecidableEq dyck.NT` instance.) -/
example : table dyck ['(', ')', '(', ')'] 4 0 4 = [show dyck.NT from D.S, dyck.initial] := by
  decide

/-- The empty word is free; on `()()` the cost is `(9 + 1) (4 + C(5, 3)) = 140`. -/
example : (cykM dyck []).time = 0 := rfl
example : (cykM dyck ['(', ')', '(', ')']).time = 140 := by
  rw [time_cykM]
  rfl

/-! ### The invariant is not vacuous -/

/-- With the rule `S → ε`, no rule may use the start symbol on its right-hand side; `dyck` shows
that such grammars exist. -/
example (G : ChomskyNormalFormGrammar Char) (h : G.nilRule = true) :
    node G.initial G.initial G.initial ∉ G.rules :=
  fun hr => G.initial_notMem_output h _ hr (by simp [output])

example : dyck.nilRule = true := rfl

end ComplexityTests.CYK
