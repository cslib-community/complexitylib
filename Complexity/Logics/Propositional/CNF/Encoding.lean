/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair

/-!
# Encodings of clauses and CNF formulas

A machine reads a formula in conjunctive normal form through an encoding `enc : V ↪ List Bool`
of its variables. A literal `(v, b)` is the framed `enc v` followed by its polarity bit `b`
(`encPair enc encBool`); a clause is the concatenation of its framed literals
(`Cslib.Logic.PL.encClause`), and a formula the concatenation of its framed clauses
(`Cslib.Logic.PL.encCNFOver`). Both are reducible abbreviations, so `fun_prop` and the
combinators' lemmas see through the names. `omega` does not, since it compares atoms
syntactically: state the bounds it combines with the same spelling.

`Cslib.Complexity.encCNF`, the encoding of the instances of `SAT`, is definitionally
`encCNFOver encNat`: variables numbered by natural numbers written in binary.

## Main definitions

* `Cslib.Logic.PL.encClause`: clauses over an encoding of the variables.
* `Cslib.Logic.PL.encCNFOver`: formulas over an encoding of the variables.
-/

@[expose] public section

namespace Cslib.Logic.PL

open Turing.MultiTapeTM

variable {V : Type}

/-- Clauses over variables encoded by `enc`: the concatenation of the framed literals, a literal
`(v, b)` being the framed `enc v` followed by the polarity bit `b`. -/
abbrev encClause (enc : V ↪ List Bool) : Clause V ↪ List Bool :=
  encList (encPair enc encBool)

/-- Formulas in conjunctive normal form over variables encoded by `enc`: the concatenation of the
framed clauses, each encoded by `encClause enc`. -/
abbrev encCNFOver (enc : V ↪ List Bool) : CNF V ↪ List Bool :=
  encList (encClause enc)

end Cslib.Logic.PL
