/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.DNF
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair

/-!
# Encodings of terms and DNF formulas

A machine reads a formula in disjunctive normal form through an encoding `enc : V ↪ List Bool`
of its variables, dually to `Cslib.Logic.PL.encCNFOver`. A literal `(v, b)` is the framed `enc v`
followed by its polarity bit `b` (`encPair enc encBool`); a term is the concatenation of its
framed literals (`Cslib.Logic.PL.encTermOver`), and a formula the concatenation of its framed
terms (`Cslib.Logic.PL.encDNFOver`). Both are reducible abbreviations, so `fun_prop` and the
combinators' lemmas see through the names.

`Cslib.Complexity.encDNF`, the encoding of the instances of `#DNF`, is defined as
`encDNFOver encNat`: variables numbered by natural numbers written in binary.

## Main definitions

* `Cslib.Logic.PL.encTermOver`: terms over an encoding of the variables.
* `Cslib.Logic.PL.encDNFOver`: formulas over an encoding of the variables.
-/

@[expose] public section

namespace Cslib.Logic.PL

open Turing.MultiTapeTM

variable {V : Type}

/-- Terms over variables encoded by `enc`: the concatenation of the framed literals, a literal
`(v, b)` being the framed `enc v` followed by the polarity bit `b`. -/
abbrev encTermOver (enc : V ↪ List Bool) : Term V ↪ List Bool :=
  encList (encPair enc encBool)

/-- Formulas in disjunctive normal form over variables encoded by `enc`: the concatenation of the
framed terms, each encoded by `encTermOver enc`. -/
abbrev encDNFOver (enc : V ↪ List Bool) : DNF V ↪ List Bool :=
  encList (encTermOver enc)

end Cslib.Logic.PL
