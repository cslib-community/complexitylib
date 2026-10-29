/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Computability.Complexity.Problems.SAT
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# CNF construction and encoding tests

The generic constructor certificates compose with arbitrary variable encodings and specialize
to the binary encoding of SAT. Exactly-one constraints count distinct variables, including when
the input list contains repetitions.
-/

namespace ComplexityTests.CNFPolyTime

open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM

example {V : Type} [DecidableEq V] (enc : V ↪ List Bool) :
    ComputableInPolyTime
      (fun p : List V × V => CNF.exactlyOne p.1 ++ [Clause.imp p.1 p.2])
      (encPair (encList enc) enc) (encList (encList (encPair enc encBool))) := by
  fun_prop

-- Enumeration uses unary indices, while the resulting SAT instance has binary labels.
example : ComputableInPolyTime (fun n => CNF.exactlyOne (List.range n))
    encUnary encCNF := by
  have h := (CNF.computableInPolyTime_relabel (f := id)
    ComputableInPolyTime.unary_to_binary).comp
    ((CNF.computableInPolyTime_exactlyOne encUnary).comp
      ComputableInPolyTime.range)
  simpa only [Function.comp_def, CNF.relabel_id, encCNF] using h

-- Computability of relabelling does not require the renaming to be injective.
example : ComputableInPolyTime (CNF.relabel fun _ : ℕ => 0) encCNF encCNF := by
  fun_prop

example : CNF.exactlyOne ([] : List ℕ) = [[]] := rfl

example : (CNF.exactlyOne [7, 7]).eval (fun _ => true) = true := rfl

example : (CNF.exactlyOne [7, 9]).eval (fun _ => true) = false := rfl

end ComplexityTests.CNFPolyTime
