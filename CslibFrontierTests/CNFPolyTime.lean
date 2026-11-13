/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Computability.Complexity.Problems.SAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# CNF construction and encoding tests

The generic constructor and evaluation certificates compose with arbitrary variable encodings
and specialize to the binary encoding of SAT. Exactly-one constraints count distinct variables,
including when the input list contains repetitions. Literal occurrence records keep the encoded
words of the right-nested tuple and expose their fields to `fun_prop`.
-/

namespace CslibFrontierTests.CNFPolyTime

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

-- Evaluation composes without unfolding `CNF.eval`, `Clause.eval` or `Literal.eval`: the
-- assignment needs a certificate as a function of the input and the variable.
example {V : Type} (enc : V ↪ List Bool) {σ : List Bool → V → Bool}
    (hσ : ComputableInPolyTime (fun p : List Bool × V => σ p.1 p.2) (encPair encBits enc)
      encBool) :
    ComputableInPolyTime (fun p : CNF V × List Bool => p.1.eval (σ p.2) && !p.1.isEmpty)
      (encPair (encCNFOver enc) encBits) encBool := by
  have hσ' : ComputableInPolyTime (fun p : (CNF V × List Bool) × V => σ p.1.2 p.2)
      (encPair (encPair (encCNFOver enc) encBits) enc) encBool := by fun_prop
  fun_prop

-- An arbitrary assignment still needs its own certificate.
example {V : Type} (_enc : V ↪ List Bool) (_σ : List Bool → V → Bool) : True := by
  fail_if_success
    have : ComputableInPolyTime (fun p : CNF V × List Bool => p.1.eval (_σ p.2))
        (encPair (encCNFOver _enc) encBits) encBool := by fun_prop
  trivial

example : CNF.exactlyOne ([] : List ℕ) = [[]] := rfl

example : (CNF.exactlyOne [7, 7]).eval (fun _ => true) = true := rfl

example : (CNF.exactlyOne [7, 9]).eval (fun _ => true) = false := rfl

-- Occurrences record clause and literal positions, keeping repeated literals.
example : occurrences [[(7, true), (7, true)], [(9, false)]] =
    [⟨0, 0, (7, true)⟩, ⟨0, 1, (7, true)⟩, ⟨1, 0, (9, false)⟩] := by decide

-- The occurrence record has the same encoded words as the right-nested tuple
-- `(clause, pos, lit)`.
example {V : Type} (enc : V ↪ List Bool) (o : Occurrence V) :
    encOccurrence enc o = encPair encUnary (encPair encUnary (encPair enc encBool))
      (o.clause, o.pos, o.lit) := rfl

-- Field reads compose through the generated rules without unfolding the encoding.
example {α V : Type} {encA : α ↪ List Bool} (enc : V ↪ List Bool) {f : α → Occurrence V}
    (hf : ComputableInPolyTime f encA (encOccurrence enc)) :
    ComputableInPolyTime (fun a => ((f a).clause, (f a).lit.1)) encA (encPair encUnary enc) := by
  fun_prop

end CslibFrontierTests.CNFPolyTime
