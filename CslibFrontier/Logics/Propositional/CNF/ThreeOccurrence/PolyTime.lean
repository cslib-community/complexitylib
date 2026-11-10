/-
Copyright (c) 2026 Erik Demaine, Stefan Langerman, GPT 5.6. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ThreeOccurrence
public import CslibFrontier.Logics.Propositional.CNF.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time occurrence splitting

The occurrence-splitting construction of [Papadimitriou, Proposition 9.3][Papadimitriou94] is
polynomial-time. Original variable labels keep their supplied encoding. The new clause and literal
positions use unary encodings bounded by the input's literal and clause counts. In particular,
binary natural labels are never expanded into unary labels.

## Main results

* `Cslib.Logic.PL.CNF.computableInPolyTime_implicationCycle`: constructing binary cycles.
* `Cslib.Logic.PL.CNF.computableInPolyTime_toThreeOccurrence`: certified splitting.

## References

* [C. H. Papadimitriou, *Computational Complexity*, Proposition 9.3][Papadimitriou94]
-/

public section

namespace Cslib.Logic.PL.CNF

open Turing.MultiTapeTM

variable {V : Type} (enc : V ↪ List Bool)

private theorem implicationPath_eq_zip (first current : V) (rest : List V) :
    implicationPath first current rest =
      ((current :: rest).zip (rest ++ [first])).map (fun p => [(p.1, false), (p.2, true)]) := by
  induction rest generalizing current with
  | nil => rfl
  | cons next rest ih => simp [implicationPath, ih]

private theorem implicationCycle_eq_zip (vs : List V) :
    implicationCycle vs =
      (vs.zip (vs.tail ++ vs.take 1)).map (fun p => [(p.1, false), (p.2, true)]) := by
  cases vs <;> simp [implicationCycle, implicationPath_eq_zip]

/-- Building binary implication cycles is polynomial-time for any variable encoding. -/
@[fun_prop]
theorem computableInPolyTime_implicationCycle :
    ComputableInPolyTime (implicationCycle (V := V)) (encList enc)
      (encCNFOver enc) := by
  rw [show (implicationCycle (V := V)) =
    (fun vs => (vs.zip (vs.tail ++ vs.take 1)).map
      (fun p => [(p.1, false), (p.2, true)])) from funext implicationCycle_eq_zip]
  fun_prop

/-- Separating occurrences uses unary positions and preserves the original variable encoding. -/
@[fun_prop]
theorem computableInPolyTime_occurrenceClauses :
    ComputableInPolyTime (occurrenceClauses (V := V))
      (encCNFOver enc) (encCNFOver (encPair enc (encPair encUnary encUnary))) := by
  unfold occurrenceClauses
  fun_prop

/-- Splitting is polynomial-time, with no unary expansion of original variable labels. -/
@[fun_prop]
theorem computableInPolyTime_toThreeOccurrence [DecidableEq V] :
    ComputableInPolyTime (toThreeOccurrence (V := V))
      (encCNFOver enc) (encCNFOver (encPair enc (encPair encUnary encUnary))) := by
  unfold toThreeOccurrence occurrenceCopies
  fun_prop

end Cslib.Logic.PL.CNF
