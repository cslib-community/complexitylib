/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Occurrence
public import CslibFrontier.Computability.PolyTime.CSP.Vars
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Native polynomial-time CSP occurrence enumeration

The existing ordered scan uses unary constraint and scope positions and retains the supplied
variable encoding. Its certificate needs neither graph construction nor augmentation.

## Main results

* `Cslib.Complexity.CSP.computableInPolyTime_occurrences`: native enumeration of every record.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Turing.MultiTapeTM

variable {Rel V : Type}

/-- A record consists of a unary constraint index paired with a unary scope index and the source
variable; the outer index and the inner index are framed by `encPair`. -/
@[expose] def encOccurrenceRecord (encV : V ↪ List Bool) : (ℕ × ℕ × V) ↪ List Bool :=
  encPair encUnary (encPair encUnary encV)

/-- Ordered occurrence enumeration is polynomial-time, with unary positions and binary (or any
other fixed encoded) source variables. No bound on arity or degree is needed. -/
@[fun_prop]
theorem computableInPolyTime_occurrences (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.occurrences (Rel := Rel) (V := V))
      (encCSP encRel encV) (encList (encOccurrenceRecord encV)) := by
  have ho := Cslib.Logic.PL.computableInPolyTime_occurrences encV
  have hv := computableInPolyTime_varCNF encRel encV
  unfold Cslib.Logic.PL.encOccurrence at ho
  unfold CSP.occurrences encOccurrenceRecord
  fun_prop

end Cslib.Complexity.CSP
