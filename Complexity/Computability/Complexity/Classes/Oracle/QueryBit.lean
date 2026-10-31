/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Probabilistic.Oracle.Composition

/-!
# One request to an oracle language

`Cslib.Complexity.queryBit w` submits the word `w` and reads the first bit of the reply. Against
an oracle language `A` it returns `decide (w ∈ A)` and makes exactly the one request `w`; for a
polynomial-time word it is strict oracle PPT, since the word is written on the query buffer and
only one bit of the reply is read. The oracle closure rules and the bounded-query classes build
their one-request certificates from this program.

## Main definitions

* `Cslib.Complexity.queryBit`: one request, reading one bit of the reply.

## Main results

* `Cslib.Complexity.interpret_queryBit`: against `A`, the request answers membership in `A`.
* `Cslib.Complexity.queriesWith_queryBit`: the program makes exactly one request.
* `Cslib.Complexity.isOraclePPTOn_queryBit`: one request for a polynomial-time word is strict
  oracle PPT.
-/

@[expose] public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α : Type}

/-- **One request**: submit the word `w` and read the first bit of the reply. -/
def queryBit (w : List Bool) : WordQueryComp Unit Bool :=
  (fun reply => decide (reply = [true])) <$> (List.take 1 <$> OracleComp.query ((), w))

open Classical in
/-- Against an oracle language, one request answers membership of its word. -/
theorem interpret_queryBit (A : Set (List Bool)) (w : List Bool) :
    OracleComp.interpret (m := Id) (languageOracle A) (queryBit w) = decide (w ∈ A) := by
  change decide (List.take 1 (languageOracle A ((), w)) = [true]) = decide (w ∈ A)
  rw [languageOracle_apply]
  cases decide (w ∈ A) <;> rfl

/-- One request makes one request. -/
@[simp]
theorem queriesWith_queryBit (answer : Unit × List Bool → List Bool) (w : List Bool) :
    OracleComp.queriesWith answer (queryBit w) = [((), w)] := by
  simp [queryBit]

/-- One request for a polynomial-time word is strict oracle PPT: the word is written on the query
buffer and one bit of the reply is read. -/
theorem isOraclePPTOn_queryBit {req : α → List Bool} {input : α ↪ List Bool}
    (hreq : ComputableInPolyTime req input encBits) :
    IsOraclePPTOn input encBool
      (fun a => OracleComp.interpret ProbOracleComp.query (queryBit (req a))) := by
  simp only [queryBit, OracleComp.interpret_map, OracleComp.interpret_query]
  exact (IsOraclePPTOn.query_take' () hreq (limit := fun _ => 1)
    (ComputableInPolyTime.const 1)).map'
    (ComputableInPolyTime.id'.decide_eq' (ComputableInPolyTime.const [true]))

end Cslib.Complexity
