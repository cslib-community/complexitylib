/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Encoded.AssignmentTester
public import Mathlib.Data.FinEnum

/-!
# Constructive enumeration of assignment-tester coins

The conjunction and selected testers use the same product coins. Batching their component
enumerations keeps instance synthesis within its ordinary limits.

## Main definitions

* `Cslib.PCP.HadamardTester.Rand.finEnum`: constructive enumeration of the product coins.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.HadamardTester

/-- Concrete bit enumeration, registered locally while constructing the tester's coins. -/
local instance instFinEnumBool : FinEnum Bool :=
  FinEnum.ofList [false, true] (by decide)

/-- Constructively enumerate the tester's coins. Batching the repeated factors keeps the nested
product within instance-synthesis limits. -/
@[instance_reducible]
def Rand.finEnum (α : Type) [FinEnum α] : FinEnum (Rand α) :=
  let linear : FinEnum (LinPos α) := inferInstance
  let quadratic : FinEnum (QuadPos α) := inferInstance
  let equations : FinEnum (EqnRand α) := inferInstance
  letI := linear
  letI := quadratic
  letI := equations
  inferInstanceAs (FinEnum (_ × _ × _ × _ × _))

end Cslib.PCP.HadamardTester
