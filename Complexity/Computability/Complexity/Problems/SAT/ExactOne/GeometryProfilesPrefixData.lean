/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfilesData
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryPrefix

/-!
# Actual source-boundary prefix data for positive exact-one profiles

The source placeholders in each fixed positive profile are moved to their boundary ports and
their sole incidence routes are extended accordingly. The large finite continuous certificates
are separate, in `GeometryProfilesPrefix`.

## Main definitions

* `profilePrefixGeometry`: the actual profile with source endpoints at boundary ports.

## References

The composed geometric data are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

/-- The actual positive profile with its source ends extended to the cell boundary. -/
def profilePrefixGeometry (p : ClauseProfile) : LocalGeometry := (profileGeometry p).toPrefix

end Cslib.Complexity.SAT.ExactOne
