/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier
import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id
import Cslib.Foundations.Data.PFunctor.Free

/-!
# Smoke test

Checks that the cslib base pin exposes the upstream APIs this library builds on.
-/

namespace ComplexityTests

/-- The upstream time-and-space computability predicate. -/
example := @Turing.MultiTapeTM.ComputableInTimeAndSpace

/-- The upstream complexity of the identity function. -/
example := @Turing.MultiTapeTM.computableInTimeAndSpace_id

/-- The free monad the program layer is built on. -/
example := @PFunctor.FreeM

end ComplexityTests
