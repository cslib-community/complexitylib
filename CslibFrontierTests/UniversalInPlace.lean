/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.InPlace

/-! The records of the in-place universal fold keep the words of the tuples they replace. -/

namespace CslibFrontierTests.UniversalInPlace

open Turing.MultiTapeTM Turing.MultiTapeTM.Universal

-- A simulated machine is encoded as the pair of its description and configuration.
example (r : Sim) : eSim r = encPair eDesc eCfg (r.desc, r.cfg) := rfl

end CslibFrontierTests.UniversalInPlace
