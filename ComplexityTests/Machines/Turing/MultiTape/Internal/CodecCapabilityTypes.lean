/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Capabilities

/-! The capability declarations alone do not import any tidy computability predicate. -/

run_cmd do
  let env ← Lean.getEnv
  for n in [``Turing.MultiTapeTM.ComputableInLinearTimeAndSpace,
      ``Turing.MultiTapeTM.PairEncoding, ``Turing.MultiTapeTM.ListEncoding,
      ``Turing.MultiTapeTM.OptionEncoding] do
    unless env.contains n do throwError "missing plain capability {n}"
  for n in [`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace,
      `Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace,
      `Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree,
      `Turing.MultiTapeTM.ComputableTidilyInO] do
    if env.contains n then throwError "high tidy predicate in capability closure: {n}"
