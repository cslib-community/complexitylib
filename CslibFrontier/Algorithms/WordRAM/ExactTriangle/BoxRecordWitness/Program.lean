/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.Program
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Program

/-!
# The box product followed by original-weight witness verification

The selected record executes the actual threshold-aware box backend and then the existing
read-only verifier. Register banks, query decoding and witness semantics are shared with
`RecordWitness`; the changed output layout is established by execution of the box program.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.BoxRecordWitness

open Cslib.WordRAM RecordWitness

/-- Actual box-product call followed by the unchanged original-weight consumer. -/
@[expose] def program : Code .standard 400 :=
  .seq (RecordBoxProduct.program.rename productBank) consume

end Cslib.Algorithms.WordRAM.ExactTriangle.BoxRecordWitness
