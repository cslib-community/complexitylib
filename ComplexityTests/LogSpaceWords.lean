/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-! # Logspace pair manipulation built from the word operations -/

@[expose] public section

namespace Turing.MultiTapeTM.Tests.LogSpaceWords

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

/-- Swapping the components of a pair. -/
example : ComputableInLogSpace (fun p : α × β => (p.2, p.1)) (encPair encA encB)
    (encPair encB encA) :=
  (ComputableInLogSpace.snd encA encB).pair (ComputableInLogSpace.fst encA encB)

/-- Duplicating a value into both components. -/
example : ComputableInLogSpace (fun a : α => (a, a)) encA (encPair encA encA) :=
  ComputableInLogSpace.id.pair ComputableInLogSpace.id

/-- Whether the second component of a pair of bit strings is empty. -/
example : ComputableInLogSpace (fun p : List Bool × List Bool => p.2.isEmpty)
    (encPair encBits encBits) encBool :=
  (ComputableInLogSpace.of_isEmpty (encIn := encBits) fun _ => rfl).comp
    (ComputableInLogSpace.snd encBits encBits)

end Turing.MultiTapeTM.Tests.LogSpaceWords
