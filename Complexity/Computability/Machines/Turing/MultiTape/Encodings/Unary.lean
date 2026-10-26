/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Words

/-! # Unary natural numbers

The encoding and its equation are moved unchanged from the former quantitative primitives.
-/

namespace Turing.MultiTapeTM

/-- Natural numbers in unary: `n` is encoded by `n` ones. -/
@[expose] public def encUnary : ℕ ↪ List Bool :=
  ⟨fun n => List.replicate n true, fun m n h => by simpa using congrArg List.length h⟩

@[simp]
public lemma encUnary_apply (n : ℕ) : encUnary n = List.replicate n true := rfl

end Turing.MultiTapeTM
