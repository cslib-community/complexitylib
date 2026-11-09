/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- Also in cslib PR #1112 @0b9e55ce.

public import Cslib.Foundations.Data.Fin.Tuple

/-!
# Appending constant tuples

The addition of Christian Reitwiessner's branch `crei/tidy-universal` (and of cslib PR #1112) to
`Cslib.Foundations.Data.Fin.Tuple`: appending constant tuples gives a constant tuple.
-/

@[expose] public section

namespace Fin

variable {α : Sort*} {m n : ℕ}

/-- Appending two constant tuples gives a constant tuple. -/
theorem append_const (x : α) : append (fun _ : Fin m => x) (fun _ : Fin n => x) = fun _ => x :=
  append_castAdd_natAdd (f := fun _ => x)

end Fin
