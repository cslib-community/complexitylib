/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Memory.Record

/-!
# Normalizing record programs linked to memory

These equations expose primitive reads, writes and conditional source branches without
unfolding an entire record interpreter. Native method proofs can normalize the same source at
the program boundary and in reached-state hypotheses.

## Main results

* `Record.Layout.lift_read`, `Record.Layout.lift_write`: linked primitives are memory primitives.
* `Record.lift_ite`: conditional distribution specialized to the record-to-memory interpreter.

These are source equations, with no execution, validity or resource-bound claim.
-/

public section

namespace Cslib.DataStructure.Record

variable {ι α : Type} [DecidableEq ι] {ok : ι → Prop}

/-- A layout interprets a record read at its literal memory address. -/
theorem Layout.lift_read (L : Layout ok) (w : ℕ) (i : ι) :
    (PFunctor.FreeM.liftM (L.methods w) (read i) : Memory.Prog ℕ) = Memory.read (L.addr i) := rfl

/-- A layout interprets a record write at its literal memory address. -/
theorem Layout.lift_write (L : Layout ok) (w : ℕ) (i : ι) (k : ℕ) :
    (PFunctor.FreeM.liftM (L.methods w) (write i k) : Memory.Prog Unit) =
      Memory.write (L.addr i) k := rfl

omit [DecidableEq ι] in
/-- Interpreting a source branch distributes over that branch. Specializing `apply_ite` to the
interpreter avoids arbitrary conditional permutations during simplification. -/
theorem lift_ite (interp : (o : Op ι) → Memory.Prog (Op.Result o))
    (P : Prop) [Decidable P] (yes no : Prog ι α) :
    (PFunctor.FreeM.liftM interp (if P then yes else no) : Memory.Prog α) =
      if P then PFunctor.FreeM.liftM interp yes else PFunctor.FreeM.liftM interp no :=
  apply_ite _ _ _ _

end Cslib.DataStructure.Record
