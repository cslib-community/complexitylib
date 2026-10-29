/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Allocation
import Mathlib.Data.List.GetD

/-!
# Array blocks in ordinary initialized inputs

## Main results

* `WordRAM.Data.init_realizes_append`: a list segment appears at its actual initialized address,
  including the machine's length header.

This is a representation lemma for the existing `Data.init`, with no alternate input convention.
It lives in a narrow input-array module to keep the list `getD` dependency and initialization
bridge out of `Allocation`. This avoids changing the allocation interface and rebuilding its
unrelated importers when the input representation API changes.
-/

@[expose] public section

namespace Cslib.WordRAM

/-- The payload between an arbitrary prefix and suffix occupies its corresponding actual
input block. The extra address word is the standard unsigned input-length header. -/
theorem Data.init_realizes_append {r : ℕ} (pre payload post : List ℕ) :
    (Block.mk (pre.length + 1) payload.length).Realizes
      (Data.init (pre ++ (payload ++ post)) : Data r).mem payload.get := by
  intro i
  change (Data.init (pre ++ (payload ++ post)) : Data r).mem
    (pre.length + 1 + i.val) = payload.get i
  rw [show pre.length + 1 + i.val = (pre.length + i.val) + 1 by omega,
    Data.init_mem_succ, List.getD_append_right _ _ _ _ (by omega),
    Nat.add_sub_cancel_left, List.getD_append _ _ _ _ i.isLt, List.getD_eq_get]

end Cslib.WordRAM
