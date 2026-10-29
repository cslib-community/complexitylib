/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Structured

/-!
# Register frames for renamed native programs

## Main results

* `Code.preserves_rename_of_forall_ne`: registers outside an embedded register bank are
  preserved without unfolding the subroutine's instruction graph.
-/

public section

namespace Cslib.WordRAM

/-- A renamed subroutine cannot write a register outside the image of its register embedding.
This generalizes the former private framing rule of the fusion-node register banks. -/
theorem Code.preserves_rename_of_forall_ne {B : Basis} {r r' : ℕ}
    (c : Code B r) (f : Fin r → Fin r') (i : Fin r') (hi : ∀ j, f j ≠ i) :
    (c.rename f).Preserves i := by
  induction c with
  | op o =>
    cases o <;> simp only [Code.rename, Code.Preserves, Op.rename, Op.dest,
      ne_eq, Option.some.injEq, reduceCtorEq, not_false_eq_true] <;> apply hi
  | seq a b iha ihb => exact ⟨iha, ihb⟩
  | branch cond pos neg ihp ihn => exact ⟨ihp, ihn⟩
  | loop cond body ih => exact ih
  | rand dst src => simpa only [Code.rename, Code.Preserves] using hi dst

end Cslib.WordRAM
