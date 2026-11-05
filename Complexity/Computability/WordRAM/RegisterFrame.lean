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

* `Code.preserves_rename`: injective renaming retains a register preservation guarantee.
* `Code.preserves_rename_of_forall_ne`: registers outside an embedded register bank are
  preserved without unfolding the subroutine's instruction graph.
* `Code.preserves_rename_of_offset`: a contiguous bank preserves registers outside its interval.
-/

public section

namespace Cslib.WordRAM

/-- An injectively embedded routine preserves the corresponding embedded register. -/
theorem Code.preserves_rename {B : Basis} {r s : ℕ} {f : Fin r → Fin s}
    (hf : f.Injective) {i : Fin r} {c : Code B r} (h : c.Preserves i) :
    (c.rename f).Preserves (f i) := by
  induction c with
  | op o =>
    cases o <;> simp only [Code.rename, Code.Preserves, Op.rename, Op.dest,
      ne_eq, Option.some.injEq, hf.eq_iff, reduceCtorEq, not_false_eq_true] at h ⊢ <;> exact h
  | seq a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | branch cond pos neg ihp ihn => exact ⟨ihp h.1, ihn h.2⟩
  | loop cond body ih => exact ih h
  | rand dst src => simpa only [Code.rename, Code.Preserves, ne_eq, hf.eq_iff] using h

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

/-- A subroutine placed at a fixed register offset preserves every register outside its bank.
The value equation also covers enumerated embeddings once their offset is checked. -/
theorem Code.preserves_rename_of_offset {B : Basis} {r s offset : ℕ}
    (c : Code B r) (f : Fin r → Fin s) (hf : ∀ j, (f j).val = offset + j.val)
    (i : Fin s) (hi : i.val < offset ∨ offset + r ≤ i.val) :
    (c.rename f).Preserves i := by
  apply c.preserves_rename_of_forall_ne
  intro j he
  have hv := congrArg Fin.val he
  rw [hf] at hv
  have hj := j.isLt
  omega

end Cslib.WordRAM
