/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem
public import CslibFrontier.Foundations.GroupTheory.Perm.Fin

/-!
# The original ordered-scope permutation

The permutation follows the actual argument positions of each constraint. Its complete
orbits are precisely the nonempty constraint-position fibers, including singleton scopes.
Repeated names and duplicate rows keep their positional identity; nullary scopes have no
occurrences. These unchanged declarations are relocated from `Primal.Graph` for use without
polygon graphs, geometry or native gadget runtime.

## Main definitions

* `Cslib.Complexity.CSP.argumentPermutation`: ordered argument succession with its inverse.

## Main results

* `Cslib.Complexity.CSP.sameCycle_argumentPermutation`: exact constraint-position fibers.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

/-- Argument succession, with an explicit inverse at each constraint position. -/
@[expose] def argumentPermutation (F : CSP Rel V) : Equiv.Perm F.Occurrence where
  toFun := argumentSuccessor
  invFun o := ⟨o.1, (finRotate _).symm o.2⟩
  left_inv := by
    rintro ⟨i, j⟩
    exact congrArg (fun k : Fin F[i.val].2.length => (⟨i, k⟩ : F.Occurrence))
      ((finRotate _).symm_apply_apply j)
  right_inv := by
    rintro ⟨i, j⟩
    exact congrArg (fun k : Fin F[i.val].2.length => (⟨i, k⟩ : F.Occurrence))
      ((finRotate _).apply_symm_apply j)

omit [DecidableEq V] in
/-- The scope permutation has exactly one orbit per nonempty constraint position. -/
theorem sameCycle_argumentPermutation (o p : F.Occurrence) :
    (argumentPermutation F).SameCycle o p ↔ o.1 = p.1 := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hi (k : ℕ) : ((argumentPermutation F)^[k] o).1 = o.1 := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact ih
    simpa only [Equiv.Perm.iterate_eq_pow, hn] using (hi n).symm
  · rcases o with ⟨i, j⟩
    rcases p with ⟨k, l⟩
    intro h
    change i = k at h
    subst k
    obtain ⟨n, hn⟩ := (Equiv.Perm.sameCycle_finRotate j l).exists_nat_pow_eq
    have hi (k : ℕ) : (argumentPermutation F)^[k] ⟨i, j⟩ =
        ⟨i, (finRotate _)^[k] j⟩ := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
        rfl
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, ← Equiv.Perm.iterate_eq_pow, hi, Equiv.Perm.iterate_eq_pow, hn]

end Cslib.Complexity.CSP
