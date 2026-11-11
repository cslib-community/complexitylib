/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.RandomPermutation
import CslibFrontier.Probability.PMF.Uniform

/-!
# Reprogramming one entry of a permutation

`force` swaps two images, so forcing an entry always leaves a genuine permutation.
The old image is retained by `forceEquiv`; this change of variables is an involution.
Consequently forcing an independent uniform target into a uniform permutation gives the
exact planted joint law, including arbitrary subsequent observations of the permutation.

## Main definitions

* `Cslib.RandomPermutation.force`: force a chosen input to a chosen output by an image swap.
* `Cslib.RandomPermutation.forceEquiv`: the reversible change of variables retaining the old image.

## Main results

* `Cslib.RandomPermutation.force_apply`: the required entry is installed.
* `Cslib.RandomPermutation.force_restore`: forcing the old image restores the original permutation.
* `Cslib.RandomPermutation.uniform_force`: the exact planted joint distribution.
-/

public section

namespace Cslib.RandomPermutation

open Probability

variable {Word : Type} [DecidableEq Word]

/-- Force `π input = target` by swapping the old image and target. No entry is overwritten
without repairing its other preimage, even when the target was already in use. -/
@[expose] def force (π : Equiv.Perm Word) (input target : Word) : Equiv.Perm Word :=
  π.trans (Equiv.swap (π input) target)

/-- The forced entry has exactly the requested output. -/
@[simp] theorem force_apply (π : Equiv.Perm Word) (input target : Word) :
    force π input target input = target := by
  simp [force]

/-- Only the original input and the original preimage of the target can change. -/
theorem force_apply_of_ne (π : Equiv.Perm Word) (input target query : Word)
    (hi : query ≠ input) (ht : π query ≠ target) : force π input target query = π query := by
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hi (π.injective h)) ht

/-- Inverse answers can change only at the old image and the forced target. -/
theorem force_symm_apply_of_ne (π : Equiv.Perm Word) (input target query : Word)
    (hi : query ≠ π input) (ht : query ≠ target) :
    (force π input target).symm query = π.symm query := by
  change π.symm ((Equiv.swap (π input) target).symm query) = π.symm query
  rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hi ht]

/-- Forcing the original image restores the whole permutation, not only its forced entry. -/
theorem force_restore (π : Equiv.Perm Word) (input target : Word) :
    force (force π input target) input (π input) = π := by
  ext query
  simp only [force, Equiv.trans_apply, Equiv.swap_apply_left]
  rw [Equiv.swap_comm target (π input)]
  exact (Equiv.swap (π input) target).symm_apply_apply (π query)

/-- Reversible forcing: exchange the requested image with the old image, retaining both
permutation and displaced value. This is an involution, including the no-change case. -/
@[expose] def forceEquiv (input : Word) :
    (Equiv.Perm Word × Word) ≃ (Equiv.Perm Word × Word) :=
  (show Function.Involutive (fun p : Equiv.Perm Word × Word =>
      (force p.1 input p.2, p.1 input)) from by
    rintro ⟨π, target⟩
    simp only [force_restore, force_apply]).toPerm

/-- The exact joint planted law: force an independent uniform target, then perform any
observation of the entire permutation and target. -/
theorem uniform_force [Fintype Word] [Nonempty Word] {Output : Type}
    (input : Word) (observe : Equiv.Perm Word → Word → PMF Output) :
    ((PMF.uniformOfFintype (Equiv.Perm Word)).bind fun π =>
      (PMF.uniformOfFintype Word).bind fun target => observe (force π input target) target) =
        (PMF.uniformOfFintype (Equiv.Perm Word)).bind fun π => observe π (π input) := by
  have h := PMF.uniformOfFintype_bind_bind_fst_equiv (forceEquiv input)
    (fun π => observe π (π input))
  change ((PMF.uniformOfFintype (Equiv.Perm Word)).bind fun π =>
    (PMF.uniformOfFintype Word).bind fun target =>
      observe (force π input target) (force π input target input)) = _ at h
  simpa only [force_apply] using h

end Cslib.RandomPermutation
