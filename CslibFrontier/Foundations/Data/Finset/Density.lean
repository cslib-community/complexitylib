/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Finset/Density.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Density

/-!
# Density of an event under relabelling

Relabelling a finite type by an equivalence does not change the density of an event: for
`e : α ≃ β`, the density of `{a | p (e a)}` in `α` equals the density of `{b | p b}` in `β`
(`Fintype.dens_filter_comp_equiv`). This is the form needed to reindex uniform seeds or
sample spaces; Mathlib's `Finset.dens_map_equiv` states the same invariance for the image of a
finset.

## Main results

* `Fintype.dens_filter_comp_equiv`: relabelling the sample space by an equivalence preserves the
  density of an event.
-/

public section

open Finset

namespace Fintype

/-- Relabelling the sample space by an equivalence does not change the density of an event. -/
theorem dens_filter_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (p : β → Prop)
    [DecidablePred p] : dens {a | p (e a)} = dens {b | p b} := by
  rw [← dens_map_equiv e, map_filter, map_univ_equiv]
  simp only [Function.comp_def, Equiv.apply_symm_apply]

end Fintype
