/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Fintype/BigOperators.lean`, next to
-- `Fintype.card_filter_piFinset_eq`)

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.BigOperators

/-!
# Functions that agree with a fixed function on a set

The functions `b : ι → β` that agree with a fixed `y` on a finite set `P` of coordinates number
`#β ^ #Pᶜ`, since the coordinates outside `P` are free. Mathlib fixes a single coordinate
(`Fintype.card_filter_piFinset_eq`); this file fixes a set of them.

## Main results

* `Fintype.card_filter_forall_mem_eq`: `#{b | ∀ i ∈ P, b i = y i} = #β ^ #Pᶜ`.
-/

public section

namespace Fintype

open Finset

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

/-- The functions that agree with `y` on `P` number `#β ^ #Pᶜ`. The filter's decidability is an
instance argument, so the lemma rewrites whichever instance elaborated the filter (on `Fin n`,
`Nat.decidableForallFin`). -/
theorem card_filter_forall_mem_eq (P : Finset ι) (y : ι → β)
    [DecidablePred fun b : ι → β => ∀ i ∈ P, b i = y i] :
    #{b : ι → β | ∀ i ∈ P, b i = y i} = Fintype.card β ^ #Pᶜ := by
  have h : ({b : ι → β | ∀ i ∈ P, b i = y i} : Finset (ι → β)) =
      piFinset fun i => if i ∈ P then {y i} else univ := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_piFinset]
    refine forall_congr' fun i => ?_
    by_cases hi : i ∈ P <;> simp [hi]
  rw [h, card_piFinset]
  simp only [apply_ite Finset.card, card_singleton, card_univ, prod_ite, prod_const_one, one_mul,
    prod_const]
  congr 2
  ext i
  simp

end Fintype
