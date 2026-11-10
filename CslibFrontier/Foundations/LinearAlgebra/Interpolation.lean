/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, an interpolation bound on dimension)

public import CslibFrontier.Init
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Finset.Card
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Interpolation bounds the number of points

If a space of functions `α → K` interpolates every function on a finite set `G`, restricting to
`G` maps it onto `G → K`, so its dimension is at least `|G|`. For the span of finitely many
functions `v a`, `a ∈ s`, this gives `|G| ≤ |s|`
(`Cslib.LinearAlgebra.card_le_of_forall_exists_mem_span_eq`). This is the dimension count of the
polynomial method: if every function agrees on `G` with a combination of few functions, `G` is
small.

## Main results

* `Cslib.LinearAlgebra.card_le_of_forall_exists_mem_span_eq`: if every function agrees on `G` with
  a combination of the functions `v a` for `a ∈ s`, then `#G ≤ #s`.
-/

public section

namespace Cslib.LinearAlgebra

open Finset

/-- If every function agrees on `G` with a combination of the functions `v a` for `a ∈ s`, then `G`
has at most `#s` points: restricting the span to `G` is onto `G → K`. -/
theorem card_le_of_forall_exists_mem_span_eq {α ι K : Type*} [Field K]
    (G : Finset α) (s : Finset ι) (v : ι → α → K)
    (h : ∀ f : α → K, ∃ g ∈ Submodule.span K (v '' s), ∀ x ∈ G, g x = f x) : #G ≤ #s := by
  classical
  rw [← coe_image] at h
  -- restricting to `G` is onto
  let restrict := (LinearMap.funLeft K K ((↑) : G → α)).comp
    (Submodule.span K (s.image v : Set (α → K))).subtype
  have hsurj : Function.Surjective restrict := fun g => by
    obtain ⟨p, hp, hpx⟩ := h fun x => if hx : x ∈ G then g ⟨x, hx⟩ else 0
    exact ⟨⟨p, hp⟩, funext fun x => (by simpa using hpx x.1 x.2 : p x.1 = g x)⟩
  calc
    #G = Module.finrank K (G → K) := by simp
    _ ≤ _ := LinearMap.finrank_le_finrank_of_surjective hsurj
    _ ≤ #(s.image v) := finrank_span_finset_le_card _
    _ ≤ #s := card_image_le

end Cslib.LinearAlgebra
