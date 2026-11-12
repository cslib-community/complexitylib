/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card

/-!
# Perfect hash families

A finite family of maps `α → β` is a perfect hash family for `s`-element sets when every
`s`-element subset of `α` is mapped injectively by some member of the family.

## Main definitions

* `Cslib.IsPerfectHashFamily`: the predicate.

## Main results

* `Cslib.IsPerfectHashFamily.mono`: a family containing a perfect hash family is one.
-/

@[expose] public section

namespace Cslib

variable {α β : Type*}

/-- `P` is a perfect hash family for `s`-element sets: every `s`-element subset of the domain is
mapped injectively by some member of `P`. -/
def IsPerfectHashFamily (P : Finset (α → β)) (s : ℕ) : Prop :=
  ∀ S : Finset α, S.card = s → ∃ h ∈ P, Set.InjOn h S

/-- A family containing a perfect hash family is a perfect hash family. -/
theorem IsPerfectHashFamily.mono {P Q : Finset (α → β)} {s : ℕ} (hP : IsPerfectHashFamily P s)
    (hPQ : P ⊆ Q) : IsPerfectHashFamily Q s := fun S hS =>
  let ⟨h, hh, hinj⟩ := hP S hS
  ⟨h, hPQ hh, hinj⟩

end Cslib
