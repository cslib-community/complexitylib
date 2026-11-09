/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `GroupTheory/Perm/Cycle/Type.lean`, next to `IsThreeCycle`)

public import Cslib.Init
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic.Group

/-!
# Five-cycles

A five-cycle is a permutation of cycle type `{5}` (`Equiv.Perm.IsFiveCycle`), defined like
Mathlib's `Equiv.Perm.IsThreeCycle`. Five-cycles are even (`Equiv.Perm.IsFiveCycle.sign`), all
five-cycles are conjugate (`Equiv.Perm.IsFiveCycle.isConj`), and in `Fin 5` every five-cycle is a
commutator of two five-cycles (`Equiv.Perm.IsFiveCycle.exists_commutator`), the fact behind
Barrington's theorem [Barrington1989].

## Main definitions

* `Equiv.Perm.IsFiveCycle`: the permutations of cycle type `{5}`.

## Main results

* `Equiv.Perm.IsFiveCycle.mem_alternatingGroup`: five-cycles are even.
* `Equiv.Perm.IsFiveCycle.exists_commutator`: every five-cycle of `Fin 5` is the commutator of two
  five-cycles.

## References

* [D. A. Barrington, *Bounded-width polynomial-size branching programs recognize exactly those
  languages in NC¹*][Barrington1989]
-/

@[expose] public section

namespace Equiv.Perm

open scoped commutatorElement

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- A five-cycle is a cycle of length 5. -/
def IsFiveCycle (σ : Perm α) : Prop :=
  σ.cycleType = {5}

namespace IsFiveCycle

variable {σ τ : Perm α}

/-- A five-cycle has cycle type `{5}`. -/
theorem cycleType (h : IsFiveCycle σ) : σ.cycleType = {5} :=
  h

/-- A five-cycle is not the identity. -/
theorem ne_one (h : IsFiveCycle σ) : σ ≠ 1 := by
  rintro rfl
  simpa using h.cycleType

/-- The inverse of a five-cycle is a five-cycle. -/
theorem inv (h : IsFiveCycle σ) : IsFiveCycle σ⁻¹ := by
  rwa [IsFiveCycle, cycleType_inv]

/-- `σ⁻¹` is a five-cycle exactly when `σ` is. -/
@[simp] theorem inv_iff : IsFiveCycle σ⁻¹ ↔ IsFiveCycle σ :=
  ⟨by simpa using inv (σ := σ⁻¹), inv⟩

/-- A five-cycle has sign `1`. -/
theorem sign (h : IsFiveCycle σ) : sign σ = 1 := by
  rw [Equiv.Perm.sign_of_cycleType, h.cycleType]
  rfl

/-- Five-cycles are even. -/
theorem mem_alternatingGroup (h : IsFiveCycle σ) : σ ∈ alternatingGroup α :=
  Perm.mem_alternatingGroup.mpr h.sign

/-- A conjugate `ρ * σ * ρ⁻¹` of a five-cycle is a five-cycle. -/
theorem conj (h : IsFiveCycle σ) (ρ : Perm α) : IsFiveCycle (ρ * σ * ρ⁻¹) := by
  rwa [IsFiveCycle, cycleType_conj]

/-- All five-cycles are conjugate. -/
theorem isConj (hσ : IsFiveCycle σ) (hτ : IsFiveCycle τ) : IsConj σ τ :=
  isConj_iff_cycleType_eq.2 (hσ.trans hτ.symm)

end IsFiveCycle

/-- The cyclic permutation of a list of five distinct elements is a five-cycle. -/
theorem isFiveCycle_formPerm {l : List α} (hl : l.Nodup) (hlen : l.length = 5) :
    IsFiveCycle l.formPerm := by
  rw [IsFiveCycle, (List.isCycle_formPerm hl (by omega)).cycleType,
    List.support_formPerm_of_nodup l hl fun x h => by simp [h] at hlen,
    List.toFinset_card_of_nodup hl, hlen]

/-- Every five-cycle of `Fin 5` is the commutator of two five-cycles [Barrington1989]. -/
theorem IsFiveCycle.exists_commutator {σ : Perm (Fin 5)} (hσ : IsFiveCycle σ) :
    ∃ τ₁ τ₂ : Perm (Fin 5), IsFiveCycle τ₁ ∧ IsFiveCycle τ₂ ∧ ⁅τ₁, τ₂⁆ = σ := by
  -- `(0 1 2 3 4)` and `(0 2 4 3 1)` have the commutator `(0 3 2 4 1)`.
  have h₁ := isFiveCycle_formPerm (l := ([0, 1, 2, 3, 4] : List (Fin 5))) (by decide) rfl
  have h₂ := isFiveCycle_formPerm (l := ([0, 2, 4, 3, 1] : List (Fin 5))) (by decide) rfl
  have h₃ := isFiveCycle_formPerm (l := ([0, 3, 2, 4, 1] : List (Fin 5))) (by decide) rfl
  have hcomm : ⁅List.formPerm ([0, 1, 2, 3, 4] : List (Fin 5)),
      List.formPerm ([0, 2, 4, 3, 1] : List (Fin 5))⁆ = List.formPerm [0, 3, 2, 4, 1] := by
    decide
  obtain ⟨ρ, rfl⟩ := isConj_iff.1 (h₃.isConj hσ)
  exact ⟨_, _, h₁.conj ρ, h₂.conj ρ, by rw [← hcomm]; group⟩

end Equiv.Perm
