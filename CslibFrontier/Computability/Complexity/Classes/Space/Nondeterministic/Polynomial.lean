/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space
public import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic

/-!
# Nondeterministic polynomial space as a union of space classes

`Cslib.Complexity.NPSPACE` is the union of the classes `Cslib.Complexity.NSPACE (n ^ k)`
(`Cslib.Complexity.mem_NPSPACE_iff_exists_mem_NSPACE`), the nondeterministic counterpart of
`Cslib.Complexity.mem_PSPACE_iff_exists_mem_DSPACE`. Results about the parametric classes, such as
the nondeterministic space hierarchy theorem, thereby apply to `NPSPACE`.

## Main results

* `Cslib.Complexity.NSPACE_subset_NPSPACE`: polynomially bounded nondeterministic space is within
  `NPSPACE`.
* `Cslib.Complexity.mem_NPSPACE_iff_exists_mem_NSPACE`: `NPSPACE` is the union of the classes
  `NSPACE (n ^ k)`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.2][Sipser2013]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- A nondeterministic space class of a polynomially bounded bound is within `NPSPACE`. -/
theorem NSPACE_subset_NPSPACE {s : ℕ → ℕ} (hs : PolynomiallyBounded s) :
    NSPACE enc s ⊆ NPSPACE enc := by
  rintro A ⟨k, State, hfin, ntm, c₁, c₂, hA⟩
  have : PolynomiallyBounded fun n => c₁ * s n + c₂ := by fun_prop
  exact ⟨k, State, hfin, ntm, _, .of_polynomiallyBounded (fun a => (enc a).length) this, hA⟩

/-- **`NPSPACE` is the union of the classes `NSPACE (n ^ k)`** [Sipser, Section 8.2][Sipser2013]. -/
theorem mem_NPSPACE_iff_exists_mem_NSPACE : A ∈ NPSPACE enc ↔ ∃ k, A ∈ NSPACE enc (· ^ k) := by
  refine ⟨fun ⟨k, State, hfin, ntm, s, hs, hA⟩ => ?_,
    fun ⟨k, h⟩ => NSPACE_subset_NPSPACE (by fun_prop) h⟩
  obtain ⟨c, d, hle⟩ := hs.exists_le
  exact ⟨d, k, State, hfin, ntm, c * 2 ^ d, c,
    hA.mono fun a => (hle a).trans (Nat.mul_add_one_pow_le_two_pow c d _)⟩

end Cslib.Complexity
