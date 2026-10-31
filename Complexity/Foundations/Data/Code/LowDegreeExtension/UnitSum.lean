/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.LowDegreeExtension
public import Complexity.Foundations.FieldTheory.Finite.UnitSum

/-!
# Unmasking low-degree extensions

Summing a low-degree function along a punctured affine line removes its mask. This combines the
existing Reed–Muller polynomial witness with the finite-field unit-sum identity. For a function
on `n` coordinates over an alphabet `H`, the sufficient bound is strictly
`n * (|H| - 1) < |F| - 1`.

## Main results

* `Cslib.Code.sum_units_mul_add_of_mem_reedMuller`: unmask a Reed–Muller codeword.
* `Cslib.Code.sum_units_lowDegreeExtension_mul_add`: unmask an extension at a grid point.

## References

* [R. Williams, *Simulating Time With Square-Root Space*][Williams2025], Appendix A,
  equations (5)–(6). The signed identity here works in arbitrary finite characteristic;
  in characteristic two its minus sign disappears.
-/

public section

namespace Cslib.Code

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n D : ℕ}

/-- A Reed–Muller codeword below the strict unit-sum degree threshold loses its mask when
summed over the units. -/
theorem sum_units_mul_add_of_mem_reedMuller {f : (Fin n → F) → F}
    (hf : f ∈ reedMuller F n D) (hD : D < Fintype.card F - 1) (τ x : Fin n → F) :
    ∑ u : Fˣ, f (fun i => (u : F) * τ i + x i) = -f x := by
  obtain ⟨P, hP, rfl⟩ := mem_reedMuller.mp hf
  exact FiniteField.sum_units_eval_mul_add (hP.trans_lt hD) τ x

/-- Summing the masked extension at a grid point gives minus the original table entry.
The strict bound is on the total degree, not just on the alphabet size. -/
theorem sum_units_lowDegreeExtension_mul_add {H : Type*} [Fintype H] [DecidableEq H]
    (h : H ↪ F) (f : (Fin n → H) → F)
    (hD : n * (Fintype.card H - 1) < Fintype.card F - 1)
    (τ : Fin n → F) (a : Fin n → H) :
    ∑ u : Fˣ, lowDegreeExtension h f (fun i => (u : F) * τ i + h (a i)) = -f a := by
  rw [sum_units_mul_add_of_mem_reedMuller
    (lowDegreeExtension_mem_reedMuller h f) hD, lowDegreeExtension_apply_embed]

end Cslib.Code
