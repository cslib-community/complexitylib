/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic

/-!
# Zero-sum pads and their punctured projections

The pads of STOC submission 886, Section 5, properties (P1) and (P2), PDF p. 10.
An index is an actual vector of `n` field elements for `n + 1` parties. The last
pad is minus their sum, equal to their sum in characteristic two. Deleting any
one party gives a bijection, rather than an assumed pad property.
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness.AllOutOfR

open Finset

variable {V : Type*} {n : ℕ}

/-- Dealer indices for `n + 1` parties. -/
abbrev Index (V : Type*) (n : ℕ) := Fin n → V

/-- The first `n` pads are the index coordinates; the last makes their sum zero. -/
@[expose] def pad [AddCommGroup V] (u : Index V n) : Fin (n + 1) → V :=
  Fin.lastCases (-(∑ i, u i)) u

/-- Every pad vector has sum zero (property P1). -/
theorem sum_pad [AddCommGroup V] (u : Index V n) : ∑ j, pad u j = 0 := by
  simp [Fin.sum_univ_castSucc, pad]

/-- In characteristic two the last pad is the sum, as in the manuscript. -/
theorem pad_last [Field V] [CharP V 2] (u : Index V n) :
    pad u (Fin.last n) = ∑ i, u i := by
  simp [pad, CharTwo.neg_eq]

/-- Party indices visible when party `j` is omitted. -/
abbrev Others (j : Fin (n + 1)) := {i : Fin (n + 1) // i ≠ j}

/-- The pads jointly visible to all parties except `j`. -/
@[expose] def padProjection [AddCommGroup V] (j : Fin (n + 1)) (u : Index V n) :
    Others j → V := fun i => pad u i

/-- A zero-sum vector is determined by any punctured projection. -/
theorem eq_of_sum_zero_of_eq_off [AddCommGroup V] {x y : Fin (n + 1) → V}
    (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) (j : Fin (n + 1))
    (h : ∀ i, i ≠ j → x i = y i) : x = y := by
  have he : ∑ i ∈ univ.erase j, x i = ∑ i ∈ univ.erase j, y i :=
    sum_congr rfl (fun i hi => h i (mem_erase.mp hi).1)
  have hx' := sum_erase_add univ x (mem_univ j)
  have hy' := sum_erase_add univ y (mem_univ j)
  rw [hx] at hx'
  rw [hy, ← he] at hy'
  have hj : x j = y j := add_left_cancel (hx'.trans hy'.symm)
  funext i
  by_cases hi : i = j
  · simpa [hi] using hj
  · exact h i hi

/-- Omitting any one party preserves all index information. -/
theorem padProjection_injective [AddCommGroup V] (j : Fin (n + 1)) :
    Function.Injective (padProjection (V := V) j) := by
  intro u v h
  have hp : pad u = pad v := eq_of_sum_zero_of_eq_off (sum_pad u) (sum_pad v) j
    (fun i hi => congrFun h ⟨i, hi⟩)
  funext i
  simpa [pad] using congrFun hp i.castSucc

/-- Exactly `n` parties remain after omitting one. -/
theorem card_others (j : Fin (n + 1)) : Fintype.card (Others j) = n := by
  classical
  simp [Others]

/-- Every punctured pad projection is bijective (property P2). -/
theorem padProjection_bijective [AddCommGroup V] [Finite V] (j : Fin (n + 1)) :
    Function.Bijective (padProjection (V := V) j) := by
  classical
  let := Fintype.ofFinite V
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨padProjection_injective j, by simp [Others]⟩

/-- The inverse projection is a fixed bijection; no extra randomness is used. -/
noncomputable def padEquiv [AddCommGroup V] [Fintype V] (j : Fin (n + 1)) :
    Index V n ≃ (Others j → V) := Equiv.ofBijective _ (padProjection_bijective j)

end Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness.AllOutOfR
