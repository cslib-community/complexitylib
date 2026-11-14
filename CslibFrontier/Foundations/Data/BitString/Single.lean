/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.InformationTheory.Hamming

/-!
# Unit vectors in Boolean vectors

The unit vectors in `ι → Bool` are the functions `Pi.single i true`: they have a unique true
coordinate and Hamming weight one. For a Boolean vector `t : ι → Bool` with exclusive or as
addition, the two vectors obtained by adding `Pi.single i b` with `b = false` and `b = true` add
up to `Pi.single i true`: the shared mask `t` cancels. This is the reconstruction step of the
two-server and subcube private information retrieval schemes of Chor, Goldreich, Kushilevitz and
Sudan.

## Main definitions

* `Cslib.BitString.IsSingle`: a Boolean unit vector.

## Main results

* `Cslib.BitString.hammingNorm_single_true`: a unit vector has Hamming weight one.
* `Cslib.BitString.hammingNorm_eq_one_iff_isSingle`: weight one characterizes unit vectors.
* `Cslib.BitString.add_single_false_add_add_single_true`: `(t + e_i·0) + (t + e_i·1) = e_i`.
-/

public section

namespace Cslib.BitString

/-- A bit string is a unit vector if it is `Pi.single i true` for some `i`. -/
@[expose]
def IsSingle {ι : Type*} [DecidableEq ι] (c : ι → Bool) : Prop :=
  ∃ i, c = Pi.single i true

instance {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → Bool) : Decidable (IsSingle c) :=
  inferInstanceAs (Decidable (∃ i, c = Pi.single i true))

/-- A Boolean unit vector has Hamming weight one. -/
@[simp]
theorem hammingNorm_single_true {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    hammingNorm (Pi.single i true : ι → Bool) = 1 := by
  rw [hammingNorm, Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  change ((Pi.single i true : ι → Bool) j ≠ false ↔ j = i)
  simp [Pi.single_apply]

/-- A Boolean vector has Hamming weight one exactly when it is a unit vector. -/
theorem hammingNorm_eq_one_iff_isSingle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → Bool) : hammingNorm c = 1 ↔ IsSingle c := by
  constructor
  · rw [hammingNorm, Finset.card_eq_one]
    rintro ⟨i, hi⟩
    refine ⟨i, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst j
      have hi_mem := (Finset.ext_iff.mp hi i).mpr
        (by simp : i ∈ ({i} : Finset ι))
      have hcne : c i ≠ 0 := by simpa using hi_mem
      have hctrue : c i = true := by cases h : c i <;> simp_all
      rw [Pi.single_eq_same]
      exact hctrue
    · have hczero : c j = 0 := not_ne_iff.mp fun hcne => hj <| by
        have hright := (Finset.ext_iff.mp hi j).mp (by simpa using hcne)
        simpa using hright
      rw [Pi.single_eq_of_ne hj]
      exact hczero
  · rintro ⟨i, rfl⟩
    exact hammingNorm_single_true i

/-- Adding the two choices of the `i`-th unit vector to a shared mask `t` and summing leaves the
unit vector: `(t + e_i·0) + (t + e_i·1) = e_i`. -/
theorem add_single_false_add_add_single_true {ι : Type*} [DecidableEq ι] (t : ι → Bool) (i : ι) :
    (t + Pi.single i false) + (t + Pi.single i true) = Pi.single i true := by
  rw [show (Pi.single i false : ι → Bool) = 0 from Pi.single_zero i, add_zero]
  ext j
  rw [Pi.add_apply, Pi.add_apply, ← add_assoc, BooleanRing.add_self, zero_add]

end Cslib.BitString
