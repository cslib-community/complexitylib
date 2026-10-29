/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.SmallBias.Powering

/-!
# Pseudorandom objects

Concrete instances of small-bias spaces: the uniform distribution is unbiased, a point mass is not,
and the powering construction over the two-element field attains its bias bound. Linear
composition applies to independent parities, and the stretching corollary yields small-bias spaces
for every output length.
-/

namespace ComplexityTests.PseudorandomObjects

open Cslib Cslib.BitString Cslib.Probability Finset
open scoped Cslib.Probability.PMF

/-- The uniform distribution on three bits is unbiased at a nonempty set. -/
example : bias (PMF.uniformOfFintype (Fin 3 → Bool)) {0, 2} = 0 := by
  rw [bias_uniformOfFintype]
  simp

/-- A point mass has bias one everywhere, so it is not `ε`-biased for any `ε < 1`. -/
example (S : Finset (Fin 3)) : bias (PMF.pure 0) S = 1 := by
  simp

example : ¬IsSmallBias (1 / 2) (PMF.pure (0 : Fin 3 → Bool)) := by
  intro h
  have := h {0} (singleton_nonempty 0)
  norm_num at this

/-- The two-element field as one-bit strings. -/
def bitsZMod2 : ZMod 2 ≃+ BitString 1 where
  toFun a _ := decide (a = 1)
  invFun v := if v 0 then 1 else 0
  left_inv a := by fin_cases a <;> rfl
  right_inv v := by
    funext i
    fin_cases i
    cases h : v 0 <;> simp [h]
  map_add' a b := by
    funext i
    fin_cases a <;> fin_cases b <;> rfl

/-- Over the two-element field the powering space on two bits has bias `1 / 2` at `{0, 1}`:
the polynomial `1 + X` has one root among two field elements, so the bound of
`isSmallBias_powering` is attained. -/
example :
    bias ((PMF.uniformOfFintype (ZMod 2 × ZMod 2)).map (powering bitsZMod2 2)) univ = 1 / 2 ∧
      IsSmallBias (1 / 2 : ℝ)
        ((PMF.uniformOfFintype (ZMod 2 × ZMod 2)).map (powering bitsZMod2 2)) := by
  refine ⟨?_, ?_⟩
  · rw [bias_powering]
    have : #({x : ZMod 2 | ∑ i : Fin 2, x ^ (i : ℕ) = 0} : Finset (ZMod 2)) = 1 := by decide
    rw [dens, this]
    simp
  · simpa using isSmallBias_powering bitsZMod2 (n := 2)

/-- Twenty bits of seed stretch to a thousand bits of bias below `1 / 1000`. -/
example : ∃ g : BitString (2 * 20) → BitString 1000,
    IsSmallBias ((1000 - 1 : ℕ) / 2 ^ 20 : ℝ) ((PMF.uniformOfFintype _).map g) :=
  exists_isSmallBias_uniformOfFintype_map 1000 (by norm_num)

example : ((1000 - 1 : ℕ) / 2 ^ 20 : ℝ) < 1 / 1000 := by norm_num

/-- The standard basis vectors are linearly independent, so the identity parities of a small-bias
distribution are `k`-wise small-biased for every `k`. -/
example {ε : ℝ} {X : PMF (Fin 3 → Bool)} (hX : IsSmallBias ε X) :
    IsKWiseSmallBias 3 ε (X.map fun x j => Pi.single j true ⬝ᵥ x) := by
  refine hX.isKWiseSmallBias_map_dotProduct fun T hT _ => ?_
  obtain ⟨j, hj⟩ := hT
  intro h
  have := congrFun h j
  simp only [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq, hj, ite_true,
    Pi.zero_apply] at this
  exact Bool.noConfusion this

/-- A `1`-wise `0`-biased distribution has uniform single bits. -/
example {X : PMF (Fin 3 → Bool)} (hX : IsKWiseSmallBias 1 0 X) (i : Fin 3) :
    dist (X.map ({i} : Finset (Fin 3)).restrict) (PMF.uniformOfFintype _) = 0 := by
  refine le_antisymm ?_ dist_nonneg
  simpa using hX.dist_map_restrict_le (T := {i}) (by simp)

end ComplexityTests.PseudorandomObjects
