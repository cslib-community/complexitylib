/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.InaccessibleEntropy.OneWay
import Complexity.Probability.Collision
import Complexity.Tactic.PPT

/-!
# Tests for 3-wise Boolean affine hashes and inaccessible average max-entropy

Checks concrete unconditional instances of:
1. `3`-wise independence and prefix-collision seed adjustment (`affineHash`, `prefixProj`,
   `adjustAffineSeed`).
2. Real sample entropy vs. accessible set expectation on a concrete `2`-to-`1` projection,
   verifying a strict `1 / 2`-bit entropy gap when only `{x}` is accessible and verifying that
   declaring the full fiber accessible collapses the gap to `0` (so `InaccessibleEntropyFamily`
   cannot be trivially satisfied by taking `accSet = fiberSet`).
3. Concrete unconditional instantiations of `isPPT_rompelBaseInverter`,
   `rompelBase_escape_le_four_mul_inversion`, and `rompelBase_accessible_le_conditionalEntropy_sub`
   on `g = id` at security parameter `n = 2`.
4. The `OneWay.exists_inaccessibleEntropyFamily` endpoint under `OneWay f`.
-/

namespace ComplexityTests.Crypto.InaccessibleEntropy

open Cslib Cslib.BitString.LinearHash Cslib.Crypto Cslib.Probability Finset Turing.MultiTapeTM

/-! ### 1. Three-wise independence and prefix-collision conditioning -/

example (k n : ℕ) : IsKWiseIndependentHash 3 (BitString.LinearHash.affineHash (k := k) (n := n)) :=
  isThreeWiseIndependentHash_affineHash k n

example (k n r : ℕ) :
    IsKWiseIndependentHash 3
      (fun s x => prefixProj k r (BitString.LinearHash.affineHash (k := k) (n := n) s x)) :=
  isThreeWiseIndependentHash_prefixProj_affineHash k n r

/-- Concrete check of `toReal_map_adjustAffineSeed_eq` on `y = 11`, `y₀ = 00`, `s₀ = 0` at
`k = 2, n = 2, r = 1`: projecting onto the prefix-colliding seed subgroup doubles the uniform mass
of `s₀ = 0`. -/
theorem toReal_map_adjustAffineSeed_allOnes_zero :
    (((PMF.uniformOfFintype ((Fin 2 → BitString 2) × BitString 2)).map
      (adjustAffineSeed 1 ((fun _ : Fin 2 => true) + 0))) 0).toReal =
      2 * ((PMF.uniformOfFintype ((Fin 2 → BitString 2) × BitString 2)) 0).toReal := by
  have hy : (fun _ : Fin 2 => true) ≠ (0 : BitString 2) := by
    intro h
    cases congrFun h 0
  have hs₀ :
      prefixProj 2 1
        (BitString.LinearHash.affineHash (0 : (Fin 2 → BitString 2) × BitString 2)
          (fun _ => true)) =
      prefixProj 2 1
        (BitString.LinearHash.affineHash (0 : (Fin 2 → BitString 2) × BitString 2) 0) := by
    decide
  simpa only [Nat.min_eq_left (by decide : 1 ≤ 2), pow_one] using
    toReal_map_adjustAffineSeed_eq (k := 2) (n := 2) 1 hy hs₀

/-! ### 2. Real vs. accessible entropy on a concrete 2-to-1 map -/

/-- Two-to-one projection dropping the second bit of `BitString 2`. -/
def firstBitProj (x : BitString 2) : BitString 1 := fun _ => x 0

example (A : BitString 2 → PMF (BitString 2)) :
    IsCollisionFinder firstBitProj (sanitizeCollisionFinder firstBitProj A) :=
  isCollisionFinder_sanitizeCollisionFinder firstBitProj A

/-- On `firstBitProj : BitString 2 → BitString 1` with singleton accessible sets `L x = {x}`,
every fiber has size `2`, so `conditionalEntropy_sub_accessibleSetExpectation_ge` witnesses an
unconditional `1 / 2`-bit gap. -/
theorem firstBitProj_singleton_gap_ge_half :
    (1 / 2 : ℝ) ≤
      PMF.conditionalEntropy ((PMF.uniformOfFintype (BitString 2)).map fun x =>
        (firstBitProj x, x)) -
        accessibleSetExpectation (fun x : BitString 2 => ({x} : Finset (BitString 2))) := by
  have hbound := conditionalEntropy_sub_accessibleSetExpectation_ge firstBitProj
    (fun x => ({x} : Finset (BitString 2)))
    (fun x => mem_singleton_self x)
    (fun x z hz => by
      rw [mem_singleton.mp hz]
      exact self_mem_fiberSet firstBitProj x)
  have hfib (x : BitString 2) : #(fiberSet firstBitProj (firstBitProj x)) = 2 := by
    let flip1 : BitString 2 := Function.update x 1 (!x 1)
    have hne : x ≠ flip1 := by
      intro h
      have h1 := congrFun h 1
      simp only [flip1, Function.update_self] at h1
      cases x 1 <;> simp_all
    have hset : fiberSet firstBitProj (firstBitProj x) = {x, flip1} := by
      ext z
      simp only [fiberSet, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · intro hz0
        have hz0' : z 0 = x 0 := congrFun hz0 0
        by_cases hz1 : z 1 = x 1
        · left
          funext i
          fin_cases i
          · exact hz0'
          · exact hz1
        · right
          funext i
          fin_cases i
          · change z 0 = flip1 0
            simpa only [flip1, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)] using hz0'
          · change z 1 = flip1 1
            simp only [flip1, Function.update_self]
            cases hx1 : x 1 <;> cases hzv : z 1 <;> simp_all
      · rintro (rfl | rfl)
        · rfl
        · funext i
          simp only [firstBitProj, flip1, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
    rw [hset, card_pair hne]
  have hsdiff (x : BitString 2) :
      #(fiberSet firstBitProj (firstBitProj x) \ ({x} : Finset (BitString 2))) = 1 := by
    have hsub : ({x} : Finset (BitString 2)) ⊆ fiberSet firstBitProj (firstBitProj x) := by
      intro z hz
      rw [mem_singleton.mp hz]
      exact self_mem_fiberSet firstBitProj x
    rw [card_sdiff_of_subset hsub, hfib x, card_singleton]
  have hlhs : (∑ x : BitString 2, ((PMF.uniformOfFintype (BitString 2)) x).toReal *
      ((#(fiberSet firstBitProj (firstBitProj x) \ ({x} : Finset (BitString 2))) : ℝ) /
        #(fiberSet firstBitProj (firstBitProj x)))) = 1 / 2 := by
    simp only [hsdiff, hfib, Nat.cast_one, Nat.cast_ofNat, PMF.uniformOfFintype_apply,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, ENNReal.toReal_inv, sum_const,
      card_univ, nsmul_eq_mul]
    norm_num
  linarith

/-- Declaring the entire fiber accessible (`L x = fiberSet F (F x)`) makes accessible expectation
equal to real conditional entropy, confirming that
`InaccessibleEntropyFamily.eventually_entropy_gap` (`1 / denom n > 0`) rejects the trivial
full-fiber choice. -/
theorem fullFiber_accessibleSetExpectation_eq_conditionalEntropy {α β : Type*}
    [Fintype α] [Nonempty α] [Finite β] [DecidableEq β] (F : α → β) :
    accessibleSetExpectation (fun x => fiberSet F (F x)) =
      PMF.conditionalEntropy ((PMF.uniformOfFintype α).map fun x => (F x, x)) :=
  expected_realSampleEntropy_eq_conditionalEntropy F

/-! ### 3. Unconditional checks on the Rompel–HHRVW base construction for `g = id` -/

example :
    IsPPT encBits
      (rompelBaseInverter id id (fun n _ => pure (List.replicate n false))) :=
  isPPT_rompelBaseInverter .id' .id' (by ppt)

example (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (accessibleEscapeGame (rompelBaseEvalWord id id)
        (fun k => rompelBaseInLen k k) (rompelAccessibleSet id id) A n)) : ℝ) ≤
      4 * (Game.succProbability (ProbComp.eval
        (inversionGame id (rompelBaseInverter id id A) n)) : ℝ) :=
  rompelBase_escape_le_four_mul_inversion id id A n (fun _ hw => hw)

/-- Unconditional concrete check of `rompelBase_accessible_le_conditionalEntropy_sub` on `g = id`
at `n = 2`: since `collisionProbability (uniformList 2) = 1 / 4 ≤ 1 / 2`, the Rompel base hash has
an unconditional real-vs-accessible entropy gap of at least `1 / 192` bits. -/
theorem rompelBase_id_two_entropy_gap :
    accessibleSetExpectation (rompelAccessibleSet id id 2) ≤
      PMF.conditionalEntropy
        ((PMF.uniformOfFintype (BitString (rompelBaseInLen 2 2))).map fun b =>
          (wordToFinMap (rompelBaseInLen 2 2) (rompelBaseOutLen 2 2)
            (rompelBaseEvalWord id id 2) b, b)) -
        1 / 192 := by
  have hcoll : PMF.collisionProbability ((Cslib.BitString.uniformList 2).map id) ≤ 1 / 2 := by
    rw [PMF.map_id, Cslib.BitString.uniformList,
      PMF.collisionProbability_map_of_injective _ _ List.ofFn_injective,
      PMF.collisionProbability_uniform]
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
    norm_num
  have hgap := rompelBase_accessible_le_conditionalEntropy_sub id id 2 (fun _ hw => hw) hcoll
  norm_num at hgap ⊢
  exact hgap

/-! ### 4. Endpoint check under `OneWay f` -/

example {f : List Bool → List Bool} (hf : OneWay f) : Nonempty InaccessibleEntropyFamily :=
  hf.exists_inaccessibleEntropyFamily

end ComplexityTests.Crypto.InaccessibleEntropy
