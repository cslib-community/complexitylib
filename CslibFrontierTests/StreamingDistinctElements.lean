/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Streaming.DistinctElements
public import CslibFrontier.Probability.KWiseIndependent.Polynomial
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime

/-!
# Unit tests for the k-minimum-values sketch

Verifies non-vacuity and concrete behavior of:
1. the sketch on a concrete stream with a fixed hash: the state holds the `t` lowest keys, the
   answer is `t M / (v + 1)` once `t` keys are held, and it is exactly `F₀` below `t` keys;
2. the accuracy bound `Cslib.Streaming.dens_abs_kmvEstimate_sub_gt_le`, applied to a genuine
   pairwise independent family with a short seed (the affine maps over `ZMod 31`,
   `Cslib.Probability.isKWiseIndependentHash_polynomialHash`) on a set of `d ≥ t` items, so that
   the estimate is not trivially exact, and the amplified `Cslib.Streaming.solves_kmv` for the same
   family;
3. the memory bounds `Cslib.Streaming.spaceLE_kmv` (seeds not charged) and
   `Cslib.Streaming.exists_injOn_iUnion_reachable_kmvSketch` (seeds stored), with explicit numbers;
4. failure cases: with a constant hash the keys are ordered by the items alone, and the sketch
   overestimates `F₀` by a factor `2`; with `t = 0` it always answers `0`.
-/

public section

namespace ComplexityTests.StreamingDistinctElements

open Cslib Cslib.Probability Cslib.Streaming Finset

/-! ## 1. A concrete run -/

/-- `F₀` of a concrete stream. -/
example : freqMoment 0 [(0 : Fin 4), 1, 0, 2] = 3 := by decide

/-- A fixed hash `a ↦ 3 a + 1 mod 4` with a single seed. -/
def fixedHash : Unit → Fin 4 → Fin 4 := fun _ a => 3 * a + 1

/-- The keys of `0, 1, 2` are `(1, 0)`, `(0, 1)` and `(3, 2)`; the two lowest are `(0, 1)` and
`(1, 0)`. -/
theorem lowest_fixedHash : lowest 2 ([(0 : Fin 4), 1, 0, 2].toFinset.image (kmvKey fixedHash ())) =
    {toLex (0, 1), toLex (1, 0)} := by decide

/-- The state of one copy with `t = 2` after the stream `0, 1, 0, 2`. -/
example : (kmvSketch fixedHash 2 1 fun _ => ()).state [0, 1, 0, 2] =
    (fun _ => (), fun _ => {toLex (0, 1), toLex (1, 0)}) := by
  rw [state_kmvSketch, lowest_fixedHash]

/-- With two keys held and largest hash value `1`, one copy answers `t M / (v + 1) = 2 · 4 / 2 = 4`
(the true value is `F₀ = 3`). -/
example : (kmvSketch fixedHash 2 1 fun _ => ()).run [0, 1, 0, 2] = 4 := by
  have hcard : (({toLex (0, 1), toLex (1, 0)} : Finset (Fin 4 ×ₗ Fin 4))).card = 2 := by decide
  have hmax : kmvMaxHash (({toLex (0, 1), toLex (1, 0)} : Finset (Fin 4 ×ₗ Fin 4))) = 1 := by
    decide
  rw [run_kmvSketch]
  simp only [lowest_fixedHash, kmvEstimate_of_le_card hcard.ge, hmax, median_const]
  norm_num

/-- With `t = 4` and three distinct items, the sketch is exact for every seed. -/
example (ω : Fin 3 → Unit) : (kmvSketch fixedHash 4 3 ω).run [0, 1, 0, 2] = 3 := by
  have h3 : [(0 : Fin 4), 1, 0, 2].toFinset.card = 3 := by decide
  rw [run_kmvSketch_of_card_lt (t := 4) (s := [(0 : Fin 4), 1, 0, 2]) ω (by omega), h3,
    Nat.cast_ofNat]

/-! ## 2. Accuracy for a pairwise independent family -/

private instance : Fact (Nat.Prime 31) := ⟨by norm_num⟩

/-- The affine maps `x ↦ c₀ + c₁ x` over `ZMod 31`, which is `Fin 31`, hash the items `Fin 31` into
`Fin 31` with a seed of two field elements. -/
def affineHash : (Fin 2 → ZMod 31) → Fin 31 → Fin 31 := polynomialHash

/-- The affine family is pairwise independent. -/
theorem isPairwiseIndependentHash_affineHash : IsPairwiseIndependentHash affineHash :=
  (isKWiseIndependentHash_polynomialHash (F := ZMod 31) 2).isPairwiseIndependentHash le_rfl

/-- With `t = 24` and `ε = 1 / 2`, one copy misses the size `31` of the whole universe by more than
`31 / 2` for at most a third of the `31²` seeds; with `31 > 24` items the estimate uses the hash
values, so this is not the exact case. -/
example : (dens {c : Fin 2 → ZMod 31 |
      (1 / 2 : ℝ) * (univ : Finset (Fin 31)).card <
        |kmvEstimate 31 24 (lowest 24 ((univ : Finset (Fin 31)).image (kmvKey affineHash c))) -
          (univ : Finset (Fin 31)).card|} : ℝ) ≤ 1 / 3 := by
  have h := dens_abs_kmvEstimate_sub_gt_le isPairwiseIndependentHash_affineHash
    (D := (univ : Finset (Fin 31))) (ε := 1 / 2) (t := 24) (by norm_num)
    (by norm_num) (by norm_num) (by rw [card_univ, Fintype.card_fin])
  refine h.trans ?_
  norm_num

/-- With `t = 24`, `ε = 1 / 2` (so `t ε² = 6`) and `2 · 6` copies, the randomized sketch solves
`F₀` estimation on streams of length at most `31` with error probability `1 / 2 ≥ (8 / 9) ^ 6`. -/
example : (kmv affineHash 24 (2 * 6)).Solves (1 / 2)
    (fun s Y => |Y - freqMoment 0 s| ≤ 1 / 2 * freqMoment 0 s) 31 :=
  solves_kmv isPairwiseIndependentHash_affineHash (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) le_rfl

/-! ## 3. Memory -/

/-- Over a universe of `31` items, every sketch with `2` copies of `t = 24` keys uses at most
`240 = 2 · 24 · 5` bits on streams of any length, since `31 + 1 = 2 ^ 5`. -/
example (m : ℕ) : (kmv affineHash 24 2).SpaceLE m 240 :=
  spaceLE_kmv (le_of_eq (by
    calc (Fintype.card (Fin 31) + 1) ^ (2 * 24) = (2 ^ 5) ^ 48 := by simp
      _ = 2 ^ 240 := by rw [← pow_mul]))

/-- With the seeds stored, each seed costs `10` bits since `31² ≤ 2 ^ 10`:
`(31² · 32 ^ 24) ^ 2 ≤ 2 ^ 260`. -/
example (m : ℕ) : ∃ enc : KMVState (Fin 2 → ZMod 31) (Fin 31) 31 2 → BitString 260,
    Set.InjOn enc (⋃ ω, (kmvSketch affineHash 24 2 ω).reachable m) :=
  exists_injOn_iUnion_reachable_kmvSketch (by
    calc (Fintype.card (Fin 2 → ZMod 31) * (Fintype.card (Fin 31) + 1) ^ 24) ^ 2 =
          (961 * (2 ^ 5) ^ 24) ^ 2 := by norm_num [ZMod.card]
      _ ≤ (2 ^ 10 * (2 ^ 5) ^ 24) ^ 2 := by gcongr; norm_num
      _ = 2 ^ 260 := by rw [← pow_mul, ← pow_add, ← pow_mul])

/-! ## 4. Failure cases -/

/-- A constant hash gives no information: the keys are ordered by the items alone, so on the
items `0, …, 7` with `t = 2` the two lowest keys have hash value `0`, and one copy answers
`2 · 8 / 1 = 16`, twice `F₀ = 8`. -/
example : (kmvSketch (fun (_ : Unit) (_ : Fin 8) => (0 : Fin 8)) 2 1 fun _ => ()).run
    (List.finRange 8) = 16 := by
  have hlow : lowest 2 ((List.finRange 8).toFinset.image
      (kmvKey (fun (_ : Unit) (_ : Fin 8) => (0 : Fin 8)) ())) =
      {toLex (0, 0), toLex (0, 1)} := by decide
  have hcard : (({toLex (0, 0), toLex (0, 1)} : Finset (Fin 8 ×ₗ Fin 8))).card = 2 := by decide
  have hmax : kmvMaxHash (({toLex (0, 0), toLex (0, 1)} : Finset (Fin 8 ×ₗ Fin 8))) = 0 := by
    decide
  rw [run_kmvSketch]
  simp only [hlow, kmvEstimate_of_le_card hcard.ge, hmax, median_const]
  norm_num

/-- With `t = 0` the sketch keeps no key and always answers `0`, missing `F₀ = 3` for every seed.
The hypothesis `0 < t` of `Cslib.Streaming.dens_abs_kmvEstimate_sub_gt_le` excludes this case. -/
example (ω : Fin 1 → Unit) : (kmvSketch fixedHash 0 1 ω).run [0, 1, 0, 2] = 0 := by
  rw [run_kmvSketch]
  simp only [kmvEstimate_of_le_card (Nat.zero_le _), CharP.cast_eq_zero, zero_mul, zero_div,
    median_const]

end ComplexityTests.StreamingDistinctElements
