/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Streaming.JoinSize
public import CslibFrontier.Probability.KWiseIndependent.Trinomial
public import CslibFrontier.Probability.KWiseIndependent.TugOfWarProduct
public import CslibFrontierTests.StreamingAMS

/-!
# Unit tests for the tug-of-war join signature

Verifies non-vacuity and concrete behavior of:
1. `Cslib.Streaming.joinSize` on concrete relations, including the relations read off a tagged
   stream, and its self-join `Cslib.Streaming.joinSize_self`;
2. the variance identity
   `Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_mul_sum_mul_sign_sub` for the
   four-wise independent trinomial hash family;
3. the join sketch: the hypotheses of `Cslib.Streaming.solves_joinSketchRandom`,
   `Cslib.Streaming.solves_joinSketchRandom_relative`, `Cslib.Streaming.spaceLE_joinSketchRandom`
   (seeds not charged) and `Cslib.Streaming.exists_injOn_iUnion_reachable_joinSketch` (seeds
   stored) hold for the trinomial hash family with explicit parameters, while without independence
   (a constant sign) the sketch reports `|F| |G|` instead of the join size.
-/

public section

namespace CslibFrontierTests.StreamingJoinSize

open Cslib Cslib.Probability Cslib.Streaming CslibFrontierTests.StreamingAMS
open scoped BigOperators

/-! ## 1. Join sizes -/

example : joinSize [(0 : Fin 3), 1, 1] [1, 1, 2] = 4 := by decide
example : joinSize [(0 : Fin 3), 1] [2, 2] = 0 := by decide
example : joinSize [(0 : Fin 3), 0, 1] [(0 : Fin 3), 0, 1] = freqMoment 2 [(0 : Fin 3), 0, 1] :=
  joinSize_self _

/-- The two relations of the tagged stream `[inl 0, inr 0, inl 1, inr 0]` are `[0, 1]` and
`[0, 0]`, whose join has `2` tuples. -/
example : joinSize
    ([Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 0].filterMap (Sum.getLeft? (α := Fin 3)))
    ([Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 0].filterMap (Sum.getRight? (β := Fin 3))) = 2 := by
  decide

/-! ## 2. The variance of the join signature -/

theorem sq_sgnBit_real (y : Fin (2 ^ 1)) : ((sgnBit y : ℤ) : ℝ) ^ 2 = 1 := by
  exact_mod_cast sq_sgnBit y

theorem expect_sgnBit_real : 𝔼 y, ((sgnBit y : ℤ) : ℝ) = 0 := by
  rw [Fintype.expect_eq_sum_div_card, ← Int.cast_sum, sum_sgnBit, Int.cast_zero, zero_div]

/-- The exact variance of the join signature for the trinomial hash family. -/
example (S : Finset (Fin 64)) (f g : Fin 64 → ℝ) :
    𝔼 i, ((∑ x ∈ S, f x * (sgnBit (trinomialPolyHash 1 4 64 1 i x) : ℝ)) *
        (∑ x ∈ S, g x * (sgnBit (trinomialPolyHash 1 4 64 1 i x) : ℝ)) - ∑ x ∈ S, f x * g x) ^ 2 =
      (∑ x ∈ S, f x ^ 2) * (∑ x ∈ S, g x ^ 2) + (∑ x ∈ S, f x * g x) ^ 2 -
        2 * ∑ x ∈ S, f x ^ 2 * g x ^ 2 :=
  IsKWiseIndependentHash.expect_sq_sum_mul_sign_mul_sum_mul_sign_sub
    (h := trinomialPolyHash 1 4 64 1) (ε := fun y => (sgnBit y : ℝ))
    (isKWiseIndependentHash_trinomialPolyHash (by norm_num) (by norm_num))
    sq_sgnBit_real expect_sgnBit_real S f g

/-! ## 3. The join sketch -/

/-- With the four-wise independent trinomial hash family on `64` attribute values, `20` groups of
`6` counter pairs estimate the join size within `√(F₂(F) F₂(G))` with probability `2 / 3`. -/
theorem solves_joinSketchRandom_trinomial (m : ℕ) :
    (joinSketchRandom (trinomialPolyHash 1 4 64 1) sgnBit 10 6).Solves (1 / 3) (fun s J =>
      |J - joinSize (s.filterMap Sum.getLeft?) (s.filterMap Sum.getRight?)| ≤
        1 * √((freqMoment 2 (s.filterMap Sum.getLeft?) : ℝ) *
          freqMoment 2 (s.filterMap Sum.getRight?))) m :=
  solves_joinSketchRandom (isKWiseIndependentHash_trinomialPolyHash (by norm_num) (by norm_num))
    sq_sgnBit sum_sgnBit one_pos (by norm_num) (by norm_num) m

/-- If the join has at least `10` tuples and both self-joins at most `20`, then `20` groups of
`96` counter pairs estimate the join size within relative error `1 / 2` with probability
`2 / 3`. -/
theorem solves_joinSketchRandom_relative_trinomial (m : ℕ) :
    (joinSketchRandom (trinomialPolyHash 1 4 64 1) sgnBit 10 96).Solves (1 / 3) (fun s J =>
      (10 : ℝ) ≤ joinSize (s.filterMap Sum.getLeft?) (s.filterMap Sum.getRight?) →
      (freqMoment 2 (s.filterMap Sum.getLeft?) : ℝ) ≤ 20 →
      (freqMoment 2 (s.filterMap Sum.getRight?) : ℝ) ≤ 20 →
      |J - joinSize (s.filterMap Sum.getLeft?) (s.filterMap Sum.getRight?)| ≤
        1 / 2 * joinSize (s.filterMap Sum.getLeft?) (s.filterMap Sum.getRight?)) m :=
  solves_joinSketchRandom_relative (ε := 1 / 2) (B₁ := 10) (B₂ := 20)
    (isKWiseIndependentHash_trinomialPolyHash (by norm_num) (by norm_num)) sq_sgnBit sum_sgnBit
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) m

/-- Every sketch drawn uses `2640` bits of memory on streams of at most `1023` items: under the
public-coin convention only its `240` counters in `[-1023, 1023]` are charged. -/
theorem spaceLE_joinSketchRandom_trinomial :
    (joinSketchRandom (trinomialPolyHash 1 4 64 1) sgnBit 10 6).SpaceLE 1023 2640 := by
  refine spaceLE_joinSketchRandom abs_sgnBit_le ?_
  calc (2 * 1023 + 1) ^ (4 * 10 * 6) ≤ (2 ^ 11) ^ (4 * 10 * 6) :=
        Nat.pow_le_pow_left (by norm_num) _
    _ = 2 ^ 2640 := by rw [← pow_mul]

/-- With its seeds stored as well, the sketch fits in `5520` bits on streams of at most `1023`
items: one encoding works for the states reachable from all seeds. -/
theorem exists_injOn_iUnion_reachable_joinSketch_trinomial :
    ∃ enc : JoinState (Fin 4 → Fin (2 ^ (2 * 3 ^ 1))) 10 6 → BitString 5520,
      Set.InjOn enc
        (⋃ ω, (joinSketch (trinomialPolyHash 1 4 64 1) sgnBit 10 6 ω).reachable 1023) := by
  refine exists_injOn_iUnion_reachable_joinSketch abs_sgnBit_le ?_
  have hc : Fintype.card (Fin 4 → Fin (2 ^ (2 * 3 ^ 1))) = 2 ^ 24 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    norm_num
  rw [hc]
  calc (2 ^ 24 * (2 * 1023 + 1) ^ 2) ^ (2 * 10 * 6) ≤ (2 ^ 24 * (2 ^ 11) ^ 2) ^ (2 * 10 * 6) := by
        gcongr
        norm_num
    _ = 2 ^ 5520 := by rw [← pow_mul, ← pow_add, ← pow_mul]

/-- Without independence the sketch fails: with a constant sign each counter holds the size of its
relation, so on the tagged stream `[inl 0, inr 1]`, whose relations `[0]` and `[1]` have an empty
join, it reports `1 · 1 = 1` instead of `0`. -/
example : (joinSketch (fun (_ : Unit) (_ : Fin 2) => ()) (fun _ => (1 : ℤ)) 1 1
    (fun _ _ => ())).run [Sum.inl 0, Sum.inr 1] = 1 ∧
    joinSize ([Sum.inl 0, Sum.inr 1].filterMap (Sum.getLeft? (α := Fin 2)))
      ([Sum.inl 0, Sum.inr 1].filterMap (Sum.getRight? (β := Fin 2))) = 0 := by
  refine ⟨?_, by decide⟩
  have hl : [Sum.inl 0, Sum.inr 1].filterMap (Sum.getLeft? (α := Fin 2) (β := Fin 2)) = [0] :=
    rfl
  have hr : [Sum.inl 0, Sum.inr 1].filterMap (Sum.getRight? (α := Fin 2) (β := Fin 2)) = [1] :=
    rfl
  rw [run_joinSketch, hl, hr]
  have : Nonempty (Fin (2 * 1)) := ⟨⟨0, by norm_num⟩⟩
  simp [uniformMedianOfMeans, median_const]

end CslibFrontierTests.StreamingJoinSize
