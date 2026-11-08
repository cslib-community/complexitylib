/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Streaming.CountSketch
public import CslibFrontier.Computability.Streaming.MisraGries
public import CslibFrontier.Probability.KWiseIndependent.Trinomial
public import CslibFrontier.Probability.PairwiseIndependentHash.Universal

/-!
# Unit tests for heavy-hitter streaming algorithms

Verifies non-vacuity and concrete behavior of:
1. the Misra–Gries summary `Cslib.Streaming.misraGries`: concrete runs, including one where the
   error bound `m / (k + 1)` of `Cslib.Streaming.MisraGries.count_sub_div_le_run` is attained, the
   majority vote `Cslib.Streaming.MisraGries.toFinset_state_one_eq`, and the memory bound
   `Cslib.Streaming.MisraGries.spaceLE_misraGries` with explicit parameters;
2. the Count-Sketch `Cslib.Streaming.countSketch`: the hypotheses of
   `Cslib.Streaming.solves_countSketchRandom_freqMoment`,
   `Cslib.Streaming.spaceLE_countSketchRandom` (seeds not charged) and
   `Cslib.Streaming.exists_injOn_iUnion_reachable_countSketch` (seeds stored) hold for the trinomial
   hash families with explicit parameters, while without independence (one bucket and a constant
   sign) the sketch reports the stream length instead of the frequency.
-/

public section

namespace ComplexityTests.StreamingHeavyHitters

open Cslib Cslib.Probability Cslib.Streaming

/-! ## 1. The Misra–Gries summary -/

/-- With one counter, `1 2 1 3 1` keeps the majority item `1` once. -/
example : (misraGries 1).state [1, 2, 1, 3, 1] = ({1} : Multiset ℕ) := by decide

example : (misraGries 1).run [1, 2, 1, 3, 1] 1 = 1 := by decide

/-- With two counters, the third distinct item of `0 1 2 0 1 2 0` decrements every counter. -/
example : (misraGries 2).state [0, 1, 2, 0, 1, 2, 0] = ({0} : Multiset ℕ) := by decide

/-- The error bound is attained: on `0 1 2 0 1 2` two counters end empty, although every item
occurs `m / (k + 1) = 2` times. -/
example : (misraGries 2).state [0, 1, 2, 0, 1, 2] = (0 : Multiset ℕ) := by decide

example : ([0, 1, 2, 0, 1, 2].count 0 : ℝ) - [0, 1, 2, 0, 1, 2].length / (2 + 1) =
    (misraGries 2).run [0, 1, 2, 0, 1, 2] 0 := by
  have h1 : [0, 1, 2, 0, 1, 2].count 0 = 2 := by decide
  have h2 : (misraGries 2).run [0, 1, 2, 0, 1, 2] 0 = 0 := by decide
  rw [h1, h2, List.length]
  norm_num

/-- The majority item of `1 2 1 3 1` is the only item with a counter. -/
example : ((misraGries 1).state [1, 2, 1, 3, 1]).toFinset = {1} :=
  MisraGries.toFinset_state_one_eq (by decide)

/-- Two counters over a universe of `4` items fit in `11` bits on streams of at most `7` items. -/
example : (misraGries (α := Fin 4) 2).SpaceLE 7 11 :=
  MisraGries.spaceLE_misraGries (by norm_num)

/-! ## 2. The Count-Sketch -/

/-- The sign of a bit: `0 ↦ 1`, `1 ↦ -1`. -/
def sgnBit (y : Fin (2 ^ 1)) : ℤ :=
  if y = 0 then 1 else -1

theorem sq_sgnBit : ∀ y, sgnBit y ^ 2 = 1 := by decide

theorem sum_sgnBit : ∑ y, sgnBit y = 0 := by decide

theorem abs_sgnBit_le : ∀ y, |sgnBit y| ≤ 1 := by decide

/-- The trinomial family into `16` buckets is two-universal. -/
theorem isTwoUniversal_trinomialPolyHash :
    IsTwoUniversal (PMF.uniformOfFintype (Fin 2 → Fin (2 ^ (2 * 3 ^ 1))))
      (trinomialPolyHash 1 2 64 4) :=
  ((isKWiseIndependentHash_trinomialPolyHash (k := 2) (by norm_num)
    (by norm_num)).isPairwiseIndependentHash le_rfl).isTwoUniversal

/-- With two-universal buckets and pairwise independent signs from the trinomial families on a
universe of `64` items, `40` rows of `16` counters answer every point query within `√F₂ / 2`
except with probability `1 / 10`. -/
theorem solves_countSketchRandom_trinomial (a : Fin 64) (m : ℕ) :
    (countSketchRandom (trinomialPolyHash 1 2 64 4) (trinomialPolyHash 1 2 64 1) sgnBit 20).Solves
      (1 / 10) (fun s est => |est a - s.count a| ≤ 1 / 2 * √(freqMoment 2 s : ℝ)) m :=
  solves_countSketchRandom_freqMoment isTwoUniversal_trinomialPolyHash
    (isKWiseIndependentHash_trinomialPolyHash (by norm_num) (by norm_num)) sq_sgnBit sum_sgnBit
    (by norm_num) (by norm_num) (by norm_num) a m

/-- Every sketch drawn uses `7040` bits of memory on streams of at most `1023` items: under the
public-coin convention only its `640` counters in `[-1023, 1023]` are charged. -/
theorem spaceLE_countSketchRandom_trinomial :
    (countSketchRandom (trinomialPolyHash 1 2 64 4) (trinomialPolyHash 1 2 64 1) sgnBit
      20).SpaceLE 1023 7040 := by
  refine spaceLE_countSketchRandom abs_sgnBit_le ?_
  calc (2 * 1023 + 1) ^ (2 * 20 * 2 ^ 4) ≤ (2 ^ 11) ^ (2 * 20 * 2 ^ 4) :=
        Nat.pow_le_pow_left (by norm_num) _
    _ = 2 ^ 7040 := by rw [← pow_mul, show 11 * (2 * 20 * 2 ^ 4) = 7040 by norm_num]

/-- With its seeds stored as well, the sketch fits in `8000` bits on streams of at most `1023`
items: one encoding works for the states reachable from all seeds. -/
theorem exists_injOn_iUnion_reachable_countSketch_trinomial :
    ∃ enc : CountSketchState (Fin 2 → Fin (2 ^ (2 * 3 ^ 1))) (Fin 2 → Fin (2 ^ (2 * 3 ^ 1)))
        20 (2 ^ 4) → BitString 8000,
      Set.InjOn enc (⋃ ω, (countSketch (trinomialPolyHash 1 2 64 4) (trinomialPolyHash 1 2 64 1)
        sgnBit 20 ω).reachable 1023) := by
  refine exists_injOn_iUnion_reachable_countSketch abs_sgnBit_le ?_
  have hc : Fintype.card (Fin 2 → Fin (2 ^ (2 * 3 ^ 1))) = 2 ^ 12 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    norm_num
  rw [hc]
  calc (2 ^ 12 * 2 ^ 12) ^ (2 * 20) * (2 * 1023 + 1) ^ (2 * 20 * 2 ^ 4) ≤
        (2 ^ 12 * 2 ^ 12) ^ (2 * 20) * (2 ^ 11) ^ (2 * 20 * 2 ^ 4) := by
        gcongr
        norm_num
    _ = 2 ^ 8000 := by
      rw [← pow_add, ← pow_mul, ← pow_mul, ← pow_add,
        show (12 + 12) * (2 * 20) + 11 * (2 * 20 * 2 ^ 4) = 8000 by norm_num]

/-- Without independence the sketch fails: with one bucket and a constant sign the counter holds
the stream length, so on `[0, 0, 1]` the query `0` is answered `3` instead of `2`. -/
example : (countSketch (fun (_ : Unit) (_ : Fin 2) => (0 : Fin 1))
    (fun (_ : Unit) (_ : Fin 2) => (0 : Fin (2 ^ 1))) sgnBit 1 fun _ => ((), ())).run
      [0, 0, 1] 0 = 3 := by
  have : Nonempty (Fin (2 * 1)) := ⟨⟨0, by norm_num⟩⟩
  rw [Algorithm.run, state_countSketch, output_countSketch]
  simp only [median_const]
  norm_num [sgnBit]

end ComplexityTests.StreamingHeavyHitters
