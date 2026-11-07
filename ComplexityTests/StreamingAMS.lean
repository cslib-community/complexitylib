/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Streaming.AMS
public import Complexity.Computability.Streaming.Distinctness
public import Complexity.Probability.KWiseIndependent.Trinomial
public import Complexity.Probability.KWiseIndependent.TugOfWar

/-!
# Unit tests for streaming algorithms and the AMS sketch

Verifies non-vacuity and concrete behavior of:
1. `Cslib.Streaming.freqMoment` and `Cslib.Streaming.maxFreq` on a concrete stream;
2. the deterministic streaming model: an algorithm storing the set of items seen and a flag decides
   distinctness with `n + 1` bits, so `Cslib.Streaming.Algorithm.le_of_run_eq_decide_nodup` is
   within one bit of optimal, and the randomized lower bound
   `Cslib.Streaming.le_of_solves_nodup_one_third` applies to it through
   `Cslib.Streaming.Randomized.solves_pure`;
3. the AMS sketch: the hypotheses of `Cslib.Streaming.solves_ams`, `Cslib.Streaming.spaceLE_ams`
   (seeds not charged) and `Cslib.Streaming.exists_injOn_iUnion_reachable_amsSketch` (seeds
   stored) hold for the four-wise independent trinomial hash family with explicit parameters, while
   without independence (a constant sign) the sketch reports `F₁²` instead of `F₂`.
-/

public section

namespace ComplexityTests.StreamingAMS

open Cslib Cslib.Probability Cslib.Streaming

/-! ## 1. Frequency moments -/

example : freqMoment 2 [(0 : Fin 3), 0, 1] = 5 := by decide
example : freqMoment 1 [(0 : Fin 3), 0, 1] = 3 := by decide
example : maxFreq [(0 : Fin 3), 0, 1] = 2 := by decide
example : maxFreq ([] : List (Fin 3)) = 0 := by decide

/-! ## 2. Deciding distinctness with `n + 1` bits -/

/-- Store the set of items seen and whether all items so far were distinct. -/
def distinctAlg (n : ℕ) : Algorithm (Finset (Fin n) × Bool) (Fin n) Bool where
  init := (∅, true)
  update q a := (insert a q.1, q.2 && decide (a ∉ q.1))
  output q := q.2

theorem stateFrom_distinctAlg {n : ℕ} (q : Finset (Fin n) × Bool) (s : List (Fin n)) :
    (distinctAlg n).stateFrom q s =
      (q.1 ∪ s.toFinset, q.2 && decide (s.Nodup ∧ ∀ a ∈ s, a ∉ q.1)) := by
  induction s generalizing q with
  | nil => simp
  | cons a s ih =>
    rw [Algorithm.stateFrom_cons, ih]
    refine Prod.ext ?_ ?_
    · change insert a q.1 ∪ s.toFinset = q.1 ∪ (a :: s).toFinset
      rw [List.toFinset_cons, Finset.union_insert, Finset.insert_union]
    · change ((q.2 && decide (a ∉ q.1)) && decide (s.Nodup ∧ ∀ b ∈ s, b ∉ insert a q.1)) =
        (q.2 && decide ((a :: s).Nodup ∧ ∀ b ∈ a :: s, b ∉ q.1))
      rw [Bool.and_assoc, ← Bool.decide_and]
      congr 1
      refine decide_eq_decide.2 ?_
      simp only [List.nodup_cons, List.forall_mem_cons, Finset.mem_insert, not_or]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨fun h => (h3 a h).1 rfl, h2⟩, h1, fun b hb => (h3 b hb).2⟩
      · rintro ⟨⟨ha, h2⟩, h1, h4⟩
        exact ⟨h1, h2, fun b hb => ⟨fun e => ha (e ▸ hb), h4 b hb⟩⟩

theorem run_distinctAlg {n : ℕ} (s : List (Fin n)) : (distinctAlg n).run s = decide s.Nodup := by
  rw [Algorithm.run, Algorithm.state, stateFrom_distinctAlg]
  simp [distinctAlg]

theorem spaceLE_distinctAlg (n m : ℕ) : (distinctAlg n).SpaceLE m (n + 1) :=
  Algorithm.spaceLE_of_card_le (by
    rw [Fintype.card_prod, Fintype.card_finset, Fintype.card_fin, Fintype.card_bool, pow_succ])

/-- The deterministic lower bound `n ≤ b` is within one bit of the store-everything algorithm. -/
example (n : ℕ) : n ≤ n + 1 :=
  (distinctAlg n).le_of_run_eq_decide_nodup (fun s _ => run_distinctAlg s)
    (spaceLE_distinctAlg n n)

/-- The hypotheses of the randomized lower bound are satisfiable. -/
example (n : ℕ) : n ≤ 36864 * (n + 1 + 1) + 2 ^ 12 :=
  le_of_solves_nodup_one_third (PMF.pure (distinctAlg n))
    ((Randomized.solves_pure _ fun s _ => run_distinctAlg s).mono (by norm_num) le_rfl)
    (Randomized.spaceLE_pure (spaceLE_distinctAlg n n))

/-! ## 3. The AMS sketch -/

/-- The sign of a bit: `0 ↦ 1`, `1 ↦ -1`. -/
def sgnBit (y : Fin (2 ^ 1)) : ℤ :=
  if y = 0 then 1 else -1

theorem sq_sgnBit : ∀ y, sgnBit y ^ 2 = 1 := by decide

theorem sum_sgnBit : ∑ y, sgnBit y = 0 := by decide

theorem abs_sgnBit_le : ∀ y, |sgnBit y| ≤ 1 := by decide

/-- With the four-wise independent trinomial hash family on a universe of `64` items, `40` groups
of `6` counters estimate `F₂` within a factor of two except with probability `1 / 10`. -/
theorem solves_ams_trinomial (m : ℕ) :
    (ams (trinomialPolyHash 1 4 64 1) sgnBit 20 6).Solves (1 / 10)
      (fun s Y => |Y - freqMoment 2 s| ≤ 1 * freqMoment 2 s) m :=
  solves_ams (isKWiseIndependentHash_trinomialPolyHash (by norm_num) (by norm_num)) sq_sgnBit
    sum_sgnBit one_pos (by norm_num) (by norm_num) m

/-- Every sketch drawn uses `2640` bits of memory on streams of at most `1023` items: under the
public-coin convention only its `240` counters in `[-1023, 1023]` are charged. -/
theorem spaceLE_ams_trinomial :
    (ams (trinomialPolyHash 1 4 64 1) sgnBit 20 6).SpaceLE 1023 2640 := by
  refine spaceLE_ams abs_sgnBit_le ?_
  calc (2 * 1023 + 1) ^ (2 * 20 * 6) ≤ (2 ^ 11) ^ (2 * 20 * 6) :=
        Nat.pow_le_pow_left (by norm_num) _
    _ = 2 ^ 2640 := by rw [← pow_mul]

/-- With its seeds stored as well, the sketch fits in `8400` bits on streams of at most `1023`
items: one encoding works for the states reachable from all seeds. -/
theorem exists_injOn_iUnion_reachable_amsSketch_trinomial :
    ∃ enc : AMSState (Fin 4 → Fin (2 ^ (2 * 3 ^ 1))) 20 6 → BitString 8400,
      Set.InjOn enc
        (⋃ ω, (amsSketch (trinomialPolyHash 1 4 64 1) sgnBit 20 6 ω).reachable 1023) := by
  refine exists_injOn_iUnion_reachable_amsSketch abs_sgnBit_le ?_
  have hc : Fintype.card (Fin 4 → Fin (2 ^ (2 * 3 ^ 1))) = 2 ^ 24 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    norm_num
  rw [hc]
  calc (2 ^ 24 * (2 * 1023 + 1)) ^ (2 * 20 * 6) ≤ (2 ^ 24 * 2 ^ 11) ^ (2 * 20 * 6) := by
        gcongr
        norm_num
    _ = 2 ^ 8400 := by rw [← pow_add, ← pow_mul]

/-- Without independence the sketch fails: with a constant sign every counter holds the stream
length, so on `[0, 0, 1]` it reports `F₁² = 9` instead of `F₂ = 5`. -/
example : (amsSketch (fun (_ : Unit) (_ : Fin 2) => (0 : Fin (2 ^ 1))) sgnBit 1 1
    (fun _ _ => ())).run [0, 0, 1] = 9 := by
  rw [run_amsSketch]
  have hc : (∑ a ∈ [(0 : Fin 2), 0, 1].toFinset, ([(0 : Fin 2), 0, 1].count a : ℝ) *
      sgnBit (0 : Fin (2 ^ 1))) ^ 2 = 9 := by
    have : ∑ a ∈ [(0 : Fin 2), 0, 1].toFinset, ([(0 : Fin 2), 0, 1].count a : ℝ) = 3 := by
      rw [← Nat.cast_sum, List.sum_toFinset_count_eq_length]
      norm_num
    rw [← Finset.sum_mul, this]
    norm_num [sgnBit]
  have : Nonempty (Fin (2 * 1)) := ⟨⟨0, by norm_num⟩⟩
  simp only [medianOfMeans, hc, Fintype.expect_const, median_const]

end ComplexityTests.StreamingAMS
