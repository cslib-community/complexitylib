/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PairwiseIndependentHash.Affine
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.ZMod.Defs
import Complexity.Foundations.Combinatorics.MajorityVote
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.ZMod

/-!
# Approximate counting by hashing

Stockmeyer's approximate counting [Stockmeyer1983] estimates the size of a set `S` with
`#S ≤ 2 ^ n` from the answers, for each level `j ≤ n`, to the question whether `S` meets a random
one of `2 ^ j` cells, the fibers of a pairwise independent hash family into a set of size `2 ^ j`.
The cells at level `j` have mean size `#S / 2 ^ j`: if it is at least `8`, then `S` meets a random
cell with probability at least `7 / 8`, and if it is at most `1 / 8`, with probability at most
`1 / 8`.

The estimate (`Cslib.Probability.ApproximateCounting.estimate`) is `2 ^ k` for the largest level
`k ≤ n` answered yes, or `0` if the level `0`, whose single cell is `S`, is answered no. If the
answers are correct wherever the mean cell size is at least `8` or at most `1 / 8`
(`Cslib.Probability.ApproximateCounting.AnswersCorrect`), the estimate is at most `8 #S` and at
least `#S / 16`. Answering each question by the majority of `2 r` independent trials
(`Cslib.Probability.ApproximateCounting.hashAnswer`), the answers are correct except with
probability at most `(n + 1) (8 / 9) ^ r`, so with `r = 12 (n + 1)` the estimate is within these
bounds with probability at least `3 / 4`. Each question is an `NP` question when membership in `S`
is decidable in polynomial time, which is how Stockmeyer approximates `#P` functions with an `NP`
oracle; this file contains the finite, probabilistic part of the argument.

## Main definitions

* `Cslib.Probability.ApproximateCounting.estimate`: the estimate from the answers.
* `Cslib.Probability.ApproximateCounting.AnswersCorrect`: correct answers for a set of a given
  size.
* `Cslib.Probability.ApproximateCounting.hashAnswer`,
  `Cslib.Probability.ApproximateCounting.hashEstimate`: the answers and the estimate from
  majority votes over independent seeds of pairwise independent hash families.

## Main results

* `Cslib.Probability.ApproximateCounting.AnswersCorrect.estimate_le`,
  `Cslib.Probability.ApproximateCounting.AnswersCorrect.le_estimate`: correct answers give an
  estimate between `#S / 16` and `8 #S`.
* `Cslib.Probability.ApproximateCounting.dens_filter_not_answersCorrect_le`: the majority answers
  are correct except with probability at most `(n + 1) (8 / 9) ^ r`.
* `Cslib.Probability.ApproximateCounting.three_quarters_le_dens_filter_hashEstimate`: with
  `r = 12 (n + 1)` the estimate is between `#S / 16` and `8 #S` with probability at least `3 / 4`,
  and `Cslib.Probability.ApproximateCounting.three_quarters_le_dens_filter_affineHashEstimate` for
  the affine hash families over `ZMod 2`.

## References

* [L. Stockmeyer, *The complexity of approximate counting*][Stockmeyer1983]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 8.2][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Probability.ApproximateCounting

open Finset

/-! ### The estimate from the answers -/

section Estimate

variable {n c : ℕ} {a : ℕ → Prop} [DecidablePred a]

/-- Stockmeyer's estimate of the size of a set from answers `a j`, for the levels `j ≤ n`, to the
question whether the set meets a random one of `2 ^ j` cells: `0` if level `0` is answered no, and
otherwise `2 ^ k` for the largest level `k ≤ n` answered yes. -/
def estimate (n : ℕ) (a : ℕ → Prop) [DecidablePred a] : ℕ :=
  if a 0 then 2 ^ Nat.findGreatest a n else 0

/-- Answers `a j`, for the levels `j ≤ n`, to the question whether a set of `c` elements meets a
random one of `2 ^ j` cells are *correct* if level `0` answers whether `c ≠ 0`, and every level
`j ≤ n` answers yes when the mean cell size `c / 2 ^ j` is at least `8` and no when it is at most
`1 / 8`. -/
structure AnswersCorrect (n c : ℕ) (a : ℕ → Prop) : Prop where
  /-- Level `0` answers whether `c ≠ 0`. -/
  apply_zero_iff : a 0 ↔ 0 < c
  /-- A level with mean cell size at least `8` answers yes. -/
  apply_of_le : ∀ j ≤ n, 8 * 2 ^ j ≤ c → a j
  /-- A level with mean cell size at most `1 / 8` answers no. -/
  not_apply_of_le : ∀ j ≤ n, 8 * c ≤ 2 ^ j → ¬ a j

/-- Correctness of decidable answers is decidable. -/
instance : Decidable (AnswersCorrect n c a) :=
  decidable_of_iff ((a 0 ↔ 0 < c) ∧ (∀ j ≤ n, 8 * 2 ^ j ≤ c → a j) ∧
    ∀ j ≤ n, 8 * c ≤ 2 ^ j → ¬ a j)
    ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩, fun h => ⟨h.1, h.2, h.3⟩⟩

/-- The estimate from correct answers is at most `8` times the size of the set. -/
theorem AnswersCorrect.estimate_le (ha : AnswersCorrect n c a) : estimate n a ≤ 8 * c := by
  unfold estimate
  split_ifs with h0
  · have hk : a (Nat.findGreatest a n) := Nat.findGreatest_spec (Nat.zero_le n) h0
    by_contra! hlt
    exact ha.not_apply_of_le _ (Nat.findGreatest_le (P := a) n) hlt.le hk
  · exact Nat.zero_le _

/-- The estimate from correct answers is at least a sixteenth of the size `c ≤ 2 ^ n` of the
set. -/
theorem AnswersCorrect.le_estimate (ha : AnswersCorrect n c a) (hc : c ≤ 2 ^ n) :
    c ≤ 16 * estimate n a := by
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · exact Nat.zero_le _
  have h0 : a 0 := ha.apply_zero_iff.2 hc0
  rw [estimate, ite_eq_left h0]
  rcases Nat.lt_or_ge c 8 with hc8 | hc8
  · have := Nat.one_le_two_pow (n := Nat.findGreatest a n)
    omega
  -- the level `j = log₂ (c / 8)` has mean cell size at least `8`
  have hj : 2 ^ Nat.log 2 (c / 8) ≤ c / 8 := Nat.pow_log_le_self 2 (by omega)
  have hcj : c / 8 < 2 ^ Nat.log 2 (c / 8) * 2 := by
    rw [← pow_succ]
    exact Nat.lt_pow_succ_log_self (by norm_num) (c / 8)
  have hjn : Nat.log 2 (c / 8) ≤ n := by
    rw [← Nat.pow_le_pow_iff_right (le_refl 2)]
    omega
  have hk := Nat.le_findGreatest hjn (ha.apply_of_le _ hjn (by omega))
  have := Nat.pow_le_pow_right (by norm_num : 2 > 0) hk
  omega

end Estimate

/-! ### Majority votes and the union bound -/

/-- The event that the coordinate `k` of a tuple of independent samples lies in `t` has at most
the density of `t`, with equality unless another coordinate ranges over an empty type. -/
private theorem dens_filter_apply_mem_le {κ : Type*} [Fintype κ] [DecidableEq κ] {α : κ → Type*}
    [∀ k, Fintype (α k)] [∀ k, DecidableEq (α k)] (k : κ) (t : Finset (α k)) :
    dens {ω : ∀ k, α k | ω k ∈ t} ≤ dens t := by
  set P := ∏ j ∈ univ \ {k}, Fintype.card (α j)
  have hcard : #{ω : ∀ k, α k | ω k ∈ t} = #t * P := by
    rw [← Fintype.piFinset_univ, ← Fintype.piFinset_update_eq_filter_piFinset_mem _ _
      (subset_univ t), Fintype.card_piFinset]
    have : ∀ j, #(Function.update (fun j => (univ : Finset (α j))) k t j) =
        Function.update (fun j => Fintype.card (α j)) k #t j := fun j => by
      rcases eq_or_ne j k with rfl | hj
      · simp
      · simp [hj]
    simp only [this, prod_update_of_mem (mem_univ k), P]
  have htotal : Fintype.card (∀ k, α k) = Fintype.card (α k) * P := by
    rw [Fintype.card_pi, ← prod_update_of_mem (mem_univ k), Function.update_eq_self]
  rcases Nat.eq_zero_or_pos P with hP | hP
  · simp [dens_eq_card_div_card, hcard, hP]
  · rw [dens_eq_card_div_card, dens_eq_card_div_card, hcard, htotal, Nat.cast_mul, Nat.cast_mul,
      mul_div_mul_right _ _ (Nat.cast_ne_zero.2 hP.ne')]

/-- **Majority votes**, in density form: if `G` has density at least `2 / 3`, then at most `r` of
`2 r` independent samples lie in `G` with probability at most `(8 / 9) ^ r`. -/
private theorem dens_filter_card_filter_le_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {G : Finset Ω} (hG : 2 / 3 ≤ G.dens) (r : ℕ) :
    dens {ω : Fin (2 * r) → Ω | #{i | ω i ∈ G} ≤ r} ≤ (8 / 9) ^ r := by
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with hΩ | hΩ
  · rw [dens_eq_card_div_card, hΩ, Nat.cast_zero, div_zero] at hG
    norm_num at hG
  have hG' : 2 * Fintype.card Ω ≤ 3 * #G := by
    rw [dens_eq_card_div_card, div_le_div_iff₀ (by norm_num) (by exact_mod_cast hΩ)] at hG
    exact_mod_cast hG.trans_eq (mul_comm _ _)
  have hmaj := card_filter_card_filter_le_le G hG' r
  rw [dens_eq_card_div_card, Fintype.card_fun, Fintype.card_fin,
    div_le_iff₀ (by positivity), div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  rw [mul_comm]
  exact_mod_cast hmaj

/-- If `a + b = 1` and `b ≤ 1 / 8`, then `a ≥ 2 / 3`. -/
private theorem two_thirds_le_of_add_eq_one {a b : ℚ≥0} (hab : a + b = 1) (hb : b ≤ 1 / 8) :
    2 / 3 ≤ a := by
  rw [← NNRat.cast_le (K := ℚ)]
  have hab' := congrArg (NNRat.cast : ℚ≥0 → ℚ) hab
  have hb' := NNRat.cast_le (K := ℚ).2 hb
  push_cast at hab' hb' ⊢
  linarith

/-! ### Answers from hashing -/

section Hashing

variable {ι : ℕ → Type*} [∀ j, Fintype (ι j)] {X : Type*} {Y : ℕ → Type*} [∀ j, Fintype (Y j)]
  [∀ j, DecidableEq (Y j)] (h : ∀ j, ι j → X → Y j) (y : ∀ j, Y j) (S : Finset X) {n r : ℕ}

/-- The answers from hashing, with seeds `ω j k` for the levels `j ≤ n` and the trials
`k < 2 r`: level `j` answers yes if more than `r` of the hash functions `h j (ω j k)` send an
element of `S` to the target `y j`. -/
def hashAnswer (ω : ∀ j : Fin (n + 1), Fin (2 * r) → ι j) (j : ℕ) : Prop :=
  ∃ hj : j < n + 1, r < #{k | y j ∈ S.image (h j (ω ⟨j, hj⟩ k))}

/-- The answers from hashing are decidable. -/
instance (ω : ∀ j : Fin (n + 1), Fin (2 * r) → ι j) : DecidablePred (hashAnswer h y S ω) :=
  fun _ => inferInstanceAs (Decidable (∃ _, _))

/-- Stockmeyer's estimate of `#S` from the answers from hashing with seeds `ω`. -/
def hashEstimate (ω : ∀ j : Fin (n + 1), Fin (2 * r) → ι j) : ℕ :=
  estimate n (hashAnswer h y S ω)

/-- The seeds on which level `j` answers incorrectly for `S`: no although the mean cell size is
at least `8`, or yes although it is at most `1 / 8`. -/
private def wrongSeeds (j : Fin (n + 1)) : Finset (∀ j : Fin (n + 1), Fin (2 * r) → ι j) :=
  {ω | ¬ ((8 * 2 ^ (j : ℕ) ≤ #S → r < #{k | y j ∈ S.image (h j (ω j k))}) ∧
    (8 * #S ≤ 2 ^ (j : ℕ) → ¬ r < #{k | y j ∈ S.image (h j (ω j k))}))}

variable [∀ j, Nonempty (ι j)]

/-- Each level answers incorrectly with probability at most `(8 / 9) ^ r`. -/
private theorem dens_wrongSeeds_le (hh : ∀ j, IsPairwiseIndependentHash (h j))
    (hY : ∀ j, Fintype.card (Y j) = 2 ^ j) (j : Fin (n + 1)) :
    dens (wrongSeeds h y S (r := r) j) ≤ (8 / 9) ^ r := by
  classical
  set G : Finset (ι j) := {i | y j ∈ S.image (h j i)}
  set Gc : Finset (ι j) := {i | ¬ y j ∈ S.image (h j i)}
  have hcount : ∀ v : Fin (2 * r) → ι j,
      #{k | y j ∈ S.image (h j (v k))} = #{k | v k ∈ G} := fun v => by
    simp only [G, mem_filter, mem_univ, true_and]
  refine (dens_le_dens fun ω hω => ?_).trans ((dens_filter_apply_mem_le j
    {v : Fin (2 * r) → ι j | ¬ ((8 * 2 ^ (j : ℕ) ≤ #S → r < #{k | v k ∈ G}) ∧
      (8 * #S ≤ 2 ^ (j : ℕ) → ¬ r < #{k | v k ∈ G}))}).trans ?_)
  · simp only [wrongSeeds, mem_filter, mem_univ, true_and, hcount] at hω ⊢
    exact hω
  have hYj : (Fintype.card (Y j) : ℚ≥0) = 2 ^ (j : ℕ) := by rw [hY, Nat.cast_pow, Nat.cast_ofNat]
  by_cases hhigh : 8 * 2 ^ (j : ℕ) ≤ #S
  · -- the mean cell size is at least `8`, and `S` misses `y j` with probability at most `1 / 8`
    have hS : S.Nonempty := card_pos.1 (by have := Nat.one_le_two_pow (n := (j : ℕ)); omega)
    have hG : 2 / 3 ≤ G.dens := by
      refine two_thirds_le_of_add_eq_one (dens_filter_add_dens_filter_not_eq_dens
        (s := (univ : Finset (ι j))) _ |>.trans dens_univ) ?_
      refine ((hh j).dens_filter_notMem_image_le hS (y j)).trans ?_
      rw [hYj, div_le_div_iff₀ (by exact_mod_cast hS.card_pos) (by norm_num)]
      exact_mod_cast (by omega : 2 ^ (j : ℕ) * 8 ≤ 1 * #S)
    refine le_trans (dens_le_dens fun v hv => ?_) (dens_filter_card_filter_le_le hG r)
    simp only [mem_filter, mem_univ, true_and, not_and_or, not_imp, not_lt] at hv ⊢
    rcases hv with ⟨-, hv⟩ | ⟨hlow, -⟩
    · exact hv
    · have := Nat.one_le_two_pow (n := (j : ℕ))
      omega
  by_cases hlow : 8 * #S ≤ 2 ^ (j : ℕ)
  · -- the mean cell size is at most `1 / 8`, and `S` hits `y j` with probability at most `1 / 8`
    have hGc : 2 / 3 ≤ Gc.dens := by
      refine two_thirds_le_of_add_eq_one ((add_comm _ _).trans
        (dens_filter_add_dens_filter_not_eq_dens (s := (univ : Finset (ι j))) _ |>.trans
          dens_univ)) ?_
      refine ((hh j).dens_filter_mem_image_le S (y j)).trans ?_
      rw [hYj, div_le_div_iff₀ (by positivity) (by norm_num)]
      exact_mod_cast (by omega : #S * 8 ≤ 1 * 2 ^ (j : ℕ))
    refine le_trans (dens_le_dens fun v hv => ?_) (dens_filter_card_filter_le_le hGc r)
    simp only [mem_filter, mem_univ, true_and, not_and_or, not_imp, not_lt] at hv ⊢
    rcases hv with ⟨hhigh', -⟩ | ⟨-, hv⟩
    · exact absurd hhigh' hhigh
    · have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * r))))
        (fun k => v k ∈ G)
      have hGc' : ∀ k, v k ∈ Gc ↔ ¬ v k ∈ G := fun k => by simp [G, Gc]
      simp only [card_univ, Fintype.card_fin] at hsum
      simp only [hGc']
      omega
  · -- neither condition holds, so no seed is wrong
    refine le_trans (le_of_eq (dens_eq_zero.2 (eq_empty_of_forall_notMem fun v hv => ?_)))
      (by positivity)
    simp only [mem_filter, mem_univ, true_and] at hv
    exact hv ⟨fun h' => absurd h' hhigh, fun h' => absurd h' hlow⟩

/-- **The answers from hashing are correct with high probability**: if every `h j` is a pairwise
independent hash family into a set of `2 ^ j` elements, with seeds from a nonempty type `ι j`, then
for `2 r` independent uniform seeds per level `j ≤ n`, the majority answers are correct for `S`
except with probability at most `(n + 1) (8 / 9) ^ r`. -/
theorem dens_filter_not_answersCorrect_le (hh : ∀ j, IsPairwiseIndependentHash (h j))
    (hY : ∀ j, Fintype.card (Y j) = 2 ^ j) :
    dens {ω : ∀ j : Fin (n + 1), Fin (2 * r) → ι j |
      ¬ AnswersCorrect n #S (hashAnswer h y S ω)} ≤ (n + 1) * (8 / 9) ^ r := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp only [pow_zero, mul_one]
    exact dens_le_one.trans (by simp)
  have hsub : ({ω | ¬ AnswersCorrect n #S (hashAnswer h y S ω)} : Finset _) ⊆
      univ.biUnion (wrongSeeds h y S (n := n) (r := r)) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    simp only [mem_biUnion, mem_univ, true_and]
    by_contra! hright
    simp only [wrongSeeds, mem_filter, mem_univ, true_and, not_not] at hright
    refine hω ⟨?_, fun j hj hc => ⟨by omega, (hright ⟨j, by omega⟩).1 hc⟩,
      fun j hj hc ⟨hj', ha⟩ => (hright ⟨j, hj'⟩).2 hc ha⟩
    -- level `0` has a single cell, `S` itself
    have : Subsingleton (Y 0) := Fintype.card_le_one_iff_subsingleton.1 (by rw [hY]; rfl)
    have hcell : ∀ i : ι 0, y 0 ∈ S.image (h 0 i) ↔ S.Nonempty := fun i => by
      rw [mem_image]
      exact ⟨fun ⟨x, hx, _⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, hx, Subsingleton.elim _ _⟩⟩
    simp only [hashAnswer]
    rw [card_pos]
    by_cases hS : S.Nonempty
    · simp only [hcell, hS, filter_true, card_univ, Fintype.card_fin, iff_true]
      exact ⟨by omega, by omega⟩
    · simp only [hcell, hS, filter_false, card_empty, iff_false]
      omega
  calc dens {ω | ¬ AnswersCorrect n #S (hashAnswer h y S ω)}
      ≤ dens (univ.biUnion (wrongSeeds h y S (n := n) (r := r))) := dens_le_dens hsub
    _ ≤ ∑ j, dens (wrongSeeds h y S (n := n) (r := r) j) := dens_biUnion_le
    _ ≤ ∑ _j : Fin (n + 1), (8 / 9 : ℚ≥0) ^ r :=
        sum_le_sum fun j _ => dens_wrongSeeds_le h y S hh hY j
    _ = (n + 1) * (8 / 9) ^ r := by simp

/-- `(n + 1) (8 / 9) ^ (12 (n + 1)) ≤ 1 / 4`, as `4 (n + 1) 8 ^ (12 (n + 1)) ≤ 9 ^ (12 (n + 1))`. -/
private theorem four_mul_mul_eight_pow_le (n : ℕ) :
    4 * (n + 1) * 8 ^ (12 * (n + 1)) ≤ 9 ^ (12 * (n + 1)) := by
  have hn : n + 1 ≤ 4 ^ n := Nat.lt_pow_self (by norm_num)
  calc 4 * (n + 1) * 8 ^ (12 * (n + 1)) ≤ 4 * 4 ^ n * 8 ^ (12 * (n + 1)) := by gcongr
    _ = (4 * 8 ^ 12) ^ (n + 1) := by rw [mul_pow, pow_mul, pow_succ]; ring
    _ ≤ (9 ^ 12) ^ (n + 1) := Nat.pow_le_pow_left (by norm_num) _
    _ = 9 ^ (12 * (n + 1)) := by rw [pow_mul]

/-- **Stockmeyer's approximate counting**: if every `h j` is a pairwise independent hash family
into a set of `2 ^ j` elements, with seeds from a nonempty type `ι j`, and `#S ≤ 2 ^ n`, then for
`24 (n + 1)` independent uniform seeds per level `j ≤ n`, the estimate from the majority answers is
between `#S / 16` and `8 #S` with probability at least `3 / 4`. -/
theorem three_quarters_le_dens_filter_hashEstimate (hh : ∀ j, IsPairwiseIndependentHash (h j))
    (hY : ∀ j, Fintype.card (Y j) = 2 ^ j) (hS : #S ≤ 2 ^ n) :
    3 / 4 ≤ dens {ω : ∀ j : Fin (n + 1), Fin (2 * (12 * (n + 1))) → ι j |
      hashEstimate h y S ω ≤ 8 * #S ∧ #S ≤ 16 * hashEstimate h y S ω} := by
  have hbad := dens_filter_not_answersCorrect_le h y S hh hY (n := n) (r := 12 * (n + 1))
  have hsub : ({ω | ¬ (hashEstimate h y S ω ≤ 8 * #S ∧ #S ≤ 16 * hashEstimate h y S ω)} :
      Finset (∀ j : Fin (n + 1), Fin (2 * (12 * (n + 1))) → ι j)) ⊆
      ({ω | ¬ AnswersCorrect n #S (hashAnswer h y S ω)} : Finset _) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω ⊢
    exact fun ha => hω ⟨ha.estimate_le, ha.le_estimate hS⟩
  have hsplit := dens_filter_add_dens_filter_not_eq_dens
    (s := (univ : Finset (∀ j : Fin (n + 1), Fin (2 * (12 * (n + 1))) → ι j)))
    (fun ω => hashEstimate h y S ω ≤ 8 * #S ∧ #S ≤ 16 * hashEstimate h y S ω)
  rw [dens_univ] at hsplit
  have harith : ((n : ℚ≥0) + 1) * (8 / 9) ^ (12 * (n + 1)) ≤ 1 / 4 := by
    have h' := Nat.cast_le (α := ℚ≥0).2 (four_mul_mul_eight_pow_le n)
    push_cast at h'
    rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num), one_mul]
    exact le_of_eq_of_le (by ring) h'
  have hle := (dens_le_dens hsub).trans (hbad.trans harith)
  rw [← NNRat.cast_le (K := ℚ)]
  have hsplit' := congrArg (NNRat.cast : ℚ≥0 → ℚ) hsplit
  have hle' := NNRat.cast_le (K := ℚ).2 hle
  push_cast at hsplit' hle' ⊢
  linarith

end Hashing

/-! ### Affine hash families -/

/-- **Approximate counting with affine hashes**: for a set `S` of vectors in `(ZMod 2) ^ n`, with
the affine hash families `x ↦ A x + b` into `(ZMod 2) ^ j` for the levels `j ≤ n`, target `0`, and
`24 (n + 1)` independent seeds per level, the estimate is between `#S / 16` and `8 #S` with
probability at least `3 / 4`. -/
theorem three_quarters_le_dens_filter_affineHashEstimate {n : ℕ} (S : Finset (Fin n → ZMod 2)) :
    3 / 4 ≤ dens {ω : ∀ j : Fin (n + 1), Fin (2 * (12 * (n + 1))) →
        Matrix (Fin j) (Fin n) (ZMod 2) × (Fin j → ZMod 2) |
      hashEstimate (fun _ => affineHash) (fun _ => 0) S ω ≤ 8 * #S ∧
        #S ≤ 16 * hashEstimate (fun _ => affineHash) (fun _ => 0) S ω} := by
  have hh : ∀ j, IsPairwiseIndependentHash
      (affineHash : Matrix (Fin j) (Fin n) (ZMod 2) × (Fin j → ZMod 2) → _) :=
    fun _ => isPairwiseIndependentHash_affineHash
  have hY : ∀ j, Fintype.card (Fin j → ZMod 2) = 2 ^ j := fun j => by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hS : #S ≤ 2 ^ n := by
    simpa only [Fintype.card_fun, ZMod.card, Fintype.card_fin] using card_le_univ S
  exact three_quarters_le_dens_filter_hashEstimate
    (ι := fun j => Matrix (Fin j) (Fin n) (ZMod 2) × (Fin j → ZMod 2))
    (Y := fun j => Fin j → ZMod 2) _ _ _ hh hY hS

end Cslib.Probability.ApproximateCounting
