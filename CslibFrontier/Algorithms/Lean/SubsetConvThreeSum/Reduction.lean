/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Probability
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# The reduction from 3SUM to selected entries of subset convolution

[ChanItakuraMaYu2026], Theorem 2.3: decide `c ∈ A + B` for every query `c ∈ C` by hashing modulo
a random prime `p` and `μ` trials of `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Trial`.
`threeSumM d t s p seeds A B C` is the algorithm for given random choices: the prime `p` and the
list `seeds` of the trials' seeds.

1. It counts the residues of `A` and `B` modulo `p` and splits off the elements that share their
   residue class (`A_bad`, `B_bad`; `isolatedM`).
2. It reports every `c ∈ A_bad + B` or `c ∈ A + B_bad` (the sums are listed exactly).
3. It runs one trial per seed on the isolated elements and reports the accepted queries.

## Results

* **Soundness** (`exists_add_eq_of_mem_ret_threeSumM`): every reported `c` is a sum `a + b` with
  `a ∈ A`, `b ∈ B`, for every prime and all seeds; the error is one-sided.
* **What it returns** (`ret_threeSumM`) and its **exact cost** (`time_threeSumM`).
* **Error probability** (`miss_le`): for `c ∈ A + B`, a prime `p` of the window `[2 ^ d, 2 ^ (d+1))`
  that is good for `c`, and `μ` independent uniform seeds, the probability that `c` is not reported
  is at most `(1 - 3 #P / (4 p ^ 2)) ^ μ`, where `#P = (d choose 2 t) (2 t choose t)`
  (`card_rankedPairs`). Bad primes are rare by `card_badPrimes_le` and
  `two_pow_le_card_primeWindow`. Averaged over a uniform prime of the window
  (`average_miss_le`), the error is at most `#bad / #window + (1 - 3 #P / 4 ^ (d + 2)) ^ μ`.

The parameter choices, the expected cost, the conversion to worst-case time and the truly
subquadratic exponent of Corollary 2.4 are in
`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Corollary`.

## Cost model

The `TimeM` unit-cost model of `CslibFrontier.Algorithms.Lean.TrimmedYates`: residues, numbers
below `N ^ O(1)` and sets of at most `d` coordinates are words and dictionary operations cost one
tick. Charged: one tick per element when counting residues and when splitting, one per listed bad
sum and per inserted reported value, one per query in the final look-up, and the ticks of the
trials (`time_trialM`). The random choices are inputs; sampling them is uncharged. The cost depends
on the random choices through `|A_bad|`, `|B_bad|`, `|A*|`, `|B*|`, `|C*|` and the number of
reported values; `time_threeSumM` states it exactly. Their expectations are bounded in
`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Expectation`.

## Main definitions

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.isolatedM`, `threeSumM`.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.BadHit`: `c ∈ A_bad + B ∪ A + B_bad`.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.exists_add_eq_of_mem_ret_threeSumM`: soundness.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.ret_threeSumM`, `time_threeSumM`.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.miss_le`, `average_miss_le`: error probability.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset Cslib.Algorithms.Lean.TimeM

variable {p : ℕ}

/-! ### Isolated elements -/

/-- Count the residue of `a` in the dictionary `F` of residue counts, at one tick. -/
@[expose] def countStepM (F : ZMod p → ℕ) (a : ℕ) : TimeM ℕ (ZMod p → ℕ) := do
  ✓ pure (fun r : ZMod p => if r = (a : ZMod p) then F r + 1 else F r)

/-- The elements of `A` isolated modulo `p`, and the others (`A_bad`): residues are counted in a
dictionary at one tick per element, then each element is tested at one tick. -/
@[expose] def isolatedM (p : ℕ) (A : List ℕ) : TimeM ℕ (List ℕ × List ℕ) := do
  let cnt ← A.foldlM countStepM (0 : ZMod p → ℕ)
  let good ← filterTickM (fun a : ℕ => cnt (a : ZMod p) = 1) A
  let bad ← filterTickM (fun a : ℕ => cnt (a : ZMod p) ≠ 1) A
  pure (good, bad)

private theorem ret_count_foldl (A : List ℕ) (F₀ : ZMod p → ℕ) (r : ZMod p) :
    (A.foldl (fun F a => (countStepM F a).ret) F₀) r =
      F₀ r + A.countP fun a' : ℕ => (a' : ZMod p) = r := by
  induction A generalizing F₀ with
  | nil => simp
  | cons a A ih =>
    rw [List.foldl_cons, ih, List.countP_cons]
    simp only [countStepM, ret_bind, ret_pure]
    by_cases h : r = a
    · subst h; simp; ring
    · simp [h, Ne.symm h]

theorem ret_isolatedM (p : ℕ) (A : List ℕ) :
    (isolatedM p A).ret = (A.filter fun a => decide (Isolated p A a),
      A.filter fun a => decide (¬ Isolated p A a)) := by
  have hcnt : ∀ r : ZMod p, (A.foldlM countStepM (0 : ZMod p → ℕ)).ret r =
      A.countP fun a' : ℕ => (a' : ZMod p) = r := fun r => by
    rw [ret_foldlM, ret_count_foldl]; simp
  simp only [isolatedM, ret_bind, ret_pure, ret_filterTickM, hcnt, Isolated, ne_eq]
  rfl

@[simp] theorem time_isolatedM (p : ℕ) (A : List ℕ) : (isolatedM p A).time = 3 * A.length := by
  simp only [isolatedM, time_bind, time_pure, time_filterTickM, add_zero]
  rw [time_foldlM_of_time_eq _ _ _ (c := 1) fun _ _ => by simp [countStepM]]
  ring

/-! ### The algorithm -/

/-- `c` is the sum of `a ∈ A` and `b ∈ B` where `a` or `b` shares its residue class modulo `p`:
`c ∈ A_bad + B ∪ A + B_bad`. -/
@[expose] def BadHit (p : ℕ) (A B : List ℕ) (c : ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, a + b = c ∧ (¬ Isolated p A a ∨ ¬ Isolated p B b)

instance (p : ℕ) (A B : List ℕ) (c : ℕ) : Decidable (BadHit p A B c) :=
  inferInstanceAs (Decidable (∃ a ∈ A, ∃ b ∈ B, _))

/-- The bad sums `A_bad + B` and `A + B_bad`, listed. -/
@[expose] def badSums (Abad Bbad A B : List ℕ) : List ℕ :=
  (Abad.flatMap fun a => B.map (a + ·)) ++ A.flatMap fun a => Bbad.map (a + ·)

/-- **The reduction** for given random choices: the prime `p` and the seeds of the trials. -/
@[expose] def threeSumM (d t s p : ℕ) (seeds : List (Seed p)) (A B C : List ℕ) :
    TimeM ℕ (List ℕ) := do
  let (Ag, Abad) ← isolatedM p A
  let (Bg, Bbad) ← isolatedM p B
  let rs ← seeds.mapM fun σ => trialM d t s σ Ag Bg C
  let yes := badSums Abad Bbad A B ++ rs.flatten
  ✓[yes.length] filterTickM (· ∈ yes) C

theorem mem_badSums {Abad Bbad A B : List ℕ} {c : ℕ} :
    c ∈ badSums Abad Bbad A B ↔
      (∃ a ∈ Abad, ∃ b ∈ B, a + b = c) ∨ ∃ a ∈ A, ∃ b ∈ Bbad, a + b = c := by
  simp [badSums, List.mem_flatMap]

/-- **What the reduction returns**: the queries of `C` that are bad sums or accepted by a trial. -/
theorem ret_threeSumM {d t s p : ℕ} (seeds : List (Seed p)) (A B C : List ℕ) (hs : s ≤ 2 * t) :
    (threeSumM d t s p seeds A B C).ret = C.filter fun c => decide (BadHit p A B c ∨
      ∃ σ ∈ seeds, Accepts d t σ (A.filter fun a => decide (Isolated p A a))
        (B.filter fun b => decide (Isolated p B b)) c) := by
  have e₃ : seeds.map (fun σ => (trialM d t s σ (A.filter fun a => decide (Isolated p A a))
      (B.filter fun b => decide (Isolated p B b)) C).ret) =
      seeds.map fun σ => C.filter fun c => decide (Accepts d t σ
        (A.filter fun a => decide (Isolated p A a))
        (B.filter fun b => decide (Isolated p B b)) c) :=
    List.map_congr_left fun σ _ => ret_trialM _ _ _ _ hs
  rw [threeSumM]
  simp only [ret_bind]
  rw [ret_isolatedM, ret_isolatedM]
  dsimp only
  rw [ret_listMapM, e₃, ret_filterTickM]
  refine List.filter_congr fun c hc => decide_eq_decide.mpr ?_
  simp only [List.mem_append, mem_badSums, List.mem_flatten, List.mem_map, BadHit]
  constructor
  · rintro (((⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)) | ⟨_, ⟨σ, hσ, rfl⟩, hmem⟩)
    · obtain ⟨ha, hna⟩ := List.mem_filter.mp ha
      exact Or.inl ⟨a, ha, b, hb, rfl, Or.inl (by simpa using hna)⟩
    · obtain ⟨hb, hnb⟩ := List.mem_filter.mp hb
      exact Or.inl ⟨a, ha, b, hb, rfl, Or.inr (by simpa using hnb)⟩
    · exact Or.inr ⟨σ, hσ, by simpa using (List.mem_filter.mp hmem).2⟩
  · rintro (⟨a, ha, b, hb, rfl, hna | hnb⟩ | ⟨σ, hσ, hacc⟩)
    · exact Or.inl (Or.inl ⟨a, List.mem_filter.mpr ⟨ha, by simpa using hna⟩, b, hb, rfl⟩)
    · exact Or.inl (Or.inr ⟨a, ha, b, List.mem_filter.mpr ⟨hb, by simpa using hnb⟩, rfl⟩)
    · exact Or.inr ⟨_, ⟨σ, hσ, rfl⟩, List.mem_filter.mpr ⟨hc, by simpa using hacc⟩⟩

/-- **Soundness of the reduction** (one-sided error): every reported query is a sum `a + b` with
`a ∈ A` and `b ∈ B`, for every modulus and all seeds. -/
theorem exists_add_eq_of_mem_ret_threeSumM {d t s p : ℕ} {seeds : List (Seed p)}
    {A B C : List ℕ} (hs : s ≤ 2 * t) {c : ℕ} (hc : c ∈ (threeSumM d t s p seeds A B C).ret) :
    ∃ a ∈ A, ∃ b ∈ B, a + b = c := by
  rw [ret_threeSumM seeds A B C hs] at hc
  obtain ⟨-, h⟩ := List.mem_filter.mp hc
  rcases of_decide_eq_true h with ⟨a, ha, b, hb, habc, -⟩ | ⟨σ, -, hacc⟩
  · exact ⟨a, ha, b, hb, habc⟩
  · obtain ⟨a, ha, b, hb, habc⟩ := exists_add_eq_of_accepts hacc
    exact ⟨a, List.mem_of_mem_filter ha, b, List.mem_of_mem_filter hb, habc⟩

/-- **Completeness for given random choices**: a sum `c = a + b` with `a ∈ A`, `b ∈ B` that is in
`C` is reported if it is a bad sum or some trial accepts it, and otherwise `a` and `b` are
isolated. -/
theorem mem_ret_threeSumM_or_isolated {d t s p : ℕ} (seeds : List (Seed p)) {A B C : List ℕ}
    (hs : s ≤ 2 * t) {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ B) (habc : a + b = c) (hc : c ∈ C) :
    c ∈ (threeSumM d t s p seeds A B C).ret ∨ (Isolated p A a ∧ Isolated p B b ∧
      ∀ σ ∈ seeds, ¬ Accepts d t σ (A.filter fun a => decide (Isolated p A a))
        (B.filter fun b => decide (Isolated p B b)) c) := by
  rw [ret_threeSumM seeds A B C hs]
  by_cases hbad : ¬ Isolated p A a ∨ ¬ Isolated p B b
  · exact Or.inl (List.mem_filter.mpr ⟨hc, decide_eq_true (Or.inl ⟨a, ha, b, hb, habc, hbad⟩)⟩)
  push Not at hbad
  by_cases hacc : ∃ σ ∈ seeds, Accepts d t σ (A.filter fun a => decide (Isolated p A a))
      (B.filter fun b => decide (Isolated p B b)) c
  · exact Or.inl (List.mem_filter.mpr ⟨hc, decide_eq_true (Or.inr hacc)⟩)
  · push Not at hacc
    exact Or.inr ⟨hbad.1, hbad.2, hacc⟩

theorem length_badSums (Abad Bbad A B : List ℕ) :
    (badSums Abad Bbad A B).length = Abad.length * B.length + A.length * Bbad.length := by
  simp [badSums, List.length_flatMap]

/-- **The cost of the reduction**, exactly: `3 (|A| + |B|)` ticks to split off `A_bad` and
`B_bad`, the ticks of the trials (`time_trialM`), one tick per listed bad sum
(`|A_bad| |B| + |A| |B_bad|`) and per reported value of a trial, and one per query. -/
theorem time_threeSumM {d t s p : ℕ} (seeds : List (Seed p)) (A B C : List ℕ) (hs : s ≤ 2 * t) :
    let Ag := A.filter fun a => decide (Isolated p A a)
    let Bg := B.filter fun b => decide (Isolated p B b)
    (threeSumM d t s p seeds A B C).time = 3 * A.length + 3 * B.length +
      (seeds.map fun σ => (trialM d t s σ Ag Bg C).time).sum +
      ((A.filter fun a => decide (¬ Isolated p A a)).length * B.length +
        A.length * (B.filter fun b => decide (¬ Isolated p B b)).length) +
      (seeds.map fun σ => (C.filter fun c => decide (Accepts d t σ Ag Bg c)).length).sum +
      C.length := by
  intro Ag Bg
  have e₃ : seeds.map (fun σ => (trialM d t s σ Ag Bg C).ret) =
      seeds.map fun σ => C.filter fun c => decide (Accepts d t σ Ag Bg c) :=
    List.map_congr_left fun σ _ => ret_trialM _ _ _ _ hs
  rw [threeSumM]
  simp only [time_bind]
  rw [ret_isolatedM, ret_isolatedM, time_isolatedM, time_isolatedM]
  dsimp only
  rw [time_listMapM, ret_listMapM, e₃, time_tick, time_filterTickM, List.length_append,
    length_badSums, List.length_flatten, List.map_map]
  simp only [Function.comp_def]
  ring

/-! ### Error probability -/

theorem card_rankedPairs_le (d t : ℕ) : #(rankedPairs d t) ≤ 2 ^ d * 2 ^ d := by
  refine (card_filter_le _ _).trans ?_
  rw [card_product, card_range]

/-- **The miss probability for a good prime** ([ChanItakuraMaYu2026], Theorem 2.3): let
`c = a + b ∈ C` with `a ∈ A`, `b ∈ B`, let `p ≥ 2 ^ d` be prime and good for `c`
(`4 #L (2 t choose t) ≤ p - 1`). Over `μ` independent uniform seeds, the reduction misses `c`
with probability at most `(1 - 3 #P / (4 p ^ 2)) ^ μ`, where `#P = (d choose 2 t) (2 t choose t)`
(`card_rankedPairs`). -/
theorem miss_le [Fact p.Prime] {d t s μ : ℕ} (hs : s ≤ 2 * t) (hp : 2 ^ d ≤ p) {A B C : List ℕ}
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ B) (habc : a + b = c) (hc : c ∈ C)
    (hgood : 4 * (#(falsePairs p c (A.filter fun a => decide (Isolated p A a))
      (B.filter fun b => decide (Isolated p B b))) * (2 * t).choose t) ≤ p - 1) :
    (#((Fintype.piFinset fun _ : Fin μ => seeds p).filter fun ss =>
        c ∉ (threeSumM d t s p (List.ofFn ss) A B C).ret) : ℝ) / (#(seeds p) : ℝ) ^ μ ≤
      (1 - 3 * #(rankedPairs d t) / (4 * (p : ℝ) ^ 2)) ^ μ := by
  set Ag := A.filter fun a => decide (Isolated p A a)
  set Bg := B.filter fun b => decide (Isolated p B b)
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hN : (#(seeds p) : ℝ) = ((p : ℝ) - 1) * (p : ℝ) ^ 2 := by
    rw [card_seeds]; push_cast [Nat.cast_sub hp1.le]; ring
  have hNpos : (0 : ℝ) < #(seeds p) := by
    rw [hN]; have : (1 : ℝ) < p := by exact_mod_cast hp1
    positivity
  have hPle : (3 * #(rankedPairs d t) : ℝ) ≤ 4 * (p : ℝ) ^ 2 := by
    have h1 := card_rankedPairs_le d t
    have h2 : 2 ^ d * 2 ^ d ≤ p * p := Nat.mul_le_mul hp hp
    have : (#(rankedPairs d t) : ℝ) ≤ (p : ℝ) ^ 2 := by
      rw [sq]; exact_mod_cast h1.trans h2
    linarith
  have hbase : 0 ≤ 1 - 3 * (#(rankedPairs d t) : ℝ) / (4 * (p : ℝ) ^ 2) := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact hPle
  rcases mem_ret_threeSumM_or_isolated (d := d) (t := t) (s := s) ([] : List (Seed p))
      hs ha hb habc hc with
    hrep | ⟨hia, hib, -⟩
  · -- `c` is a bad sum: it is reported for all seeds
    have hempty : ((Fintype.piFinset fun _ : Fin μ => seeds p).filter fun ss =>
        c ∉ (threeSumM d t s p (List.ofFn ss) A B C).ret) = ∅ := by
      refine filter_eq_empty_iff.mpr fun ss _ hmiss => hmiss ?_
      rw [ret_threeSumM ([] : List (Seed p)) A B C hs] at hrep
      rw [ret_threeSumM (List.ofFn ss) A B C hs]
      obtain ⟨-, h⟩ := List.mem_filter.mp hrep
      rcases of_decide_eq_true h with hbad | ⟨σ, hσ, -⟩
      · exact List.mem_filter.mpr ⟨hc, decide_eq_true (Or.inl hbad)⟩
      · simp at hσ
    rw [hempty, card_empty, Nat.cast_zero, zero_div]
    exact pow_nonneg hbase μ
  -- both are isolated: a miss means every trial rejects
  have hsub : ((Fintype.piFinset fun _ : Fin μ => seeds p).filter fun ss =>
      c ∉ (threeSumM d t s p (List.ofFn ss) A B C).ret) ⊆
      (Fintype.piFinset fun _ : Fin μ => seeds p).filter fun ss =>
        ∀ i, ¬ Accepts d t (ss i) Ag Bg c := by
    intro ss hss
    obtain ⟨hpi, hmiss⟩ := mem_filter.mp hss
    refine mem_filter.mpr ⟨hpi, fun i hacc => hmiss ?_⟩
    rw [ret_threeSumM _ A B C hs]
    exact List.mem_filter.mpr ⟨hc, decide_eq_true (Or.inr ⟨ss i, List.mem_ofFn.mpr ⟨i, rfl⟩,
      hacc⟩)⟩
  have hcount := card_forall_not_accepts (p := p) d t μ Ag Bg c
  have hsplit := card_filter_add_card_filter_not (s := seeds p)
    (fun s => Accepts d t s Ag Bg c)
  have hacc := four_mul_card_accepts_ge (d := d) (t := t) hp (fun x hx => List.mem_of_mem_filter hx)
    (fun x hx => List.mem_of_mem_filter hx) (List.mem_filter.mpr ⟨ha, decide_eq_true hia⟩)
    (List.mem_filter.mpr ⟨hb, decide_eq_true hib⟩) hia hib habc hgood
  set R := #((seeds p).filter fun s => ¬ Accepts d t s Ag Bg c)
  set Q := #((seeds p).filter fun s => Accepts d t s Ag Bg c)
  have hratio : (R : ℝ) / #(seeds p) ≤ 1 - 3 * #(rankedPairs d t) / (4 * (p : ℝ) ^ 2) := by
    have hR : (R : ℝ) = #(seeds p) - Q := by
      rw [← hsplit]; push_cast; ring
    have hQ : (3 * (#(rankedPairs d t) * ((p : ℝ) - 1)) : ℝ) ≤ 4 * Q := by
      have := hacc
      have hc' : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by push_cast [Nat.cast_sub hp1.le]; ring
      rw [← hc']; exact_mod_cast this
    rw [hR, div_le_iff₀ hNpos, hN]
    have hp' : (1 : ℝ) < p := by exact_mod_cast hp1
    have : (3 * #(rankedPairs d t) / (4 * (p : ℝ) ^ 2)) * (((p : ℝ) - 1) * (p : ℝ) ^ 2) =
        3 * (#(rankedPairs d t) * ((p : ℝ) - 1)) / 4 := by
      field_simp
    nlinarith [this]
  calc (#((Fintype.piFinset fun _ : Fin μ => seeds p).filter fun ss =>
        c ∉ (threeSumM d t s p (List.ofFn ss) A B C).ret) : ℝ) / (#(seeds p) : ℝ) ^ μ
      ≤ (R : ℝ) ^ μ / (#(seeds p) : ℝ) ^ μ := by
        gcongr
        exact_mod_cast (card_le_card hsub).trans_eq hcount
    _ = ((R : ℝ) / #(seeds p)) ^ μ := (div_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hratio μ

theorem card_falsePairs_mono {q c : ℕ} {Ag Bg A B : List ℕ} (hA : ∀ x ∈ Ag, x ∈ A)
    (hB : ∀ x ∈ Bg, x ∈ B) : #(falsePairs q c Ag Bg) ≤ #(falsePairs q c A B) := by
  refine card_le_card fun ab hab => ?_
  obtain ⟨hmem, h⟩ := mem_filter.mp hab
  obtain ⟨ha, hb⟩ := mem_product.mp hmem
  exact mem_filter.mpr ⟨mem_product.mpr ⟨List.mem_toFinset.mpr (hA _ (List.mem_toFinset.mp ha)),
    List.mem_toFinset.mpr (hB _ (List.mem_toFinset.mp hb))⟩, h⟩

/-- The probability that the reduction misses `c` over `μ` uniform seeds, for the modulus `q`
(`0` if `q` is not prime). -/
@[expose] noncomputable def missProb (d t s μ : ℕ) (A B C : List ℕ) (c q : ℕ) : ℝ :=
  if h : q.Prime then
    haveI : Fact q.Prime := ⟨h⟩
    (#((Fintype.piFinset fun _ : Fin μ => seeds q).filter fun ss =>
      c ∉ (threeSumM d t s q (List.ofFn ss) A B C).ret) : ℝ) / (#(seeds q) : ℝ) ^ μ
  else 0

theorem missProb_le_one (d t s μ : ℕ) (A B C : List ℕ) (c q : ℕ) :
    missProb d t s μ A B C c q ≤ 1 := by
  unfold missProb
  split_ifs with h
  · have : Fact q.Prime := ⟨h⟩
    have hpos : (0 : ℝ) < (#(seeds q) : ℝ) ^ μ := by
      have : 0 < #(seeds q) := by
        rw [card_seeds]; exact Nat.mul_pos (by have := h.one_lt; omega) (pow_pos h.pos 2)
      positivity
    rw [div_le_one hpos]
    have := card_filter_le (Fintype.piFinset fun _ : Fin μ => seeds q) fun ss =>
      c ∉ (threeSumM d t s q (List.ofFn ss) A B C).ret
    rw [Fintype.card_piFinset_const] at this
    exact_mod_cast this
  · exact zero_le_one

/-- **The error of the reduction** ([ChanItakuraMaYu2026], Theorem 2.3): for `c = a + b ∈ C` with
`a ∈ A`, `b ∈ B`, a uniform prime `q` of the window `[2 ^ d, 2 ^ (d + 1))` and `μ` independent
uniform seeds, the reduction misses `c` with probability at most
`#bad / #window + (1 - 3 #P / 4 ^ (d + 2)) ^ μ`. Bad primes are rare by `card_badPrimes_le`;
`#P = (d choose 2 t) (2 t choose t)` (`card_rankedPairs`); the window has at least
`2 ^ d / (3 (d + 1))` primes (`two_pow_le_card_primeWindow`). -/
theorem average_miss_le {d t s μ : ℕ} (hs : s ≤ 2 * t) {A B C : List ℕ} {a b c : ℕ}
    (ha : a ∈ A) (hb : b ∈ B) (habc : a + b = c) (hc : c ∈ C)
    (hW : (primeWindow d).Nonempty) :
    (∑ q ∈ primeWindow d, missProb d t s μ A B C c q) / #(primeWindow d) ≤
      (#(badPrimes d t c A B) : ℝ) / #(primeWindow d) +
        (1 - 3 * #(rankedPairs d t) / (4 : ℝ) ^ (d + 2)) ^ μ := by
  have hWpos : (0 : ℝ) < #(primeWindow d) := by exact_mod_cast hW.card_pos
  set r := 1 - 3 * (#(rankedPairs d t) : ℝ) / (4 : ℝ) ^ (d + 2)
  have hgoodq : ∀ q ∈ primeWindow d, q ∉ badPrimes d t c A B →
      missProb d t s μ A B C c q ≤ r ^ μ := by
    intro q hq hnb
    obtain ⟨hprime, hlo, hhi⟩ := mem_primeWindow.mp hq
    have : Fact q.Prime := ⟨hprime⟩
    have hgood : 4 * (#(falsePairs q c (A.filter fun a => decide (Isolated q A a))
        (B.filter fun b => decide (Isolated q B b))) * (2 * t).choose t) ≤ q - 1 := by
      have h1 : ¬ q - 1 < 4 * (#(falsePairs q c A B) * (2 * t).choose t) := fun h =>
        hnb (mem_filter.mpr ⟨hq, h⟩)
      have h2 := card_falsePairs_mono (q := q) (c := c)
        (fun x hx => List.mem_of_mem_filter hx) (fun x hx => List.mem_of_mem_filter hx)
        (A := A) (B := B) (Ag := A.filter fun a => decide (Isolated q A a))
        (Bg := B.filter fun b => decide (Isolated q B b))
      have h3 := Nat.mul_le_mul_right ((2 * t).choose t) h2
      omega
    have hmiss := miss_le (μ := μ) hs hlo ha hb habc hc hgood
    unfold missProb
    rw [dite_eq_left_of_eq_true (eq_true hprime)]
    have hqpos : (0 : ℝ) < 4 * (q : ℝ) ^ 2 := by
      have : (0 : ℝ) < q := by exact_mod_cast hprime.pos
      positivity
    refine hmiss.trans (pow_le_pow_left₀ ?_ ?_ μ)
    · have hP : (#(rankedPairs d t) : ℝ) ≤ (q : ℝ) ^ 2 := by
        rw [sq]; exact_mod_cast (card_rankedPairs_le d t).trans (Nat.mul_le_mul hlo hlo)
      rw [sub_nonneg, div_le_one hqpos]
      linarith
    · have hq2 : (4 : ℝ) * (q : ℝ) ^ 2 ≤ (4 : ℝ) ^ (d + 2) := by
        have : q * q ≤ 2 ^ (d + 1) * 2 ^ (d + 1) := Nat.mul_le_mul hhi.le hhi.le
        have h' : ((q : ℝ)) ^ 2 ≤ (2 : ℝ) ^ (d + 1) * 2 ^ (d + 1) := by
          rw [sq]; exact_mod_cast this
        have h4 : (4 : ℝ) ^ (d + 2) = 4 * ((2 : ℝ) ^ (d + 1) * 2 ^ (d + 1)) := by
          rw [← mul_pow, show (2 : ℝ) * 2 = 4 by norm_num, pow_succ]; ring
        rw [h4]; linarith
      have : 3 * (#(rankedPairs d t) : ℝ) / (4 : ℝ) ^ (d + 2) ≤
          3 * (#(rankedPairs d t) : ℝ) / (4 * (q : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) hqpos hq2
      linarith
  have hsum : ∑ q ∈ primeWindow d, missProb d t s μ A B C c q ≤
      #(badPrimes d t c A B) + #(primeWindow d) * r ^ μ := by
    rw [← sum_filter_add_sum_filter_not (primeWindow d) fun q => q ∈ badPrimes d t c A B]
    have hb1 : ∑ q ∈ (primeWindow d).filter (· ∈ badPrimes d t c A B),
        missProb d t s μ A B C c q ≤ #(badPrimes d t c A B) := by
      refine (sum_le_sum fun q _ => missProb_le_one d t s μ A B C c q).trans ?_
      rw [sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast card_le_card fun q hq => (mem_filter.mp hq).2
    have hb2 : ∑ q ∈ (primeWindow d).filter (· ∉ badPrimes d t c A B),
        missProb d t s μ A B C c q ≤ #(primeWindow d) * r ^ μ := by
      refine (sum_le_sum fun q hq => hgoodq q (mem_filter.mp hq).1 (mem_filter.mp hq).2).trans ?_
      rw [sum_const, nsmul_eq_mul]
      have hr : 0 ≤ r ^ μ := by
        refine pow_nonneg ?_ μ
        have hP : (#(rankedPairs d t) : ℝ) ≤ (2 : ℝ) ^ d * 2 ^ d := by
          exact_mod_cast card_rankedPairs_le d t
        have h4 : (4 : ℝ) ^ (d + 2) = 16 * ((2 : ℝ) ^ d * 2 ^ d) := by
          rw [pow_add, ← mul_pow]; norm_num; ring
        have hpos : (0 : ℝ) < (2 : ℝ) ^ d * 2 ^ d := by positivity
        rw [sub_nonneg, div_le_one (by positivity), h4]
        linarith
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_le _ _) hr
    linarith
  rw [div_le_iff₀ hWpos, add_mul, div_mul_cancel₀ _ hWpos.ne']
  linarith

end Cslib.Algorithms.Lean.SubsetConvThreeSum
