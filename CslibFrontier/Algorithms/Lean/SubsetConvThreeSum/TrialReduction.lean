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
# The hashing reduction for an arbitrary trial

The reduction of [ChanItakuraMaYu2026], Theorems 2.3 and 3.4, is the same for every kind of
trial: split off the elements of `A` and `B` that share a residue class modulo `p` (`isolatedM`),
list the bad sums `A_bad + B` and `A + B_bad` exactly, and report a query if it is a bad sum or some
trial accepts it. `reduceM trial seeds A B C` runs this for a trial program `trial σ Ag Bg C` that
returns the queries accepted under the seed `σ` (`TrialSpec`), so that the base-`2` trial of
Theorem 2.3 and the base-`r` trial of Theorem 3.4 share one reduction and one error analysis.

* `ret_reduceM`: the reported queries are the bad sums and the queries accepted by a trial on the
  isolated elements.
* `exists_add_eq_of_mem_ret_reduceM`: one-sided error, for every modulus and all seeds, if every
  accepted query is a sum.
* `time_reduceM`: the exact cost.
* `reduceM_miss_le`: for `c = a + b ∈ C`, if a trial on isolated `a`, `b` accepts `c` for at least a
  `3 P / (4 p ^ 2)` fraction of the seeds, then `μ` independent uniform seeds miss `c` with
  probability at most `(1 - 3 P / (4 p ^ 2)) ^ μ`.
* `average_le_of_good`: averaged over a window of moduli, the miss probability is at most the
  fraction of bad moduli plus the bound for good ones.

`threeSumM` (`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Reduction`) is
`reduceM (fun σ => trialM d t s σ)` and `vthreeSumM`
(`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorReduction`) is
`reduceM (fun σ => vtrialM r d s σ)`. Both instantiate `TrialSpec` with the `ret_trialM` /
`ret_vtrialM` theorems of their trial modules, and get their success counts from the proved trial
analyses (`four_mul_card_accepts_ge`, `four_mul_card_vaccepts_ge`); `TrialSpec` itself only states
what a trial program returns.

* `average_miss_le_of_window`: the same over a binary window of primes `[2 ^ e, 2 ^ (e + 1))`,
  where the bad primes are `badPrimesOf e K c A B` (`good_of_not_mem_badPrimesOf`).

## Main definitions

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.isolatedM`, `BadHit`, `badSums`: the split into
  isolated elements and the bad sums `A_bad + B ∪ A + B_bad`.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.TrialSpec`, `reduceM`, `missProbOf`.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.ret_reduceM`, `exists_add_eq_of_mem_ret_reduceM`,
  `mem_ret_reduceM_or_isolated`, `time_reduceM`: what the reduction returns and costs.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.card_forall_not_le`,
  `reduceM_miss_le`, `average_le_of_good`, `average_miss_le_of_window`: its error.

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

theorem mem_badSums {Abad Bbad A B : List ℕ} {c : ℕ} :
    c ∈ badSums Abad Bbad A B ↔
      (∃ a ∈ Abad, ∃ b ∈ B, a + b = c) ∨ ∃ a ∈ A, ∃ b ∈ Bbad, a + b = c := by
  simp [badSums, List.mem_flatMap]

theorem length_badSums (Abad Bbad A B : List ℕ) :
    (badSums Abad Bbad A B).length = Abad.length * B.length + A.length * Bbad.length := by
  simp [badSums, List.length_flatMap]

/-! ### The reduction for a trial -/

/-- A trial program `trial σ Ag Bg C` returns the queries of `C` accepted under the seed `σ` by the
acceptance test `Acc σ Ag Bg`. -/
@[expose] def TrialSpec (trial : Seed p → List ℕ → List ℕ → List ℕ → TimeM ℕ (List ℕ))
    (Acc : Seed p → List ℕ → List ℕ → ℕ → Prop) [∀ σ Ag Bg, DecidablePred (Acc σ Ag Bg)] :
    Prop :=
  ∀ σ Ag Bg C, (trial σ Ag Bg C).ret = C.filter fun c => decide (Acc σ Ag Bg c)

/-- **The reduction** for a trial program and given random choices: the modulus `p` and the seeds
of the trials. -/
@[expose] def reduceM (trial : Seed p → List ℕ → List ℕ → List ℕ → TimeM ℕ (List ℕ))
    (seeds : List (Seed p)) (A B C : List ℕ) : TimeM ℕ (List ℕ) := do
  let (Ag, Abad) ← isolatedM p A
  let (Bg, Bbad) ← isolatedM p B
  let rs ← seeds.mapM fun σ => trial σ Ag Bg C
  let yes := badSums Abad Bbad A B ++ rs.flatten
  ✓[yes.length] filterTickM (· ∈ yes) C

variable {trial : Seed p → List ℕ → List ℕ → List ℕ → TimeM ℕ (List ℕ)}
  {Acc : Seed p → List ℕ → List ℕ → ℕ → Prop} [∀ σ Ag Bg, DecidablePred (Acc σ Ag Bg)]

/-- **What the reduction returns**: the queries of `C` that are bad sums or accepted by a trial on
the isolated elements. -/
theorem ret_reduceM (htrial : TrialSpec trial Acc) (seeds : List (Seed p)) (A B C : List ℕ) :
    (reduceM trial seeds A B C).ret = C.filter fun c => decide (BadHit p A B c ∨
      ∃ σ ∈ seeds, Acc σ (A.filter fun a => decide (Isolated p A a))
        (B.filter fun b => decide (Isolated p B b)) c) := by
  rw [reduceM]
  simp only [ret_bind]
  rw [ret_isolatedM, ret_isolatedM]
  dsimp only
  rw [ret_listMapM, List.map_congr_left fun σ _ => htrial σ _ _ C, ret_filterTickM]
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

/-- **Soundness of the reduction** (one-sided error): if every query a trial accepts is a sum of
elements of its inputs, every reported query is a sum `a + b` with `a ∈ A` and `b ∈ B`, for every
modulus and all seeds. -/
theorem exists_add_eq_of_mem_ret_reduceM (htrial : TrialSpec trial Acc)
    (hsound : ∀ σ Ag Bg c, Acc σ Ag Bg c → ∃ a ∈ Ag, ∃ b ∈ Bg, a + b = c)
    {seeds : List (Seed p)} {A B C : List ℕ} {c : ℕ}
    (hc : c ∈ (reduceM trial seeds A B C).ret) : ∃ a ∈ A, ∃ b ∈ B, a + b = c := by
  rw [ret_reduceM htrial] at hc
  obtain ⟨-, h⟩ := List.mem_filter.mp hc
  rcases of_decide_eq_true h with ⟨a, ha, b, hb, habc, -⟩ | ⟨σ, -, hacc⟩
  · exact ⟨a, ha, b, hb, habc⟩
  · obtain ⟨a, ha, b, hb, habc⟩ := hsound _ _ _ _ hacc
    exact ⟨a, List.mem_of_mem_filter ha, b, List.mem_of_mem_filter hb, habc⟩

/-- **Completeness for given random choices**: a sum `c = a + b ∈ C` is reported if it is a bad
sum or some trial accepts it, and otherwise `a` and `b` are isolated and every trial rejects. -/
theorem mem_ret_reduceM_or_isolated (htrial : TrialSpec trial Acc) (seeds : List (Seed p))
    {A B C : List ℕ} {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ B) (habc : a + b = c) (hc : c ∈ C) :
    c ∈ (reduceM trial seeds A B C).ret ∨ (Isolated p A a ∧ Isolated p B b ∧
      ∀ σ ∈ seeds, ¬ Acc σ (A.filter fun a => decide (Isolated p A a))
        (B.filter fun b => decide (Isolated p B b)) c) := by
  rw [ret_reduceM htrial]
  by_cases hbad : ¬ Isolated p A a ∨ ¬ Isolated p B b
  · exact Or.inl (List.mem_filter.mpr ⟨hc, decide_eq_true (Or.inl ⟨a, ha, b, hb, habc, hbad⟩)⟩)
  push Not at hbad
  by_cases hacc : ∃ σ ∈ seeds, Acc σ (A.filter fun a => decide (Isolated p A a))
      (B.filter fun b => decide (Isolated p B b)) c
  · exact Or.inl (List.mem_filter.mpr ⟨hc, decide_eq_true (Or.inr hacc)⟩)
  · push Not at hacc
    exact Or.inr ⟨hbad.1, hbad.2, hacc⟩

/-- **The cost of the reduction**, exactly: `3 (|A| + |B|)` ticks to split off `A_bad` and
`B_bad`, the ticks of the trials, one tick per listed bad sum (`|A_bad| |B| + |A| |B_bad|`) and per
value reported by a trial, and one per query. -/
theorem time_reduceM (htrial : TrialSpec trial Acc) (seeds : List (Seed p)) (A B C : List ℕ) :
    let Ag := A.filter fun a => decide (Isolated p A a)
    let Bg := B.filter fun b => decide (Isolated p B b)
    (reduceM trial seeds A B C).time = 3 * A.length + 3 * B.length +
      (seeds.map fun σ => (trial σ Ag Bg C).time).sum +
      ((A.filter fun a => decide (¬ Isolated p A a)).length * B.length +
        A.length * (B.filter fun b => decide (¬ Isolated p B b)).length) +
      (seeds.map fun σ => (C.filter fun c => decide (Acc σ Ag Bg c)).length).sum +
      C.length := by
  intro Ag Bg
  rw [reduceM]
  simp only [time_bind]
  rw [ret_isolatedM, ret_isolatedM, time_isolatedM, time_isolatedM]
  dsimp only
  rw [time_listMapM, ret_listMapM, List.map_congr_left fun σ _ => htrial σ _ _ C, time_tick,
    time_filterTickM, List.length_append, length_badSums, List.length_flatten, List.map_map]
  simp only [Function.comp_def]
  ring

/-! ### Error probability -/

/-- `μ` independent uniform seeds all fail a test `P` for exactly the `μ`-th power of the failing
seeds. -/
theorem card_forall_not_le [NeZero p] (P : Seed p → Prop) [DecidablePred P] (μ : ℕ) :
    #((Fintype.piFinset fun _ : Fin μ => seeds p).filter fun ss => ∀ i, ¬ P (ss i)) =
      #((seeds p).filter fun s => ¬ P s) ^ μ := by
  rw [← Fintype.card_piFinset_const]
  congr 1
  ext ss
  simp only [mem_filter, Fintype.mem_piFinset]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- **The miss probability for given success counts**: let `c = a + b ∈ C` with `a ∈ A`, `b ∈ B`
and `P ≤ p ^ 2`. If, whenever `a` and `b` are isolated, at least a `3 P / (4 (p - 1) p ^ 2)`
fraction of the `(p - 1) p ^ 2` seeds accept `c` (`3 P (p - 1) ≤ 4 #accepting`), then over `μ`
independent uniform seeds the reduction misses `c` with probability at most
`(1 - 3 P / (4 p ^ 2)) ^ μ`. -/
theorem reduceM_miss_le [Fact p.Prime] (htrial : TrialSpec trial Acc) {P μ : ℕ}
    (hP : P ≤ p ^ 2) {A B C : List ℕ} {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ B) (habc : a + b = c)
    (hc : c ∈ C)
    (hacc : Isolated p A a → Isolated p B b →
      3 * (P * (p - 1)) ≤ 4 * #((seeds p).filter fun s =>
        Acc s (A.filter fun a => decide (Isolated p A a))
          (B.filter fun b => decide (Isolated p B b)) c)) :
    (#((Fintype.piFinset fun _ : Fin μ => seeds p).filter fun ss =>
        c ∉ (reduceM trial (List.ofFn ss) A B C).ret) : ℝ) / (#(seeds p) : ℝ) ^ μ ≤
      (1 - 3 * P / (4 * (p : ℝ) ^ 2)) ^ μ := by
  set Ag := A.filter fun a => decide (Isolated p A a)
  set Bg := B.filter fun b => decide (Isolated p B b)
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hN : (#(seeds p) : ℝ) = ((p : ℝ) - 1) * (p : ℝ) ^ 2 := by
    rw [card_seeds]; push_cast [Nat.cast_sub hp1.le]; ring
  have hNpos : (0 : ℝ) < #(seeds p) := by
    rw [hN]; have : (1 : ℝ) < p := by exact_mod_cast hp1
    positivity
  have hbase : 0 ≤ 1 - 3 * (P : ℝ) / (4 * (p : ℝ) ^ 2) := by
    have : (P : ℝ) ≤ (p : ℝ) ^ 2 := by exact_mod_cast hP
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  rcases mem_ret_reduceM_or_isolated htrial ([] : List (Seed p)) ha hb habc hc with
    hrep | ⟨hia, hib, -⟩
  · -- `c` is a bad sum: it is reported for all seeds
    have hempty : ((Fintype.piFinset fun _ : Fin μ => seeds p).filter fun ss =>
        c ∉ (reduceM trial (List.ofFn ss) A B C).ret) = ∅ := by
      refine filter_eq_empty_iff.mpr fun ss _ hmiss => hmiss ?_
      rw [ret_reduceM htrial] at hrep
      rw [ret_reduceM htrial]
      obtain ⟨-, h⟩ := List.mem_filter.mp hrep
      rcases of_decide_eq_true h with hbad | ⟨σ, hσ, -⟩
      · exact List.mem_filter.mpr ⟨hc, decide_eq_true (Or.inl hbad)⟩
      · simp at hσ
    rw [hempty, card_empty, Nat.cast_zero, zero_div]
    exact pow_nonneg hbase μ
  -- both are isolated: a miss means every trial rejects
  have hsub : ((Fintype.piFinset fun _ : Fin μ => seeds p).filter fun ss =>
      c ∉ (reduceM trial (List.ofFn ss) A B C).ret) ⊆
      (Fintype.piFinset fun _ : Fin μ => seeds p).filter fun ss =>
        ∀ i, ¬ Acc (ss i) Ag Bg c := by
    intro ss hss
    obtain ⟨hpi, hmiss⟩ := mem_filter.mp hss
    refine mem_filter.mpr ⟨hpi, fun i hacc => hmiss ?_⟩
    rw [ret_reduceM htrial]
    exact List.mem_filter.mpr ⟨hc, decide_eq_true (Or.inr ⟨ss i, List.mem_ofFn.mpr ⟨i, rfl⟩,
      hacc⟩)⟩
  have hNZ : NeZero p := ⟨by omega⟩
  have hcount := card_forall_not_le (p := p) (fun s => Acc s Ag Bg c) μ
  have hsplit := card_filter_add_card_filter_not (s := seeds p) (fun s => Acc s Ag Bg c)
  have hacc' := hacc hia hib
  set R := #((seeds p).filter fun s => ¬ Acc s Ag Bg c)
  set Q := #((seeds p).filter fun s => Acc s Ag Bg c)
  have hratio : (R : ℝ) / #(seeds p) ≤ 1 - 3 * P / (4 * (p : ℝ) ^ 2) := by
    have hR : (R : ℝ) = #(seeds p) - Q := by
      rw [← hsplit]; push_cast; ring
    have hQ : (3 * (P * ((p : ℝ) - 1)) : ℝ) ≤ 4 * Q := by
      have hc' : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by push_cast [Nat.cast_sub hp1.le]; ring
      rw [← hc']; exact_mod_cast hacc'
    rw [hR, div_le_iff₀ hNpos, hN]
    have : (3 * P / (4 * (p : ℝ) ^ 2)) * (((p : ℝ) - 1) * (p : ℝ) ^ 2) =
        3 * (P * ((p : ℝ) - 1)) / 4 := by
      have : (p : ℝ) ≠ 0 := by have := hp1; positivity
      field_simp
    nlinarith [this]
  calc (#((Fintype.piFinset fun _ : Fin μ => seeds p).filter fun ss =>
        c ∉ (reduceM trial (List.ofFn ss) A B C).ret) : ℝ) / (#(seeds p) : ℝ) ^ μ
      ≤ (R : ℝ) ^ μ / (#(seeds p) : ℝ) ^ μ := by
        gcongr
        exact_mod_cast (card_le_card hsub).trans_eq hcount
    _ = ((R : ℝ) / #(seeds p)) ^ μ := (div_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hratio μ

/-- The probability that the reduction with the trials `trial q` misses `c` over `μ` uniform
seeds, for the modulus `q` (`0` if `q` is not prime). -/
@[expose] noncomputable def missProbOf
    (trial : (q : ℕ) → Seed q → List ℕ → List ℕ → List ℕ → TimeM ℕ (List ℕ))
    (μ : ℕ) (A B C : List ℕ) (c q : ℕ) : ℝ :=
  if h : q.Prime then
    haveI : Fact q.Prime := ⟨h⟩
    (#((Fintype.piFinset fun _ : Fin μ => seeds q).filter fun ss =>
      c ∉ (reduceM (trial q) (List.ofFn ss) A B C).ret) : ℝ) / (#(seeds q) : ℝ) ^ μ
  else 0

theorem missProbOf_le_one
    (trial : (q : ℕ) → Seed q → List ℕ → List ℕ → List ℕ → TimeM ℕ (List ℕ))
    (μ : ℕ) (A B C : List ℕ) (c q : ℕ) : missProbOf trial μ A B C c q ≤ 1 := by
  unfold missProbOf
  split_ifs with h
  · have : Fact q.Prime := ⟨h⟩
    have hpos : (0 : ℝ) < (#(seeds q) : ℝ) ^ μ := by
      have : 0 < #(seeds q) := by
        rw [card_seeds]; exact Nat.mul_pos (by have := h.one_lt; omega) (pow_pos h.pos 2)
      positivity
    rw [div_le_one hpos]
    have := card_filter_le (Fintype.piFinset fun _ : Fin μ => seeds q) fun ss =>
      c ∉ (reduceM (trial q) (List.ofFn ss) A B C).ret
    rw [Fintype.card_piFinset_const] at this
    exact_mod_cast this
  · exact zero_le_one

/-- **Averaging over a window of moduli**: if the miss probability is at most `ρ ^ μ ≥ 0` for every
modulus of the window `W` outside a set `bad`, the average miss probability over `W` is at most
`#bad / #W + ρ ^ μ`. -/
theorem average_le_of_good
    {trial : (q : ℕ) → Seed q → List ℕ → List ℕ → List ℕ → TimeM ℕ (List ℕ)}
    {μ : ℕ} {A B C : List ℕ} {c : ℕ} {W bad : Finset ℕ} (hW : W.Nonempty) {ρ : ℝ}
    (hρ : 0 ≤ ρ ^ μ) (hgood : ∀ q ∈ W, q ∉ bad → missProbOf trial μ A B C c q ≤ ρ ^ μ) :
    (∑ q ∈ W, missProbOf trial μ A B C c q) / #W ≤ (#(W.filter (· ∈ bad)) : ℝ) / #W + ρ ^ μ := by
  have hWpos : (0 : ℝ) < #W := by exact_mod_cast hW.card_pos
  have hsum : ∑ q ∈ W, missProbOf trial μ A B C c q ≤ #(W.filter (· ∈ bad)) + #W * ρ ^ μ := by
    rw [← sum_filter_add_sum_filter_not W fun q => q ∈ bad]
    have hb1 : ∑ q ∈ W.filter (· ∈ bad), missProbOf trial μ A B C c q ≤
        #(W.filter (· ∈ bad)) := by
      refine (sum_le_sum fun q _ => missProbOf_le_one trial μ A B C c q).trans ?_
      rw [sum_const, nsmul_eq_mul, mul_one]
    have hb2 : ∑ q ∈ W.filter (· ∉ bad), missProbOf trial μ A B C c q ≤ #W * ρ ^ μ := by
      refine (sum_le_sum fun q hq => hgood q (mem_filter.mp hq).1 (mem_filter.mp hq).2).trans ?_
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_le _ _) hρ
    linarith
  rw [div_le_iff₀ hWpos, add_mul, div_mul_cancel₀ _ hWpos.ne']
  linarith

theorem card_falsePairs_mono {q c : ℕ} {Ag Bg A B : List ℕ} (hA : ∀ x ∈ Ag, x ∈ A)
    (hB : ∀ x ∈ Bg, x ∈ B) : #(falsePairs q c Ag Bg) ≤ #(falsePairs q c A B) := by
  refine card_le_card fun ab hab => ?_
  obtain ⟨hmem, h⟩ := mem_filter.mp hab
  obtain ⟨ha, hb⟩ := mem_product.mp hmem
  exact mem_filter.mpr ⟨mem_product.mpr ⟨List.mem_toFinset.mpr (hA _ (List.mem_toFinset.mp ha)),
    List.mem_toFinset.mpr (hB _ (List.mem_toFinset.mp hb))⟩, h⟩

/-- A prime of the window outside `badPrimesOf e K c A B` is good for the isolated elements:
`4 #L K ≤ q - 1`, with `L` the false pairs of the isolated sublists. -/
theorem good_of_not_mem_badPrimesOf {e K c q : ℕ} {A B : List ℕ} (hq : q ∈ primeWindow e)
    (hnb : q ∉ badPrimesOf e K c A B) :
    4 * (#(falsePairs q c (A.filter fun a => decide (Isolated q A a))
      (B.filter fun b => decide (Isolated q B b))) * K) ≤ q - 1 := by
  have h1 : ¬ q - 1 < 4 * (#(falsePairs q c A B) * K) := fun h =>
    hnb (mem_filter.mpr ⟨hq, h⟩)
  have h2 := card_falsePairs_mono (q := q) (c := c)
    (fun x hx => List.mem_of_mem_filter hx) (fun x hx => List.mem_of_mem_filter hx)
    (A := A) (B := B) (Ag := A.filter fun a => decide (Isolated q A a))
    (Bg := B.filter fun b => decide (Isolated q B b))
  have h3 := Nat.mul_le_mul_right K h2
  omega

/-- The miss probability at a prime modulus is the count of missing seed tuples, so a bound on
that count bounds it. -/
theorem missProbOf_le_of_prime
    {trial : (q : ℕ) → Seed q → List ℕ → List ℕ → List ℕ → TimeM ℕ (List ℕ)}
    {μ : ℕ} {A B C : List ℕ} {c q : ℕ} (hq : q.Prime) {x : ℝ}
    (h : ∀ _ : Fact q.Prime, (#((Fintype.piFinset fun _ : Fin μ => seeds q).filter fun ss =>
      c ∉ (reduceM (trial q) (List.ofFn ss) A B C).ret) : ℝ) / (#(seeds q) : ℝ) ^ μ ≤ x) :
    missProbOf trial μ A B C c q ≤ x := by
  unfold missProbOf
  rw [dite_eq_left_of_eq_true (eq_true hq)]
  exact h ⟨hq⟩

/-- **Averaging over a binary window of primes**: if every prime `q` of `[2 ^ e, 2 ^ (e + 1))`
outside `bad ⊆ window` has miss probability at most `(1 - 3 P / (4 q ^ 2)) ^ μ`, with
`P ≤ 2 ^ e 2 ^ e`, the average miss probability over the window is at most
`#bad / #window + (1 - 3 P / 4 ^ (e + 2)) ^ μ`. -/
theorem average_miss_le_of_window
    {trial : (q : ℕ) → Seed q → List ℕ → List ℕ → List ℕ → TimeM ℕ (List ℕ)}
    {μ e P : ℕ} {A B C : List ℕ} {c : ℕ} (hW : (primeWindow e).Nonempty) {bad : Finset ℕ}
    (hbad : bad ⊆ primeWindow e) (hP : P ≤ 2 ^ e * 2 ^ e)
    (hgood : ∀ q ∈ primeWindow e, q ∉ bad →
      missProbOf trial μ A B C c q ≤ (1 - 3 * P / (4 * (q : ℝ) ^ 2)) ^ μ) :
    (∑ q ∈ primeWindow e, missProbOf trial μ A B C c q) / #(primeWindow e) ≤
      (#bad : ℝ) / #(primeWindow e) + (1 - 3 * P / (4 : ℝ) ^ (e + 2)) ^ μ := by
  have hP' : (P : ℝ) ≤ (2 : ℝ) ^ e * 2 ^ e := by exact_mod_cast hP
  have h4 : (4 : ℝ) ^ (e + 2) = 16 * ((2 : ℝ) ^ e * 2 ^ e) := by
    rw [pow_add, ← mul_pow]; norm_num; ring
  have hρ : 0 ≤ 1 - 3 * (P : ℝ) / (4 : ℝ) ^ (e + 2) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ e * 2 ^ e := by positivity
    rw [sub_nonneg, div_le_one (by positivity), h4]
    linarith
  have hfilter : (primeWindow e).filter (· ∈ bad) = bad := by
    ext q
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hbad h, h⟩⟩
  rw [← hfilter]
  refine average_le_of_good hW (pow_nonneg hρ μ) fun q hq hnb => (hgood q hq hnb).trans ?_
  obtain ⟨hprime, hlo, hhi⟩ := mem_primeWindow.mp hq
  have hqpos : (0 : ℝ) < 4 * (q : ℝ) ^ 2 := by
    have : (0 : ℝ) < q := by exact_mod_cast hprime.pos
    positivity
  refine pow_le_pow_left₀ ?_ ?_ μ
  · have hPq : (P : ℝ) ≤ (q : ℝ) ^ 2 := by
      have : (2 : ℝ) ^ e ≤ q := by exact_mod_cast hlo
      nlinarith [pow_pos (two_pos (α := ℝ)) e]
    rw [sub_nonneg, div_le_one hqpos]
    linarith
  · have hq2 : (4 : ℝ) * (q : ℝ) ^ 2 ≤ (4 : ℝ) ^ (e + 2) := by
      have : q * q ≤ 2 ^ (e + 1) * 2 ^ (e + 1) := Nat.mul_le_mul hhi.le hhi.le
      have h' : ((q : ℝ)) ^ 2 ≤ (2 : ℝ) ^ (e + 1) * 2 ^ (e + 1) := by
        rw [sq]; exact_mod_cast this
      have h4' : (4 : ℝ) ^ (e + 2) = 4 * ((2 : ℝ) ^ (e + 1) * 2 ^ (e + 1)) := by
        rw [← mul_pow, show (2 : ℝ) * 2 = 4 by norm_num, pow_succ]; ring
      rw [h4']; linarith
    have : 3 * (P : ℝ) / (4 : ℝ) ^ (e + 2) ≤ 3 * (P : ℝ) / (4 * (q : ℝ) ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) hqpos hq2
    linarith

end Cslib.Algorithms.Lean.SubsetConvThreeSum
