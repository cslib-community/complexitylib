/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.TrialReduction
import CslibFrontier.Foundations.Data.Nat.LargePrimeDivisors
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.FieldSimp

/-!
# Expected costs of hashing reductions

Shared finite counting and averaging for the subset and base-`r` reductions of
[ChanItakuraMaYu2026], Theorems 2.3 and 3.4. The average is the actual tick cost of `reduceM`
over uniform primes in a binary window and uniform tuples of seeds. Sampling is uncharged.
The generic bounds take a per-trial estimate; each concrete reduction proves that estimate
from its own program before applying these lemmas.

## Main definitions

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.avgTimeOf`: finite expected tick cost.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.sum_length_filter_target`: target-query count.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.exists_ne_of_not_isolated`: a collision witness.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.mul_sum_length_bad_le`: bad-element bound.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.mul_sum_time_reduceM_le`: cost over seed tuples.
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.avgTimeOf_le`: averaging over a prime window.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset

private theorem length_filter_eq_sum {l : List ℕ} (P : ℕ → Prop) [DecidablePred P] :
    (l.filter fun x => decide (P x)).length = (l.map fun x => if P x then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : P x <;> simp [h, ih, Nat.add_comm]

private theorem list_sum_comm {α : Type*} (l : List ℕ) (s : Finset α) (f : ℕ → α → ℕ) :
    ∑ a ∈ s, (l.map fun x => f x a).sum = (l.map fun x => ∑ a ∈ s, f x a).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [sum_add_distrib, ih]

variable {p : ℕ} [Fact p.Prime]

/-- **The expected number of queries with target in a set**: summed over all seeds, the queries
whose target hash lies in a set `T` of numbers below `p` number `|C| #T (p - 1) p`. -/
theorem sum_length_filter_target {T : Finset ℕ} {P : ℕ → Prop} [DecidablePred P]
    (hT : ∀ z ∈ T, z < p) (hmem : ∀ z, P z ↔ z ∈ T) (C : List ℕ) :
    ∑ s ∈ seeds p, (C.filter fun c => decide (P (s.target c))).length =
      C.length * (#T * ((p - 1) * p)) := by
  simp only [hmem, length_filter_eq_sum]
  rw [list_sum_comm]
  have hc : ∀ c, ∑ s ∈ seeds p, (if s.target c ∈ T then 1 else 0) = #T * ((p - 1) * p) :=
    fun c => by
    rw [← card_filter, card_eq_sum_card_fiberwise (f := fun s : Seed p => s.target c)
      (s := (seeds p).filter fun s => s.target c ∈ T) (t := T) fun s hs => (mem_filter.mp hs).2]
    rw [← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun z hz => ?_
    rw [filter_filter, ← card_seeds_target c (hT z hz)]
    congr 1
    refine filter_congr fun s _ => ?_
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hz, h⟩
  simp only [hc, List.map_const', List.sum_replicate, smul_eq_mul]

/-- An element that is not isolated has a partner in its residue class. -/
theorem exists_ne_of_not_isolated {q : ℕ} {A : List ℕ} (hA : A.Nodup) {a : ℕ} (ha : a ∈ A)
    (hbad : ¬ Isolated q A a) : ∃ a' ∈ A, a' ≠ a ∧ (a' : ZMod q) = a := by
  by_contra h
  push Not at h
  apply hbad
  unfold Isolated
  rw [List.countP_congr (q := fun x => decide (x = a)) fun x hx => by
    constructor
    · intro hx'
      have := of_decide_eq_true hx'
      by_contra hne
      exact h x hx (by simpa using hne) this
    · intro hx'
      rw [of_decide_eq_true hx']
      simp]
  exact (List.countP_congr fun x _ => by simp [beq_iff_eq]).trans (List.count_eq_one_of_mem hA ha)

/-- A prime divides the difference of two numbers exactly when they are congruent. -/
private theorem natCast_eq_iff_dvd_natAbs {q a a' : ℕ} :
    (a' : ZMod q) = a ↔ q ∣ ((a : ℤ) - a').natAbs := by
  rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs, dvd_abs,
    ← ZMod.intCast_eq_intCast_iff_dvd_sub]
  push_cast; rfl

/-- **Few bad elements on average over the prime window**: for duplicate-free `A` with elements
below `M`, `d ∑_{q ∈ window} |A_bad(q)| ≤ |A| ^ 2 log₂ M`. -/
theorem mul_sum_length_bad_le {A : List ℕ} (hA : A.Nodup) {M d : ℕ} (hM : ∀ a ∈ A, a < M) :
    d * ∑ q ∈ primeWindow d, (A.filter fun a => decide (¬ Isolated q A a)).length ≤
      A.length * A.length * Nat.log 2 M := by
  have hdist : ∀ a ∈ A, ∀ a' ∈ A, a' ≠ a → ((a : ℤ) - a').natAbs ≠ 0 ∧
      ((a : ℤ) - a').natAbs ≤ M := fun a ha a' ha' hne => by
    have h1 := hM a ha; have h2 := hM a' ha'
    constructor <;> omega
  -- each bad element is charged to its partners
  have hq : ∀ q, (A.filter fun a => decide (¬ Isolated q A a)).length ≤
      (A.map fun (a : ℕ) => (A.map fun (a' : ℕ) =>
        if a' ≠ a ∧ q ∣ ((a : ℤ) - a').natAbs then 1 else 0).sum).sum := fun q => by
    rw [length_filter_eq_sum]
    refine List.sum_le_sum fun a ha => ?_
    by_cases hbad : Isolated q A a
    · simp [hbad]
    · obtain ⟨a', ha', hne, hcong⟩ := exists_ne_of_not_isolated hA ha hbad
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun (a' : ℕ) =>
        if a' ≠ a ∧ q ∣ ((a : ℤ) - a').natAbs then 1 else 0) ha')
      simp only [hne, ne_eq, not_false_eq_true, natCast_eq_iff_dvd_natAbs.mp hcong, and_self,
        ite_true] at this
      simpa [hbad] using this
  calc d * ∑ q ∈ primeWindow d, (A.filter fun a => decide (¬ Isolated q A a)).length
      ≤ d * ∑ q ∈ primeWindow d, (A.map fun (a : ℕ) => (A.map fun (a' : ℕ) =>
          if a' ≠ a ∧ q ∣ ((a : ℤ) - a').natAbs then 1 else 0).sum).sum :=
        Nat.mul_le_mul_left _ (sum_le_sum fun q _ => hq q)
    _ = (A.map fun (a : ℕ) => (A.map fun (a' : ℕ) => d * ∑ q ∈ primeWindow d,
          (if a' ≠ a ∧ q ∣ ((a : ℤ) - a').natAbs then 1 else 0)).sum).sum := by
        rw [list_sum_comm, ← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left fun a _ => ?_
        rw [list_sum_comm, ← List.sum_map_mul_left]
    _ ≤ (A.map fun _ => (A.map fun _ => Nat.log 2 M).sum).sum := by
        refine List.sum_le_sum fun a ha => List.sum_le_sum fun a' ha' => ?_
        by_cases hne : a' ≠ a
        · obtain ⟨hz, hle⟩ := hdist a ha a' ha' hne
          simp only [ne_eq, hne, not_false_eq_true, true_and]
          rw [← card_filter, mul_comm]
          exact (Nat.card_filter_dvd_mul_le_log (fun q hq => ⟨(mem_primeWindow.mp hq).1,
            (mem_primeWindow.mp hq).2.1⟩) hz).trans (Nat.log_mono_right hle)
        · simp [hne]
    _ = A.length * A.length * Nat.log 2 M := by
        simp only [List.map_const', List.sum_replicate, smul_eq_mul]
        ring

/-- **The total cost of a reduction over all seed tuples for one prime**: if the cost of one
trial plus the number of values it reports is at most `G₀ + G₁ c σ` and `∑_σ c σ = X (p - 1) p`,
then `p ∑ time ≤ #seeds ^ μ (p (3 |A| + 3 |B| + |C| + |A_bad| |B| + |A| |B_bad| + μ G₀) +
μ G₁ X)`. -/
theorem mul_sum_time_reduceM_le
    {trial : Seed p → List ℕ → List ℕ → List ℕ → TimeM ℕ (List ℕ)}
    {Acc : Seed p → List ℕ → List ℕ → ℕ → Prop} [∀ σ Ag Bg, DecidablePred (Acc σ Ag Bg)]
    (htrial : TrialSpec trial Acc) {μ : ℕ} (A B C : List ℕ) {G₀ G₁ X : ℕ} {c : Seed p → ℕ}
    (hper : ∀ σ, (trial σ (A.filter fun a => decide (Isolated p A a))
        (B.filter fun b => decide (Isolated p B b)) C).time +
      (C.filter fun x => decide (Acc σ (A.filter fun a => decide (Isolated p A a))
        (B.filter fun b => decide (Isolated p B b)) x)).length ≤ G₀ + G₁ * c σ)
    (hc : ∑ σ ∈ seeds p, c σ = X * ((p - 1) * p)) :
    p * ∑ ss ∈ Fintype.piFinset (fun _ : Fin μ => seeds p),
        (reduceM trial (List.ofFn ss) A B C).time ≤
      #(seeds p) ^ μ * (p * (3 * A.length + 3 * B.length + C.length +
        (A.filter fun a => decide (¬ Isolated p A a)).length * B.length +
        A.length * (B.filter fun b => decide (¬ Isolated p B b)).length + μ * G₀) +
        μ * (G₁ * X)) := by
  set K₀ := 3 * A.length + 3 * B.length + C.length +
    (A.filter fun a => decide (¬ Isolated p A a)).length * B.length +
    A.length * (B.filter fun b => decide (¬ Isolated p B b)).length
  -- the cost of one tuple
  have hpt : ∀ ss : Fin μ → Seed p, (reduceM trial (List.ofFn ss) A B C).time ≤
      K₀ + ∑ i, (G₀ + G₁ * c (ss i)) := fun ss => by
    have ht := time_reduceM htrial (List.ofFn ss) A B C
    dsimp only at ht
    rw [ht]
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def]
    have := sum_le_sum fun i (_ : i ∈ univ) => hper (ss i)
    rw [sum_add_distrib] at this
    simp only [K₀] at this ⊢
    omega
  have hsumc : ∑ ss ∈ Fintype.piFinset (fun _ : Fin μ => seeds p), ∑ i, G₁ * c (ss i) =
      μ * (G₁ * (#(seeds p) ^ (μ - 1) * ∑ σ ∈ seeds p, c σ)) := by
    rw [sum_comm]
    simp only [Fintype.sum_piFinset_apply, Fintype.card_fin, smul_eq_mul, ← mul_sum, sum_const,
      card_univ]
    ring
  have hcard : #(seeds p) = (p - 1) * p ^ 2 := card_seeds
  calc p * ∑ ss ∈ Fintype.piFinset (fun _ : Fin μ => seeds p),
        (reduceM trial (List.ofFn ss) A B C).time
      ≤ p * ∑ ss ∈ Fintype.piFinset (fun _ : Fin μ => seeds p),
          (K₀ + ∑ i, G₀ + ∑ i, G₁ * c (ss i)) := by
        refine Nat.mul_le_mul_left _ (sum_le_sum fun ss _ => (hpt ss).trans_eq ?_)
        rw [sum_add_distrib]; ring
    _ = p * (#(seeds p) ^ μ * (K₀ + μ * G₀)) +
          p * (μ * (G₁ * (#(seeds p) ^ (μ - 1) * ∑ σ ∈ seeds p, c σ))) := by
        rw [sum_add_distrib, hsumc, sum_const, Fintype.card_piFinset_const, smul_eq_mul, sum_const,
          card_univ, Fintype.card_fin, smul_eq_mul]
        ring
    _ ≤ _ := by
        rw [hc]
        rcases Nat.eq_zero_or_pos μ with rfl | hμ
        · simp
        · have hpow : #(seeds p) ^ (μ - 1) * #(seeds p) = #(seeds p) ^ μ := by
            rw [← pow_succ]; congr 1; omega
          have : p * (μ * (G₁ * (#(seeds p) ^ (μ - 1) * (X * ((p - 1) * p))))) =
              #(seeds p) ^ (μ - 1) * #(seeds p) * (μ * (G₁ * X)) := by
            rw [hcard]; ring
          rw [this, hpow]
          nlinarith [Nat.zero_le (#(seeds p) ^ μ)]

/-- Dividing `q S ≤ X (q R + Y)` by `q ≥ 2 ^ D`. -/
private theorem le_mul_of_mul_le {q S X R Y P : ℝ} (hP : 0 < P) (hq : P ≤ q) (hY : 0 ≤ Y)
    (hX : 0 ≤ X) (h : q * S ≤ X * (q * R + Y)) : S ≤ (R + Y / P) * X := by
  have hq0 : 0 < q := hP.trans_le hq
  have hYq : Y / q ≤ Y / P := div_le_div_of_nonneg_left hY hP hq
  calc S = q * S / q := by field_simp
    _ ≤ X * (q * R + Y) / q := by gcongr
    _ = (R + Y / q) * X := by field_simp
    _ ≤ (R + Y / P) * X := by gcongr

omit [Fact p.Prime] in
/-- The expected cost of a reduction over a uniform prime `q` of `[2 ^ e, 2 ^ (e + 1))` and `μ`
uniform seeds (a non-prime contributes `0`; the window has only primes). -/
@[expose] noncomputable def avgTimeOf
    (trial : (q : ℕ) → Seed q → List ℕ → List ℕ → List ℕ → TimeM ℕ (List ℕ))
    (μ e : ℕ) (A B C : List ℕ) : ℝ :=
  (∑ q ∈ primeWindow e, if h : q.Prime then
      haveI : Fact q.Prime := ⟨h⟩
      (∑ ss ∈ Fintype.piFinset (fun _ : Fin μ => seeds q),
        ((reduceM (trial q) (List.ofFn ss) A B C).time : ℝ)) / (#(seeds q) : ℝ) ^ μ
    else 0) / #(primeWindow e)

omit [Fact p.Prime] in
/-- **Averaging the cost over the window**: if for every prime `q` of the window
`q ∑ time ≤ #seeds ^ μ (q (K + bad q) + Y)`, the expected cost is at most
`K + Y / 2 ^ e + (∑_q bad q) / #window`. -/
theorem avgTimeOf_le
    {trial : (q : ℕ) → Seed q → List ℕ → List ℕ → List ℕ → TimeM ℕ (List ℕ)}
    {μ e : ℕ} {A B C : List ℕ} (hW : (primeWindow e).Nonempty) {K Y : ℕ} {bad : ℕ → ℕ}
    (hq : ∀ q ∈ primeWindow e, ∀ _ : Fact q.Prime,
      q * ∑ ss ∈ Fintype.piFinset (fun _ : Fin μ => seeds q),
          (reduceM (trial q) (List.ofFn ss) A B C).time ≤
        #(seeds q) ^ μ * (q * (K + bad q) + Y)) :
    avgTimeOf trial μ e A B C ≤
      K + Y / 2 ^ e + ((∑ q ∈ primeWindow e, bad q : ℕ) : ℝ) / #(primeWindow e) := by
  have hW0 : (0 : ℝ) < #(primeWindow e) := by exact_mod_cast hW.card_pos
  unfold avgTimeOf
  rw [div_le_iff₀ hW0, add_mul, div_mul_cancel₀ _ hW0.ne']
  calc _ ≤ ∑ q ∈ primeWindow e, (((K : ℝ) + Y / 2 ^ e) + (bad q : ℝ)) := by
        refine sum_le_sum fun q hqW => ?_
        obtain ⟨hp, hq2, -⟩ := mem_primeWindow.1 hqW
        simp only [hp, ↓reduceDIte]
        have : Fact q.Prime := ⟨hp⟩
        have h := hq q hqW this
        have hseeds : (0 : ℝ) < #(seeds q) := by
          have := hp.two_le
          rw [card_seeds]
          exact_mod_cast Nat.mul_pos (by omega) (by positivity)
        rw [← Nat.cast_sum, div_le_iff₀ (by positivity)]
        have h' : (q : ℝ) * ((∑ ss ∈ Fintype.piFinset (fun _ : Fin μ => seeds q),
            (reduceM (trial q) (List.ofFn ss) A B C).time : ℕ) : ℝ) ≤
            (#(seeds q) : ℝ) ^ μ * (q * ((K : ℝ) + bad q) + Y) := by exact_mod_cast h
        have := le_mul_of_mul_le (P := (2 : ℝ) ^ e) (q := q) (by positivity)
          (by exact_mod_cast hq2) (by positivity) (by positivity) h'
        calc _ ≤ _ := this
          _ = _ := by ring
    _ = _ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul, Nat.cast_sum]; ring

end Cslib.Algorithms.Lean.SubsetConvThreeSum
