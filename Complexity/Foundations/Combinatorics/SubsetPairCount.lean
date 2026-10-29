/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Truncated subset-pair counts

Counts the pairs `(E, U)` of subsets of an `n`-element set with `#E ≤ q` and `U ⊆ E`
([OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], eq. (3.14), p. 25):
`C_q = ∑_{s = 0}^{min(q, n)} 2 ^ s * n.choose s`.

## Main definitions

* `Cslib.subsetPairCount`: `C_q = ∑_{s = 0}^{min(q, n)} 2 ^ s * n.choose s`.

## Main results

* `Cslib.subsetPairCount_zero_right`, `Cslib.subsetPairCount_zero_left`,
  `Cslib.subsetPairCount_mono_right`, `Cslib.subsetPairCount_pos`,
  `Cslib.subsetPairCount_eq_three_pow`, `Cslib.subsetPairCount_le_three_pow`: boundary values,
  monotonicity, positivity, and `3 ^ n` bounds.
* `Cslib.sum_powerset_filter_card_le_two_pow`, `Cslib.subsetPairCount_eq_sum_powerset_fin`,
  `Cslib.card_subsetPairs_eq_subsetPairCount`, `Cslib.card_subsetPairs_eq_subsetPairCount_of_card`:
  fiberwise powerset sum and finite subset-pair cardinality identities.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §3.5, eq. (3.14), p. 25.
-/

public section

namespace Cslib

open Finset
open scoped BigOperators

/-- Number of subset pairs `(E, U)` of an `n`-element set with `#E ≤ q` and `U ⊆ E`
([OpenAI2026ETH], eq. (3.14), p. 25): `C_q = ∑_{s = 0}^{min(q, n)} 2^s C(n, s)`. -/
@[expose] def subsetPairCount (n q : ℕ) : ℕ :=
  ∑ s ∈ range (min q n + 1), 2 ^ s * n.choose s

/-- At `q = 0`, only `(∅, ∅)` is retained, so `C_0 = 1`. -/
@[simp] theorem subsetPairCount_zero_right (n : ℕ) : subsetPairCount n 0 = 1 := by
  simp [subsetPairCount]

/-- On an empty ground set (`n = 0`), `C_q = 1` for every `q`. -/
@[simp] theorem subsetPairCount_zero_left (q : ℕ) : subsetPairCount 0 q = 1 := by
  simp [subsetPairCount]

/-- `subsetPairCount` is monotone in the truncation order `q`. -/
theorem subsetPairCount_mono_right (n : ℕ) {q₁ q₂ : ℕ} (hq : q₁ ≤ q₂) :
    subsetPairCount n q₁ ≤ subsetPairCount n q₂ :=
  sum_le_sum_of_subset (range_mono (by omega))

/-- Every `subsetPairCount` is strictly positive. -/
theorem subsetPairCount_pos (n q : ℕ) : 0 < subsetPairCount n q :=
  (subsetPairCount_zero_right n ▸ Nat.zero_lt_one).trans_le
    (subsetPairCount_mono_right n (Nat.zero_le q))

/-- When `n ≤ q`, all subset sizes occur and `C_q = 3 ^ n` ([OpenAI2026ETH], p. 25). -/
theorem subsetPairCount_eq_three_pow {n q : ℕ} (hq : n ≤ q) : subsetPairCount n q = 3 ^ n := by
  rw [subsetPairCount, Nat.min_eq_right hq]
  simpa only [one_pow, mul_one, Nat.cast_id, show 2 + 1 = 3 from rfl] using
    (add_pow (2 : ℕ) 1 n).symm

/-- `subsetPairCount n q ≤ 3 ^ n` for all `n, q : ℕ`. -/
theorem subsetPairCount_le_three_pow (n q : ℕ) : subsetPairCount n q ≤ 3 ^ n :=
  (subsetPairCount_mono_right n (le_max_left q n)).trans_eq
    (subsetPairCount_eq_three_pow (le_max_right q n))

/-- Summing `2 ^ #E` over `E ⊆ univ` with `#E ≤ q` equals `subsetPairCount (Fintype.card ι) q`. -/
theorem sum_powerset_filter_card_le_two_pow {ι : Type*} [Fintype ι] (q : ℕ) :
    (∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q), 2 ^ #E) =
      subsetPairCount (Fintype.card ι) q := by
  classical
  set S := (univ : Finset ι).powerset.filter (fun E => #E ≤ q)
  have hmaps : ∀ E ∈ S, #E ∈ range (min q (Fintype.card ι) + 1) := fun E hE =>
    mem_range.mpr (Nat.lt_succ_of_le (le_min (mem_filter.mp hE).2 (card_le_univ E)))
  rw [← sum_fiberwise_of_maps_to hmaps, subsetPairCount]
  refine sum_congr rfl fun s hs => ?_
  have hsq : s ≤ q := (Nat.le_of_lt_succ (mem_range.mp hs)).trans (min_le_left q _)
  have hfiber : S.filter (fun E => #E = s) = (univ : Finset ι).powersetCard s := by
    ext E; simp only [S, mem_filter, mem_powerset, subset_univ, true_and, mem_powersetCard]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hsq, h⟩⟩
  have hcongr : ∑ E ∈ S.filter (fun E => #E = s), 2 ^ #E =
      ∑ _E ∈ S.filter (fun E => #E = s), 2 ^ s :=
    sum_congr rfl fun E hE => by rw [(mem_filter.mp hE).2]
  rw [hcongr, hfiber, sum_const, card_powersetCard, card_univ, nsmul_eq_mul, Nat.cast_id, mul_comm]

/-- `subsetPairCount n q` equals `∑_{E ⊆ Fin n, #E ≤ q} 2 ^ #E`. -/
theorem subsetPairCount_eq_sum_powerset_fin (n q : ℕ) :
    subsetPairCount n q = ∑ E ∈ (univ : Finset (Fin n)).powerset.filter (fun E => #E ≤ q), 2 ^ #E :=
  by simpa only [Fintype.card_fin] using (sum_powerset_filter_card_le_two_pow (ι := Fin n) q).symm

/-- `subsetPairCount (Fintype.card ι) q` counts `{p : Finset ι × Finset ι | #p.1 ≤ q ∧ p.2 ⊆ p.1}`
([OpenAI2026ETH], eq. (3.14), p. 25). -/
theorem card_subsetPairs_eq_subsetPairCount {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ) :
    #{p : Finset ι × Finset ι | #p.1 ≤ q ∧ p.2 ⊆ p.1} = subsetPairCount (Fintype.card ι) q := by
  set base := (univ : Finset ι).powerset.filter (fun E => #E ≤ q)
  have hbij : #{p : Finset ι × Finset ι | #p.1 ≤ q ∧ p.2 ⊆ p.1} =
      #(base.sigma fun E => E.powerset) := by
    refine (Finset.card_nbij (fun x : Σ _ : Finset ι, Finset ι => (x.1, x.2)) ?_ ?_ ?_).symm
    · rintro ⟨E, U⟩ hx; rw [mem_coe, mem_sigma] at hx
      exact mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx.1).2, mem_powerset.mp hx.2⟩)
    · rintro ⟨_, _⟩ _ ⟨_, _⟩ _ h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl
    · rintro ⟨E, U⟩ hp; rw [mem_coe, mem_filter] at hp
      exact ⟨⟨E, U⟩, mem_coe.mpr (mem_sigma.mpr
        ⟨mem_filter.mpr ⟨mem_powerset.mpr (subset_univ E), hp.2.1⟩, mem_powerset.mpr hp.2.2⟩), rfl⟩
  rw [hbij, card_sigma]; simp only [card_powerset]; exact sum_powerset_filter_card_le_two_pow q

/-- Specialization of `card_subsetPairs_eq_subsetPairCount` when `Fintype.card ι = n`. -/
theorem card_subsetPairs_eq_subsetPairCount_of_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : Fintype.card ι = n) (q : ℕ) :
    #{p : Finset ι × Finset ι | #p.1 ≤ q ∧ p.2 ⊆ p.1} = subsetPairCount n q := by
  rw [card_subsetPairs_eq_subsetPairCount, hn]

end Cslib
