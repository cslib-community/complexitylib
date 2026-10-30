/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Finset.Max

/-!
# The `k`-th largest value, padded with zeros

`Finset.kthLargest k s h` is the `k`-th largest member of the multiset of values `h x`, `x ∈ s`,
padded with infinitely many zeros. It is the largest value `h x` that is reached or exceeded by at
least `k` of the values, or `0` if that is larger. So it is nonnegative, and it is `0` when fewer
than `k` of the values are positive. This is the order statistic `rank_k` of the detectors in the
OpenAI preprint [OpenAI2026LogSpace, Section 4.2].

It is characterized by threshold counts: for `0 < k` and `0 ≤ t`, the `k`-th largest value exceeds
`t` exactly when at least `k` values exceed `t` (`Finset.lt_kthLargest_iff`), and for `0 < t` it
is at least `t` exactly when at least `k` values are at least `t` (`Finset.le_kthLargest_iff`).

## Main definitions

* `Finset.kthLargest`: the `k`-th largest value, padded with zeros.

## Main results

* `Finset.kthLargest_nonneg`, `Finset.kthLargest_le`: bounds.
* `Finset.lt_kthLargest_iff`, `Finset.le_kthLargest_iff`: the threshold characterizations.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 4.2 (preprint, not peer reviewed)
-/

public section

namespace Finset

variable {α R : Type*} [LinearOrder R] [Zero R]

/-- The **`k`-th largest value** of `h` on `s`, padded with zeros: the largest value `h x`,
`x ∈ s`, that at least `k` values `h w`, `w ∈ s`, reach or exceed, or `0` if that is larger. -/
@[expose] def kthLargest (k : ℕ) (s : Finset α) (h : α → R) : R :=
  (insert 0 ((s.filter fun x => k ≤ #{w ∈ s | h x ≤ h w}).image h)).max' (insert_nonempty _ _)

variable {k : ℕ} {s : Finset α} {h : α → R} {t : R}

theorem kthLargest_nonneg : 0 ≤ kthLargest k s h :=
  le_max' _ _ (mem_insert_self _ _)

/-- The `k`-th largest value is at most any nonnegative upper bound of the values. -/
theorem kthLargest_le (ht : 0 ≤ t) (hh : ∀ x ∈ s, h x ≤ t) : kthLargest k s h ≤ t := by
  refine max'_le _ _ _ fun a ha => ?_
  rcases mem_insert.mp ha with rfl | ha
  · exact ht
  · obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
    exact hh x (mem_filter.mp hx).1

/-- A value of `s` reached or exceeded by at least `k` values is at most the `k`-th largest. -/
private theorem le_kthLargest_of_le_card {x : α} (hx : x ∈ s)
    (hk : k ≤ #{w ∈ s | h x ≤ h w}) : h x ≤ kthLargest k s h :=
  le_max' _ _ (mem_insert_of_mem (mem_image_of_mem h (mem_filter.mpr ⟨hx, hk⟩)))

omit [Zero R] in
/-- If at least `k > 0` values satisfy a threshold condition, so does the smallest of them, which
is reached or exceeded by all of them. -/
private theorem exists_le_card (hk : 0 < k) (p : R → Prop) [DecidablePred p]
    (hp : k ≤ #{x ∈ s | p (h x)}) :
    ∃ x ∈ s, p (h x) ∧ k ≤ #{w ∈ s | h x ≤ h w} := by
  have hne : ({x ∈ s | p (h x)} : Finset α).Nonempty := card_pos.mp (hk.trans_le hp)
  obtain ⟨x, hx, hmin⟩ := exists_min_image _ h hne
  obtain ⟨hxs, hpx⟩ := mem_filter.mp hx
  refine ⟨x, hxs, hpx, hp.trans (card_le_card fun w hw => ?_)⟩
  exact mem_filter.mpr ⟨(mem_filter.mp hw).1, hmin w hw⟩

/-- **The `k`-th largest value exceeds `t ≥ 0`** exactly when at least `k > 0` values do. -/
theorem lt_kthLargest_iff (hk : 0 < k) (ht : 0 ≤ t) :
    t < kthLargest k s h ↔ k ≤ #{x ∈ s | t < h x} := by
  constructor
  · intro hlt
    obtain ⟨a, ha, hta⟩ : ∃ a ∈ _, t < a := ⟨_, max'_mem _ _, hlt⟩
    rcases mem_insert.mp ha with rfl | ha
    · exact absurd ht (not_le.mpr hta)
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
    obtain ⟨-, hkx⟩ := mem_filter.mp hx
    exact hkx.trans (card_le_card fun w hw => by
      obtain ⟨hws, hxw⟩ := mem_filter.mp hw
      exact mem_filter.mpr ⟨hws, hta.trans_le hxw⟩)
  · intro hcard
    obtain ⟨x, hxs, htx, hkx⟩ := exists_le_card hk (t < ·) hcard
    exact htx.trans_le (le_kthLargest_of_le_card hxs hkx)

/-- **The `k`-th largest value is at least `t > 0`** exactly when at least `k > 0` values are. -/
theorem le_kthLargest_iff (hk : 0 < k) (ht : 0 < t) :
    t ≤ kthLargest k s h ↔ k ≤ #{x ∈ s | t ≤ h x} := by
  constructor
  · intro hle
    obtain ⟨a, ha, hta⟩ : ∃ a ∈ _, t ≤ a := ⟨_, max'_mem _ _, hle⟩
    rcases mem_insert.mp ha with rfl | ha
    · exact absurd ht (not_lt.mpr hta)
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
    obtain ⟨-, hkx⟩ := mem_filter.mp hx
    exact hkx.trans (card_le_card fun w hw => by
      obtain ⟨hws, hxw⟩ := mem_filter.mp hw
      exact mem_filter.mpr ⟨hws, hta.trans hxw⟩)
  · intro hcard
    obtain ⟨x, hxs, htx, hkx⟩ := exists_le_card hk (t ≤ ·) hcard
    exact htx.trans (le_kthLargest_of_le_card hxs hkx)

end Finset
