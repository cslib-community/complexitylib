/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Streaming.Basic
public import Mathlib.Data.Multiset.Dedup
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.Filter
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The Misra–Gries summary

The **Misra–Gries summary** with `k` counters [MisraGries1982] reads a stream of items and keeps a
counter for at most `k` distinct items. On reading `a`, it increments the counter of `a` if `a` has
one or if fewer than `k` counters are in use, and otherwise decrements every counter, discarding the
counters that reach zero. A point query reports the counter of the queried item, or zero.

We store the counters as a multiset `c : Multiset α` with at most `k` distinct elements
(`Cslib.Streaming.MisraGries.card_toFinset_state_le`), the counter of `a` being `c.count a`. A
decrement removes one copy of each of the `k` stored items together with the arriving item, that is
`k + 1` distinct items of the stream, so after a stream of `m` items there were at most
`m / (k + 1)` decrements. Hence the estimate `f̂_a` of the frequency `f_a = count a s` satisfies
`f_a - m / (k + 1) ≤ f̂_a ≤ f_a` (`Cslib.Streaming.MisraGries.run_le_count`,
`Cslib.Streaming.MisraGries.count_sub_div_le_run`), in the sharper form
`(k + 1) (f_a - f̂_a) + m̂ ≤ m` where `m̂` is the sum of the counters
(`Cslib.Streaming.MisraGries.mul_count_sub_run_add_card_le`). In particular every item occurring
more than `m / (k + 1)` times keeps a counter
(`Cslib.Streaming.MisraGries.mem_state_of_length_lt_mul_count`): this is the deterministic
heavy-hitters guarantee. With `k = 1` the single counter holds the majority item whenever there is
one, which solves the MAJORITY problem of [Chakrabarti2025, Section 1.1] up to a check of the
candidate (`Cslib.Streaming.MisraGries.toFinset_state_one_eq`).

**Memory.** On streams of at most `m` items over a universe of `n` items each counter is at most
`m`, so the summary is determined by `k` slots each holding nothing or an item with a counter, and
there are at most `(n (m + 1) + 1) ^ k` reachable summaries
(`Cslib.Streaming.MisraGries.spaceLE_misraGries`): `O(k (log n + log m))` bits.

Chakrabarti's notes [Chakrabarti2025, Algorithm 1 and Theorem 1.3.1] use a parameter `k` with at
most `k - 1` counters and error `m / k`; our `misraGries k` is their algorithm with parameter
`k + 1`.

## Main definitions

* `Cslib.Streaming.misraGries`: the Misra–Gries summary with `k` counters.

## Main results

* `Cslib.Streaming.MisraGries.run_le_count`,
  `Cslib.Streaming.MisraGries.mul_count_sub_run_add_card_le`,
  `Cslib.Streaming.MisraGries.count_sub_div_le_run`: the estimate errs by at most `m / (k + 1)`,
  from below.
* `Cslib.Streaming.MisraGries.mem_state_of_length_lt_mul_count`: frequent items are kept.
* `Cslib.Streaming.MisraGries.card_toFinset_state_le`: at most `k` counters.
* `Cslib.Streaming.MisraGries.spaceLE_misraGries`: the memory bound.
* `Cslib.Streaming.MisraGries.toFinset_state_one_eq`: one counter finds the majority item.

## References

* [J. Misra, D. Gries, *Finding repeated elements*][MisraGries1982]
* [A. Chakrabarti, *Data Stream Algorithms*, Unit 1][Chakrabarti2025]
-/

public section

namespace Cslib.Streaming

variable {α : Type*} [DecidableEq α]

namespace MisraGries

/-- One step of the Misra–Gries summary with `k` counters, stored as a multiset whose multiplicities
are the counters: add the item `a` if it has a counter or fewer than `k` counters are in use, and
otherwise decrement every counter. -/
@[expose] def step (k : ℕ) (c : Multiset α) (a : α) : Multiset α :=
  if a ∈ c ∨ c.toFinset.card < k then a ::ₘ c else c - c.dedup

end MisraGries

/-- The **Misra–Gries summary** with `k` counters [MisraGries1982]: the memory is a multiset `c`
with at most `k` distinct elements, whose multiplicity `c.count a` is the counter of `a`, and a
point query `a` is answered with the counter of `a`. -/
@[expose] def misraGries (k : ℕ) : Algorithm (Multiset α) α (α → ℕ) where
  init := 0
  update := MisraGries.step k
  output c a := c.count a

namespace MisraGries

variable {k : ℕ}

/-- The invariant of the Misra–Gries summary `c` of a stream with multiset of items `S`. -/
private structure Inv (k : ℕ) (c S : Multiset α) : Prop where
  le : c ≤ S
  card_toFinset_le : c.toFinset.card ≤ k
  decrements : ∃ D, (k + 1) * D + Multiset.card c ≤ Multiset.card S ∧
    ∀ x, S.count x ≤ c.count x + D

private theorem inv_zero : Inv k (0 : Multiset α) 0 :=
  ⟨le_rfl, by simp, ⟨0, by simp, fun x => by simp⟩⟩

private theorem inv_step {c S : Multiset α} (h : Inv k c S) (a : α) :
    Inv k (step k c a) (a ::ₘ S) := by
  obtain ⟨hle, hcard, D, hD, hcount⟩ := h
  unfold step
  split_ifs with ha
  · refine ⟨Multiset.cons_le_cons a hle, ?_, D, ?_, fun x => ?_⟩
    · rw [Multiset.toFinset_cons]
      rcases ha with ha | ha
      · rwa [Finset.insert_eq_of_mem (Multiset.mem_toFinset.2 ha)]
      · exact (Finset.card_insert_le _ _).trans ha
    · simp only [Multiset.card_cons]
      omega
    · simp only [Multiset.count_cons]
      have := hcount x
      split_ifs <;> omega
  · push Not at ha
    obtain ⟨hac, hk⟩ := ha
    have hk' : c.toFinset.card = k := le_antisymm hcard hk
    have hdedup : Multiset.card c.dedup = k := by
      rw [← hk', Multiset.card_toFinset]
    have hdedup_le : Multiset.card c.dedup ≤ Multiset.card c :=
      Multiset.card_le_card (Multiset.dedup_le c)
    refine ⟨tsub_le_self.trans (hle.trans (Multiset.le_cons_self S a)), ?_, D + 1, ?_,
      fun x => ?_⟩
    · exact (Finset.card_le_card (Multiset.toFinset_subset.2
        (Multiset.subset_of_le tsub_le_self))).trans hcard
    · rw [Multiset.card_sub (Multiset.dedup_le c), Multiset.card_cons, mul_add, mul_one]
      omega
    · rw [Multiset.count_cons, Multiset.count_sub, Multiset.count_dedup]
      have := hcount x
      by_cases hx : x = a
      · subst hx
        rw [Multiset.count_eq_zero_of_notMem hac] at this ⊢
        simp only [↓reduceIte, hac]
        omega
      · have hpos : x ∈ c → 1 ≤ c.count x := fun h => Multiset.count_pos.2 h
        simp only [hx, ↓reduceIte]
        split_ifs with hxc
        · have := hpos hxc
          omega
        · omega

private theorem inv_state (s : List α) : Inv k ((misraGries k).state s) (s : Multiset α) := by
  induction s using List.reverseRecOn with
  | nil => exact inv_zero
  | append_singleton s a ih =>
    rw [Algorithm.state_append, Algorithm.stateFrom_cons, Algorithm.stateFrom_nil,
      ← Multiset.coe_add, Multiset.coe_singleton, add_comm, Multiset.singleton_add]
    exact inv_step ih a

/-- The Misra–Gries summary of a stream is part of the stream. -/
theorem state_le (s : List α) : (misraGries k).state s ≤ (s : Multiset α) :=
  (inv_state s).le

/-- The Misra–Gries summary uses at most `k` counters. -/
theorem card_toFinset_state_le (s : List α) : ((misraGries k).state s).toFinset.card ≤ k :=
  (inv_state s).card_toFinset_le

/-- The Misra–Gries estimate never exceeds the frequency. -/
theorem run_le_count (s : List α) (a : α) : (misraGries k).run s a ≤ s.count a := by
  rw [← Multiset.coe_count]
  exact Multiset.le_iff_count.1 (state_le s) a

/-- **The Misra–Gries error bound** [Chakrabarti2025, Theorem 1.3.1 and Exercise 1-1]: after a
stream of `m` items, the estimate `f̂_a` of the frequency `f_a` of `a` satisfies
`(k + 1) (f_a - f̂_a) + m̂ ≤ m`, where `m̂` is the sum of the counters. -/
theorem mul_count_sub_run_add_card_le (s : List α) (a : α) :
    (k + 1) * (s.count a - (misraGries k).run s a) +
      Multiset.card ((misraGries k).state s) ≤ s.length := by
  obtain ⟨D, hD, hcount⟩ := (inv_state (k := k) s).decrements
  have h := hcount a
  rw [Multiset.coe_count, Multiset.coe_card] at *
  have : s.count a - (misraGries k).run s a ≤ D := by
    change s.count a - ((misraGries k).state s).count a ≤ D
    omega
  calc (k + 1) * (s.count a - (misraGries k).run s a) + Multiset.card ((misraGries k).state s)
      ≤ (k + 1) * D + Multiset.card ((misraGries k).state s) := by gcongr
    _ ≤ s.length := hD

/-- **The Misra–Gries error bound** [Chakrabarti2025, Theorem 1.3.1]: after a stream of `m` items
the estimate of the frequency `f_a` of `a` lies in `[f_a - m / (k + 1), f_a]`. -/
theorem count_sub_div_le_run (s : List α) (a : α) :
    (s.count a : ℝ) - s.length / (k + 1) ≤ (misraGries k).run s a := by
  have h := mul_count_sub_run_add_card_le (k := k) s a
  have hle := run_le_count (k := k) s a
  have hk : (0 : ℝ) < k + 1 := by positivity
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hk]
  have : ((k + 1) * (s.count a - (misraGries k).run s a) : ℕ) ≤ (s.length : ℝ) := by
    exact_mod_cast (Nat.le_add_right _ _).trans h
  push_cast [Nat.cast_sub hle] at this
  linarith

/-- **Frequent items are kept** [Chakrabarti2025, Section 1.4]: an item occurring more than
`m / (k + 1)` times in a stream of `m` items has a positive counter. -/
theorem mem_state_of_length_lt_mul_count {s : List α} {a : α}
    (h : s.length < (k + 1) * s.count a) : a ∈ (misraGries k).state s := by
  rw [← Multiset.count_pos]
  have := mul_count_sub_run_add_card_le (k := k) s a
  change (k + 1) * (s.count a - ((misraGries k).state s).count a) + _ ≤ _ at this
  by_contra h0
  rw [Nat.lt_iff_add_one_le, Nat.not_le, Nat.lt_one_iff] at h0
  rw [h0, Nat.sub_zero] at this
  omega

/-- **The majority vote** [Chakrabarti2025, Section 1.1]: with one counter, an item occurring in
more than half of the stream is the only item with a counter. -/
theorem toFinset_state_one_eq {s : List α} {a : α} (h : s.length < 2 * s.count a) :
    ((misraGries 1).state s).toFinset = {a} := by
  have ha := Multiset.mem_toFinset.2 (mem_state_of_length_lt_mul_count (k := 1) h)
  exact Finset.eq_singleton_iff_unique_mem.2 ⟨ha, fun b hb =>
    Finset.card_le_one.1 (card_toFinset_state_le s) b hb a ha⟩

/-- The multiset with the counters listed in `k` slots, each holding nothing or an item and its
counter. -/
private def ofSlots {m : ℕ} (g : Fin k → Option (α × Fin (m + 1))) : Multiset α :=
  ∑ i, (g i).elim 0 fun p => Multiset.replicate p.2 p.1

/-- A multiset with at most `k` distinct elements, each occurring at most `m` times, is listed in
`k` slots. -/
private theorem exists_ofSlots_eq {m : ℕ} :
    ∀ {k : ℕ} (c : Multiset α), c.toFinset.card ≤ k → (∀ x, c.count x ≤ m) →
      ∃ g : Fin k → Option (α × Fin (m + 1)), ofSlots g = c
  | 0, c, hc, _ => by
    refine ⟨Fin.elim0, ?_⟩
    rw [Nat.le_zero, Finset.card_eq_zero, Multiset.toFinset_eq_empty] at hc
    simp [ofSlots, hc]
  | k + 1, c, hc, hm => by
    rcases Multiset.empty_or_exists_mem c with rfl | ⟨a, ha⟩
    · exact ⟨fun _ => none, by simp [ofSlots]⟩
    have hc' : (c.filter (· ≠ a)).toFinset.card ≤ k := by
      rw [Multiset.toFinset_filter, Finset.filter_ne']
      rw [Finset.card_erase_of_mem (Multiset.mem_toFinset.2 ha)]
      omega
    obtain ⟨g, hg⟩ := exists_ofSlots_eq (c.filter (· ≠ a)) hc' fun x =>
      (Multiset.count_le_of_le x (Multiset.filter_le _ c)).trans (hm x)
    refine ⟨Fin.cons (some (a, ⟨c.count a, Nat.lt_succ_of_le (hm a)⟩)) g, ?_⟩
    rw [ofSlots, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Option.elim_some]
    change Multiset.replicate (c.count a) a + ofSlots g = c
    rw [hg, ← Multiset.filter_eq' c a]
    exact Multiset.filter_add_not (· = a) c

/-- **The memory of the Misra–Gries summary** [Chakrabarti2025, Theorem 1.3.1]: over a universe
of `n` items, the summary with `k` counters uses at most `b` bits of memory on streams of at most
`m` items when `(n (m + 1) + 1) ^ k ≤ 2 ^ b`, that is `O(k (log n + log m))` bits. -/
theorem spaceLE_misraGries [Fintype α] {m b : ℕ}
    (hb : (Fintype.card α * (m + 1) + 1) ^ k ≤ 2 ^ b) :
    (misraGries (α := α) k).SpaceLE m b := by
  refine Algorithm.spaceLE_of_subset_finset
    (T := Finset.univ.image (ofSlots (k := k) (m := m))) ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨g, hg⟩ := exists_ofSlots_eq (m := m) ((misraGries k).state s)
      (card_toFinset_state_le s) fun x =>
        ((Multiset.count_le_card x _).trans
          (Multiset.card_le_card (state_le s))).trans (by rwa [Multiset.coe_card])
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨g, Finset.mem_univ g, hg⟩)
  · refine Finset.card_image_le.trans (le_of_eq_of_le ?_ hb)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_option, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]

end MisraGries

end Cslib.Streaming
