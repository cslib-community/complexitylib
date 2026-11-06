/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.TwoBoundary
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Weighted signed rows

The row-local constructions of [ChenJiangZhu2027], Theorem 7.1, equations (24)–(25),
PDF pp. 23–24. A row has distinct variables, fixed signs and positive natural weights.
`upper` forbids small overweight subsets; `attainment` lists small exact-weight subsets.
These constructions do not normalize arbitrary repeated signed occurrences, cap weights,
select independent rows, deduplicate across rows or certify encoded runtime.

## Main results

* `upper_eval`: the constructed CNF expresses the weighted upper bound.
* `attainment_eval`: under that bound, the constructed DNF expresses equality.

The proofs work even without the source's coefficient cap; `Row.capped` records the
additional hypothesis used by the subsequent reduction.
-/

public noncomputable section

namespace Cslib.Logic.PL.WeightedRow

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- A signed row on distinct variables with positive integer coefficients and bounded demand. -/
structure Row (V : Type*) [DecidableEq V] (d : ℕ) where
  /-- Distinct variables used in the row. -/
  support : Finset V
  /-- Polarity at each variable. -/
  sign : V → Bool
  /-- Integer coefficient at each variable. -/
  weight : V → ℕ
  /-- Target weighted contribution. -/
  demand : ℕ
  positive : ∀ i ∈ support, 0 < weight i
  bounded : demand ≤ d
  capped : ∀ i ∈ support, weight i ≤ demand + 1

variable {d : ℕ}

/-- The true row literals under an assignment. -/
@[expose] def Row.active (R : Row V d) (σ : V → Bool) : Finset V :=
  R.support.filter fun i => σ i = R.sign i

/-- Weighted contribution of the true literals. -/
@[expose] def Row.value (R : Row V d) (σ : V → Bool) : ℕ :=
  ∑ i ∈ R.active σ, R.weight i

/-- Conjunction of the row literals indexed by a subset. -/
@[expose] def Row.term (R : Row V d) (s : Finset V) : Term V :=
  s.toList.map fun i => (i, R.sign i)

/-- Equation (24): clauses forbidding all overweight subsets of size at most `b + 1`. -/
@[expose] def Row.upper (R : Row V d) : CNF V :=
  (R.support.powerset.filter fun s =>
    s.card ≤ R.demand + 1 ∧ R.demand < ∑ i ∈ s, R.weight i).toList.map
      fun s => (R.term s).negate

/-- Equation (25): exact-weight subsets of size at most `d`. -/
@[expose] def Row.attainment (R : Row V d) : DNF V :=
  (R.support.powerset.filter fun s =>
    s.card ≤ d ∧ ∑ i ∈ s, R.weight i = R.demand).toList.map R.term

/-- Positive integer weights bound the size of a subset by its weight. -/
private theorem Row.card_le_weight (R : Row V d) {s : Finset V} (hs : s ⊆ R.support) :
    s.card ≤ ∑ i ∈ s, R.weight i := by
  calc
    s.card = ∑ _i ∈ s, 1 := by simp
    _ ≤ ∑ i ∈ s, R.weight i := Finset.sum_le_sum fun i hi => R.positive i (hs hi)

/-- Shrink an overweight set until every one-element deletion is within the demand.
This is the inclusion-minimal overweight-subset argument of the source. -/
private theorem Row.small_overweight (R : Row V d) (s : Finset V) (hs : s ⊆ R.support)
    (hover : R.demand < ∑ i ∈ s, R.weight i) :
    ∃ t ⊆ s, t.card ≤ R.demand + 1 ∧ R.demand < ∑ i ∈ t, R.weight i := by
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | ind n ih =>
    by_cases he : ∃ i ∈ s, R.demand < ∑ j ∈ s.erase i, R.weight j
    · obtain ⟨i, hi, hdel⟩ := he
      obtain ⟨t, ht, hcard, hw⟩ := ih (s.erase i).card
        (by
          rw [Finset.card_erase_of_mem hi]
          have := Finset.card_pos.mpr ⟨i, hi⟩
          omega) (s.erase i)
        (Finset.Subset.trans (Finset.erase_subset i s) hs) hdel rfl
      exact ⟨t, Finset.Subset.trans ht (Finset.erase_subset i s), hcard, hw⟩
    · have hnon : s.Nonempty := by
        by_contra h
        have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        simp [this] at hover
      obtain ⟨i, hi⟩ := hnon
      have hw : ∑ j ∈ s.erase i, R.weight j ≤ R.demand := by
        by_contra h
        exact he ⟨i, hi, by omega⟩
      have hc := R.card_le_weight (Finset.Subset.trans (Finset.erase_subset i s) hs)
      rw [Finset.card_erase_of_mem hi] at hc
      exact ⟨s, Finset.Subset.refl s, by omega, hover⟩

private theorem Row.term_eval (R : Row V d) (s : Finset V) (σ : V → Bool) :
    (R.term s).eval σ = true ↔ ∀ i ∈ s, σ i = R.sign i := by
  simp [Row.term, Term.eval_eq_true_iff]

/-- The generated clauses enforce exactly the weighted upper bound. -/
theorem upper_eval (R : Row V d) (σ : V → Bool) :
    R.upper.eval σ = true ↔ R.value σ ≤ R.demand := by
  have he : R.upper.eval σ = true ↔
      ∀ s ⊆ R.support, s.card ≤ R.demand + 1 →
        R.demand < ∑ i ∈ s, R.weight i → ¬ (∀ i ∈ s, σ i = R.sign i) := by
    simp [Row.upper, CNF.eval, List.all_map, Term.eval_negate,
      Bool.eq_false_iff, R.term_eval]
  rw [he]
  constructor
  · intro h
    by_contra hn
    obtain ⟨s, hs, hc, hw⟩ := R.small_overweight (R.active σ)
      (Finset.filter_subset _ _) (by simpa [Row.value] using hn)
    exact h s (Finset.Subset.trans hs (Finset.filter_subset _ _)) hc hw
      (fun i hi => (Finset.mem_filter.mp (hs hi)).2)
  · intro h s hs hc hw ht
    have hsub : s ⊆ R.active σ := fun i hi => Finset.mem_filter.mpr ⟨hs hi, ht i hi⟩
    have := Finset.sum_le_sum_of_subset (f := R.weight) hsub
    change (∑ i ∈ R.active σ, R.weight i) ≤ R.demand at h
    omega

/-- Under the upper bound, attainment is equivalent to row equality. -/
theorem attainment_eval (R : Row V d) (σ : V → Bool) (hu : R.value σ ≤ R.demand) :
    R.attainment.eval σ = true ↔ R.value σ = R.demand := by
  have he : R.attainment.eval σ = true ↔ ∃ s ⊆ R.support,
      s.card ≤ d ∧ (∑ i ∈ s, R.weight i) = R.demand ∧
        ∀ i ∈ s, σ i = R.sign i := by
    simp [Row.attainment, DNF.eval_eq_true_iff, R.term_eval, and_assoc]
  rw [he]
  constructor
  · rintro ⟨s, hs, hc, hw, ht⟩
    have hsub : s ⊆ R.active σ := fun i hi => Finset.mem_filter.mpr ⟨hs hi, ht i hi⟩
    have := Finset.sum_le_sum_of_subset (f := R.weight) hsub
    change (∑ i ∈ R.active σ, R.weight i) ≤ R.demand at hu
    change (∑ i ∈ R.active σ, R.weight i) = R.demand
    omega
  · intro h
    refine ⟨R.active σ, Finset.filter_subset _ _, ?_, h, ?_⟩
    · exact (R.card_le_weight (Finset.filter_subset _ _)).trans (h.le.trans R.bounded)
    · exact fun i hi => (Finset.mem_filter.mp hi).2

/-- Counting all subsets of bounded size, without an extra factor for the row width. -/
private theorem bounded_subsets {V : Type*} (s : Finset V) (k : ℕ) (p : Finset V → Prop)
    [DecidablePred p] :
    (s.powerset.filter fun t => t.card ≤ k ∧ p t).card ≤
      ∑ j ∈ Finset.range (k + 1), s.card.choose j := by
  classical
  calc
    _ ≤ ((Finset.range (k + 1)).biUnion fun j => s.powersetCard j).card := by
      apply Finset.card_le_card
      intro t ht
      have ht := Finset.mem_filter.mp ht
      exact Finset.mem_biUnion.mpr ⟨t.card, Finset.mem_range.mpr (by omega),
        Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp ht.1, rfl⟩⟩
    _ ≤ ∑ j ∈ Finset.range (k + 1), (s.powersetCard j).card := Finset.card_biUnion_le
    _ = _ := by simp

/-- Per-row clause count; global deduplication is a separate obligation. -/
theorem upper_length (R : Row V d) :
    R.upper.length ≤ ∑ j ∈ Finset.range (R.demand + 2), R.support.card.choose j := by
  simpa [Row.upper, Nat.add_assoc] using
    bounded_subsets R.support (R.demand + 1) (fun s => R.demand < ∑ i ∈ s, R.weight i)

/-- The source's per-row binomial term bound. -/
theorem attainment_length (R : Row V d) :
    R.attainment.length ≤ ∑ j ∈ Finset.range (d + 1), R.support.card.choose j := by
  simpa [Row.attainment] using
    bounded_subsets R.support d (fun s => (∑ i ∈ s, R.weight i) = R.demand)

/-- Clause width in equation (24). -/
theorem upper_width (R : Row V d) (c : Clause V) (hc : c ∈ R.upper) :
    c.length ≤ d + 1 := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
  have h := (Finset.mem_filter.mp (Finset.mem_toList.mp hs)).2
  simpa [Row.term, Term.negate] using h.1.trans (Nat.add_le_add_right R.bounded 1)

/-- Term width in equation (25). -/
theorem attainment_width (R : Row V d) (t : Term V) (ht : t ∈ R.attainment) :
    t.length ≤ d := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have h := (Finset.mem_filter.mp (Finset.mem_toList.mp hs)).2
  simpa [Row.term] using h.1

/-- A zero demand includes the empty, true term. -/
theorem empty_mem_attainment (R : Row V d) (h : R.demand = 0) :
    [] ∈ R.attainment := by
  apply List.mem_map.mpr
  refine ⟨∅, ?_, by simp [Row.term]⟩
  simp [h]

/-- An unattainable demand gives the empty DNF, including the false semantics. -/
theorem attainment_eq_nil (R : Row V d)
    (h : ∀ s ⊆ R.support, (∑ i ∈ s, R.weight i) ≠ R.demand) :
    R.attainment = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have hs := Finset.mem_filter.mp (Finset.mem_toList.mp hs)
  exact h s (Finset.mem_powerset.mp hs.1) hs.2.2

/-- The two constructed formulas together express the original row equation. -/
theorem row_eval (R : Row V d) (σ : V → Bool) :
    (R.upper.eval σ = true ∧ R.attainment.eval σ = true) ↔ R.value σ = R.demand := by
  rw [upper_eval]
  constructor
  · rintro ⟨hu, ha⟩
    exact (attainment_eval R σ hu).mp ha
  · intro h
    exact ⟨h.le, (attainment_eval R σ h.le).mpr h⟩

/-- Concatenate the per-row upper bounds. No global deduplication is performed. -/
@[expose] def base {r : ℕ} (R : Fin (r + 1) → Row V d) : CNF V :=
  (List.finRange (r + 1)).flatMap fun j => (R j).upper

/-- Weighted rows use exactly the existing two-boundary query syntax. -/
@[expose] def query {r : ℕ} (R : Fin (r + 1) → Row V d) (β : Bool) : CNF (V ⊕ Fin r) :=
  TwoBoundary.query (base R) r (fun j => (R j).attainment) β

/-- The shared base and predicates express all row equalities. -/
theorem base_attainment_eval {r : ℕ} (R : Fin (r + 1) → Row V d) (σ : V → Bool) :
    ((base R).eval σ = true ∧ ∀ j, (R j).attainment.eval σ = true) ↔
      ∀ j, (R j).value σ = (R j).demand := by
  have hb : (base R).eval σ = true ↔ ∀ j, (R j).upper.eval σ = true := by
    simp only [base, CNF.eval_eq_true_iff, List.mem_flatMap, List.mem_finRange, true_and,
      forall_exists_index]
    exact forall_comm
  rw [hb]
  constructor
  · rintro ⟨hu, ha⟩ j
    exact (row_eval (R j) σ).mp ⟨hu j, ha j⟩
  · intro h
    exact ⟨fun j => ((row_eval (R j) σ).mpr (h j)).1,
      fun j => ((row_eval (R j) σ).mpr (h j)).2⟩

/-- Exact row-solution counting by the two ordinary boundary queries. -/
theorem counting_identity [Fintype V] {r : ℕ} (R : Fin (r + 1) → Row V d) :
    Fintype.card {σ : V → Bool // ∀ j, (R j).value σ = (R j).demand} =
      Fintype.card {σ : V ⊕ Fin r → Bool // (query R false).eval σ = true} -
      Fintype.card {σ : V ⊕ Fin r → Bool // (query R true).eval σ = true} := by
  classical
  calc
    _ = Fintype.card {σ : V → Bool // (base R).eval σ = true ∧
        ∀ j, (R j).attainment.eval σ = true} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun σ => (base_attainment_eval R σ).symm)
    _ = _ := TwoBoundary.counting_identity (base R) (fun j => (R j).attainment)

/-- The weighted wrapper has width at most `d + 2`. -/
theorem query_width {r : ℕ} (R : Fin (r + 1) → Row V d) (β : Bool)
    (c : Clause (V ⊕ Fin r)) (hc : c ∈ query R β) : c.length ≤ d + 2 := by
  have hb : ∀ c ∈ base R, c.length ≤ d + 1 := by
    intro c hc
    obtain ⟨j, hj, hc⟩ := List.mem_flatMap.mp hc
    exact upper_width (R j) c hc
  have h := TwoBoundary.query_width (base R) (fun j => (R j).attainment)
    (d + 1) d hb (fun j t ht => attainment_width (R j) t ht) β c hc
  simpa using h

end Cslib.Logic.PL.WeightedRow
