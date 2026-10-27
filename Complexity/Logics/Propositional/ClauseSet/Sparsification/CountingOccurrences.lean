/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingUnits

/-!
# Marked clause occurrences in counting sparsification

Appendix A.2, Lemma A.2 [OpenAI2026ETH] bounds the marked clauses still present at a node. A
clause present in the root is excluded. This is distinct from the sum of insertion events in
`CountingUnits`: a higher-width clause may later be deleted.

The minimum-width and maximum-heart priorities of `Choice` control the old clauses and the new
petals, respectively. This follows the existing proof of `Path.card_newContaining_lt`
[Calabro, Lemma 5.9][Calabro2009], applied directly to counting steps. The B-child's additional
negated-heart units have width one and cannot enter the filter considered here, whose width is at
least two. No decision-path `Refines` or tree-size theorem is transferred.

This present-clause upper bound requires positive thresholds and valid choices, but not root
reducedness or nontautology. Those stronger conditions remain relevant to later immediate-survival
and deletion-charge arguments. No higher-width insertion-event, depth, leaf or runtime bound is
asserted here.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.card_lt_of_mem_countingIntro`: payload widths decrease.
* `Cslib.Logic.PL.ClauseSet.Sparsification.card_counting_newContaining_lt`: marked-present bound.
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset

variable {V : Type*} [DecidableEq V]

/-- Every counting payload clause is smaller than the selected width, including negated units. -/
theorem card_lt_of_mem_countingIntro {θ : ℕ → ℕ} {ψ : ClauseSet V} {c : ℕ}
    {H : Finset (Literal V)} (h : Heavy θ ψ c H) {b : Bool} {C : Finset (Literal V)}
    (hC : C ∈ countingIntro ψ c H b) : C.card < c := by
  cases b with
  | false =>
    have hCH : C = H := by simpa only [countingIntro, mem_singleton] using hC
    simpa only [hCH] using h.2.1
  | true =>
    rcases mem_union.mp hC with hC | hC
    · rw [card_of_mem_petals hC]
      have := h.1
      have := h.2.1
      omega
    · obtain ⟨l, -, rfl⟩ := mem_image.mp hC
      simp only [card_singleton]
      have := h.1
      have := h.2.1
      omega

private theorem mem_petals_of_mem_countingIntro_true {ψ : ClauseSet V} {c : ℕ}
    {H C : Finset (Literal V)} (hC : C ∈ countingIntro ψ c H true) (hwidth : 2 ≤ C.card) :
    C ∈ petals ψ c H := by
  rcases mem_union.mp hC with hC | hC
  · exact hC
  · obtain ⟨l, -, hCl⟩ := mem_image.mp hC
    have hcard : C.card = 1 := by rw [← hCl]; exact card_singleton _
    omega

/-- At every prefix of an actual counting path, fewer than `2 * θ (j - |S|)` root-absent clauses
of width `j` containing a fixed nonempty proper literal set `S` are present.

The selected choices retain both priority conditions. The additional B-units are explicitly
excluded using `j ≥ 2`. Root clauses remain excluded, and no ambient finite variable type or
resource assumption is needed. This counts clauses currently present, not all insertion events.
-/
theorem card_counting_newContaining_lt {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hchoice : ∀ i < N, Choice θ (ψ i) (c i) (H i))
    {t j : ℕ} (ht : t ≤ N) {S : Finset (Literal V)} (hS : 1 ≤ S.card) (hSj : S.card < j) :
    ((ψ t).filter fun C => C ∉ ψ 0 ∧ C.card = j ∧ S ⊆ C).card < 2 * θ (j - S.card) := by
  set γ := (ψ t).filter fun C => C ∉ ψ 0 ∧ C.card = j ∧ S ⊆ C
  by_contra hge
  push Not at hge
  have hγ : ∀ C ∈ γ, C ∉ ψ 0 ∧ C.card = j ∧ S ⊆ C := fun C hC => (mem_filter.mp hC).2
  have hex : ∃ m, γ ⊆ ψ m := ⟨t, filter_subset _ _⟩
  set x := Nat.find hex
  have hxsub : γ ⊆ ψ x := Nat.find_spec hex
  have hxle : x ≤ t := Nat.find_min' hex (filter_subset _ _)
  have hγne : γ.Nonempty := by rw [← card_pos]; have := hθ (j - S.card); omega
  have hx0 : x ≠ 0 := by
    intro hx
    obtain ⟨C, hC⟩ := hγne
    exact (hγ C hC).1 (hx ▸ hxsub hC)
  obtain ⟨m, hxm⟩ : ∃ m, x = m + 1 := ⟨x - 1, by omega⟩
  have hm : m < N := by omega
  have hnotsub : ¬ γ ⊆ ψ m := Nat.find_min hex (by omega)
  have hnext : ψ (m + 1) ⊆ ψ m ∪ countingIntro (ψ m) (c m) (H m) (b m) := by
    rw [hstep m hm, countingChild_eq_reduce_union]
    exact reduce_subset _
  obtain ⟨C₀, hC₀γ, hC₀old⟩ := not_subset.mp hnotsub
  have hC₀intro : C₀ ∈ countingIntro (ψ m) (c m) (H m) (b m) := by
    exact (mem_union.mp (hnext (hxm ▸ hxsub hC₀γ))).resolve_left hC₀old
  have hjc : j < c m := by
    have := card_lt_of_mem_countingIntro (hchoice m hm).1 hC₀intro
    rwa [(hγ C₀ hC₀γ).2.1] at this
  have hlight : (flower (ψ m) j S).card < θ (j - S.card) := by
    by_contra hheavy
    push Not at hheavy
    have := (hchoice m hm).2.1 j S ⟨hS, hSj, hheavy⟩
    omega
  have hold : (γ.filter (· ∈ ψ m)).card < θ (j - S.card) := by
    refine lt_of_le_of_lt (card_le_card fun C hC => ?_) hlight
    obtain ⟨hCγ, hCold⟩ := mem_filter.mp hC
    exact mem_flower.mpr ⟨hCold, (hγ C hCγ).2.1, (hγ C hCγ).2.2⟩
  set Q := γ.filter (· ∉ ψ m)
  have hsplit : (γ.filter (· ∈ ψ m)).card + Q.card = γ.card :=
    card_filter_add_card_filter_not (s := γ) (· ∈ ψ m)
  have hQcard : θ (j - S.card) + 1 ≤ Q.card := by omega
  have hQintro : Q ⊆ countingIntro (ψ m) (c m) (H m) (b m) := by
    intro C hC
    obtain ⟨hCγ, hCold⟩ := mem_filter.mp hC
    exact (mem_union.mp (hnext (hxm ▸ hxsub hCγ))).resolve_left hCold
  cases hdir : b m with
  | false =>
    have hQone : Q.card ≤ 1 := by
      have := card_le_card hQintro
      simpa only [hdir, countingIntro, card_singleton] using this
    have := hθ (j - S.card)
    omega
  | true =>
    have hQpetal : ∀ q ∈ Q, q ∈ petals (ψ m) (c m) (H m) := by
      intro q hq
      have hqintro := hQintro hq
      rw [hdir] at hqintro
      apply mem_petals_of_mem_countingIntro_true hqintro
      have := (hγ q (mem_filter.mp hq).1).2.1
      omega
    obtain ⟨q₀, hq₀⟩ : Q.Nonempty := by rw [← card_pos]; omega
    obtain ⟨D₀, hD₀, hD₀q⟩ := mem_petals.mp (hQpetal q₀ hq₀)
    have hSq₀ : S ⊆ q₀ := (hγ q₀ (mem_filter.mp hq₀).1).2.2
    have hdisj : Disjoint (H m) S := by
      rw [Finset.disjoint_right]
      intro l hlS hlH
      have := hSq₀ hlS
      rw [← hD₀q] at this
      exact (mem_sdiff.mp this).2 hlH
    have hcardHS : (H m ∪ S).card = (H m).card + S.card := card_union_of_disjoint hdisj
    have hj : j = c m - (H m).card := by
      rw [← (hγ q₀ (mem_filter.mp hq₀).1).2.1]
      exact card_of_mem_petals (hQpetal q₀ hq₀)
    have hHc : (H m).card < c m := (hchoice m hm).1.2.1
    have hQle : Q.card ≤ (flower (ψ m) (c m) (H m ∪ S)).card := by
      have hsub : Q ⊆ ((flower (ψ m) (c m) (H m)).filter (S ⊆ ·)).image (· \ H m) := by
        intro q hq
        obtain ⟨D, hD, rfl⟩ := mem_petals.mp (hQpetal q hq)
        have hSD : S ⊆ D \ H m := (hγ _ (mem_filter.mp hq).1).2.2
        exact mem_image.mpr ⟨D, mem_filter.mpr ⟨hD, hSD.trans sdiff_subset⟩, rfl⟩
      refine (card_le_card hsub).trans (card_image_le.trans (card_le_card fun D hD => ?_))
      obtain ⟨hDf, hSD⟩ := mem_filter.mp hD
      obtain ⟨hDψ, hDcard, hHD⟩ := mem_flower.mp hDf
      exact mem_flower.mpr ⟨hDψ, hDcard, union_subset hHD hSD⟩
    have hheavy : Heavy θ (ψ m) (c m) (H m ∪ S) := by
      refine ⟨by omega, by omega, ?_⟩
      have heq : c m - (H m ∪ S).card = j - S.card := by omega
      rw [heq]
      omega
    have := (hchoice m hm).2.2 (H m ∪ S) hheavy
    omega

end Cslib.Logic.PL.ClauseSet.Sparsification
