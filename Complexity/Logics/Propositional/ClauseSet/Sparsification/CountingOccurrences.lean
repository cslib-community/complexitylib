/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingUnits
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Path

/-!
# Marked clause occurrences in counting sparsification

Appendix A.2, Lemma A.2 [OpenAI2026ETH] bounds the marked clauses still present at a node. A
clause present in the root is excluded. This is distinct from the sum of insertion events in
`CountingUnits`: a higher-width clause may later be deleted.

The bound is the shared `card_newContaining_lt_of_steps` [Calabro, Lemma 5.9][Calabro2009]: the
minimum-width and maximum-heart priorities of `Choice` control the old clauses and the new petals,
respectively. The B-child's additional negated-heart units have width one and cannot enter the
filter considered here, whose width is at least two. No decision-path `Refines` or tree-size
theorem is transferred.

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
  refine card_newContaining_lt_of_steps hθ N ψ c H b hchoice (fun i hi C hC hCi hC2 => ?_) ht hS hSj
  rw [hstep i hi, countingChild_eq_reduce_union] at hC
  have hCI := (mem_union.mp (reduce_subset _ hC)).resolve_left hCi
  cases hb : b i with
  | false => simpa only [hb, countingIntro, intro] using hCI
  | true => exact mem_petals_of_mem_countingIntro_true (hb ▸ hCI) hC2

end Cslib.Logic.PL.ClauseSet.Sparsification
