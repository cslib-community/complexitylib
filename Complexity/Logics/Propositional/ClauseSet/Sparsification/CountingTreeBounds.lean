/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Bounds
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingBounds
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingTree

/-!
# Representation Bridge and Leaf Bounds for `CountingTree.countingLeaves`

This module provides the representation bridge between the recursive leaf list
`CountingTree.countingLeaves` (`CountingTree.lean`) and the generic `CountingBranchingRule`
interface (`CountingSearch.lean`), and applies the leaf-word cardinality bounds of
`CountingBounds.lean` (Appendix A.2–A.3 of [OpenAI, *The Exponential Time Hypothesis is
False*][OpenAI2026ETH], pp. 45–47) to bound `(countingLeaves θ ψ).length`.

## Mathematical overview

1. **Nontautological clause filtering (`nontautological`).**
   The higher-width survival and insertion balance along counting paths (`CountingSurvival.lean`,
   `CountingInsertions.lean`, `CountingPathBounds.lean`) require that no root clause contains
   complementary literals `l` and `Std.Sat.Literal.negate l`. Because any clause containing
   complementary literals is satisfied by every assignment, filtering out such clauses via
   `nontautological ψ` before applying `reduce` preserves `ClauseSet.Sat`
   (`sat_nontautological_iff`) and `CNF.modelCountOn` (`modelCountOn_toCNF_nontautological`,
   `modelCountOn_toCNF_reduce_nontautological`), while ensuring that `reduce (nontautological ψ)` is
   both `Reduced` and nontautological (`nontautological_of_mem_reduce_nontautological`).

2. **Branch-word representation bridge (`countingTreeRule`, `countingLeafWords`).**
   Instantiates `CountingBranchingRule` with `CountingTree`'s deterministic chooser `chooseBranch θ`
   (`countingTreeRule`), enumerates the duplicate-free list of branch-word addresses
   (`countingLeafWords`, `nodup_countingLeafWords`), proves that those addresses are exactly the
   leaf words of `countingTreeRule` (`mem_countingLeafWords_iff_isLeafWord`,
   `isLeafWord_of_mem_countingLeafWords`), and shows that walking `countingTreeRule` along
   `countingLeafWords θ ψ` reproduces `countingLeaves θ ψ` as a list preserving multiplicity
   (`countingLeaves_eq_map_walk_countingLeafWords`).

3. **Leaf-count and leaf-sparsity corollaries for `countingLeaves`.**
   Applies `CountingBranchingRule.card_le_of_isLeafWord`,
   `CountingBranchingRule.card_le_two_pow_of_isLeafWord`, and
   `CountingBranchingRule.card_le_two_pow_thresholdBase` from `CountingBounds.lean` to the address
   finset `(countingLeafWords θ ψ).toFinset` to bound `(countingLeaves θ ψ).length` (counting
   duplicate or unsatisfiable leaf formulas with multiplicity), and packages the resulting
   Lemma 6.3 / Appendix A.3 leaf-count, occurrence, and model-count conservation bounds for
   `reduce (nontautological φ.toClauseSet)`.

## Main definitions

* `Cslib.Logic.PL.ClauseSet.Sparsification.nontautological`: filter removing clauses that contain a
  literal together with its negation.
* `Cslib.Logic.PL.ClauseSet.Sparsification.countingTreeRule`: the `CountingBranchingRule` on
  `ClauseSet V` driven by `chooseBranch θ` and `countingChild`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.countingLeafWords`: the duplicate-free list of
  branch-word addresses of the leaves of `countingLeaves θ ψ`.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.sat_nontautological_iff`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.modelCountOn_toCNF_nontautological`: removing
  tautological clauses preserves satisfying assignments and `CNF.modelCountOn`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.countingLeaves_eq_map_walk_countingLeafWords`:
  `countingLeaves θ ψ = (countingLeafWords θ ψ).map ((countingTreeRule θ).walk ψ)`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.mem_countingLeafWords_iff_isLeafWord`:
  under `∀ j, 1 ≤ j → 2 ≤ θ j`, `w ∈ countingLeafWords θ ψ ↔ (countingTreeRule θ).IsLeafWord ψ w`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.length_countingLeaves_pow_le`: binomial-sum leaf-count
  bound for `countingLeaves (M ^ ·) ψ`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.length_countingLeaves_countingThresholdBase_le`:
  exponential `2 ^ (n / B + 1)` leaf-count bound at `countingThresholdBase k B`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.countingLeaves_nontautological_thresholdBase_spec`:
  combined Lemma 6.3 model-count partition, leaf occurrence/clause bounds, and `2 ^ (n / B + 1)`
  leaf-count bound for an arbitrary `k`-CNF `φ : CNF V`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*, Section 6.4 (Lemma 6.3) and Appendix A.1–A.3,
  pp. 43–47][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset

variable {V : Type*} [DecidableEq V]

/-! ### Nontautological clause filtering -/

/-- Filter a clause set to retain only clauses containing no complementary literal pair
`l` and `Std.Sat.Literal.negate l`. -/
def nontautological (ψ : ClauseSet V) : ClauseSet V :=
  ψ.filter fun C => ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C

/-- Membership in `nontautological ψ`. -/
theorem mem_nontautological {ψ : ClauseSet V} {C : Finset (Literal V)} :
    C ∈ nontautological ψ ↔ C ∈ ψ ∧ ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C :=
  mem_filter

/-- `nontautological ψ` is a subset of `ψ`. -/
theorem nontautological_subset (ψ : ClauseSet V) : nontautological ψ ⊆ ψ :=
  filter_subset _ _

/-- Every clause in `nontautological ψ` is free of complementary literals. -/
theorem nontautological_of_mem_nontautological {ψ : ClauseSet V} {C : Finset (Literal V)}
    (hC : C ∈ nontautological ψ) : ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C :=
  (mem_nontautological.mp hC).2

/-- Every clause in `reduce (nontautological ψ)` is free of complementary literals. -/
theorem nontautological_of_mem_reduce_nontautological {ψ : ClauseSet V} {C : Finset (Literal V)}
    (hC : C ∈ reduce (nontautological ψ)) : ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C :=
  nontautological_of_mem_nontautological (reduce_subset _ hC)

/-- `nontautological` preserves clause width bounds. -/
theorem card_le_of_mem_nontautological {ψ : ClauseSet V} {k : ℕ}
    (hk : ∀ C ∈ ψ, C.card ≤ k) {C : Finset (Literal V)} (hC : C ∈ nontautological ψ) :
    C.card ≤ k :=
  hk C (nontautological_subset ψ hC)

/-- `reduce (nontautological ψ)` preserves clause width bounds. -/
theorem card_le_of_mem_reduce_nontautological {ψ : ClauseSet V} {k : ℕ}
    (hk : ∀ C ∈ ψ, C.card ≤ k) {C : Finset (Literal V)} (hC : C ∈ reduce (nontautological ψ)) :
    C.card ≤ k :=
  card_le_of_mem_nontautological hk (reduce_subset _ hC)

/-- `nontautological` preserves declared-variable support bounds. -/
theorem support_of_mem_nontautological {ψ : ClauseSet V} {declared : Finset V}
    (hsupport : ∀ C ∈ ψ, ∀ l ∈ C, l.1 ∈ declared) {C : Finset (Literal V)}
    (hC : C ∈ nontautological ψ) : ∀ l ∈ C, l.1 ∈ declared :=
  hsupport C (nontautological_subset ψ hC)

/-- `reduce (nontautological ψ)` preserves declared-variable support bounds. -/
theorem support_of_mem_reduce_nontautological {ψ : ClauseSet V} {declared : Finset V}
    (hsupport : ∀ C ∈ ψ, ∀ l ∈ C, l.1 ∈ declared) {C : Finset (Literal V)}
    (hC : C ∈ reduce (nontautological ψ)) : ∀ l ∈ C, l.1 ∈ declared :=
  support_of_mem_nontautological hsupport (reduce_subset _ hC)

/-- Removing tautological clauses does not change the satisfying assignments of `ψ`, because any
clause containing both `l` and `Std.Sat.Literal.negate l` is satisfied by every assignment. -/
theorem sat_nontautological_iff (ψ : ClauseSet V) (x : V → Bool) :
    (nontautological ψ).Sat x ↔ ψ.Sat x := by
  constructor
  · intro hx C hC
    by_cases hnt : ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C
    · exact hx C (mem_nontautological.mpr ⟨hC, hnt⟩)
    · push Not at hnt
      obtain ⟨⟨v, b⟩, hl, hneg⟩ := hnt
      by_cases hxv : x v = b
      · exact ⟨(v, b), hl, hxv⟩
      · refine ⟨(v, !b), hneg, ?_⟩
        cases h : x v <;> cases b <;> simp_all
  · exact fun hx C hC => hx C (nontautological_subset ψ hC)

/-- Combined nontautological filtering and subsumption reduction preserve `ClauseSet.Sat`. -/
theorem sat_reduce_nontautological_iff (ψ : ClauseSet V) (x : V → Bool) :
    (reduce (nontautological ψ)).Sat x ↔ ψ.Sat x :=
  sat_reduce_iff.trans (sat_nontautological_iff ψ x)

/-- Removing tautological clauses preserves `CNF.modelCountOn` on any declared variable set. -/
@[simp]
theorem modelCountOn_toCNF_nontautological (ψ : ClauseSet V) (declared : Finset V) :
    (nontautological ψ).toCNF.modelCountOn declared = ψ.toCNF.modelCountOn declared := by
  unfold CNF.modelCountOn
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and, ClauseSet.eval_toCNF_eq_true_iff,
    sat_nontautological_iff]

/-- Normalizing a clause set with `reduce (nontautological ψ)` preserves `CNF.modelCountOn` on any
declared variable set. -/
theorem modelCountOn_toCNF_reduce_nontautological (ψ : ClauseSet V) (declared : Finset V) :
    (reduce (nontautological ψ)).toCNF.modelCountOn declared = ψ.toCNF.modelCountOn declared := by
  rw [modelCountOn_toCNF_reduce, modelCountOn_toCNF_nontautological]

/-- **Nontautology preservation at leaves.** When `1 ≤ θ r` for all `r` and the root `ψ` has no
clause with complementary literals, every leaf `L ∈ countingLeaves θ ψ` is likewise free of
complementary literals within each clause. -/
theorem nontautological_of_mem_countingLeaves {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    {ψ L : ClauseSet V} (hnt : ∀ C ∈ ψ, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C)
    (hL : L ∈ countingLeaves θ ψ) :
    ∀ C ∈ L, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C := by
  suffices ∀ n (ψ : ClauseSet V), potential ψ = n →
      (∀ C ∈ ψ, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C) → L ∈ countingLeaves θ ψ →
      ∀ C ∈ L, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C from
    this (potential ψ) ψ rfl hnt hL
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ψ hp hnt hL
    rw [countingLeaves] at hL
    by_cases h : ¬ Sparse θ ψ ∧ 2 ≤ (flower ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2).card
    · rw [ite_eq_left h, List.mem_append] at hL
      set ch := chooseBranch θ ψ
      have hch := (choice_chooseBranch h.1).1
      rcases hL with hL | hL
      · have hlt := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 false
        exact ih _ (hp ▸ hlt) _ rfl (nontautological_countingChild hθ hnt hch false) hL
      · have hlt := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 true
        exact ih _ (hp ▸ hlt) _ rfl (nontautological_countingChild hθ hnt hch true) hL
    · rw [ite_eq_right h, List.mem_singleton] at hL
      exact hL ▸ hnt

/-! ### Branch-word representation bridge between `countingLeaves` and `CountingBranchingRule` -/

/-- The `CountingBranchingRule` on `ClauseSet V` instantiated with `CountingTree`'s deterministic
chooser `chooseBranch θ` and step `countingChild`. -/
noncomputable def countingTreeRule (θ : ℕ → ℕ) :
    CountingBranchingRule θ V (ClauseSet V) where
  toClauseSet ψ := ψ
  next ψ b := countingChild ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2 b
  exists_choice_next ψ hns :=
    ⟨(chooseBranch θ ψ).1, (chooseBranch θ ψ).2, choice_chooseBranch hns, fun _ => rfl⟩

/-- Branch-direction words (`false` for the heart child, `true` for the petal-plus-negated-units
child) corresponding 1-to-1 with the leaf occurrences in `countingLeaves θ ψ`. -/
noncomputable def countingLeafWords (θ : ℕ → ℕ) (ψ : ClauseSet V) : List (List Bool) :=
  open Classical in
  if ¬ Sparse θ ψ ∧ 2 ≤ (flower ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2).card then
    let ch := chooseBranch θ ψ
    (countingLeafWords θ (countingChild ψ ch.1 ch.2 false)).map (false :: ·) ++
      (countingLeafWords θ (countingChild ψ ch.1 ch.2 true)).map (true :: ·)
  else
    [[]]
termination_by potential ψ
decreasing_by
  · rename_i h
    exact potential_countingChild_lt_of_two_le_card_flower
      (choice_chooseBranch h.1).1.1 (choice_chooseBranch h.1).1.2.1 h.2 false
  · rename_i h
    exact potential_countingChild_lt_of_two_le_card_flower
      (choice_chooseBranch h.1).1.1 (choice_chooseBranch h.1).1.2.1 h.2 true

private theorem countingLeafWords_of_sparse {θ : ℕ → ℕ} {ψ : ClauseSet V} (h : Sparse θ ψ) :
    countingLeafWords θ ψ = [[]] := by
  rw [countingLeafWords]
  exact ite_eq_right fun h' => h'.1 h

private theorem countingLeafWords_of_not_sparse {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j)
    {ψ : ClauseSet V} (h : ¬ Sparse θ ψ) :
    countingLeafWords θ ψ =
      (countingLeafWords θ (countingChild ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2 false)).map
          (false :: ·) ++
        (countingLeafWords θ (countingChild ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2 true)).map
          (true :: ·) := by
  have hz : 2 ≤ (flower ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2).card :=
    two_le_card_flower_of_heavy hθ (choice_chooseBranch h).1
  rw [countingLeafWords]
  exact ite_eq_left ⟨h, hz⟩

/-- Walking `countingTreeRule θ` from `ψ` along the branch-word addresses in
`countingLeafWords θ ψ` reproduces `countingLeaves θ ψ` in exact list order, preserving
multiplicity across equal or unsatisfiable leaf clause sets. -/
theorem countingLeaves_eq_map_walk_countingLeafWords (θ : ℕ → ℕ) (ψ : ClauseSet V) :
    countingLeaves θ ψ = (countingLeafWords θ ψ).map ((countingTreeRule θ).walk ψ) := by
  induction hp : potential ψ using Nat.strong_induction_on generalizing ψ with
  | _ n ih =>
    rw [countingLeaves, countingLeafWords]
    by_cases h : ¬ Sparse θ ψ ∧ 2 ≤ (flower ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2).card
    · rw [ite_eq_left h, ite_eq_left h]
      dsimp only
      set ch := chooseBranch θ ψ
      have hch := (choice_chooseBranch h.1).1
      have hlt₀ := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 false
      have hlt₁ := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 true
      rw [List.map_append, List.map_map, List.map_map, ih _ (hp ▸ hlt₀) _ rfl,
        ih _ (hp ▸ hlt₁) _ rfl]
      rfl
    · rw [ite_eq_right h, ite_eq_right h]
      rfl

/-- The number of leaves in `countingLeaves θ ψ` (counted with list multiplicity) equals the
number of branch-word addresses in `countingLeafWords θ ψ`. -/
theorem length_countingLeaves_eq_length_countingLeafWords (θ : ℕ → ℕ) (ψ : ClauseSet V) :
    (countingLeaves θ ψ).length = (countingLeafWords θ ψ).length := by
  rw [countingLeaves_eq_map_walk_countingLeafWords, List.length_map]

/-- The branch-word addresses in `countingLeafWords θ ψ` are pairwise distinct. -/
theorem nodup_countingLeafWords (θ : ℕ → ℕ) (ψ : ClauseSet V) :
    (countingLeafWords θ ψ).Nodup := by
  induction hp : potential ψ using Nat.strong_induction_on generalizing ψ with
  | _ n ih =>
    rw [countingLeafWords]
    by_cases h : ¬ Sparse θ ψ ∧ 2 ≤ (flower ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2).card
    · rw [ite_eq_left h]
      set ch := chooseBranch θ ψ
      have hch := (choice_chooseBranch h.1).1
      have hlt₀ := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 false
      have hlt₁ := potential_countingChild_lt_of_two_le_card_flower hch.1 hch.2.1 h.2 true
      have hnodup₀ := (ih _ (hp ▸ hlt₀) _ rfl).map (List.cons_injective (a := false))
      have hnodup₁ := (ih _ (hp ▸ hlt₁) _ rfl).map (List.cons_injective (a := true))
      refine hnodup₀.append hnodup₁ (List.disjoint_left.mpr fun w hw₀ hw₁ => ?_)
      obtain ⟨u₀, -, rfl⟩ := List.mem_map.mp hw₀
      obtain ⟨u₁, -, hu₁⟩ := List.mem_map.mp hw₁
      exact Bool.false_ne_true (List.head_eq_of_cons_eq hu₁).symm
    · rw [ite_eq_right h]
      exact List.nodup_singleton []

/-- Because `countingLeafWords θ ψ` is duplicate-free, the list length `(countingLeaves θ ψ).length`
equals the cardinality of the address finset `(countingLeafWords θ ψ).toFinset`. -/
theorem length_countingLeaves_eq_card_toFinset_countingLeafWords (θ : ℕ → ℕ) (ψ : ClauseSet V) :
    (countingLeaves θ ψ).length = (countingLeafWords θ ψ).toFinset.card := by
  rw [length_countingLeaves_eq_length_countingLeafWords,
    List.toFinset_card_of_nodup (nodup_countingLeafWords θ ψ)]

private theorem mem_countingLeafWords_cons_iff {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j)
    {ψ : ClauseSet V} (hs : ¬ Sparse θ ψ) {b : Bool} {u : List Bool} :
    b :: u ∈ countingLeafWords θ ψ ↔
      u ∈ countingLeafWords θ (countingChild ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2 b) := by
  rw [countingLeafWords_of_not_sparse hθ hs, List.mem_append, List.mem_map, List.mem_map]
  cases b with
  | false =>
    constructor
    · rintro (⟨u', hu', heq⟩ | ⟨u', -, heq⟩)
      · exact (List.cons.inj heq).2 ▸ hu'
      · exact absurd (List.cons.inj heq).1.symm Bool.false_ne_true
    · intro hu
      exact Or.inl ⟨u, hu, rfl⟩
  | true =>
    constructor
    · rintro (⟨u', -, heq⟩ | ⟨u', hu', heq⟩)
      · exact absurd (List.cons.inj heq).1 Bool.false_ne_true
      · exact (List.cons.inj heq).2 ▸ hu'
    · intro hu
      exact Or.inr ⟨u, hu, rfl⟩

/-- When `∀ j, 1 ≤ j → 2 ≤ θ j`, `countingLeafWords θ ψ` enumerates data-exact the leaf words of
`countingTreeRule θ` starting from `ψ`. -/
theorem mem_countingLeafWords_iff_isLeafWord {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j)
    (ψ : ClauseSet V) (w : List Bool) :
    w ∈ countingLeafWords θ ψ ↔ (countingTreeRule θ).IsLeafWord ψ w := by
  induction hp : potential ψ using Nat.strong_induction_on generalizing ψ w with
  | _ n ih =>
    by_cases hs : Sparse θ ψ
    · rw [countingLeafWords_of_sparse hs, List.mem_singleton]
      cases w with
      | nil => exact ⟨fun _ => hs, fun _ => rfl⟩
      | cons b u =>
        exact ⟨fun h => absurd h (List.cons_ne_nil b u), fun hw => absurd hs hw.1⟩
    · cases w with
      | nil =>
        rw [countingLeafWords_of_not_sparse hθ hs, List.mem_append, List.mem_map, List.mem_map]
        refine ⟨?_, fun hw => absurd hw hs⟩
        rintro (⟨u, -, h⟩ | ⟨u, -, h⟩)
        · exact absurd h (List.cons_ne_nil false u)
        · exact absurd h (List.cons_ne_nil true u)
      | cons b u =>
        have hlt := potential_countingChild_lt hθ (choice_chooseBranch hs).1 b
        rw [mem_countingLeafWords_cons_iff hθ hs, ih _ (hp ▸ hlt) _ u rfl]
        exact ⟨fun hu => ⟨hs, hu⟩, fun hw => hw.2⟩

/-- When `∀ j, 1 ≤ j → 2 ≤ θ j`, every address `w ∈ countingLeafWords θ ψ` is a leaf word of
`countingTreeRule θ` starting from `ψ`. -/
theorem isLeafWord_of_mem_countingLeafWords {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j)
    {ψ : ClauseSet V} {w : List Bool} (hw : w ∈ countingLeafWords θ ψ) :
    (countingTreeRule θ).IsLeafWord ψ w :=
  (mem_countingLeafWords_iff_isLeafWord hθ ψ w).mp hw

/-! ### Leaf-count bounds for `countingLeaves` via `CountingBounds` -/

/-- **Appendix A.3 binomial-sum leaf-count bound for `countingLeaves`.**
For any geometric threshold base `M ≥ 2` and any reduced, nontautological clause set `ψ` of width
at most `k` whose occurring variables lie in `declared`, the number of leaves in
`countingLeaves (M ^ ·) ψ` (counted with list multiplicity) is at most
`∑_{j ≤ Γ |declared| / M} (C |declared| choose j)`, where `C = countingDepthCoeff k M` and
`Γ = countingBChoiceCoeff k`. -/
theorem length_countingLeaves_pow_le {k M : ℕ} (hM : 2 ≤ M)
    {ψ : ClauseSet V} (hred : Reduced ψ)
    (hnt : ∀ C ∈ ψ, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C)
    (hk : ∀ C ∈ ψ, C.card ≤ k) (declared : Finset V)
    (hsupport : ∀ C ∈ ψ, ∀ l ∈ C, l.1 ∈ declared) :
    (countingLeaves (M ^ ·) ψ).length ≤
      ∑ j ∈ range (countingBChoiceCoeff k * declared.card / M + 1),
        (countingDepthCoeff k M * declared.card).choose j := by
  have hθ : ∀ j, 1 ≤ j → 2 ≤ M ^ j := fun j hj =>
    hM.trans (by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < M) hj)
  rw [length_countingLeaves_eq_card_toFinset_countingLeafWords]
  exact CountingBranchingRule.card_le_of_isLeafWord (R := countingTreeRule (M ^ ·))
    hM hred hnt hk declared hsupport (countingLeafWords (M ^ ·) ψ).toFinset
    (fun w hw => isLeafWord_of_mem_countingLeafWords hθ (List.mem_toFinset.mp hw))

/-- **Leaf-count bound under explicit Appendix A.3 parameter-test hypotheses.**
When `2 ≤ M`, `1 ≤ B`, and (for `2 ≤ k`) `M` passes the integer budget test of Appendix A.3,
`countingLeaves` over `declared` (`declared.card ≤ n`) produces at most `2 ^ (n / B + 1)` leaves. -/
theorem length_countingLeaves_pow_le_two_pow_of_budget {k M B : ℕ}
    (hM : 2 ≤ M) (hB : 1 ≤ B)
    (hbudget : 2 ≤ k → countingBChoiceCoeff k ≤ M ∧
      B * countingBChoiceCoeff k * Nat.clog 2 (4 * countingDepthCoeff k M * M) ≤ M)
    {ψ : ClauseSet V} (hred : Reduced ψ)
    (hnt : ∀ C ∈ ψ, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C)
    (hk : ∀ C ∈ ψ, C.card ≤ k) (declared : Finset V)
    (hsupport : ∀ C ∈ ψ, ∀ l ∈ C, l.1 ∈ declared) {n : ℕ} (hn : declared.card ≤ n) :
    (countingLeaves (M ^ ·) ψ).length ≤ 2 ^ (n / B + 1) := by
  have hθ : ∀ j, 1 ≤ j → 2 ≤ M ^ j := fun j hj =>
    hM.trans (by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < M) hj)
  rw [length_countingLeaves_eq_card_toFinset_countingLeafWords]
  refine (CountingBranchingRule.card_le_two_pow_of_isLeafWord (R := countingTreeRule (M ^ ·))
    hM hred hnt hk declared hsupport hB hbudget (countingLeafWords (M ^ ·) ψ).toFinset
    (fun w hw => isLeafWord_of_mem_countingLeafWords hθ (List.mem_toFinset.mp hw))).trans ?_
  exact Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.add_le_add_right (Nat.div_le_div_right hn) 1)

/-- **Appendix A.3 `2 ^ (n / B + 1)` leaf-count bound at `countingThresholdBase k B`.**
For any width `k : ℕ`, inverse error budget `1 ≤ B`, and reduced, nontautological clause set `ψ`
of width at most `k` over `declared` (`declared.card ≤ n`), `countingLeaves` with threshold base
`countingThresholdBase k B` produces at most `2 ^ (n / B + 1)` leaves. -/
theorem length_countingLeaves_countingThresholdBase_le {k B : ℕ} (hB : 1 ≤ B)
    {ψ : ClauseSet V} (hred : Reduced ψ)
    (hnt : ∀ C ∈ ψ, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C)
    (hk : ∀ C ∈ ψ, C.card ≤ k) (declared : Finset V)
    (hsupport : ∀ C ∈ ψ, ∀ l ∈ C, l.1 ∈ declared) {n : ℕ} (hn : declared.card ≤ n) :
    (countingLeaves (fun j => (countingThresholdBase k B) ^ j) ψ).length ≤ 2 ^ (n / B + 1) :=
  length_countingLeaves_pow_le_two_pow_of_budget (two_le_countingThresholdBase k B) hB
    (fun hk2 => countingThresholdBase_spec hk2 hB) hred hnt hk declared hsupport hn

/-! ### Leaf occurrence and clause-count bounds for `countingLeaves` -/

/-- Every leaf `L ∈ countingLeaves θ ψ` of a width-`≤ k` root has variable occurrence degree at most
`2 * ∑ c ∈ range k, θ c` whenever `1 ≤ θ 0` and `2 ≤ θ j` for `1 ≤ j`. -/
theorem occurrences_le_of_mem_countingLeaves {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j)
    (hθ0 : 1 ≤ θ 0) {ψ L : ClauseSet V} {k : ℕ} (hk : ∀ C ∈ ψ, C.card ≤ k)
    (hL : L ∈ countingLeaves θ ψ) (v : V) :
    L.occurrences v ≤ 2 * ∑ c ∈ range k, θ c := by
  have hθ1 : ∀ j, 1 ≤ θ j := by
    intro j
    rcases j with _ | j
    · exact hθ0
    · exact (by decide : 1 ≤ 2).trans (hθ (j + 1) (by omega))
  exact occurrences_le_of_sparse hθ1 (sparse_of_mem_countingLeaves hθ hL)
    (card_le_of_mem_countingLeaves hk hL) v

/-- Every leaf `L ∈ countingLeaves θ ψ` of a width-`≤ k` root supported on `declared` has at most
`2 * (∑ c ∈ range k, θ c) * declared.card + 1` clauses. -/
theorem card_le_of_mem_countingLeaves_of_support {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j)
    (hθ0 : 1 ≤ θ 0) {ψ L : ClauseSet V} {k : ℕ} (hk : ∀ C ∈ ψ, C.card ≤ k)
    {declared : Finset V} (hsupport : ∀ C ∈ ψ, ∀ l ∈ C, l.1 ∈ declared)
    (hL : L ∈ countingLeaves θ ψ) :
    L.card ≤ 2 * (∑ c ∈ range k, θ c) * declared.card + 1 := by
  have hθ1 : ∀ j, 1 ≤ θ j := by
    intro j
    rcases j with _ | j
    · exact hθ0
    · exact (by decide : 1 ≤ 2).trans (hθ (j + 1) (by omega))
  exact card_le_of_sparse hθ1 (sparse_of_mem_countingLeaves hθ hL)
    (card_le_of_mem_countingLeaves hk hL) declared (support_of_mem_countingLeaves hsupport hL)

/-- Every leaf CNF `L.toCNF` (`L ∈ countingLeaves θ ψ`) of a width-`≤ k` root supported on
`declared` has length at most `2 * (∑ c ∈ range k, θ c) * declared.card + 1`. -/
theorem length_toCNF_le_of_mem_countingLeaves_of_support {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j)
    (hθ0 : 1 ≤ θ 0) {ψ L : ClauseSet V} {k : ℕ} (hk : ∀ C ∈ ψ, C.card ≤ k)
    {declared : Finset V} (hsupport : ∀ C ∈ ψ, ∀ l ∈ C, l.1 ∈ declared)
    (hL : L ∈ countingLeaves θ ψ) :
    L.toCNF.length ≤ 2 * (∑ c ∈ range k, θ c) * declared.card + 1 := by
  simpa only [ClauseSet.toCNF, List.length_map, Finset.length_toList] using
    card_le_of_mem_countingLeaves_of_support hθ hθ0 hk hsupport hL

/-! ### Unconditional CNF counting-sparsification corollaries -/

private theorem card_le_of_mem_toClauseSet {φ : CNF V} {k : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    {C : Finset (Literal V)} (hC : C ∈ φ.toClauseSet) : C.card ≤ k := by
  simp only [CNF.toClauseSet, List.mem_toFinset, List.mem_map] at hC
  obtain ⟨c, hc, rfl⟩ := hC
  exact List.toFinset_card_le c |>.trans (hk c hc)

private theorem support_of_mem_toClauseSet {φ : CNF V} {declared : Finset V}
    (hvars : φ.vars.toFinset ⊆ declared) {C : Finset (Literal V)} (hC : C ∈ φ.toClauseSet) :
    ∀ l ∈ C, l.1 ∈ declared := by
  intro l hl
  simp only [CNF.toClauseSet, List.mem_toFinset, List.mem_map] at hC
  obtain ⟨c, hc, rfl⟩ := hC
  exact hvars (List.mem_toFinset.mpr (CNF.mem_vars.mpr ⟨c, hc, l.2, List.mem_toFinset.mp hl⟩))

/-- **Normalized CNF assignment partition.**
Evaluating `L.toCNF` across the leaves of `reduce (nontautological φ.toClauseSet)` accepts each
assignment `x` at `1` leaf occurrence when `φ.eval x = true` and `0` otherwise. -/
theorem countP_eval_toCNF_countingLeaves_nontautological (θ : ℕ → ℕ) (φ : CNF V)
    (x : V → Bool) :
    ((countingLeaves θ (reduce (nontautological φ.toClauseSet))).map ClauseSet.toCNF).countP
        (fun F => F.eval x) =
      if φ.eval x then 1 else 0 := by
  rw [List.countP_map]
  have hcongr : (Function.comp (fun F : CNF V => F.eval x) ClauseSet.toCNF) =
      fun L : ClauseSet V => decide (L.Sat x) := by
    funext L
    exact Bool.eq_iff_iff.mpr
      ((ClauseSet.eval_toCNF_eq_true_iff L x).trans decide_eq_true_iff.symm)
  rw [hcongr, countP_sat_countingLeaves]
  by_cases hev : φ.eval x = true
  · have hsat : (reduce (nontautological φ.toClauseSet)).Sat x :=
      (sat_reduce_nontautological_iff φ.toClauseSet x).mpr ((CNF.sat_toClauseSet_iff φ x).mpr hev)
    rw [ite_eq_left hsat, ite_eq_left hev]
  · have hnsat : ¬ (reduce (nontautological φ.toClauseSet)).Sat x :=
      fun h => hev ((CNF.sat_toClauseSet_iff φ x).mp
        ((sat_reduce_nontautological_iff φ.toClauseSet x).mp h))
    rw [ite_eq_right hnsat, ite_eq_right hev]

/-- **Normalized CNF model-count conservation.**
Summing `L.toCNF.modelCountOn declared` across the leaves of
`reduce (nontautological φ.toClauseSet)` equals `φ.modelCountOn declared` without any
nontautology precondition on `φ`. -/
theorem sum_modelCountOn_countingLeaves_nontautological (θ : ℕ → ℕ) (φ : CNF V)
    (declared : Finset V) :
    ((countingLeaves θ (reduce (nontautological φ.toClauseSet))).map
      fun L => L.toCNF.modelCountOn declared).sum = φ.modelCountOn declared := by
  rw [sum_modelCountOn_countingLeaves, modelCountOn_toCNF_reduce_nontautological,
    modelCountOn_toCNF_toClauseSet]

/-- **CNF binomial-sum leaf-count bound.**
For any `2 ≤ M` and any width-`≤ k` formula `φ : CNF V` with `φ.vars.toFinset ⊆ declared`,
`countingLeaves (M ^ ·) (reduce (nontautological φ.toClauseSet))` has length at most
`∑_{j ≤ Γ |declared| / M} (C |declared| choose j)`. -/
theorem length_countingLeaves_nontautological_pow_le {k M : ℕ} (hM : 2 ≤ M)
    (φ : CNF V) (hk : ∀ c ∈ φ, c.length ≤ k) (declared : Finset V)
    (hvars : φ.vars.toFinset ⊆ declared) :
    (countingLeaves (M ^ ·) (reduce (nontautological φ.toClauseSet))).length ≤
      ∑ j ∈ range (countingBChoiceCoeff k * declared.card / M + 1),
        (countingDepthCoeff k M * declared.card).choose j :=
  length_countingLeaves_pow_le hM (reduced_reduce _)
    (fun _ hC => nontautological_of_mem_reduce_nontautological hC)
    (fun _ hC => card_le_of_mem_reduce_nontautological (fun _ => card_le_of_mem_toClauseSet hk) hC)
    declared
    (fun _ hC => support_of_mem_reduce_nontautological (fun _ => support_of_mem_toClauseSet hvars)
      hC)

/-- **CNF `2 ^ (n / B + 1)` leaf-count bound at `countingThresholdBase k B`.**
For any width `k : ℕ`, inverse error budget `1 ≤ B`, and width-`≤ k` formula `φ : CNF V` with
`φ.vars.toFinset ⊆ declared` and `declared.card ≤ n`,
`countingLeaves (fun j => (countingThresholdBase k B) ^ j) (reduce (nontautological φ.toClauseSet))`
has length at most `2 ^ (n / B + 1)`. -/
theorem length_countingLeaves_nontautological_thresholdBase_le {k B : ℕ}
    (hB : 1 ≤ B) (φ : CNF V) (hk : ∀ c ∈ φ, c.length ≤ k) (declared : Finset V)
    (hvars : φ.vars.toFinset ⊆ declared) {n : ℕ} (hn : declared.card ≤ n) :
    (countingLeaves (fun j => (countingThresholdBase k B) ^ j)
        (reduce (nontautological φ.toClauseSet))).length ≤
      2 ^ (n / B + 1) :=
  length_countingLeaves_countingThresholdBase_le hB (reduced_reduce _)
    (fun _ hC => nontautological_of_mem_reduce_nontautological hC)
    (fun _ hC => card_le_of_mem_reduce_nontautological (fun _ => card_le_of_mem_toClauseSet hk) hC)
    declared
    (fun _ hC => support_of_mem_reduce_nontautological (fun _ => support_of_mem_toClauseSet hvars)
      hC)
    hn

/-- **Combined Lemma 6.3 / Appendix A counting-sparsification leaf decomposition for CNFs.**
For any width `k : ℕ`, inverse error budget `1 ≤ B`, and width-`≤ k` formula `φ : CNF V` with
occurring variables in `declared` (`declared.card ≤ n`), the leaf list
`countingLeaves (fun j => (countingThresholdBase k B) ^ j) (reduce (nontautological φ.toClauseSet))`
satisfies:
1. exact additive `modelCountOn declared` conservation,
2. exact `0`/`1` assignment partition across `map ClauseSet.toCNF`,
3. leaf count at most `2 ^ (n / B + 1)`, and
4. at every leaf `L`: sparsity, reducedness, nontautology, clause width `≤ k`, support in
   `declared`, variable occurrence degree at most `2 * ∑ c ∈ range k, M ^ c`, and clause count at
   most `2 * (∑ c ∈ range k, M ^ c) * declared.card + 1` where `M = countingThresholdBase k B`. -/
theorem countingLeaves_nontautological_thresholdBase_spec {k B : ℕ}
    (hB : 1 ≤ B) (φ : CNF V) (hk : ∀ c ∈ φ, c.length ≤ k) (declared : Finset V)
    (hvars : φ.vars.toFinset ⊆ declared) {n : ℕ} (hn : declared.card ≤ n) :
    let θ := fun j => (countingThresholdBase k B) ^ j
    let ψ₀ := reduce (nontautological φ.toClauseSet)
    ((countingLeaves θ ψ₀).map fun L => L.toCNF.modelCountOn declared).sum =
        φ.modelCountOn declared ∧
      (∀ x : V → Bool,
        ((countingLeaves θ ψ₀).map ClauseSet.toCNF).countP (fun F => F.eval x) =
          if φ.eval x then 1 else 0) ∧
      (countingLeaves θ ψ₀).length ≤ 2 ^ (n / B + 1) ∧
      ∀ L ∈ countingLeaves θ ψ₀,
        Sparse θ L ∧ Reduced L ∧
          (∀ C ∈ L, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C) ∧
          (∀ C ∈ L, C.card ≤ k) ∧
          (∀ C ∈ L, ∀ l ∈ C, l.1 ∈ declared) ∧
          (∀ v, L.occurrences v ≤ 2 * ∑ c ∈ range k, θ c) ∧
          L.card ≤ 2 * (∑ c ∈ range k, θ c) * declared.card + 1 := by
  intro θ ψ₀
  have hM : 2 ≤ countingThresholdBase k B := two_le_countingThresholdBase k B
  have hθ : ∀ j, 1 ≤ j → 2 ≤ θ j := fun j hj =>
    hM.trans (by simpa only [θ, pow_one] using Nat.pow_le_pow_right (by omega) hj)
  have hθ1 : ∀ r, 1 ≤ θ r := fun r => Nat.one_le_pow r _ (by omega)
  have hred : Reduced ψ₀ := reduced_reduce _
  have hnt : ∀ C ∈ ψ₀, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C :=
    fun _ hC => nontautological_of_mem_reduce_nontautological hC
  have hk0 : ∀ C ∈ ψ₀, C.card ≤ k :=
    fun _ hC => card_le_of_mem_reduce_nontautological (fun _ => card_le_of_mem_toClauseSet hk) hC
  have hsup0 : ∀ C ∈ ψ₀, ∀ l ∈ C, l.1 ∈ declared :=
    fun _ hC => support_of_mem_reduce_nontautological (fun _ => support_of_mem_toClauseSet hvars) hC
  refine ⟨sum_modelCountOn_countingLeaves_nontautological θ φ declared,
    countP_eval_toCNF_countingLeaves_nontautological θ φ,
    length_countingLeaves_nontautological_thresholdBase_le hB φ hk declared hvars hn,
    fun L hL => ⟨sparse_of_mem_countingLeaves hθ hL,
      reduced_of_mem_countingLeaves hred hL,
      nontautological_of_mem_countingLeaves hθ1 hnt hL,
      card_le_of_mem_countingLeaves hk0 hL,
      support_of_mem_countingLeaves hsup0 hL,
      occurrences_le_of_mem_countingLeaves hθ (hθ1 0) hk0 hL,
      card_le_of_mem_countingLeaves_of_support hθ (hθ1 0) hk0 hsup0 hL⟩⟩

end Cslib.Logic.PL.ClauseSet.Sparsification
