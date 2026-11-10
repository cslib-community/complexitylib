/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Powerset
import Complexity.Foundations.Combinatorics.FunctionalGraph.PeriodicPts

/-!
# Shapley–Scarf housing markets

This module sets up the housing market of [ShapleyScarf1974]: `n` agents, indexed by `Fin n`, each
owning one indivisible house (agent `i` owns house `i`) and each with a strict and complete
preference order over all `n` houses. An agent need not prefer its own house to the others.
Preferences follow the conventions of `Cslib.Algorithms.Lean.StableMatching`: `pref i k` is
agent `i`'s `k`-th choice, with rank `0` the favourite, and `rank i h` is the rank of house `h`.

An allocation is a permutation `μ` giving house `μ i` to agent `i`; the identity is the initial
endowment. A coalition `S` can reallocate only its own houses, so its feasible allocations are the
permutations `ν` with `ν i ∈ S` for every `i ∈ S` (the set `A(S)` of [SchummerVohra2007], §10.3).

Two cooperative solution concepts are distinguished, following [RothPostlewaite1977]:

* `S` *blocks* `μ` when some reallocation within `S` makes every member strictly better off; the
  **core** consists of the allocations no coalition blocks.
* `S` *weakly blocks* `μ` when some reallocation within `S` makes every member weakly better off
  and some member strictly better off; the **strict core** consists of the allocations no
  coalition weakly blocks. [SchummerVohra2007], §10.3, calls this set the core.

[SchummerVohra2007], p. 255, asserts that the core and the strict core coincide when preferences
are strict. With the definitions here they do not: a weakly blocking coalition may contain a member
who keeps the house `μ` gave it, which need not be its own house, so it cannot always be dropped.

With strict preferences the strict core is a single allocation, computed by top trading cycles
(`Cslib.Algorithms.Lean.HousingMarket.Instance.inStrictCore_iff`). The core can be strictly
larger; the test module `ComplexityTests.HousingMarket` exhibits a three-agent market with an
allocation in the core but not in the strict core.

An allocation `μ` is *competitive* at prices `p` when every agent can afford its house
(`p (μ i) ≤ p i`: the price of its new house is at most the price of the house it sells) and
prefers it to every house it can afford. Competitive allocations lie in the strict core
(`IsCompetitive.inStrictCore`), using budget balance: since `μ` permutes the houses, no agent
pays less than it receives.

## Main definitions

* `Cslib.Algorithms.Lean.HousingMarket.Instance`: a housing market with strict preferences.
* `Cslib.Algorithms.Lean.HousingMarket.Allocation`: allocations as permutations.
* `Instance.Blocks`, `Instance.WeaklyBlocks`, `Instance.InCore`, `Instance.InStrictCore`.
* `Instance.IsIndividuallyRational`, `Instance.IsParetoEfficient`.
* `Instance.IsCompetitive`: competitive allocations at given prices.

## Main results

* `Instance.InStrictCore.inCore`, `Instance.InStrictCore.isIndividuallyRational`,
  `Instance.InStrictCore.isParetoEfficient`: the strict core lies in the core, and its allocations
  are individually rational and Pareto efficient.
* `Instance.IsCompetitive.inStrictCore`: competitive allocations lie in the strict core
  ([RothPostlewaite1977]).

## References

* [ShapleyScarf1974]
* [RothPostlewaite1977]
* [SchummerVohra2007]
-/

public section

namespace Cslib.Algorithms.Lean.HousingMarket

/-- A Shapley–Scarf housing market with `n` agents and `n` houses, both indexed by `Fin n`; agent
`i` initially owns house `i`. `pref i k` is agent `i`'s `k`-th choice of house (rank `0` is the most
preferred). Preferences are strict and complete. -/
structure Instance (n : ℕ) where
  /-- Agent `i`'s preference list over houses, from most to least preferred. -/
  pref : Fin n → Equiv.Perm (Fin n)

/-- An allocation gives house `μ i` to agent `i`. The identity is the initial endowment. -/
abbrev Allocation (n : ℕ) := Equiv.Perm (Fin n)

namespace Instance

variable {n : ℕ} (I : Instance n)

/-- The rank of house `h` in agent `i`'s list (`0` is the favourite). -/
@[expose] def rank (i h : Fin n) : Fin n := (I.pref i).symm h

theorem rank_injective (i : Fin n) : Function.Injective (I.rank i) :=
  (I.pref i).symm.injective

@[simp] theorem rank_pref (i k : Fin n) : I.rank i (I.pref i k) = k :=
  (I.pref i).symm_apply_apply k

@[simp] theorem pref_rank (i h : Fin n) : I.pref i (I.rank i h) = h :=
  (I.pref i).apply_symm_apply h

/-! ### Blocking coalitions and the core -/

/-- Coalition `S` blocks `μ`: `S` is nonempty and some reallocation `ν` of the houses of `S` among
the members of `S` gives every member a house it strictly prefers to its house in `μ`. -/
@[expose] def Blocks (μ : Allocation n) (S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧ ∃ ν : Allocation n, (∀ i ∈ S, ν i ∈ S) ∧ ∀ i ∈ S, I.rank i (ν i) < I.rank i (μ i)

/-- Coalition `S` weakly blocks `μ`: some reallocation `ν` of the houses of `S` among the members
of `S` gives every member a house it weakly prefers to its house in `μ`, and some member a house
it strictly prefers. -/
@[expose] def WeaklyBlocks (μ : Allocation n) (S : Finset (Fin n)) : Prop :=
  ∃ ν : Allocation n, (∀ i ∈ S, ν i ∈ S) ∧ (∀ i ∈ S, I.rank i (ν i) ≤ I.rank i (μ i)) ∧
    ∃ i ∈ S, I.rank i (ν i) < I.rank i (μ i)

/-- `μ` is in the core: no coalition blocks it. -/
@[expose] def InCore (μ : Allocation n) : Prop := ∀ S, ¬ I.Blocks μ S

/-- `μ` is in the strict core: no coalition weakly blocks it. -/
@[expose] def InStrictCore (μ : Allocation n) : Prop := ∀ S, ¬ I.WeaklyBlocks μ S

/-- `μ` is individually rational: every agent weakly prefers its house to its own. -/
@[expose] def IsIndividuallyRational (μ : Allocation n) : Prop :=
  ∀ i, I.rank i (μ i) ≤ I.rank i i

/-- `μ` is Pareto efficient: no allocation makes every agent weakly better off and some agent
strictly better off. -/
@[expose] def IsParetoEfficient (μ : Allocation n) : Prop :=
  ¬ ∃ ν : Allocation n, (∀ i, I.rank i (ν i) ≤ I.rank i (μ i)) ∧
    ∃ i, I.rank i (ν i) < I.rank i (μ i)

instance (μ : Allocation n) (S : Finset (Fin n)) : Decidable (I.Blocks μ S) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (μ : Allocation n) (S : Finset (Fin n)) : Decidable (I.WeaklyBlocks μ S) :=
  inferInstanceAs (Decidable (∃ _, _))

instance (μ : Allocation n) : Decidable (I.InCore μ) :=
  inferInstanceAs (Decidable (∀ _, _))

instance (μ : Allocation n) : Decidable (I.InStrictCore μ) :=
  inferInstanceAs (Decidable (∀ _, _))

instance (μ : Allocation n) : Decidable (I.IsIndividuallyRational μ) :=
  inferInstanceAs (Decidable (∀ _, _))

instance (μ : Allocation n) : Decidable (I.IsParetoEfficient μ) :=
  inferInstanceAs (Decidable (¬ _))

variable {I}

theorem Blocks.weaklyBlocks {μ : Allocation n} {S : Finset (Fin n)} (h : I.Blocks μ S) :
    I.WeaklyBlocks μ S := by
  obtain ⟨⟨i, hi⟩, ν, hS, hlt⟩ := h
  exact ⟨ν, hS, fun j hj => (hlt j hj).le, i, hi, hlt i hi⟩

/-- The strict core is contained in the core. -/
theorem InStrictCore.inCore {μ : Allocation n} (h : I.InStrictCore μ) : I.InCore μ :=
  fun S hS => h S hS.weaklyBlocks

/-- Strict-core allocations are individually rational: otherwise an agent blocks alone by keeping
its own house. -/
theorem InStrictCore.isIndividuallyRational {μ : Allocation n} (h : I.InStrictCore μ) :
    I.IsIndividuallyRational μ := by
  intro i
  by_contra hlt
  refine h {i} ⟨1, fun j hj => hj, fun j hj => ?_, i, Finset.mem_singleton_self i, not_le.1 hlt⟩
  rw [Finset.mem_singleton.1 hj]
  exact (not_le.1 hlt).le

/-- Strict-core allocations are Pareto efficient: otherwise the grand coalition weakly blocks. -/
theorem InStrictCore.isParetoEfficient {μ : Allocation n} (h : I.InStrictCore μ) :
    I.IsParetoEfficient μ := by
  rintro ⟨ν, hle, i, hi⟩
  exact h Finset.univ ⟨ν, fun j _ => Finset.mem_univ _, fun j _ => hle j, i, Finset.mem_univ _, hi⟩

/-! ### Competitive allocations -/

variable (I) in
/-- `μ` is competitive at prices `p`: every agent `i` can afford its house, `p (μ i) ≤ p i`, and
weakly prefers it to every house `h` it can afford, `p h ≤ p i`. Prices take values in any linear
order. -/
@[expose] def IsCompetitive {α : Type*} [LinearOrder α] (μ : Allocation n) (p : Fin n → α) :
    Prop :=
  ∀ i, p (μ i) ≤ p i ∧ ∀ h, p h ≤ p i → I.rank i (μ i) ≤ I.rank i h

instance {α : Type*} [LinearOrder α] (μ : Allocation n) (p : Fin n → α) :
    Decidable (I.IsCompetitive μ p) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- Budget balance: at competitive prices every agent pays exactly the price of its own house,
because the allocation is a permutation. -/
theorem IsCompetitive.price_apply {α : Type*} [LinearOrder α] {μ : Allocation n}
    {p : Fin n → α} (h : I.IsCompetitive μ p) (i : Fin n) : p (μ i) = p i :=
  le_antisymm (h i).1 (Cslib.FunctionalGraph.apply_le_of_mem_periodicPts (β := αᵒᵈ)
    (s := Set.univ) (Set.mapsTo_univ _ _) (fun j _ => (h j).1)
    (μ.injective.mem_periodicPts i) (Set.mem_univ i))

/-- Competitive allocations lie in the strict core ([RothPostlewaite1977]). In a weakly blocking
coalition nobody trades down in price, and some member trades up to a house it could not afford;
following the reallocation around that member's cycle gives a contradiction. -/
theorem IsCompetitive.inStrictCore {α : Type*} [LinearOrder α] {μ : Allocation n}
    {p : Fin n → α} (h : I.IsCompetitive μ p) : I.InStrictCore μ := by
  rintro S ⟨ν, hS, hle, j, hj, hlt⟩
  have hup : ∀ i ∈ (S : Set (Fin n)), p i ≤ p (ν i) := by
    intro i hi
    by_contra hpi
    have heq := I.rank_injective i (le_antisymm (hle i hi) ((h i).2 (ν i) (not_le.1 hpi).le))
    rw [heq, h.price_apply] at hpi
    exact hpi le_rfl
  have hj' : p j < p (ν j) := by
    by_contra hpj
    exact absurd ((h j).2 (ν j) (not_lt.1 hpj)) (not_le.2 hlt)
  exact absurd (Cslib.FunctionalGraph.apply_le_of_mem_periodicPts (fun i hi => hS i hi) hup
    (ν.injective.mem_periodicPts j) hj) (not_le.2 hj')

end Instance

end Cslib.Algorithms.Lean.HousingMarket
