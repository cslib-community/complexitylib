/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.HousingMarket.Basic
public import Complexity.Algorithms.Lean.StableMatching.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Dynamics.PeriodicPts.Defs
import Complexity.Foundations.Combinatorics.FunctionalGraph
import Mathlib.Data.Set.Finite.Basic

/-!
# Gale's top trading cycles

This module implements Gale's top trading cycles algorithm (TTC) for the Shapley–Scarf housing
market ([ShapleyScarf1974], where it is credited to David Gale) as a total, `decide`-evaluable
Lean function, and proves that its allocation is the unique allocation in the strict core
([RothPostlewaite1977]; [SchummerVohra2007], Theorem 10.6; [Roughgarden2013CS364A], Lecture 9,
Theorem 3.2) and the unique competitive allocation.

While agents remain, every remaining agent points to the owner of its favourite remaining house,
`topChoice R i`. Each agent has one outgoing pointer, so the pointer graph has a cycle; the
agents on its cycles (`cycleAgents R`, the periodic points of `topChoice R`) receive the houses they
point to and leave with their houses. `ttcRounds k R` runs at most `k` such rounds starting from
the remaining agents `R`; every round removes at least one agent (`card_sdiff_cycleAgents_lt`), so
`n` rounds suffice and `ttc` is `ttcRounds n univ`. All cycles of a round are removed together, as
in [SchummerVohra2007], Definition 10.5; removing them one at a time yields the same allocation,
which is not stated here.

`ttcPrice h` is the number of agents present in the round in which house `h` leaves. These prices
decrease from round to round, every agent receives a house of the same price as its own, and at
these prices TTC is a competitive allocation (`isCompetitive_ttc`).

## Main definitions

* `Instance.topChoice`: an agent's favourite house among the remaining ones.
* `Instance.cycleAgents`: the agents on cycles of the pointer map.
* `Instance.ttcRounds`, `Instance.ttc`: rounds of TTC and the TTC allocation.
* `Instance.ttcPriceRounds`, `Instance.ttcPrice`: the round size at which a house leaves.

## Main results

* `Instance.mem_cycleAgents`, `Instance.cycleAgents_nonempty`: the agents removed in a round are
  the periodic points of the pointer map, and some agent is removed.
* `Instance.inStrictCore_ttc`, `Instance.inCore_ttc`, `Instance.isIndividuallyRational_ttc`,
  `Instance.isParetoEfficient_ttc`: the TTC allocation is in the strict core, hence in the core,
  individually rational and Pareto efficient.
* `Instance.InStrictCore.eq_ttc`, `Instance.inStrictCore_iff`: it is the only strict-core
  allocation ([RothPostlewaite1977]).
* `Instance.isCompetitive_ttc`, `Instance.exists_isCompetitive_iff`: TTC is competitive at the
  prices `ttcPrice`, and it is the only allocation that is competitive at some prices
  ([ShapleyScarf1974]; [RothPostlewaite1977]).
* `Instance.rank_ttcRounds_le_of_iterate`: an agent reached along pointers from house `h` receives a
  house it weakly prefers to `h`; this drives strategy-proofness in
  `Complexity.Algorithms.Lean.HousingMarket.Incentives`.

## Cost model

No running time is certified: `ttcRounds` recomputes cycles from scratch each round and is meant
for specification and kernel evaluation on small instances, not as an efficient implementation.

## References

* [ShapleyScarf1974]
* [RothPostlewaite1977]
* [SchummerVohra2007]
* [Roughgarden2013CS364A]
-/

public section

namespace Cslib.Algorithms.Lean.HousingMarket

open Function

namespace Instance

variable {n : ℕ} (I : Instance n)

/-! ### Pointers and cycles -/

/-- Agent `i`'s favourite house among the houses `R` (agent `i` itself when `R` is empty). -/
@[expose] def topChoice (R : Finset (Fin n)) (i : Fin n) : Fin n :=
  if h : R.Nonempty then I.pref i ((R.image (I.rank i)).min' (h.image _)) else i

/-- The agents of `R` on a cycle of the pointer map `topChoice R`: those that return to themselves
after following at most `n` pointers. -/
@[expose] def cycleAgents (R : Finset (Fin n)) : Finset (Fin n) :=
  R.filter fun i => ∃ k : Fin n, (I.topChoice R)^[k.val + 1] i = i

/-- At most `k` rounds of top trading cycles on the remaining agents `R`: each agent on a cycle of
the pointer map receives the house it points to, and the rest continue with the remaining
houses. Agents outside `R` keep their own houses. -/
@[expose] def ttcRounds : ℕ → Finset (Fin n) → Fin n → Fin n
  | 0, _, i => i
  | k + 1, R, i =>
    if i ∈ I.cycleAgents R then I.topChoice R i else ttcRounds k (R \ I.cycleAgents R) i

/-- The number of remaining agents in the round, among at most `k` rounds started from `R`, in
which house `h` leaves (`0` if it does not leave). -/
@[expose] def ttcPriceRounds : ℕ → Finset (Fin n) → Fin n → ℕ
  | 0, _, _ => 0
  | k + 1, R, h =>
    if h ∈ I.cycleAgents R then R.card else ttcPriceRounds k (R \ I.cycleAgents R) h

/-- The TTC price of house `h`: the number of agents present in the round in which `h` leaves. -/
@[expose] def ttcPrice (h : Fin n) : ℕ := I.ttcPriceRounds n Finset.univ h

variable {I}

theorem topChoice_mem {R : Finset (Fin n)} (hR : R.Nonempty) (i : Fin n) : I.topChoice R i ∈ R := by
  rw [topChoice, dite_eq_left hR]
  obtain ⟨h, hh, hmin⟩ := Finset.mem_image.1 ((R.image (I.rank i)).min'_mem (hR.image _))
  rw [← hmin, pref_rank]
  exact hh

/-- An agent weakly prefers its favourite house in `R` to every house in `R`. -/
theorem rank_topChoice_le {R : Finset (Fin n)} {h : Fin n} (hh : h ∈ R) (i : Fin n) :
    I.rank i (I.topChoice R i) ≤ I.rank i h := by
  rw [topChoice, dite_eq_left ⟨h, hh⟩, rank_pref]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hh)

theorem topChoice_eq_of_forall {R : Finset (Fin n)} {i h : Fin n} (hh : h ∈ R)
    (hmin : ∀ h' ∈ R, I.rank i h ≤ I.rank i h') : I.topChoice R i = h :=
  I.rank_injective i (le_antisymm (rank_topChoice_le hh i) (hmin _ (topChoice_mem ⟨h, hh⟩ i)))

/-- Removing houses other than an agent's favourite does not change its favourite. -/
theorem topChoice_of_subset {R R' : Finset (Fin n)} (hRR' : R' ⊆ R) {i : Fin n}
    (hi : I.topChoice R i ∈ R') : I.topChoice R' i = I.topChoice R i :=
  topChoice_eq_of_forall hi fun _ hh' => rank_topChoice_le (hRR' hh') i

theorem cycleAgents_subset (R : Finset (Fin n)) : I.cycleAgents R ⊆ R :=
  Finset.filter_subset _ _

/-- The agents removed in a round are exactly the periodic points of the pointer map. -/
theorem mem_cycleAgents {R : Finset (Fin n)} (hR : R.Nonempty) {i : Fin n} :
    i ∈ I.cycleAgents R ↔ i ∈ periodicPts (I.topChoice R) := by
  rw [cycleAgents, Finset.mem_filter]
  constructor
  · rintro ⟨-, k, hk⟩
    exact mk_mem_periodicPts k.val.succ_pos hk
  · intro hi
    have hpos := minimalPeriod_pos_of_mem_periodicPts hi
    have hle : minimalPeriod (I.topChoice R) i ≤ n := by
      simpa only [Fintype.card_fin] using minimalPeriod_le_card (f := I.topChoice R) (x := i)
    have hfix : (I.topChoice R)^[minimalPeriod (I.topChoice R) i] i = i := iterate_minimalPeriod
    refine ⟨?_, ⟨minimalPeriod (I.topChoice R) i - 1, by omega⟩, ?_⟩
    · rw [← hfix, ← Nat.succ_pred_eq_of_pos hpos, iterate_succ_apply']
      exact topChoice_mem hR _
    · rw [Nat.sub_add_cancel hpos]
      exact hfix

/-- An agent on a cycle points to an agent on a cycle. -/
theorem topChoice_mem_cycleAgents {R : Finset (Fin n)} {i : Fin n} (hi : i ∈ I.cycleAgents R) :
    I.topChoice R i ∈ I.cycleAgents R := by
  have hR : R.Nonempty := ⟨i, cycleAgents_subset R hi⟩
  rw [mem_cycleAgents hR] at hi ⊢
  exact (bijOn_periodicPts _).mapsTo hi

/-- No two agents on cycles point to the same house. -/
theorem topChoice_injOn_cycleAgents (R : Finset (Fin n)) :
    Set.InjOn (I.topChoice R) (I.cycleAgents R) := by
  intro a ha b hb hab
  have hR : R.Nonempty := ⟨a, cycleAgents_subset R ha⟩
  rw [Finset.mem_coe, mem_cycleAgents hR] at ha hb
  exact (bijOn_periodicPts _).injOn ha hb hab

/-- Every round removes some agent. -/
theorem cycleAgents_nonempty {R : Finset (Fin n)} (hR : R.Nonempty) :
    (I.cycleAgents R).Nonempty := by
  obtain ⟨i, -⟩ := id hR
  obtain ⟨t, ht⟩ := Cslib.FunctionalGraph.exists_iterate_mem_periodicPts (I.topChoice R) i
  exact ⟨_, (mem_cycleAgents hR).2 ht⟩

theorem card_sdiff_cycleAgents_lt {R : Finset (Fin n)} (hR : R.Nonempty) :
    (R \ I.cycleAgents R).card < R.card :=
  Finset.card_lt_card (Finset.sdiff_ssubset (cycleAgents_subset R) (cycleAgents_nonempty hR))

/-! ### Rounds -/

theorem ttcRounds_succ_of_mem {k : ℕ} {R : Finset (Fin n)} {i : Fin n}
    (hi : i ∈ I.cycleAgents R) : I.ttcRounds (k + 1) R i = I.topChoice R i :=
  ite_eq_left hi

theorem ttcRounds_succ_of_notMem {k : ℕ} {R : Finset (Fin n)} {i : Fin n}
    (hi : i ∉ I.cycleAgents R) : I.ttcRounds (k + 1) R i = I.ttcRounds k (R \ I.cycleAgents R) i :=
  ite_eq_right hi

theorem ttcPriceRounds_succ_of_mem {k : ℕ} {R : Finset (Fin n)} {h : Fin n}
    (hh : h ∈ I.cycleAgents R) : I.ttcPriceRounds (k + 1) R h = R.card :=
  ite_eq_left hh

theorem ttcPriceRounds_succ_of_notMem {k : ℕ} {R : Finset (Fin n)} {h : Fin n}
    (hh : h ∉ I.cycleAgents R) :
    I.ttcPriceRounds (k + 1) R h = I.ttcPriceRounds k (R \ I.cycleAgents R) h :=
  ite_eq_right hh

/-- With `R.card ≤ k + 1` and `R` nonempty, the next round starts with at most `k` agents. -/
private theorem card_sdiff_cycleAgents_le {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k + 1)
    (hR : R.Nonempty) : (R \ I.cycleAgents R).card ≤ k := by
  have := card_sdiff_cycleAgents_lt (I := I) hR
  omega

/-- Agents that are no longer present keep their own houses. -/
theorem ttcRounds_of_notMem {k : ℕ} {R : Finset (Fin n)} {i : Fin n} (hi : i ∉ R) :
    I.ttcRounds k R i = i := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [ttcRounds_succ_of_notMem fun h => hi (cycleAgents_subset R h)]
    exact ih fun h => hi (Finset.sdiff_subset h)

theorem ttcRounds_mem {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k) {i : Fin n} (hi : i ∈ R) :
    I.ttcRounds k R i ∈ R := by
  induction k generalizing R with
  | zero => simp_all
  | succ k ih =>
    have hR : R.Nonempty := ⟨i, hi⟩
    by_cases hC : i ∈ I.cycleAgents R
    · rw [ttcRounds_succ_of_mem hC]
      exact topChoice_mem hR i
    · rw [ttcRounds_succ_of_notMem hC]
      exact Finset.sdiff_subset
        (ih (card_sdiff_cycleAgents_le hk hR) (Finset.mem_sdiff.2 ⟨hi, hC⟩))

theorem ttcRounds_injOn {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k) :
    Set.InjOn (I.ttcRounds k R) R := by
  induction k generalizing R with
  | zero =>
    intro a ha
    simp_all
  | succ k ih =>
    intro a ha b hb hab
    have hR : R.Nonempty := ⟨a, ha⟩
    have hk' := card_sdiff_cycleAgents_le (I := I) hk hR
    by_cases hCa : a ∈ I.cycleAgents R <;> by_cases hCb : b ∈ I.cycleAgents R
    · rw [ttcRounds_succ_of_mem hCa, ttcRounds_succ_of_mem hCb] at hab
      exact topChoice_injOn_cycleAgents R hCa hCb hab
    · rw [ttcRounds_succ_of_mem hCa, ttcRounds_succ_of_notMem hCb] at hab
      exact absurd (hab ▸ topChoice_mem_cycleAgents hCa)
        (Finset.mem_sdiff.1 (ttcRounds_mem hk' (Finset.mem_sdiff.2 ⟨hb, hCb⟩))).2
    · rw [ttcRounds_succ_of_notMem hCa, ttcRounds_succ_of_mem hCb] at hab
      exact absurd (hab ▸ topChoice_mem_cycleAgents hCb)
        (Finset.mem_sdiff.1 (ttcRounds_mem hk' (Finset.mem_sdiff.2 ⟨ha, hCa⟩))).2
    · rw [ttcRounds_succ_of_notMem hCa, ttcRounds_succ_of_notMem hCb] at hab
      exact ih hk' (Finset.mem_sdiff.2 ⟨ha, hCa⟩) (Finset.mem_sdiff.2 ⟨hb, hCb⟩) hab

variable (I)

theorem ttcRounds_injective {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k) :
    Injective (I.ttcRounds k R) := by
  intro a b hab
  by_cases ha : a ∈ R <;> by_cases hb : b ∈ R
  · exact ttcRounds_injOn hk ha hb hab
  · rw [ttcRounds_of_notMem hb] at hab
    exact absurd (hab ▸ ttcRounds_mem hk ha) hb
  · rw [ttcRounds_of_notMem ha] at hab
    exact absurd (hab ▸ ttcRounds_mem hk hb) ha
  · rwa [ttcRounds_of_notMem ha, ttcRounds_of_notMem hb] at hab

/-- The top trading cycles allocation: `n` rounds of TTC starting from all agents. -/
@[expose] def ttc : Allocation n :=
  StableMatching.permOfInjective (I.ttcRounds n Finset.univ)
    (I.ttcRounds_injective (by rw [Finset.card_univ, Fintype.card_fin]))

theorem ttc_apply (i : Fin n) : I.ttc i = I.ttcRounds n Finset.univ i := rfl

variable {I}

/-! ### The strict core -/

/-- In a submarket `R` run for enough rounds, if a reallocation `ν` within `S ⊆ R` gives every
member of `S` a house it weakly prefers to its TTC house, then `ν` agrees with TTC on `S`. -/
private theorem eq_ttcRounds_of_le {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k)
    (ν : Allocation n) (S : Finset (Fin n)) (hSR : S ⊆ R) (hS : ∀ i ∈ S, ν i ∈ S)
    (hle : ∀ i ∈ S, I.rank i (ν i) ≤ I.rank i (I.ttcRounds k R i)) :
    ∀ i ∈ S, ν i = I.ttcRounds k R i := by
  induction k generalizing R S with
  | zero =>
    intro i hi
    have := hSR hi
    simp_all
  | succ k ih =>
    intro i hi
    have hR : R.Nonempty := ⟨i, hSR hi⟩
    have hk' := card_sdiff_cycleAgents_le (I := I) hk hR
    set C := I.cycleAgents R
    -- members of `S` on a cycle get their favourite remaining house
    have hC : ∀ a ∈ S, a ∈ C → ν a = I.topChoice R a := by
      intro a ha haC
      have h1 := hle a ha
      rw [ttcRounds_succ_of_mem haC] at h1
      exact I.rank_injective a (le_antisymm h1 (rank_topChoice_le (hSR (hS a ha)) a))
    by_cases hiC : i ∈ C
    · rw [hC i hi hiC, ttcRounds_succ_of_mem hiC]
    rw [ttcRounds_succ_of_notMem hiC]
    -- so `ν` maps `S ∩ C` onto itself, and hence `S \ C` into itself
    have hmaps : Set.MapsTo ν (S ∩ C : Finset (Fin n)) (S ∩ C : Finset (Fin n)) := by
      intro a ha
      obtain ⟨haS, haC⟩ := Finset.mem_inter.1 ha
      rw [Finset.mem_coe, Finset.mem_inter, hC a haS haC]
      exact ⟨hC a haS haC ▸ hS a haS, topChoice_mem_cycleAgents haC⟩
    have hsurj := ((Set.Finite.injOn_iff_bijOn_of_mapsTo (Finset.finite_toSet _) hmaps).1
      ν.injective.injOn).surjOn
    have hS' : ∀ a ∈ S \ C, ν a ∈ S \ C := by
      intro a ha
      obtain ⟨haS, haC⟩ := Finset.mem_sdiff.1 ha
      refine Finset.mem_sdiff.2 ⟨hS a haS, fun hνC => haC ?_⟩
      obtain ⟨b, hb, hba⟩ := hsurj (Finset.mem_coe.2 (Finset.mem_inter.2 ⟨hS a haS, hνC⟩))
      rw [ν.injective hba] at hb
      exact (Finset.mem_inter.1 hb).2
    refine ih hk' (S \ C) (Finset.sdiff_subset_sdiff hSR le_rfl) hS' (fun a ha => ?_) i
      (Finset.mem_sdiff.2 ⟨hi, hiC⟩)
    have h1 := hle a (Finset.sdiff_subset ha)
    rwa [ttcRounds_succ_of_notMem (Finset.mem_sdiff.1 ha).2] at h1

variable (I)

/-- The TTC allocation is in the strict core: no coalition weakly blocks it
([RothPostlewaite1977]; [SchummerVohra2007], Theorem 10.6). -/
theorem inStrictCore_ttc : I.InStrictCore I.ttc := by
  rintro S ⟨ν, hS, hle, i, hi, hlt⟩
  have h := eq_ttcRounds_of_le (I := I) (by simp) ν S (Finset.subset_univ S) hS hle i hi
  rw [ttc_apply, h] at hlt
  exact lt_irrefl _ hlt

/-- The TTC allocation is in the core ([ShapleyScarf1974]; [Roughgarden2013CS364A], Lecture 9,
Theorem 3.2). -/
theorem inCore_ttc : I.InCore I.ttc := I.inStrictCore_ttc.inCore

/-- The TTC allocation is individually rational. -/
theorem isIndividuallyRational_ttc : I.IsIndividuallyRational I.ttc :=
  I.inStrictCore_ttc.isIndividuallyRational

/-- The TTC allocation is Pareto efficient. -/
theorem isParetoEfficient_ttc : I.IsParetoEfficient I.ttc :=
  I.inStrictCore_ttc.isParetoEfficient

variable {I}

/-- A strict-core allocation that maps a submarket `R` into itself agrees with TTC on `R`. -/
private theorem eq_ttcRounds_of_inStrictCore {μ : Allocation n} (hμ : I.InStrictCore μ) {k : ℕ}
    {R : Finset (Fin n)} (hk : R.card ≤ k) (hR : ∀ i ∈ R, μ i ∈ R) :
    ∀ i ∈ R, μ i = I.ttcRounds k R i := by
  induction k generalizing R with
  | zero =>
    intro i hi
    simp_all
  | succ k ih =>
    intro i hi
    have hRne : R.Nonempty := ⟨i, hi⟩
    have hk' := card_sdiff_cycleAgents_le (I := I) hk hRne
    set C := I.cycleAgents R
    -- the agents on cycles can trade along them: `ν` follows the pointers on `C`
    classical
    let g : Fin n → Fin n := fun a => if a ∈ C then I.topChoice R a else a
    have hg : Injective g := by
      intro a b hab
      simp only [g] at hab
      split_ifs at hab with ha hb hb
      · exact topChoice_injOn_cycleAgents R ha hb hab
      · exact absurd (hab ▸ topChoice_mem_cycleAgents ha) hb
      · exact absurd (hab ▸ topChoice_mem_cycleAgents hb) ha
      · exact hab
    let ν : Allocation n := StableMatching.permOfInjective g hg
    have hνC : ∀ a ∈ C, ν a = I.topChoice R a := fun a ha => ite_eq_left ha
    -- so, unless `C` weakly blocks `μ`, every agent on a cycle gets its favourite house in `R`
    have hμC : ∀ a ∈ C, μ a = I.topChoice R a := by
      have hle : ∀ a ∈ C, I.rank a (I.topChoice R a) ≤ I.rank a (μ a) :=
        fun a ha => rank_topChoice_le (hR a (cycleAgents_subset R ha)) a
      intro a ha
      by_contra hne
      refine hμ C ⟨ν, fun b hb => ?_, fun b hb => ?_, a, ha, ?_⟩
      · rw [hνC b hb]
        exact topChoice_mem_cycleAgents hb
      · rw [hνC b hb]
        exact hle b hb
      · rw [hνC a ha]
        exact lt_of_le_of_ne (hle a ha) fun h => hne (I.rank_injective a h).symm
    by_cases hiC : i ∈ C
    · rw [hμC i hiC, ttcRounds_succ_of_mem hiC]
    rw [ttcRounds_succ_of_notMem hiC]
    -- `μ` maps `C` onto itself, hence `R \ C` into itself
    have hmaps : Set.MapsTo μ (C : Set (Fin n)) C := fun b hb =>
      hμC b hb ▸ topChoice_mem_cycleAgents hb
    have hsurj := ((Set.Finite.injOn_iff_bijOn_of_mapsTo (Finset.finite_toSet _) hmaps).1
      μ.injective.injOn).surjOn
    refine ih hk' (fun a ha => ?_) i (Finset.mem_sdiff.2 ⟨hi, hiC⟩)
    obtain ⟨haR, haC⟩ := Finset.mem_sdiff.1 ha
    refine Finset.mem_sdiff.2 ⟨hR a haR, fun hμa => haC ?_⟩
    obtain ⟨b, hb, hba⟩ := hsurj hμa
    exact μ.injective hba ▸ hb

/-- The TTC allocation is the only allocation in the strict core ([RothPostlewaite1977];
[SchummerVohra2007], Theorem 10.6). -/
theorem InStrictCore.eq_ttc {μ : Allocation n} (hμ : I.InStrictCore μ) : μ = I.ttc := by
  ext i
  rw [ttc_apply, eq_ttcRounds_of_inStrictCore hμ (k := n) (by simp)
    (fun _ _ => Finset.mem_univ _) i (Finset.mem_univ i)]

variable (I)

/-- The strict core consists of the TTC allocation alone. Uniqueness needs weak blocking: the
core, defined by strict blocking, can contain other allocations (see the test module
`ComplexityTests.HousingMarket`). -/
theorem inStrictCore_iff (μ : Allocation n) : I.InStrictCore μ ↔ μ = I.ttc :=
  ⟨InStrictCore.eq_ttc, fun h => h ▸ I.inStrictCore_ttc⟩

variable {I}

/-! ### Following pointers -/

/-- An agent `i` reached from house `h ∈ R` by following pointers in `R` receives a house it weakly
prefers to `h`. In particular (`m = 0`) TTC is individually rational on every submarket. -/
theorem rank_ttcRounds_le_of_iterate {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k)
    {i h : Fin n} (hh : h ∈ R) {m : ℕ} (hm : (I.topChoice R)^[m] h = i) :
    I.rank i (I.ttcRounds k R i) ≤ I.rank i h := by
  induction k generalizing R h m with
  | zero => simp_all
  | succ k ih =>
    have hR : R.Nonempty := ⟨h, hh⟩
    have hk' := card_sdiff_cycleAgents_le (I := I) hk hR
    by_cases hiC : i ∈ I.cycleAgents R
    · rw [ttcRounds_succ_of_mem hiC]
      exact rank_topChoice_le hh i
    rw [ttcRounds_succ_of_notMem hiC]
    -- the path from `h` to `i` avoids the cycles, since the cycles are closed under pointers
    have hout : ∀ j ≤ m, (I.topChoice R)^[j] h ∉ I.cycleAgents R := by
      intro j hj hjC
      apply hiC
      rw [← hm, show m = (m - j) + j by omega, iterate_add_apply]
      generalize m - j = l
      induction l with
      | zero => exact hjC
      | succ l ihl =>
        rw [iterate_succ_apply']
        exact topChoice_mem_cycleAgents ihl
    -- so it is a path of pointers in the next round
    have hpath : ∀ j ≤ m, (I.topChoice (R \ I.cycleAgents R))^[j] h = (I.topChoice R)^[j] h := by
      intro j hj
      induction j with
      | zero => rfl
      | succ j ihj =>
        rw [iterate_succ_apply', iterate_succ_apply', ihj (by omega)]
        refine topChoice_of_subset Finset.sdiff_subset
          (Finset.mem_sdiff.2 ⟨topChoice_mem hR _, ?_⟩)
        rw [← iterate_succ_apply' (I.topChoice R)]
        exact hout _ hj
    exact ih hk' (Finset.mem_sdiff.2 ⟨hh, hout 0 (Nat.zero_le _)⟩) ((hpath m le_rfl).trans hm)

/-! ### Competitive prices -/

theorem ttcPriceRounds_le_card {k : ℕ} {R : Finset (Fin n)} (h : Fin n) :
    I.ttcPriceRounds k R h ≤ R.card := by
  induction k generalizing R with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    by_cases hh : h ∈ I.cycleAgents R
    · rw [ttcPriceRounds_succ_of_mem hh]
    · rw [ttcPriceRounds_succ_of_notMem hh]
      exact ih.trans (Finset.card_le_card Finset.sdiff_subset)

/-- Every agent receives its house in the round in which its own house leaves. -/
theorem ttcPriceRounds_ttcRounds {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k) {i : Fin n}
    (hi : i ∈ R) : I.ttcPriceRounds k R (I.ttcRounds k R i) = I.ttcPriceRounds k R i := by
  induction k generalizing R with
  | zero => simp_all
  | succ k ih =>
    have hR : R.Nonempty := ⟨i, hi⟩
    have hk' := card_sdiff_cycleAgents_le (I := I) hk hR
    by_cases hiC : i ∈ I.cycleAgents R
    · rw [ttcRounds_succ_of_mem hiC, ttcPriceRounds_succ_of_mem (topChoice_mem_cycleAgents hiC),
        ttcPriceRounds_succ_of_mem hiC]
    · have hmem := ttcRounds_mem (I := I) hk' (Finset.mem_sdiff.2 ⟨hi, hiC⟩)
      rw [ttcRounds_succ_of_notMem hiC, ttcPriceRounds_succ_of_notMem (Finset.mem_sdiff.1 hmem).2,
        ttcPriceRounds_succ_of_notMem hiC]
      exact ih hk' (Finset.mem_sdiff.2 ⟨hi, hiC⟩)

/-- A house leaving no earlier than agent `i` is still available to `i` when `i` receives its
house. -/
theorem rank_ttcRounds_le_of_ttcPriceRounds_le {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k)
    {i h : Fin n} (hi : i ∈ R) (hh : h ∈ R)
    (hp : I.ttcPriceRounds k R h ≤ I.ttcPriceRounds k R i) :
    I.rank i (I.ttcRounds k R i) ≤ I.rank i h := by
  induction k generalizing R with
  | zero => simp_all
  | succ k ih =>
    have hR : R.Nonempty := ⟨i, hi⟩
    have hk' := card_sdiff_cycleAgents_le (I := I) hk hR
    by_cases hiC : i ∈ I.cycleAgents R
    · rw [ttcRounds_succ_of_mem hiC]
      exact rank_topChoice_le hh i
    rw [ttcPriceRounds_succ_of_notMem hiC] at hp
    have hhC : h ∉ I.cycleAgents R := by
      intro hhC
      rw [ttcPriceRounds_succ_of_mem hhC] at hp
      have := (ttcPriceRounds_le_card (I := I) (k := k) (R := R \ I.cycleAgents R) i).trans_lt
        (card_sdiff_cycleAgents_lt hR)
      omega
    rw [ttcPriceRounds_succ_of_notMem hhC] at hp
    rw [ttcRounds_succ_of_notMem hiC]
    exact ih hk' (Finset.mem_sdiff.2 ⟨hi, hiC⟩) (Finset.mem_sdiff.2 ⟨hh, hhC⟩) hp

variable (I)

/-- The TTC allocation is competitive at the TTC prices: every agent's house costs as much as its
own, and it is the agent's favourite among the houses it can afford ([ShapleyScarf1974]). -/
theorem isCompetitive_ttc : I.IsCompetitive I.ttc I.ttcPrice := by
  intro i
  refine ⟨(ttcPriceRounds_ttcRounds (by simp) (Finset.mem_univ i)).le, fun h hh => ?_⟩
  exact rank_ttcRounds_le_of_ttcPriceRounds_le (by simp) (Finset.mem_univ i) (Finset.mem_univ h) hh

variable {I} in
/-- An allocation that is competitive at some prices, in any linear order, is the TTC allocation:
competitive allocations are unique ([RothPostlewaite1977]). -/
theorem IsCompetitive.eq_ttc {α : Type*} [LinearOrder α] {μ : Allocation n} {p : Fin n → α}
    (h : I.IsCompetitive μ p) : μ = I.ttc :=
  h.inStrictCore.eq_ttc

/-- An allocation is competitive at some natural-number prices iff it is the TTC allocation. -/
theorem exists_isCompetitive_iff (μ : Allocation n) :
    (∃ p : Fin n → ℕ, I.IsCompetitive μ p) ↔ μ = I.ttc :=
  ⟨fun ⟨_, hp⟩ => hp.eq_ttc, fun h => ⟨I.ttcPrice, h ▸ I.isCompetitive_ttc⟩⟩

end Instance

end Cslib.Algorithms.Lean.HousingMarket
