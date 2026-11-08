/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.GameTheory.Congestion.CostSharing
public import Complexity.GameTheory.Strategic.StrongNash
import Complexity.Foundations.NumberTheory.Harmonic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.Linarith

/-!
# Strong Nash equilibria of fair cost-sharing games

Every strong Nash equilibrium of a `k`-player fair cost-sharing game costs at most `H k` times
the optimum (Epstein, Feldman and Mansour [EpsteinFeldmanMansour2009]; [Roughgarden2013CS364A],
Lecture #15, Theorem 3.2). Unlike the price-of-stability bound
`exists_isPureNash_fairCostSharing_socialCost_le_harmonic_mul`, this bounds *every* strong Nash
equilibrium, but it does not assert that one exists, and in general none need exist
([Roughgarden2013CS364A], Lecture #15, Section 4 and Figure 4).

The proof ([Roughgarden2013CS364A], Lecture #15, proof of Theorem 3.2) peels players off the grand
coalition. Fix a strong Nash equilibrium `s` and any profile `t`. A nonempty coalition `A` does not
gain by jointly switching to `t`, so some member `i ∈ A` has
`cost i s ≤ cost i (A.piecewise t s)` (display (5)). When latencies are nonincreasing in the load,
the players outside `A` only help `i`, so `cost i (A.piecewise t s)` is at most the cost of `i` at
`t` with only the members of `A` present (display (7)). That cost is exactly the drop of the
coalition's Rosenthal potential when `i` leaves the coalition (display (8)). Removing `i` and
repeating telescopes to `socialCost s ≤ Φ t`, Rosenthal's potential of `t`. The argument uses only
that latencies are nonincreasing in the load, so we state it for every atomic congestion game with
that property and specialize it to fair cost sharing, where `Φ t ≤ H k * socialCost t`.

The opt-out game shows that `H k` is tight: for `ε > 0`, everyone opting out is a strong Nash
equilibrium ([Roughgarden2013CS364A], Lecture #15, Section 3), indeed the only one.

When all players share one strategy set `P` and one resource map `R` (in a network, a common
source and a common sink), strong Nash equilibria exist and are optimal ([Roughgarden2013CS364A],
Exercise Set #8, Exercise 67): everyone playing a cheapest strategy is a strong Nash equilibrium,
and at a costlier profile the grand coalition gains by switching to a cheapest strategy played in
it or in the optimum.

## Main results

* `Cslib.GameTheory.CongestionGame.socialCost_le_rosenthalPotential_of_isStrongNash`: in an atomic
  congestion game whose latencies are nonincreasing in the load (on loads `≥ 1`), every strong Nash
  equilibrium costs at most Rosenthal's potential of every profile.
* `Cslib.GameTheory.CongestionGame.socialCost_fairCostSharing_le_harmonic_mul_of_isStrongNash`
  ([EpsteinFeldmanMansour2009]; [Roughgarden2013CS364A], Lecture #15, Theorem 3.2): **every strong
  Nash equilibrium of a `k`-player fair cost-sharing game costs at most `H k` times the optimum**.
* `Cslib.GameTheory.CongestionGame.isStrongNash_fairCostSharing_const`,
  `Cslib.GameTheory.CongestionGame.socialCost_fairCostSharing_le_of_isStrongNash`,
  `Cslib.GameTheory.CongestionGame.exists_isStrongNash_fairCostSharing_const`
  ([Roughgarden2013CS364A], Exercise Set #8, Exercise 67): with a common strategy set and resource
  map, everyone playing a cheapest strategy is a strong Nash equilibrium and every strong Nash
  equilibrium is optimal.
* `Cslib.GameTheory.CongestionGame.isStrongNash_optOut_true`,
  `Cslib.GameTheory.CongestionGame.isStrongNash_optOut_iff`: for `ε > 0`, the unique strong Nash
  equilibrium of the opt-out game is that every player opts out.
* `Cslib.GameTheory.CongestionGame.exists_isStrongNash_optOut_mul_lt` ([Roughgarden2013CS364A],
  Lecture #15, Section 3): **`H k` cannot be lowered**: for every `r < H k` some opt-out game has a
  strong Nash equilibrium, and every strong Nash equilibrium costs more than `r` times the optimum.

## References

* [EpsteinFeldmanMansour2009]
* [Roughgarden2013CS364A]
-/

public section

namespace Cslib.GameTheory.CongestionGame

variable {ι : Type*} {S : ι → Type*} {E : Type*} [DecidableEq E] (C : CongestionGame ι S E)

/-- The number of members of the coalition `A` that use the resource `e` at the profile `t`. -/
private def coalitionLoad (A : Finset ι) (t : ∀ i, S i) (e : E) : ℕ :=
  (A.filter fun i => e ∈ C.resources i (t i)).card

/-- Rosenthal's potential of the profile `t` restricted to the members of the coalition `A`. -/
private def coalitionPotential [Fintype E] (A : Finset ι) (t : ∀ i, S i) : ℝ :=
  ∑ e, ∑ n ∈ Finset.range (C.coalitionLoad A t e), C.latency e (n + 1)

private theorem coalitionLoad_empty (t : ∀ i, S i) (e : E) : C.coalitionLoad ∅ t e = 0 := by
  rw [coalitionLoad, Finset.filter_empty, Finset.card_empty]

variable [DecidableEq ι]

/-- The coalition's load splits off the contribution of a member `i ∈ A`. -/
private theorem coalitionLoad_eq {A : Finset ι} {i : ι} (hi : i ∈ A) (t : ∀ i, S i) (e : E) :
    C.coalitionLoad A t e
      = C.coalitionLoad (A.erase i) t e + if e ∈ C.resources i (t i) then 1 else 0 := by
  unfold coalitionLoad
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_erase_add _ _ hi]

/-- **The potential drop when a player leaves the coalition is its cost** ([Roughgarden2013CS364A],
Lecture #15, (8)): removing a member `i ∈ A` lowers the coalition's potential by
`∑ e ∈ resources i (t i), latency e (coalitionLoad A t e)`, the cost of `i` at `t` when only the
members of `A` are present. -/
private theorem coalitionPotential_eq [Fintype E] {A : Finset ι} {i : ι} (hi : i ∈ A)
    (t : ∀ i, S i) :
    C.coalitionPotential A t = C.coalitionPotential (A.erase i) t
      + ∑ e ∈ C.resources i (t i), C.latency e (C.coalitionLoad A t e) := by
  unfold coalitionPotential
  rw [← Fintype.sum_ite_mem (C.resources i (t i)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [C.coalitionLoad_eq hi t e]
  split_ifs
  · rw [Finset.sum_range_succ]
  · rw [add_zero, add_zero]

variable [Fintype ι]

/-- Only the members of `A` that use `e` at `t` are counted, so the coalition's load is at most the
load at the profile in which `A` plays `t` and the other players play `s`. -/
private theorem coalitionLoad_le_load (A : Finset ι) (t s : ∀ i, S i) (e : E) :
    C.coalitionLoad A t e ≤ C.load (A.piecewise t s) e := by
  unfold coalitionLoad load
  refine Finset.card_le_card fun i hi => ?_
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨Finset.mem_univ i, ?_⟩
  rw [Finset.piecewise_eq_of_mem _ _ _ hi.1]
  exact hi.2

omit [DecidableEq ι] in
/-- The potential of the grand coalition is Rosenthal's potential. -/
private theorem coalitionPotential_univ [Fintype E] (t : ∀ i, S i) :
    C.coalitionPotential Finset.univ t = C.rosenthalPotential t := by
  rw [coalitionPotential, rosenthalPotential_def]
  rfl

/-- **Positive externalities** ([Roughgarden2013CS364A], Lecture #15, (7)): with latencies
nonincreasing on loads `≥ 1`, a member `i ∈ A` pays at most as much at `A.piecewise t s` as at `t`
with only the members of `A` present. -/
private theorem cost_piecewise_le (hC : ∀ e, AntitoneOn (C.latency e) (Set.Ici 1))
    {A : Finset ι} {i : ι} (hi : i ∈ A) (t s : ∀ i, S i) :
    C.toCostGame.cost i (A.piecewise t s)
      ≤ ∑ e ∈ C.resources i (t i), C.latency e (C.coalitionLoad A t e) := by
  rw [toCostGame_cost, Finset.piecewise_eq_of_mem _ _ _ hi]
  refine Finset.sum_le_sum fun e he => ?_
  have hpos : 1 ≤ C.coalitionLoad A t e :=
    Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨hi, he⟩⟩
  have hle := C.coalitionLoad_le_load A t s e
  exact hC e (Set.mem_Ici.2 hpos) (Set.mem_Ici.2 (hpos.trans hle)) hle

variable {C}

/-- The telescoping step of the proof of [Roughgarden2013CS364A], Lecture #15, Theorem 3.2: the
total cost of the members of any coalition `A` at a strong Nash equilibrium `s` is at most the
coalition's potential at `t`. -/
private theorem sum_cost_le_coalitionPotential_of_isStrongNash [Fintype E]
    (hC : ∀ e, AntitoneOn (C.latency e) (Set.Ici 1)) {s : ∀ i, S i}
    (hs : C.toCostGame.IsStrongNash s) (t : ∀ i, S i) (A : Finset ι) :
    ∑ i ∈ A, C.toCostGame.cost i s ≤ C.coalitionPotential A t := by
  induction A using Finset.strongInduction with
  | H A ih =>
    rcases A.eq_empty_or_nonempty with rfl | hA
    · rw [Finset.sum_empty, coalitionPotential]
      simp only [coalitionLoad_empty, Finset.range_zero, Finset.sum_empty, Finset.sum_const_zero,
        le_refl]
    · obtain ⟨i, hi, hle⟩ := hs.exists_cost_le hA t
      have hrest := ih (A.erase i) (Finset.erase_ssubset hi)
      rw [← Finset.sum_erase_add _ _ hi, C.coalitionPotential_eq hi t]
      linarith [C.cost_piecewise_le hC hi t s]

/-- **Strong Nash equilibria cost at most Rosenthal's potential** in congestion games with
nonincreasing latencies ([Roughgarden2013CS364A], Lecture #15, proof of Theorem 3.2, displays
(5)–(8), there for fair cost sharing): if every latency is nonincreasing on loads `≥ 1`, then every
strong Nash equilibrium `s` has `socialCost s ≤ Φ t` for every profile `t`, where `Φ` is
Rosenthal's potential. -/
theorem socialCost_le_rosenthalPotential_of_isStrongNash [Fintype E]
    (hC : ∀ e, AntitoneOn (C.latency e) (Set.Ici 1)) {s : ∀ i, S i}
    (hs : C.toCostGame.IsStrongNash s) (t : ∀ i, S i) :
    C.toCostGame.socialCost s ≤ C.rosenthalPotential t := by
  have h := sum_cost_le_coalitionPotential_of_isStrongNash hC hs t Finset.univ
  rwa [coalitionPotential_univ] at h

/-- **The price of anarchy of strong Nash equilibria in fair cost-sharing games is at most `H k`**
[EpsteinFeldmanMansour2009] ([Roughgarden2013CS364A], Lecture #15, Theorem 3.2): in a fair
cost-sharing game with `k = Fintype.card ι` players and nonnegative resource costs, every strong
Nash equilibrium `s` has `socialCost s ≤ H k * socialCost t` for every profile `t`. The bound
holds for every strong Nash equilibrium, but strong Nash equilibria need not exist.
`exists_isStrongNash_optOut_mul_lt` shows that `H k` cannot be lowered. -/
theorem socialCost_fairCostSharing_le_harmonic_mul_of_isStrongNash [Finite E]
    {resources : ∀ i, S i → Finset E} {c : E → ℝ} (hc : ∀ e, 0 ≤ c e) {s : ∀ i, S i}
    (hs : (fairCostSharing resources c).toCostGame.IsStrongNash s) (t : ∀ i, S i) :
    (fairCostSharing resources c).toCostGame.socialCost s
      ≤ harmonic (Fintype.card ι) * (fairCostSharing resources c).toCostGame.socialCost t := by
  have := Fintype.ofFinite E
  exact (socialCost_le_rosenthalPotential_of_isStrongNash
    (antitoneOn_latency_fairCostSharing resources hc) hs t).trans
    (rosenthalPotential_fairCostSharing_le_harmonic_mul resources c hc t)

end Cslib.GameTheory.CongestionGame

/-! ### Common strategy sets: strong Nash equilibria are optimal -/

namespace Cslib.GameTheory.CongestionGame

variable {ι : Type*} {S : ι → Type*} {E : Type*} [Fintype ι] [DecidableEq E]
  {resources : ∀ i, S i → Finset E} {c : E → ℝ}

variable {P : Type*} {R : P → Finset E}

/-- When every player plays the same strategy `p` of a common strategy set, each pays the share
`(∑ e ∈ R p, c e) / k` of the cost of `R p`. -/
theorem cost_fairCostSharing_const (p : P) (i : ι) :
    (fairCostSharing (fun (_ : ι) => R) c).toCostGame.cost i (fun _ => p)
      = (∑ e ∈ R p, c e) / Fintype.card ι := by
  rw [toCostGame_cost, fairCostSharing_resources, Finset.sum_div]
  refine Finset.sum_congr rfl fun e he => ?_
  have hload : (fairCostSharing (fun (_ : ι) => R) c).load (fun _ => p) e = Fintype.card ι := by
    unfold load
    rw [Finset.filter_true_of_mem fun j _ => by rwa [fairCostSharing_resources], Finset.card_univ]
  rw [fairCostSharing_latency, hload]

/-- **Everyone playing a cheapest strategy is a strong Nash equilibrium** when all players share
the strategy set `P` and the resource map `R` ([Roughgarden2013CS364A], Exercise Set #8,
Exercise 67, the network case of a common source and a common sink): each player pays
`c(R p) / k`, and no player can pay less at any profile. -/
theorem isStrongNash_fairCostSharing_const [DecidableEq ι] (hc : ∀ e, 0 ≤ c e) {p : P}
    (hp : ∀ q, ∑ e ∈ R p, c e ≤ ∑ e ∈ R q, c e) :
    (fairCostSharing (fun (_ : ι) => R) c).toCostGame.IsStrongNash fun _ => p := by
  rintro A t ⟨-, i, -, hlt⟩
  have hge := sum_div_card_le_cost_fairCostSharing (fun (_ : ι) => R) c hc
    (A.piecewise t fun _ => p) i
  rw [cost_fairCostSharing_const] at hlt
  have hmono : (∑ e ∈ R p, c e) / Fintype.card ι
      ≤ (∑ e ∈ R (A.piecewise t (fun _ => p) i), c e) / Fintype.card ι :=
    div_le_div_of_nonneg_right (hp _) (Nat.cast_nonneg _)
  linarith

/-- **Strong Nash equilibria are optimal when all players share the strategy set**
([Roughgarden2013CS364A], Exercise Set #8, Exercise 67, the network case of a common source and a
common sink): in a fair cost-sharing game with nonnegative costs in which every player has the
strategy set `P` and the resource map `R`, every strong Nash equilibrium `s` has
`socialCost s ≤ socialCost t` for every profile `t`. If `t` were cheaper, a strategy `q` of least
cost among those played in `s` or `t` would cost less than `socialCost s`, and the grand coalition
would gain by switching to `q`. -/
theorem socialCost_fairCostSharing_le_of_isStrongNash [DecidableEq ι] [Finite E]
    (hc : ∀ e, 0 ≤ c e) {s : ι → P}
    (hs : (fairCostSharing (fun (_ : ι) => R) c).toCostGame.IsStrongNash s) (t : ι → P) :
    (fairCostSharing (fun (_ : ι) => R) c).toCostGame.socialCost s
      ≤ (fairCostSharing (fun (_ : ι) => R) c).toCostGame.socialCost t := by
  by_contra hlt
  push Not at hlt
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp only [CostGame.socialCost, Finset.univ_eq_empty, Finset.sum_empty, lt_irrefl] at hlt
  obtain ⟨j₀⟩ := hne
  classical
  obtain ⟨q, -, hq⟩ := (Finset.univ.image s ∪ Finset.univ.image t).exists_min_image
    (fun q => ∑ e ∈ R q, c e) ⟨s j₀, Finset.mem_union_left _ (Finset.mem_image_of_mem s
      (Finset.mem_univ j₀))⟩
  have hqs : ∀ i, ∑ e ∈ R q, c e ≤ ∑ e ∈ R (s i), c e := fun i =>
    hq _ (Finset.mem_union_left _ (Finset.mem_image_of_mem s (Finset.mem_univ i)))
  have hqt : ∑ e ∈ R q, c e ≤ ∑ e ∈ R (t j₀), c e :=
    hq _ (Finset.mem_union_right _ (Finset.mem_image_of_mem t (Finset.mem_univ j₀)))
  have hlow : ∀ i, (fairCostSharing (fun (_ : ι) => R) c).toCostGame.cost i (fun _ => q)
      ≤ (fairCostSharing (fun (_ : ι) => R) c).toCostGame.cost i s := fun i => by
    rw [cost_fairCostSharing_const]
    exact (div_le_div_of_nonneg_right (hqs i) (Nat.cast_nonneg _)).trans
      (sum_div_card_le_cost_fairCostSharing (fun (_ : ι) => R) c hc s i)
  refine hs.not_pareto (fun _ => q) ⟨hlow, ?_⟩
  by_contra hno
  push Not at hno
  have heq : (fairCostSharing (fun (_ : ι) => R) c).toCostGame.socialCost (fun _ => q)
      = (fairCostSharing (fun (_ : ι) => R) c).toCostGame.socialCost s :=
    Finset.sum_congr rfl fun i _ => le_antisymm (hlow i) (hno i)
  have hconst : (fairCostSharing (fun (_ : ι) => R) c).toCostGame.socialCost (fun _ => q)
      ≤ ∑ e ∈ R q, c e := by
    rw [CostGame.socialCost, Finset.sum_congr rfl fun i _ => cost_fairCostSharing_const q i,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.2 ⟨j₀⟩
    rw [mul_div_cancel₀ _ hk.ne']
  have ht := sum_le_socialCost_fairCostSharing (fun (_ : ι) => R) c hc t j₀
  linarith

/-- **Strong Nash equilibria exist and are optimal when all players share the strategy set**
([Roughgarden2013CS364A], Exercise Set #8, Exercise 67): a fair cost-sharing game with
nonnegative costs, a common nonempty finite strategy set `P` and a common resource map `R` has a
strong Nash equilibrium (everyone plays a cheapest strategy), and every strong Nash equilibrium is a
social optimum, so the price of anarchy of strong Nash equilibria is `1`. -/
theorem exists_isStrongNash_fairCostSharing_const [DecidableEq ι] [Finite E] [Finite P]
    [Nonempty P] (hc : ∀ e, 0 ≤ c e) :
    ∃ p, (fairCostSharing (fun (_ : ι) => R) c).toCostGame.IsStrongNash (fun _ => p) ∧
      ∀ s t, (fairCostSharing (fun (_ : ι) => R) c).toCostGame.IsStrongNash s →
        (fairCostSharing (fun (_ : ι) => R) c).toCostGame.socialCost s
          ≤ (fairCostSharing (fun (_ : ι) => R) c).toCostGame.socialCost t := by
  obtain ⟨p, hp⟩ := Finite.exists_min fun q => ∑ e ∈ R q, c e
  exact ⟨p, isStrongNash_fairCostSharing_const hc hp,
    fun s t hs => socialCost_fairCostSharing_le_of_isStrongNash hc hs t⟩

end Cslib.GameTheory.CongestionGame

namespace Cslib.GameTheory.CongestionGame

variable {k : ℕ} {ε : ℝ}

/-- **Everyone opting out is a strong Nash equilibrium** of the opt-out game for `ε > 0`
([Roughgarden2013CS364A], Lecture #15, Section 3): after any joint deviation that leaves some
player sharing, the sharing player `j` with the largest index pays more than its private cost
`1 / (j + 1)` (`exists_one_div_lt_cost_optOut`), and `j` belongs to the deviating coalition. -/
theorem isStrongNash_optOut_true (hε : 0 < ε) :
    (optOut k ε).toCostGame.IsStrongNash fun _ => true := by
  rintro A t ⟨hle, i, hi, hlt⟩
  by_cases hu : A.piecewise t (fun _ => true) = fun _ => true
  · rw [hu] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨j, hj, hjlt⟩ := exists_one_div_lt_cost_optOut hε hu
    have hjA : j ∈ A := by
      by_contra hjA
      rw [Finset.piecewise_eq_of_notMem _ _ _ hjA] at hj
      exact Bool.true_eq_false.mp hj
    have hcost : (optOut k ε).toCostGame.cost j (fun _ => true) = 1 / ((j : ℕ) + 1 : ℝ) := by
      rw [optOut_cost]
      simp only [↓reduceIte]
    linarith [hle j hjA]

/-- **The opt-out game has a unique strong Nash equilibrium** for `ε > 0`: every player opts out.
A strong Nash equilibrium is a pure Nash equilibrium, and the pure Nash equilibrium is unique
(`isPureNash_optOut_iff`). -/
theorem isStrongNash_optOut_iff (hε : 0 < ε) (s : Fin k → Bool) :
    (optOut k ε).toCostGame.IsStrongNash s ↔ s = fun _ => true := by
  refine ⟨fun hs => (isPureNash_optOut_iff hε s).1 hs.isPureNash, ?_⟩
  rintro rfl
  exact isStrongNash_optOut_true hε

/-- **The bound `H k` is tight for strong Nash equilibria** ([Roughgarden2013CS364A], Lecture #15,
Section 3: the opt-out game has a strong Nash equilibrium of cost `H k` times the optimum): for
`k ≥ 1` players and every `r < H k` there is `ε > 0` such that the opt-out game `optOut k ε` has a
strong Nash equilibrium (everyone opting out), and every strong Nash equilibrium `s` has
`socialCost s > r * socialCost s'` for the profile `s'` in which every player shares. So
`socialCost_fairCostSharing_le_harmonic_mul_of_isStrongNash` fails with `r` in place of `H k`. -/
theorem exists_isStrongNash_optOut_mul_lt (hk : k ≠ 0) {r : ℝ} (hr : r < harmonic k) :
    ∃ ε > 0, (optOut k ε).toCostGame.IsStrongNash (fun _ => true) ∧
      ∀ s, (optOut k ε).toCostGame.IsStrongNash s →
        r * (optOut k ε).toCostGame.socialCost (fun _ => false)
          < (optOut k ε).toCostGame.socialCost s := by
  obtain ⟨ε, hε, h⟩ := exists_forall_isPureNash_optOut_mul_lt hk hr
  exact ⟨ε, hε, isStrongNash_optOut_true hε, fun s hs => h s hs.isPureNash⟩

end Cslib.GameTheory.CongestionGame
