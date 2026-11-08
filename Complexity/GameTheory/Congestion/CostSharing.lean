/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.GameTheory.Congestion.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
import Complexity.Foundations.NumberTheory.Harmonic
import Complexity.GameTheory.Strategic.Stability
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.NumberTheory.Harmonic.Int
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fair cost sharing and the price of stability `H_k`

In a **fair cost-sharing game** (a network cost-sharing or Shapley network design game) every
resource `e` has a fixed cost `c e ≥ 0`, which is split equally among the players that use it: when
`k ≥ 1` players use `e`, each pays `c e / k`. This is the atomic congestion game with latencies
`latency e k = c e / k` ([TardosWexler2007], Section 19.3.2; [Roughgarden2013CS364A], Lecture #15,
Section 2). The social cost is the total cost `∑ c e` of the resources in use, the cost of the
formed network. As in `Cslib.GameTheory.CongestionGame`, the `s_i`–`t_i` paths of a network are
abstracted to finite sets of resources.

Rosenthal's potential of a fair cost-sharing game is `∑ e, c e * H (load s e)`, where `H` is the
harmonic number ([TardosWexler2007], Section 19.3.1). Since `1 ≤ H n ≤ H k` for a resource with
`1 ≤ n ≤ k` users, `socialCost s ≤ Φ s ≤ H k * socialCost s` with `k` players ([TardosWexler2007],
Lemma 19.8), and the potential function method gives the theorem of Anshelevich, Dasgupta,
Kleinberg, Tardos, Wexler and Roughgarden [AnshelevichDKTWR2008]: **the price of stability of a
`k`-player fair cost-sharing game is at most `H k`** ([TardosWexler2007], Theorem 19.10;
[Roughgarden2013CS364A], Lecture #15, Theorem 2.1).

The bound is tight ([Roughgarden2013CS364A], Lecture #15, Section 1.4 and Figure 2;
[RoughgardenTardos2007], Example 17.3). In the **opt-out game** `optOut k ε`, player `i` either
opts out on a private resource of cost `1 / (i + 1)` or meets the other players on a shared resource
of cost `1 + ε`. For `ε > 0` the unique pure Nash equilibrium is that every player opts out, of
social cost `H k`, while everyone sharing costs `1 + ε`. The source's network has, in addition,
zero-cost edges from each source to the meeting point; they change no player's cost and are omitted.

## Main definitions

* `Cslib.GameTheory.CongestionGame.fairCostSharing`: the fair cost-sharing game with resource sets
  `resources` and resource costs `c`.
* `Cslib.GameTheory.CongestionGame.optOut`: the opt-out game with `k` players and parameter `ε`.

## Main results

* `Cslib.GameTheory.CongestionGame.socialCost_fairCostSharing`: the social cost is the total cost
  of the resources in use.
* `Cslib.GameTheory.CongestionGame.rosenthalPotential_fairCostSharing`: Rosenthal's potential is
  `∑ e, c e * H (load s e)`.
* `Cslib.GameTheory.CongestionGame.socialCost_le_rosenthalPotential_fairCostSharing`,
  `Cslib.GameTheory.CongestionGame.rosenthalPotential_fairCostSharing_le_harmonic_mul`
  ([TardosWexler2007], Lemma 19.8): `socialCost s ≤ Φ s ≤ H k * socialCost s`.
* `Cslib.GameTheory.CongestionGame.exists_isPureNash_fairCostSharing_socialCost_le_harmonic_mul`
  ([AnshelevichDKTWR2008]; [TardosWexler2007], Theorem 19.10; [Roughgarden2013CS364A], Lecture #15,
  Theorem 2.1): **the price of stability is at most `H k`**.
* `exists_reflTransGen_isPureNash_fairCostSharing_socialCost_le_harmonic_mul` (in
  `Cslib.GameTheory.CongestionGame`): better-response dynamics from any profile `s₀` reach a pure
  Nash equilibrium of social cost at most `H k * socialCost s₀`.
* `Cslib.GameTheory.CongestionGame.isPureNash_optOut_iff`: for `ε > 0` the unique pure Nash
  equilibrium of the opt-out game is that every player opts out.
* `Cslib.GameTheory.CongestionGame.socialCost_optOut_true`,
  `Cslib.GameTheory.CongestionGame.socialCost_optOut_false`: its social costs `H k` and `1 + ε`.
* `Cslib.GameTheory.CongestionGame.exists_forall_isPureNash_optOut_mul_lt` ([Roughgarden2013CS364A],
  Lecture #15, Section 2, after Theorem 2.1): **`H k` cannot be lowered**: for every `r < H k`
  some opt-out game has no pure Nash equilibrium within the factor `r` of the optimum.

## References

* [AnshelevichDKTWR2008]
* [Roughgarden2013CS364A]
* [RoughgardenTardos2007]
* [TardosWexler2007]
-/

public section

namespace Cslib.GameTheory.CongestionGame

variable {ι : Type*} {S : ι → Type*} {E : Type*}

/-- The **fair cost-sharing game** (Shapley network design game) with resource sets `resources` and
resource costs `c`: the cost `c e` of a resource used by `k ≥ 1` players is split equally, so each
pays `c e / k` ([TardosWexler2007], Section 19.3.1; [Roughgarden2013CS364A], Lecture #15, (1)). The
latency at load `0` is `c e / 0 = 0`, which no player ever pays. The costs are meant to be
nonnegative; the theorems that need it assume `0 ≤ c e`. -/
noncomputable def fairCostSharing (resources : ∀ i, S i → Finset E) (c : E → ℝ) :
    CongestionGame ι S E where
  resources := resources
  latency e k := c e / k

@[simp]
theorem fairCostSharing_resources (resources : ∀ i, S i → Finset E) (c : E → ℝ) :
    (fairCostSharing resources c).resources = resources := by
  rw [fairCostSharing]

@[simp]
theorem fairCostSharing_latency (resources : ∀ i, S i → Finset E) (c : E → ℝ) (e : E) (k : ℕ) :
    (fairCostSharing resources c).latency e k = c e / k := by
  rw [fairCostSharing]

variable [Fintype ι] [DecidableEq E] (resources : ∀ i, S i → Finset E) (c : E → ℝ)

/-- The social cost of a fair cost-sharing game is **the total cost of the resources in use**,
`∑ e with load s e ≥ 1, c e` ([Roughgarden2013CS364A], Lecture #15, (2)). -/
theorem socialCost_fairCostSharing [Fintype E] (s : ∀ i, S i) :
    (fairCostSharing resources c).toCostGame.socialCost s
      = ∑ e with 0 < (fairCostSharing resources c).load s e, c e := by
  rw [socialCost_toCostGame, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [fairCostSharing_latency]
  rcases Nat.eq_zero_or_pos ((fairCostSharing resources c).load s e) with h | h
  · rw [h]
    simp
  · simp only [h, ↓reduceIte]
    have : ((fairCostSharing resources c).load s e : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp

/-- **Rosenthal's potential of a fair cost-sharing game** is `∑ e, c e * H (load s e)`
([TardosWexler2007], Section 19.3.1; [Roughgarden2013CS364A], Lecture #15, (3)). -/
theorem rosenthalPotential_fairCostSharing [Fintype E] (s : ∀ i, S i) :
    (fairCostSharing resources c).rosenthalPotential s
      = ∑ e, c e * harmonic ((fairCostSharing resources c).load s e) := by
  rw [rosenthalPotential_def]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [cast_harmonic, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fairCostSharing_latency, div_eq_mul_inv, Nat.cast_add, Nat.cast_one]

/-- **The potential bounds the social cost from above** ([TardosWexler2007], Lemma 19.8, first
inequality): with nonnegative costs, every resource in use is counted at least once. -/
theorem socialCost_le_rosenthalPotential_fairCostSharing [Fintype E] (hc : ∀ e, 0 ≤ c e)
    (s : ∀ i, S i) :
    (fairCostSharing resources c).toCostGame.socialCost s
      ≤ (fairCostSharing resources c).rosenthalPotential s := by
  rw [socialCost_fairCostSharing, rosenthalPotential_fairCostSharing, Finset.sum_filter]
  refine Finset.sum_le_sum fun e _ => ?_
  split_ifs with h
  · exact le_mul_of_one_le_right (hc e) (by exact_mod_cast one_le_harmonic h.ne')
  · exact mul_nonneg (hc e) (by exact_mod_cast harmonic_nonneg _)

/-- **The potential overestimates the social cost by at most `H k`** ([TardosWexler2007],
Lemma 19.8, second inequality): with nonnegative costs and `k = Fintype.card ι` players, no resource
has more than `k` users. -/
theorem rosenthalPotential_fairCostSharing_le_harmonic_mul [Fintype E] (hc : ∀ e, 0 ≤ c e)
    (s : ∀ i, S i) :
    (fairCostSharing resources c).rosenthalPotential s
      ≤ harmonic (Fintype.card ι) * (fairCostSharing resources c).toCostGame.socialCost s := by
  rw [socialCost_fairCostSharing, rosenthalPotential_fairCostSharing, Finset.sum_filter,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  split_ifs with h
  · rw [mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (hc e)
    exact_mod_cast harmonic_mono ((Finset.card_filter_le _ _).trans_eq Finset.card_univ)
  · rw [Nat.eq_zero_of_not_pos h, harmonic_zero, Rat.cast_zero, mul_zero, mul_zero]

variable [DecidableEq ι] [Finite E] [∀ i, Finite (S i)]

/-- **The price of stability of fair cost-sharing games is at most `H k`** [AnshelevichDKTWR2008]
([TardosWexler2007], Theorem 19.10; [Roughgarden2013CS364A], Lecture #15, Theorem 2.1): a fair
cost-sharing game with `k = Fintype.card ι` players, nonnegative resource costs, finitely many
resources and finitely many (and at least one) strategies per player has a pure Nash equilibrium
`s` with `socialCost s ≤ H k * socialCost s'` for every profile `s'`. The equilibrium is a global
minimizer of Rosenthal's potential. `exists_forall_isPureNash_optOut_mul_lt` shows that `H k` cannot
be lowered. -/
theorem exists_isPureNash_fairCostSharing_socialCost_le_harmonic_mul [∀ i, Nonempty (S i)]
    (hc : ∀ e, 0 ≤ c e) :
    ∃ s, (fairCostSharing resources c).toCostGame.IsPureNash s ∧
      ∀ s', (fairCostSharing resources c).toCostGame.socialCost s
        ≤ harmonic (Fintype.card ι) * (fairCostSharing resources c).toCostGame.socialCost s' := by
  have := Fintype.ofFinite E
  obtain ⟨s, hs, hle⟩ := (fairCostSharing resources c).isExactPotential_rosenthalPotential
    |>.isGeneralizedOrdinalPotential.exists_isPureNash_socialCost_le zero_le_one
      (fun s => by
        rw [one_mul]
        exact socialCost_le_rosenthalPotential_fairCostSharing resources c hc s)
      (rosenthalPotential_fairCostSharing_le_harmonic_mul resources c hc)
  exact ⟨s, hs, fun s' => by simpa only [one_mul] using hle s'⟩

/-- **Better-response dynamics from any profile reach a good equilibrium** in fair cost-sharing
games: from every profile `s₀`, a finite sequence of improving unilateral deviations reaches a pure
Nash equilibrium `t` with `socialCost t ≤ H k * socialCost s₀`, where `k = Fintype.card ι`. Started
at a socially optimal profile, this reaches an equilibrium within the price-of-stability bound. -/
theorem exists_reflTransGen_isPureNash_fairCostSharing_socialCost_le_harmonic_mul
    (hc : ∀ e, 0 ≤ c e) (s₀ : ∀ i, S i) :
    ∃ t, Relation.ReflTransGen (flip (fairCostSharing resources c).toCostGame.Improves) s₀ t ∧
      (fairCostSharing resources c).toCostGame.IsPureNash t ∧
      (fairCostSharing resources c).toCostGame.socialCost t
        ≤ harmonic (Fintype.card ι) * (fairCostSharing resources c).toCostGame.socialCost s₀ := by
  have := Fintype.ofFinite E
  obtain ⟨t, hpath, ht, hle⟩ := (fairCostSharing resources c).isExactPotential_rosenthalPotential
    |>.isGeneralizedOrdinalPotential.exists_reflTransGen_isPureNash_socialCost_le zero_le_one
      (fun s => by
        rw [one_mul]
        exact socialCost_le_rosenthalPotential_fairCostSharing resources c hc s)
      (rosenthalPotential_fairCostSharing_le_harmonic_mul resources c hc) s₀
  exact ⟨t, hpath, ht, by simpa only [one_mul] using hle⟩

end Cslib.GameTheory.CongestionGame

namespace Cslib.GameTheory.CongestionGame

/-- The resources of the opt-out game: player `i` either opts out (`true`) on its private resource
`some i` or meets the others (`false`) on the shared resource `none`. -/
def optOutResources (k : ℕ) (i : Fin k) : Bool → Finset (Option (Fin k))
  | true => {some i}
  | false => {none}

/-- The resource costs of the opt-out game: the private resource of player `i` costs `1 / (i + 1)`
and the shared resource costs `1 + ε`. -/
noncomputable def optOutCost (k : ℕ) (ε : ℝ) : Option (Fin k) → ℝ
  | some i => 1 / ((i : ℕ) + 1)
  | none => 1 + ε

/-- The **opt-out game** with `k` players ([Roughgarden2013CS364A], Lecture #15, Section 1.4 and
Figure 2; [RoughgardenTardos2007], Example 17.3): the fair cost-sharing game in which player `i`
(numbered from `0`) chooses between its private resource of cost `1 / (i + 1)` (strategy `true`)
and a shared resource of cost `1 + ε` (strategy `false`). The source's zero-cost edges from each
source to the meeting point change no player's cost and are omitted. -/
noncomputable def optOut (k : ℕ) (ε : ℝ) :
    CongestionGame (Fin k) (fun _ => Bool) (Option (Fin k)) :=
  fairCostSharing (optOutResources k) (optOutCost k ε)

variable {k : ℕ} {ε : ℝ}

/-- The opt-out game is the fair cost-sharing game with resources `optOutResources k` and costs
`optOutCost k ε`. -/
theorem optOut_def : optOut k ε = fairCostSharing (optOutResources k) (optOutCost k ε) := by
  rw [optOut]

private theorem optOut_resources (i : Fin k) (b : Bool) :
    (optOut k ε).resources i b = if b then {some i} else {none} := by
  cases b <;> rfl

private theorem optOut_latency (e : Option (Fin k)) (n : ℕ) :
    (optOut k ε).latency e n = optOutCost k ε e / n := rfl

/-- The private resource of player `j` has load `1` if `j` opts out and `0` otherwise. -/
private theorem optOut_load_some (s : Fin k → Bool) (j : Fin k) :
    (optOut k ε).load s (some j) = if s j then 1 else 0 := by
  have hmem : ∀ i, some j ∈ (optOut k ε).resources i (s i) ↔ i = j ∧ s j = true := by
    intro i
    rw [optOut_resources]
    by_cases hij : i = j
    · subst hij
      cases s i <;> simp
    · cases s i <;> simp [Ne.symm hij, hij]
  unfold load
  rw [Finset.filter_congr fun i _ => hmem i]
  cases s j <;> simp [Finset.filter_eq']

/-- The shared resource is used by the players that do not opt out. -/
private theorem optOut_load_none (s : Fin k → Bool) :
    (optOut k ε).load s none = (Finset.univ.filter fun i => s i = false).card := by
  unfold load
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  rw [optOut_resources]
  cases s i <;> simp

/-- The cost of player `i` in the opt-out game: `1 / (i + 1)` if it opts out, and the share
`(1 + ε) / m` of the shared resource if `m` players (including `i`) do not opt out. -/
theorem optOut_cost (s : Fin k → Bool) (i : Fin k) :
    (optOut k ε).toCostGame.cost i s
      = if s i then 1 / ((i : ℕ) + 1 : ℝ)
        else (1 + ε) / (Finset.univ.filter fun j => s j = false).card := by
  rw [toCostGame_cost, optOut_resources]
  cases hi : s i
  · simp only [Bool.false_eq_true, ↓reduceIte, Finset.sum_singleton, optOut_latency,
      optOut_load_none, optOutCost]
  · simp only [↓reduceIte, Finset.sum_singleton, optOut_latency, optOut_load_some, hi,
      optOutCost, Nat.cast_one, div_one]

/-- **The opt-out game has a unique pure Nash equilibrium** for `ε > 0`: every player opts out
([Roughgarden2013CS364A], Lecture #15, Section 1.4). If some players share, the one among them
with the largest index `j` pays at least `(1 + ε) / (j + 1)`, more than its private cost
`1 / (j + 1)`. -/
theorem isPureNash_optOut_iff (hε : 0 < ε) (s : Fin k → Bool) :
    (optOut k ε).toCostGame.IsPureNash s ↔ s = fun _ => true := by
  constructor
  · intro hs
    by_contra hne
    set F := Finset.univ.filter fun j => s j = false with hF
    have hFne : F.Nonempty := by
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
      exact ⟨j, by simpa [hF] using hj⟩
    obtain ⟨j, hjF, hjmax⟩ := F.exists_max_image (fun i : Fin k => (i : ℕ)) hFne
    have hj : s j = false := by simpa [hF] using hjF
    have hcard : F.card ≤ (j : ℕ) + 1 := by
      have := Finset.card_le_card_of_injOn (fun i : Fin k => (i : ℕ))
        (t := Finset.range ((j : ℕ) + 1))
        (fun i hi => Finset.mem_range.2 (Nat.lt_succ_of_le (hjmax i hi)))
        (fun a _ b _ hab => Fin.ext hab)
      simpa using this
    have hpos : 0 < F.card := Finset.card_pos.2 hFne
    have hdev := hs j true
    rw [optOut_cost, optOut_cost, hj, Function.update_self, ← hF] at hdev
    simp only [Bool.false_eq_true, ↓reduceIte] at hdev
    have hFR : (0 : ℝ) < F.card := by exact_mod_cast hpos
    have hcardR : (F.card : ℝ) ≤ (j : ℕ) + 1 := by exact_mod_cast hcard
    have hj1 : (0 : ℝ) < (j : ℕ) + 1 := by positivity
    rw [div_le_div_iff₀ hFR hj1] at hdev
    nlinarith [mul_pos hε hj1]
  · rintro rfl i a
    cases a
    · rw [optOut_cost, optOut_cost, Function.update_self]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hcard : (Finset.univ.filter fun j =>
          Function.update (fun _ : Fin k => true) i false j = false).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨i, Finset.ext fun j => ?_⟩
        by_cases hji : j = i
        · subst hji; simp
        · simp [hji]
      rw [hcard, Nat.cast_one, div_one]
      have : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    · rw [Function.update_eq_self]

/-- In the opt-out game, the profile in which every player opts out has social cost `H k`. -/
theorem socialCost_optOut_true :
    (optOut k ε).toCostGame.socialCost (fun _ => true) = harmonic k := by
  have h : ∀ i : Fin k, (optOut k ε).toCostGame.cost i (fun _ => true) = 1 / ((i : ℕ) + 1 : ℝ) := by
    intro i
    rw [optOut_cost]
    simp
  unfold CostGame.socialCost
  rw [Finset.sum_congr rfl fun i _ => h i,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => 1 / ((i : ℝ) + 1)), cast_harmonic]
  simp only [one_div]

/-- In the opt-out game with `k ≥ 1` players, the profile in which every player shares has social
cost `1 + ε`. -/
theorem socialCost_optOut_false (hk : k ≠ 0) :
    (optOut k ε).toCostGame.socialCost (fun _ => false) = 1 + ε := by
  have h : ∀ i : Fin k, (optOut k ε).toCostGame.cost i (fun _ => false) = (1 + ε) / k := by
    intro i
    rw [optOut_cost]
    simp
  unfold CostGame.socialCost
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  field_simp

/-- **The bound `H k` is tight** ([Roughgarden2013CS364A], Lecture #15, Section 2, the remark after
Theorem 2.1 that the opt-out example rules out any smaller factor): for `k ≥ 1` players and
every `r < H k` there is `ε > 0` such that every pure Nash equilibrium `s` of the opt-out game
`optOut k ε` has `socialCost s > r * socialCost s'` for the profile `s'` in which every player
shares. So `exists_isPureNash_fairCostSharing_socialCost_le_harmonic_mul` fails with `r` in place
of `H k`. -/
theorem exists_forall_isPureNash_optOut_mul_lt (hk : k ≠ 0) {r : ℝ} (hr : r < harmonic k) :
    ∃ ε > 0, ∀ s, (optOut k ε).toCostGame.IsPureNash s →
      r * (optOut k ε).toCostGame.socialCost (fun _ => false)
        < (optOut k ε).toCostGame.socialCost s := by
  have hH : (0 : ℝ) < harmonic k := by exact_mod_cast harmonic_pos hk
  obtain ⟨ε, hε, hlt⟩ : ∃ ε > 0, r * (1 + ε) < harmonic k := by
    rcases le_or_gt r 0 with hr0 | hr0
    · exact ⟨1, one_pos, by nlinarith⟩
    · refine ⟨(harmonic k - r) / (2 * r), div_pos (by linarith) (by linarith), ?_⟩
      have : r * (1 + (harmonic k - r) / (2 * r)) = (r + harmonic k) / 2 := by
        field_simp
        ring
      rw [this]
      linarith
  refine ⟨ε, hε, fun s hs => ?_⟩
  rw [(isPureNash_optOut_iff hε s).1 hs, socialCost_optOut_true, socialCost_optOut_false hk]
  exact hlt

end Cslib.GameTheory.CongestionGame
