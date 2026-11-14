/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MarkovChain.Basic
public import Mathlib.Logic.Relation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Expected hitting and return times of finite Markov chains

Let `P : MarkovChain V` be a Markov chain on a finite state space `V`, with transition
probabilities `P x y`. Probabilities and expectations live in `ℝ≥0∞`, so that expected values may
be infinite and need no summability side conditions.

For a target state `v`, let `τ_v = min {t ≥ 0 | X_t = v}` be the hitting time of `v`. The
probability `P_x(τ_v > t)` that the chain started at `x` avoids `v` at times `0, …, t` is
`survival P v t x`, defined by conditioning on the first step. It depends only on the first `t`
steps of the chain, so it is computed exactly from `P`. The expected hitting time is defined by the
tail-sum formula `E_x[τ_v] = ∑' t, P_x(τ_v > t)` (`hittingTime`), which is exact for random
variables with values in `ℕ ∪ {∞}`; it is not a finite-horizon approximation. Likewise the
expected return time `E_v[τ⁺_v]`, where `τ⁺_v = min {t ≥ 1 | X_t = v}`, is
`∑' t, P_v(τ⁺_v > t)` (`returnTime`).

The results are the classical facts about these quantities
[Levin and Peres, Sections 1.5 and 10.2][LevinPeres2017]:

* first-step equations: `E_x[τ_v] = 1 + ∑ y, P x y * E_y[τ_v]` for `x ≠ v`
  (`hittingTime_eq_of_ne`) and `E_v[τ⁺_v] = 1 + ∑ y, P v y * E_y[τ_v]`
  (`returnTime_eq`);
* finiteness: if every state of a set closed under transitions reaches `v` along transitions of
  positive probability, then `E_x[τ_v] < ∞` on that set (`hittingTime_ne_top`), because
  `P_x(τ_v > t)` decays geometrically;
* the triangle inequality `E_x[τ_w] ≤ E_x[τ_v] + E_v[τ_w]` (`hittingTime_le_add`), proved by
  splitting each trajectory at its first visit to `v`;
* Kac's formula: for a stationary measure `π`, `π v * E_v[τ⁺_v] = ∑ x, π x` whenever
  `∑ x, π x * E_x[τ_v]` is finite (`mul_returnTime_eq`); for a stationary distribution,
  `π v * E_v[τ⁺_v] = 1` (`IsStationary.mul_returnTime_eq_one`);
* Markov's inequality in tail form: `(t + 1) * P_x(τ_v > t) ≤ E_x[τ_v]`
  (`mul_survival_le_hittingTime`).

The simple random walk on a graph (`Cslib.Probability.MarkovChain.randomWalk`) is the main
instance.

## Main definitions

* `Cslib.Probability.MarkovChain.survival`: the probability `P_x(τ_v > t)`.
* `Cslib.Probability.MarkovChain.firstHit`: the probability `P_x(τ_v = t)`.
* `Cslib.Probability.MarkovChain.hittingTime`: the expected hitting time `E_x[τ_v]`.
* `Cslib.Probability.MarkovChain.returnSurvival`, `Cslib.Probability.MarkovChain.returnTime`:
  the probability `P_v(τ⁺_v > t)` and the expected return time `E_v[τ⁺_v]`.

## Main results

* `Cslib.Probability.MarkovChain.hittingTime_eq_of_ne`,
  `Cslib.Probability.MarkovChain.returnTime_eq`: first-step equations.
* `Cslib.Probability.MarkovChain.hittingTime_ne_top`: hitting times are finite in a closed set
  from which the target is reachable.
* `Cslib.Probability.MarkovChain.hittingTime_le_add`: the triangle inequality.
* `Cslib.Probability.MarkovChain.mul_returnTime_eq`,
  `Cslib.Probability.MarkovChain.IsStationary.mul_returnTime_eq_one`: Kac's formula.
* `Cslib.Probability.MarkovChain.mul_survival_le_hittingTime`: Markov's inequality.

## References

* [D. A. Levin, Y. Peres, *Markov Chains and Mixing Times*][LevinPeres2017]
-/

public section

namespace Cslib.Probability.MarkovChain

open Finset
open scoped ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V] (P : MarkovChain V)

omit [DecidableEq V] in
/-- The transition probabilities from each state sum to `1`. -/
theorem sum_apply (x : V) : ∑ y, P x y = 1 := by
  rw [← (P x).tsum_coe, tsum_fintype]

/-- `survival P v t x` is the probability `P_x(τ_v > t)` that the chain with transition
probabilities `P`, started at `x`, avoids `v` at all times `0, …, t`. -/
noncomputable def survival (v : V) : ℕ → V → ℝ≥0∞
  | 0, x => if x = v then 0 else 1
  | t + 1, x => if x = v then 0 else ∑ y, P x y * survival v t y

/-- `firstHit P v t x` is the probability `P_x(τ_v = t)` that the chain started at `x` visits `v`
for the first time at time `t`. -/
noncomputable def firstHit (v : V) : ℕ → V → ℝ≥0∞
  | 0, x => if x = v then 1 else 0
  | t + 1, x => if x = v then 0 else ∑ y, P x y * firstHit v t y

/-- The **expected hitting time** `E_x[τ_v]` of `v` from `x`, by the tail-sum formula
`E_x[τ_v] = ∑' t, P_x(τ_v > t)`. It is `0` when `x = v` and may be `∞`. -/
noncomputable def hittingTime (v x : V) : ℝ≥0∞ :=
  ∑' t, survival P v t x

/-- `returnSurvival P v t` is the probability `P_v(τ⁺_v > t)` that the chain started at `v` does
not return to `v` at any of the times `1, …, t`. -/
noncomputable def returnSurvival (v : V) : ℕ → ℝ≥0∞
  | 0 => 1
  | t + 1 => ∑ y, P v y * survival P v t y

/-- The **expected return time** `E_v[τ⁺_v]` to `v`, by the tail-sum formula
`E_v[τ⁺_v] = ∑' t, P_v(τ⁺_v > t)`. -/
noncomputable def returnTime (v : V) : ℝ≥0∞ :=
  ∑' t, returnSurvival P v t

variable {P}

/-! ### Survival probabilities -/

@[simp]
theorem survival_self (v : V) (t : ℕ) : survival P v t v = 0 := by
  cases t <;> simp [survival]

theorem survival_zero_of_ne {v x : V} (hx : x ≠ v) : survival P v 0 x = 1 := by
  simp [survival, hx]

theorem survival_succ_of_ne {v x : V} (hx : x ≠ v) (t : ℕ) :
    survival P v (t + 1) x = ∑ y, P x y * survival P v t y := by
  simp [survival, hx]

/-- Survival probabilities are probabilities. -/
theorem survival_le_one (v : V) : ∀ (t : ℕ) (x : V), survival P v t x ≤ 1
  | 0, x => by unfold survival; split_ifs <;> simp
  | t + 1, x => by
    unfold survival
    split_ifs
    · exact zero_le_one
    · calc ∑ y, P x y * survival P v t y ≤ ∑ y, P x y * 1 :=
            sum_le_sum fun y _ => mul_le_mul_right (survival_le_one v t y) _
        _ = 1 := by simp [sum_apply P x]

theorem survival_ne_top (v : V) (t : ℕ) (x : V) : survival P v t x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (survival_le_one v t x)

/-- **Markov property of survival.** If, from every state of a set `S` closed under transitions,
the probability of avoiding `v` for `m` more steps is at most `c`, then
`P_x(τ_v > t + m) ≤ c * P_x(τ_v > t)` for `x ∈ S`. -/
theorem survival_add_le {S : Set V} (hS : ∀ a ∈ S, ∀ b, P a b ≠ 0 → b ∈ S) {v : V} {m : ℕ}
    {c : ℝ≥0∞} (hc : ∀ y ∈ S, survival P v m y ≤ c) :
    ∀ (t : ℕ), ∀ x ∈ S, survival P v (t + m) x ≤ c * survival P v t x
  | 0, x, hx => by
    rcases eq_or_ne x v with rfl | hxv
    · simp [show 0 + m = m by omega]
    · simpa [survival_zero_of_ne hxv] using hc x hx
  | t + 1, x, hx => by
    rcases eq_or_ne x v with rfl | hxv
    · simp [show t + 1 + m = t + m + 1 by omega]
    · rw [show t + 1 + m = t + m + 1 by omega, survival_succ_of_ne hxv, survival_succ_of_ne hxv,
        mul_sum]
      refine sum_le_sum fun y _ => ?_
      rcases eq_or_ne (P x y) 0 with h | h
      · simp [h]
      · calc P x y * survival P v (t + m) y ≤ P x y * (c * survival P v t y) :=
              mul_le_mul_right (survival_add_le hS hc t y (hS x hx y h)) _
          _ = c * (P x y * survival P v t y) := mul_left_comm _ _ _

/-- Survival probabilities do not increase with time. -/
theorem survival_succ_le (v : V) (t : ℕ) (x : V) :
    survival P v (t + 1) x ≤ survival P v t x := by
  simpa using survival_add_le (S := Set.univ) (by simp) (m := 1) (c := 1)
    (fun y _ => survival_le_one v 1 y) t x trivial

theorem survival_antitone (v x : V) :
    Antitone fun t => survival P v t x :=
  antitone_nat_of_succ_le fun t => survival_succ_le v t x

/-- One step towards `y` lowers the survival probability by `P x y` times the probability of
hitting `v` from `y`. -/
theorem survival_succ_add_le {v x : V} (hx : x ≠ v) (y : V) (t : ℕ) :
    survival P v (t + 1) x + P x y * (1 - survival P v t y) ≤ 1 := by
  rw [survival_succ_of_ne hx, ← add_sum_erase _ _ (mem_univ y)]
  calc P x y * survival P v t y + ∑ z ∈ univ.erase y, P x z * survival P v t z
        + P x y * (1 - survival P v t y)
      ≤ P x y * survival P v t y + ∑ z ∈ univ.erase y, P x z
        + P x y * (1 - survival P v t y) := by
        gcongr with z
        exact mul_le_of_le_one_right' (survival_le_one v t z)
    _ = P x y * (survival P v t y + (1 - survival P v t y)) + ∑ z ∈ univ.erase y, P x z := by
        ring
    _ = 1 := by
        rw [add_tsub_cancel_of_le (survival_le_one v t y), mul_one, add_sum_erase _ _
          (mem_univ y), sum_apply P x]

/-- If `v` is reachable from `x` along transitions of positive probability, then the chain from
`x` hits `v` within some finite time with positive probability. -/
theorem exists_survival_lt_one {v x : V}
    (h : Relation.ReflTransGen (fun a b => P a b ≠ 0) x v) : ∃ m, survival P v m x < 1 := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, by simp⟩
  | @head x y hxy _ ih =>
    obtain ⟨m, hm⟩ := ih
    rcases eq_or_ne x v with rfl | hxv
    · exact ⟨0, by simp⟩
    refine ⟨m + 1, ?_⟩
    have hle := survival_succ_add_le (P := P) hxv y m
    have hpos : P x y * (1 - survival P v m y) ≠ 0 :=
      mul_ne_zero hxy (tsub_pos_of_lt hm).ne'
    exact (ENNReal.lt_add_right (survival_ne_top v (m + 1) x) hpos).trans_le hle

/-! ### Expected hitting and return times -/

@[simp]
theorem hittingTime_self (v : V) : hittingTime P v v = 0 := by
  simp [hittingTime]

/-- **First-step equation** for expected hitting times. -/
theorem hittingTime_eq_of_ne {v x : V} (hx : x ≠ v) :
    hittingTime P v x = 1 + ∑ y, P x y * hittingTime P v y := by
  rw [hittingTime, tsum_eq_zero_add' CompleteLattice.summable, survival_zero_of_ne hx]
  simp_rw [survival_succ_of_ne hx, hittingTime, ← ENNReal.tsum_mul_left]
  rw [Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]

/-- **First-step equation** for the expected return time. -/
theorem returnTime_eq (v : V) : returnTime P v = 1 + ∑ y, P v y * hittingTime P v y := by
  rw [returnTime, tsum_eq_zero_add' CompleteLattice.summable]
  simp_rw [returnSurvival, hittingTime, ← ENNReal.tsum_mul_left]
  rw [Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]

/-- **Markov's inequality** for hitting times: the probability of avoiding `v` up to time `t` is
at most `E_x[τ_v] / (t + 1)`. -/
theorem mul_survival_le_hittingTime (v : V) (t : ℕ) (x : V) :
    (t + 1 : ℝ≥0∞) * survival P v t x ≤ hittingTime P v x := by
  calc (t + 1 : ℝ≥0∞) * survival P v t x = ∑ i ∈ range (t + 1), survival P v t x := by
        simp
    _ ≤ ∑ i ∈ range (t + 1), survival P v i x :=
        sum_le_sum fun i hi => survival_antitone v x (Nat.lt_succ_iff.1 (mem_range.1 hi))
    _ ≤ hittingTime P v x := sum_le_tsum _

/-- **Finiteness of hitting times.** If every state of a set `S` closed under transitions reaches
`v` along transitions of positive probability, the expected hitting time of `v` from every state
of `S` is finite: the survival probabilities decay geometrically. -/
theorem hittingTime_ne_top {S : Set V}
    (hS : ∀ a ∈ S, ∀ b, P a b ≠ 0 → b ∈ S) {v : V}
    (hreach : ∀ y ∈ S, Relation.ReflTransGen (fun a b => P a b ≠ 0) y v) {x : V} (hx : x ∈ S) :
    hittingTime P v x ≠ ⊤ := by
  classical
  have hm : ∀ y, ∃ m, y ∈ S → survival P v m y < 1 := fun y => by
    by_cases hy : y ∈ S
    · obtain ⟨m, hm⟩ := exists_survival_lt_one (hreach y hy)
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => (hy h).elim⟩
  choose m hm using hm
  set M := univ.sup m + 1 with hM
  have hMy : ∀ y ∈ S, survival P v M y < 1 := fun y hy =>
    (survival_antitone v y (le_trans (le_sup (mem_univ y)) (Nat.le_succ _))).trans_lt
      (hm y hy)
  set c := univ.sup fun y => if y ∈ S then survival P v M y else 0 with hc
  have hc1 : c < 1 := by
    rw [hc, Finset.sup_lt_iff (by simp)]
    intro y _
    split_ifs with hy
    · exact hMy y hy
    · simp
  have hcy : ∀ y ∈ S, survival P v M y ≤ c := fun y hy => by
    have := le_sup (f := fun y => if y ∈ S then survival P v M y else 0) (mem_univ y)
    simpa [hy] using this
  have hgeom : ∀ (k r : ℕ), ∀ x ∈ S, survival P v (k * M + r) x ≤ c ^ k := by
    intro k r
    induction k with
    | zero => intro x _; simpa using survival_le_one v r x
    | succ k ih =>
      intro x hx
      calc survival P v ((k + 1) * M + r) x = survival P v ((k * M + r) + M) x := by
            congr 1; ring
        _ ≤ c * survival P v (k * M + r) x := survival_add_le hS hcy _ x hx
        _ ≤ c * c ^ k := mul_le_mul_right (ih x hx) _
        _ = c ^ (k + 1) := (pow_succ' c k).symm
  have : NeZero M := ⟨by omega⟩
  rw [hittingTime, ← (Nat.divModEquiv M).symm.tsum_eq, tsum_prod']
  refine ne_top_of_le_ne_top (b := ∑' k : ℕ, (M : ℝ≥0∞) * c ^ k) ?_ ?_
  · rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top M)
      (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hc1).ne')
  · refine tsum_le_tsum fun k => ?_
    rw [tsum_fintype]
    calc ∑ r : Fin M, survival P v ((Nat.divModEquiv M).symm (k, r)) x
        ≤ ∑ _r : Fin M, c ^ k := sum_le_sum fun r _ => hgeom k r x hx
      _ = M * c ^ k := by simp

/-! ### The triangle inequality -/

/-- The Cauchy product formula in `ℝ≥0∞`, where every family is summable. -/
private theorem tsum_mul_tsum_eq_tsum_sum_range (f g : ℕ → ℝ≥0∞) :
    (∑' n, f n) * ∑' n, g n = ∑' n, ∑ k ∈ range (n + 1), f k * g (n - k) := by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  rw [← ENNReal.tsum_mul_right]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [← tsum_prod' (f := fun p : ℕ × ℕ => f p.1 * g p.2),
    ← HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq, tsum_sigma']
  refine tsum_congr fun n => ?_
  rw [← Finset.tsum_subtype]
  rfl

theorem firstHit_self_succ (v : V) (t : ℕ) : firstHit P v (t + 1) v = 0 := by
  simp [firstHit]

theorem firstHit_zero_of_ne {v x : V} (hx : x ≠ v) : firstHit P v 0 x = 0 := by
  simp [firstHit, hx]

theorem firstHit_succ_of_ne {v x : V} (hx : x ≠ v) (t : ℕ) :
    firstHit P v (t + 1) x = ∑ y, P x y * firstHit P v t y := by
  simp [firstHit, hx]

/-- By time `t`, the chain has either visited `v` for the first time at some time `j ≤ t` or
avoided it. -/
theorem sum_firstHit_add_survival (v : V) :
    ∀ (t : ℕ) (x : V), ∑ j ∈ range (t + 1), firstHit P v j x + survival P v t x = 1
  | 0, x => by
    rcases eq_or_ne x v with rfl | hx
    · simp [firstHit]
    · simp [firstHit, survival, hx]
  | t + 1, x => by
    rcases eq_or_ne x v with rfl | hx
    · rw [sum_range_succ']
      simp [firstHit]
    · rw [sum_range_succ', firstHit_zero_of_ne hx, add_zero, survival_succ_of_ne hx]
      simp_rw [firstHit_succ_of_ne hx]
      rw [sum_comm, ← sum_add_distrib]
      simp_rw [← mul_sum, ← mul_add, sum_firstHit_add_survival v t, mul_one]
      exact sum_apply P x

theorem tsum_firstHit_le_one (v x : V) : ∑' j, firstHit P v j x ≤ 1 :=
  ENNReal.tsum_le_of_sum_range_le fun n => by
    cases n with
    | zero => simp
    | succ t => exact (le_self_add).trans (sum_firstHit_add_survival v t x).le

/-- To avoid `w` up to time `t`, the chain either avoids `v` or visits `v` first at some time
`j ≤ t` and then avoids `w` for the remaining `t - j` steps. -/
theorem survival_le_survival_add_sum (v w : V) :
    ∀ (t : ℕ) (x : V), survival P w t x ≤
      survival P v t x + ∑ j ∈ range (t + 1), firstHit P v j x * survival P w (t - j) v
  | 0, x => by
    rcases eq_or_ne x v with rfl | hx
    · simp [firstHit]
    · rw [survival_zero_of_ne hx]
      exact le_add_right (survival_le_one w 0 x)
  | t + 1, x => by
    rcases eq_or_ne x w with rfl | hxw
    · simp
    rcases eq_or_ne x v with rfl | hxv
    · rw [sum_range_succ']
      simp [firstHit]
    rw [survival_succ_of_ne hxw, survival_succ_of_ne hxv, sum_range_succ', firstHit_zero_of_ne hxv,
      zero_mul, add_zero]
    simp_rw [firstHit_succ_of_ne hxv, Nat.add_sub_add_right, sum_mul]
    rw [sum_comm, ← sum_add_distrib]
    refine sum_le_sum fun y _ => ?_
    simp_rw [mul_assoc, ← mul_sum, ← mul_add]
    exact mul_le_mul_right (survival_le_survival_add_sum v w t y) _

/-- **Triangle inequality** for expected hitting times: `E_x[τ_w] ≤ E_x[τ_v] + E_v[τ_w]`. -/
theorem hittingTime_le_add (v w x : V) :
    hittingTime P w x ≤ hittingTime P v x + hittingTime P w v := by
  calc hittingTime P w x
      ≤ ∑' t, (survival P v t x +
          ∑ j ∈ range (t + 1), firstHit P v j x * survival P w (t - j) v) :=
        tsum_le_tsum fun t => survival_le_survival_add_sum v w t x
    _ = hittingTime P v x + (∑' j, firstHit P v j x) * hittingTime P w v := by
        rw [tsum_add, hittingTime, hittingTime, tsum_mul_tsum_eq_tsum_sum_range]
    _ ≤ hittingTime P v x + 1 * hittingTime P w v := by
        gcongr
        exact tsum_firstHit_le_one v x
    _ = hittingTime P v x + hittingTime P w v := by rw [one_mul]

/-! ### Kac's formula -/

/-- **Kac's formula.** If `π` is a stationary measure (`∑ x, π x * P x y = π y`) and the
`π`-average of the hitting times of `v` is finite, then `π v * E_v[τ⁺_v] = ∑ x, π x`. For a
stationary distribution, the expected return time to `v` is `1 / π v`. -/
theorem mul_returnTime_eq {π : V → ℝ≥0∞} (hπ : ∀ y, ∑ x, π x * P x y = π y) (v : V)
    (hfin : ∑ x, π x * hittingTime P v x ≠ ⊤) :
    π v * returnTime P v = ∑ x, π x := by
  have key : ∀ w, π w * (1 + ∑ y, P w y * hittingTime P v y) =
      (if w = v then π v * returnTime P v else 0) + π w * hittingTime P v w := by
    intro w
    rcases eq_or_ne w v with rfl | hw
    · simp [returnTime_eq]
    · simp [hw, ← hittingTime_eq_of_ne hw]
  have hsum := congrArg (fun f => ∑ w, f w) (funext key)
  simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true] at hsum
  have h2 : ∑ w, π w * (1 + ∑ y, P w y * hittingTime P v y) =
      ∑ x, π x + ∑ x, π x * hittingTime P v x := by
    simp_rw [mul_add, mul_one, sum_add_distrib, mul_sum, ← mul_assoc]
    rw [sum_comm]
    simp_rw [← sum_mul, hπ]
  exact (ENNReal.add_left_inj hfin).1 (hsum.symm.trans h2)

/-- **Kac's formula** for a stationary distribution `π`: if the hitting times of `v` are finite
from every state in the support of `π`, then `π v * E_v[τ⁺_v] = 1`. -/
theorem IsStationary.mul_returnTime_eq_one {π : PMF V} (h : P.IsStationary π) (v : V)
    (hfin : ∀ x, π x ≠ 0 → hittingTime P v x ≠ ⊤) : π v * returnTime P v = 1 := by
  have hπ : ∀ y, ∑ x, π x * P x y = π y := fun y => by
    rw [← tsum_fintype (L := .unconditional V), ← PMF.bind_apply]
    exact congrArg (· y) h
  rw [mul_returnTime_eq hπ v, ← tsum_fintype (L := .unconditional V), π.tsum_coe]
  refine (ENNReal.sum_lt_top.2 fun x _ => ?_).ne
  rcases eq_or_ne (π x) 0 with hx | hx
  · simp [hx]
  · exact ENNReal.mul_lt_top (π.apply_ne_top x).lt_top (hfin x hx).lt_top

end Cslib.Probability.MarkovChain
