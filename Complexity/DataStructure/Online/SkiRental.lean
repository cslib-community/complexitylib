/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Online.Basic

/-!
# Ski rental: the break-even strategy and the deterministic lower bound

This file instantiates `Cslib.DataStructure.Online.Problem` for the deterministic ski-rental
(rent-or-buy) problem. The rent-or-buy framing goes back to [Karlin, Manasse, Rudolph, and
Sleator, *Competitive snoopy caching*][KarlinManasseRudolphSleator1988]; the textbook treatment
is in [Borodin and El-Yaniv, *Online Computation and Competitive Analysis*][BorodinElYaniv1998].

Each request is one more day of skiing. Before every day the skier either rents for that day
(cost `1`) or buys (cost `B`, after which every further day is free). The online strategy does not
know how many days remain. Offline schedules use the same states, transitions and costs, so the
offline optimum on `n` days is `min n B` (`exists_optimal_schedule`,
`min_le_scheduleCost`).

The **break-even** strategy rents for `B - 1` days and buys on day `B`. On every request sequence
and against every valid offline schedule its cost satisfies `B * ALG ≤ (2B - 1) * OPT`
(`breakEven_mul_cost_le`), i.e. competitive ratio `2 - 1/B` with **no additive constant**.
Conversely every deterministic online strategy has an instance with `OPT ≥ 1` and
`(2B - 1) * OPT ≤ B * ALG` (`exists_witness`), so no deterministic strategy achieves any rational
ratio `p / q < 2 - 1/B` without an additive constant (`exists_ratio_violation_of_lt`).

The break-even strategy is `(1, B - 1)`-competitive (`breakEven_isCompetitive_one`), so with an
additive constant the factor-`1` question is trivial; the meaningful ratio has no additive
constant, and ratios for ski rental are stated with additive constant `0`.

## Main definitions

* `Cslib.DataStructure.Online.SkiRental.problem`: the ski-rental `Online.Problem` with purchase
  price `B`.
* `SkiRental.rentThenBuy`: the deterministic strategy that rents for `t` days and buys on day
  `t + 1`.
* `SkiRental.breakEven`: `rentThenBuy (B - 1)`.

## Main results

* `min_le_scheduleCost`, `exists_optimal_schedule`: the offline optimum is `min n B`.
* `cost_rentThenBuy`: exact cost of the rent-then-buy strategies.
* `breakEven_mul_cost_le`, `breakEven_isCompetitive_two`: the break-even strategy has ratio
  `2 - 1/B`, hence is `(2, 0)`-competitive.
* `exists_witness`, `exists_ratio_violation_of_lt`, `not_isCompetitive_one`: no deterministic
  strategy beats ratio `2 - 1/B` without an additive constant.
* `exists_rentThenBuy_cost_eq`: on boundedly many days, every deterministic strategy has the
  cost of a rent-then-buy strategy.

Randomized ski rental (ratio `1 / (1 - (1 - 1/B)^B) ≤ e/(e-1)` and its matching lower bound) is in
`Complexity.DataStructure.Online.SkiRental.Randomized`.

## References

* [A. R. Karlin, M. S. Manasse, L. Rudolph, and D. D. Sleator, *Competitive snoopy
  caching*][KarlinManasseRudolphSleator1988]
* [A. Borodin and R. El-Yaniv, *Online Computation and Competitive Analysis*][BorodinElYaniv1998]
-/

public section

namespace Cslib.DataStructure.Online.SkiRental

/-- Ski-rental cost of moving from ownership state `b` to `b'` while serving one ski day, with
purchase price `B`: free once owned, `B` on the day of purchase, and `1` for a rented day. -/
@[expose]
def stepCost (B : Nat) (b : Bool) (_ : Unit) (b' : Bool) : Nat :=
  if b then 0 else if b' then B else 1

/-- The ski-rental `Online.Problem` with purchase price `B`. The state records whether the skis
have been bought; buying is irreversible; every run starts without skis. -/
abbrev problem (B : Nat) : Problem where
  State := Bool
  Req := Unit
  ValidInit b := b = false
  ValidStep b _ b' := b = true → b' = true
  stepCost := stepCost B

@[simp]
theorem stepCost_true (B : Nat) (u : Unit) (b' : Bool) : stepCost B true u b' = 0 := rfl

@[simp]
theorem stepCost_false_true (B : Nat) (u : Unit) : stepCost B false u true = B := rfl

@[simp]
theorem stepCost_false_false (B : Nat) (u : Unit) : stepCost B false u false = 1 := rfl

/-! ### Offline schedules -/

/-- Once the skis are owned, every valid continuation keeps them and costs nothing. -/
theorem scheduleCost_true_eq_zero {B : Nat} {reqs : List Unit} {states : List Bool}
    (hv : (problem B).ValidSchedule true reqs states) :
    (problem B).scheduleCost true reqs states = 0 := by
  induction reqs generalizing states with
  | nil => cases states <;> rfl
  | cons r rs ih =>
    cases states with
    | nil => rfl
    | cons b bs =>
      obtain ⟨hstep, hrest⟩ := hv
      have hb : b = true := hstep rfl
      subst hb
      change stepCost B true r true + _ = 0
      rw [stepCost_true, ih hrest]

/-- **Offline lower bound.** Every valid schedule from the initial state costs at least
`min n B` on `n` ski days. -/
theorem min_le_scheduleCost {B : Nat} {reqs : List Unit} {states : List Bool}
    (hv : (problem B).ValidSchedule false reqs states) :
    min reqs.length B ≤ (problem B).scheduleCost false reqs states := by
  induction reqs generalizing states with
  | nil => simp only [List.length_nil, Nat.zero_min, Nat.zero_le]
  | cons r rs ih =>
    cases states with
    | nil => exact absurd hv id
    | cons b bs =>
      obtain ⟨-, hrest⟩ := hv
      cases b with
      | false =>
        change _ ≤ stepCost B false r false + _
        have := ih hrest
        simp only [stepCost_false_false, List.length_cons]
        omega
      | true =>
        change _ ≤ stepCost B false r true + _
        simp only [stepCost_false_true]
        omega

/-- The constant schedule `replicate n b` is valid from `b₀` whenever `b₀ = true → b = true`. -/
theorem validSchedule_replicate {B : Nat} {b₀ b : Bool} (h : b₀ = true → b = true)
    (reqs : List Unit) :
    (problem B).ValidSchedule b₀ reqs (List.replicate reqs.length b) := by
  induction reqs generalizing b₀ with
  | nil => trivial
  | cons r rs ih => exact ⟨h, ih fun hb => hb ▸ rfl⟩

/-- Renting every day costs one per day. -/
theorem scheduleCost_replicate_false (B : Nat) (reqs : List Unit) :
    (problem B).scheduleCost false reqs (List.replicate reqs.length false) = reqs.length := by
  induction reqs with
  | nil => rfl
  | cons r rs ih =>
    change stepCost B false r false + _ = _
    rw [stepCost_false_false, ih, List.length_cons, Nat.add_comm]

/-- Buying on the first day costs `B` on any nonempty request sequence. -/
theorem scheduleCost_replicate_true (B : Nat) {reqs : List Unit} (h : reqs ≠ []) :
    (problem B).scheduleCost false reqs (List.replicate reqs.length true) = B := by
  cases reqs with
  | nil => exact absurd rfl h
  | cons r rs =>
    change stepCost B false r true +
      (problem B).scheduleCost true rs (List.replicate rs.length true) = B
    rw [stepCost_false_true, scheduleCost_true_eq_zero (validSchedule_replicate (fun _ => rfl) rs),
      Nat.add_zero]

/-- **Offline optimum.** Renting every day (if `n ≤ B`) or buying on the first day (otherwise)
is a valid schedule costing exactly `min n B`. -/
theorem exists_optimal_schedule (B : Nat) (reqs : List Unit) :
    ∃ states, (problem B).ValidSchedule false reqs states ∧
      (problem B).scheduleCost false reqs states = min reqs.length B := by
  by_cases hn : reqs.length ≤ B
  · refine ⟨_, validSchedule_replicate (b := false) (fun h => h) reqs, ?_⟩
    rw [scheduleCost_replicate_false, Nat.min_eq_left hn]
  · have hne : reqs ≠ [] := by grind
    refine ⟨_, validSchedule_replicate (b := true) (fun _ => rfl) reqs, ?_⟩
    rw [scheduleCost_replicate_true B hne, Nat.min_eq_right (by omega)]

/-- A schedule that rents for `d` days and then buys costs `d + B`. -/
theorem scheduleCost_replicate_false_append_true (B d : Nat) (reqs : List Unit)
    (hlen : reqs.length = d + 1) :
    (problem B).scheduleCost false reqs (List.replicate d false ++ [true]) = d + B := by
  induction d generalizing reqs with
  | zero =>
    match reqs, hlen with
    | [r], _ =>
      change stepCost B false r true + 0 = 0 + B
      rw [stepCost_false_true]
      omega
  | succ d ih =>
    match reqs, hlen with
    | r :: rs, hlen =>
      change stepCost B false r false +
        (problem B).scheduleCost false rs (List.replicate d false ++ [true]) = _
      rw [stepCost_false_false, ih rs (by simpa using hlen)]
      omega

/-- A valid schedule that rents for `d` days and then buys costs `d + B`, whatever follows the
purchase. -/
theorem scheduleCost_replicate_false_append_true_cons {B d : Nat} {reqs : List Unit}
    {tail : List Bool}
    (hv : (problem B).ValidSchedule false reqs (List.replicate d false ++ true :: tail)) :
    (problem B).scheduleCost false reqs (List.replicate d false ++ true :: tail) = d + B := by
  induction d generalizing reqs with
  | zero =>
    cases reqs with
    | nil => cases hv
    | cons r rs =>
      change stepCost B false r true + (problem B).scheduleCost true rs tail = 0 + B
      rw [stepCost_false_true, scheduleCost_true_eq_zero hv.2]
      omega
  | succ d ih =>
    cases reqs with
    | nil => cases hv
    | cons r rs =>
      change stepCost B false r false +
        (problem B).scheduleCost false rs (List.replicate d false ++ true :: tail) = d + 1 + B
      rw [stepCost_false_false, ih hv.2]
      omega

/-! ### Rent-then-buy strategies -/

/-- The deterministic strategy that rents for the first `t` days and buys on day `t + 1`. Its
memory records whether the skis are owned and how many days have been rented. -/
abbrev rentThenBuy (B t : Nat) : DetStrategy (problem B) where
  Mem := Bool × Nat
  ValidMem _ := True
  project m := m.1
  init b := (b, 0)
  step m _ := if m.1 then m else if m.2 = t then (true, m.2) else (false, m.2 + 1)
  valid_init {b} hb := ⟨trivial, rfl⟩
  valid_step {m} _ _ := by
    refine ⟨trivial, fun h => ?_⟩
    change m.1 = true at h
    simp only [h, ↓reduceIte]

@[simp]
theorem rentThenBuy_project (B t : Nat) (m : Bool × Nat) : (rentThenBuy B t).project m = m.1 :=
  rfl

@[simp]
theorem rentThenBuy_step_true (B t k : Nat) (u : Unit) :
    (rentThenBuy B t).step (true, k) u = (true, k) := rfl

theorem rentThenBuy_step_false_eq (B t : Nat) (u : Unit) :
    (rentThenBuy B t).step (false, t) u = (true, t) := by
  simp only [rentThenBuy, Bool.false_eq_true, ↓reduceIte]

theorem rentThenBuy_step_false_ne {B t k : Nat} (hk : k ≠ t) (u : Unit) :
    (rentThenBuy B t).step (false, k) u = (false, k + 1) := by
  simp only [rentThenBuy, Bool.false_eq_true, ↓reduceIte, hk]

theorem rentThenBuy_costFrom_true (B t k : Nat) (reqs : List Unit) :
    (rentThenBuy B t).costFrom (true, k) reqs = 0 := by
  induction reqs with
  | nil => rfl
  | cons r rs ih =>
    rw [DetStrategy.costFrom_cons, rentThenBuy_step_true, ih]
    rfl

/-- From the rented state after `k ≤ t` days, the remaining cost is the number of remaining days if
the skier stops before day `t + 1`, and `t - k + B` otherwise. -/
theorem rentThenBuy_costFrom_false {B t k : Nat} (hk : k ≤ t) (reqs : List Unit) :
    (rentThenBuy B t).costFrom (false, k) reqs =
      if k + reqs.length ≤ t then reqs.length else t - k + B := by
  induction reqs generalizing k with
  | nil =>
    simp only [List.length_nil, Nat.add_zero, hk, ↓reduceIte]
    rfl
  | cons r rs ih =>
    rw [DetStrategy.costFrom_cons]
    by_cases hkt : k = t
    · subst hkt
      rw [rentThenBuy_step_false_eq, rentThenBuy_costFrom_true]
      change stepCost B false r true + 0 = _
      simp only [stepCost_false_true, List.length_cons, Nat.add_zero]
      rw [ite_eq_right (by omega), Nat.sub_self, Nat.zero_add]
    · rw [rentThenBuy_step_false_ne hkt, ih (by omega)]
      change stepCost B false r false + _ = _
      simp only [stepCost_false_false, List.length_cons]
      split_ifs with h₁ h₂ h₂ <;> omega

/-- **Exact cost of rent-then-buy.** On `n` ski days, `rentThenBuy B t` pays `n` if `n ≤ t` and
`t + B` otherwise. -/
theorem cost_rentThenBuy (B t : Nat) (reqs : List Unit) :
    (rentThenBuy B t).cost false reqs = if reqs.length ≤ t then reqs.length else t + B := by
  rw [DetStrategy.cost_eq_costFrom _ rfl]
  change (rentThenBuy B t).costFrom (false, 0) reqs = _
  rw [rentThenBuy_costFrom_false (Nat.zero_le t), Nat.zero_add, Nat.sub_zero]

/-- The break-even strategy: rent for `B - 1` days and buy on day `B`. -/
abbrev breakEven (B : Nat) : DetStrategy (problem B) :=
  rentThenBuy B (B - 1)

/-- **Break-even upper bound** (for the rent-or-buy framing of [KarlinManasseRudolphSleator1988]
only): on every request sequence and against every valid offline schedule, the break-even strategy
satisfies `B * ALG ≤ (2B - 1) * OPT`, i.e. it has competitive ratio `2 - 1/B` with no additive
constant. -/
theorem breakEven_mul_cost_le {B : Nat} {reqs : List Unit} {states : List Bool}
    (hv : (problem B).ValidSchedule false reqs states) :
    B * (breakEven B).cost false reqs ≤
      (2 * B - 1) * (problem B).scheduleCost false reqs states := by
  have hopt := min_le_scheduleCost hv
  rw [cost_rentThenBuy]
  refine Nat.le_trans ?_ (Nat.mul_le_mul_left (2 * B - 1) hopt)
  split_ifs with hn
  · rw [Nat.min_eq_left (by omega)]
    exact Nat.mul_le_mul_right _ (by omega)
  · rw [Nat.min_eq_right (by omega), Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (by omega)

/-- The break-even strategy is `(2, 0)`-competitive. -/
theorem breakEven_isCompetitive_two (B : Nat) : (breakEven B).IsCompetitive 2 0 := by
  intro s₀ hs₀ reqs states hv
  subst hs₀
  rw [Nat.add_zero]
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB
    rw [cost_rentThenBuy]
    have := min_le_scheduleCost hv
    split_ifs <;> omega
  · have h := breakEven_mul_cost_le hv
    have h2 : (2 * B - 1) * (problem B).scheduleCost false reqs states ≤
        B * (2 * (problem B).scheduleCost false reqs states) := by
      rw [← Nat.mul_assoc, Nat.mul_comm B 2]
      exact Nat.mul_le_mul_right _ (by omega)
    exact Nat.le_of_mul_le_mul_left (Nat.le_trans h h2) hB

/-- With additive constant `B - 1`, the break-even strategy is even `(1, B - 1)`-competitive, which
is why the ski-rental ratio `2 - 1/B` is a statement without additive constant. -/
theorem breakEven_isCompetitive_one (B : Nat) : (breakEven B).IsCompetitive 1 (B - 1) := by
  intro s₀ hs₀ reqs states hv
  subst hs₀
  have := min_le_scheduleCost hv
  rw [cost_rentThenBuy, Nat.one_mul]
  split_ifs <;> omega

/-- The break-even bound is attained: on `B` ski days the break-even strategy pays `2B - 1` while
buying on the first day pays `B`. -/
theorem breakEven_cost_replicate (B : Nat) :
    (breakEven B).cost false (List.replicate B ()) = 2 * B - 1 := by
  rw [cost_rentThenBuy, List.length_replicate]
  split_ifs <;> omega

/-! ### Deterministic lower bound -/

/-- A Boolean list is either constantly `false`, or consists of `d` copies of `false`, then
`true`, then an arbitrary tail. -/
private theorem bool_list_cases (L : List Bool) :
    L = List.replicate L.length false ∨
      ∃ d tail, L = List.replicate d false ++ true :: tail := by
  induction L with
  | nil => exact Or.inl rfl
  | cons b L ih =>
    cases b with
    | true => exact Or.inr ⟨0, L, rfl⟩
    | false =>
      rcases ih with h | ⟨d, tail, h⟩
      · left
        rw [List.length_cons, List.replicate_succ, ← h]
      · right
        exact ⟨d + 1, tail, by rw [List.replicate_succ, List.cons_append, ← h]⟩

/-- `(2B - 1)(d + 1) ≤ B (d + B)` whenever `d + 1 ≤ B`. -/
private theorem ski_arith {B d : Nat} (h : d + 1 ≤ B) :
    (2 * B - 1) * (d + 1) ≤ B * (d + B) := by
  obtain ⟨e, rfl⟩ : ∃ e, B = d + 1 + e := ⟨B - (d + 1), by omega⟩
  rw [show 2 * (d + 1 + e) - 1 = d + 1 + e + (d + e) by omega]
  have h₁ : (d + 1 + e + (d + e)) * (d + 1) + (e * d + e * e) =
      (d + 1 + e) * (d + (d + 1 + e)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_comm e d]
    omega
  omega

/-- **Deterministic lower-bound witness.** For every deterministic online ski-rental strategy
(`1 ≤ B`) there are a request sequence and a valid offline schedule with offline cost at least `1`
and `(2B - 1) * OPT ≤ B * ALG`. The adversary stops skiing on the day the strategy buys, or after
`2B - 1` days if it never buys. -/
theorem exists_witness {B : Nat} (hB : 1 ≤ B) (A : DetStrategy (problem B)) :
    ∃ reqs states, (problem B).ValidSchedule false reqs states ∧
      1 ≤ (problem B).scheduleCost false reqs states ∧
      (2 * B - 1) * (problem B).scheduleCost false reqs states ≤ B * A.cost false reqs := by
  have hs₀ : (problem B).ValidInit false := rfl
  set N := 2 * B - 1 with hN
  set full : List Unit := List.replicate N ()
  have hlen : (A.states false full).length = N := by
    rw [DetStrategy.length_states, List.length_replicate]
  have hvA := A.validSchedule_states hs₀ full
  rcases bool_list_cases (A.states false full) with hall | ⟨d, tail, hsplit⟩
  · -- The strategy never buys: it pays `N = 2B - 1`, while buying on day one pays `B`.
    have hcost : A.cost false full = N := by
      change (problem B).scheduleCost false full (A.states false full) = N
      rw [hall, hlen]
      have := scheduleCost_replicate_false B full
      rwa [List.length_replicate] at this
    have hne : full ≠ [] := by
      rw [Ne, List.replicate_eq_nil_iff]
      omega
    have hvopt := validSchedule_replicate (B := B) (b₀ := false) (b := true) (fun _ => rfl) full
    refine ⟨full, _, hvopt, ?_, ?_⟩ <;> rw [scheduleCost_replicate_true B hne]
    · exact hB
    · rw [hcost, Nat.mul_comm]
  · -- The strategy buys on day `d + 1`; stop skiing that day.
    have hd : d + 1 ≤ N := by
      have := congrArg List.length hsplit
      simp only [hlen, List.length_append, List.length_replicate, List.length_cons] at this
      omega
    set reqs : List Unit := List.replicate (d + 1) ()
    have hreqs : reqs = full.take (d + 1) := by
      rw [List.take_replicate, Nat.min_eq_left hd]
    have hstates : A.states false reqs = List.replicate d false ++ [true] := by
      rw [hreqs, DetStrategy.states_take, hsplit, List.take_append, List.length_replicate,
        List.take_of_length_le (by rw [List.length_replicate]; omega), Nat.add_sub_cancel_left,
        List.take_succ_cons, List.take_zero]
    have hcost : A.cost false reqs = d + B := by
      change (problem B).scheduleCost false reqs (A.states false reqs) = _
      rw [hstates, scheduleCost_replicate_false_append_true B d reqs (List.length_replicate ..)]
    by_cases hdB : d + 1 ≤ B
    · -- Renting all `d + 1` days is cheaper.
      have hvopt := validSchedule_replicate (B := B) (b₀ := false) (b := false) (fun h => h) reqs
      refine ⟨reqs, _, hvopt, ?_, ?_⟩ <;>
        rw [scheduleCost_replicate_false, List.length_replicate]
      · omega
      · rw [hcost, hN]
        exact ski_arith hdB
    · -- Buying on day one is cheaper.
      have hne : reqs ≠ [] := by
        rw [Ne, List.replicate_eq_nil_iff]
        omega
      have hvopt := validSchedule_replicate (B := B) (b₀ := false) (b := true) (fun _ => rfl) reqs
      refine ⟨reqs, _, hvopt, ?_, ?_⟩ <;> rw [scheduleCost_replicate_true B hne]
      · exact hB
      · rw [hcost, Nat.mul_comm]
        exact Nat.mul_le_mul_left B (by omega)

/-- **Deterministic lower bound** ([BorodinElYaniv1998]): for every deterministic online
ski-rental strategy and every rational ratio `p / q < 2 - 1/B` (i.e. `p * B < (2B - 1) * q`) there
are a request sequence and a valid offline schedule with `p * OPT < q * ALG`. -/
theorem exists_ratio_violation_of_lt {B : Nat} (A : DetStrategy (problem B)) {p q : Nat}
    (hpq : p * B < (2 * B - 1) * q) :
    ∃ reqs states, (problem B).ValidSchedule false reqs states ∧
      p * (problem B).scheduleCost false reqs states < q * A.cost false reqs := by
  have hB : 1 ≤ B := by grind
  obtain ⟨reqs, states, hv, hpos, hle⟩ := exists_witness hB A
  refine ⟨reqs, states, hv, ?_⟩
  set opt := (problem B).scheduleCost false reqs states
  apply Nat.lt_of_mul_lt_mul_left (a := B)
  calc
    B * (p * opt) = (p * B) * opt := by rw [Nat.mul_comm p B, Nat.mul_assoc]
    _ < ((2 * B - 1) * q) * opt := Nat.mul_lt_mul_of_pos_right hpq hpos
    _ = q * ((2 * B - 1) * opt) := by rw [Nat.mul_comm _ q, Nat.mul_assoc]
    _ ≤ q * (B * A.cost false reqs) := Nat.mul_le_mul_left q hle
    _ = B * (q * A.cost false reqs) := by rw [Nat.mul_left_comm]

/-- For `B ≥ 2`, no deterministic online ski-rental strategy is `(1, 0)`-competitive. -/
theorem not_isCompetitive_one {B : Nat} (hB : 2 ≤ B) (A : DetStrategy (problem B)) :
    ¬ A.IsCompetitive 1 0 := by
  intro h
  obtain ⟨reqs, states, hv, hlt⟩ := exists_ratio_violation_of_lt A (p := 1) (q := 1) (by omega)
  have := h false rfl reqs states hv
  omega

/-- On the first `N` ski days every deterministic strategy behaves like a rent-then-buy strategy:
there is a threshold `t` with `A.cost = (rentThenBuy B t).cost` on every `n ≤ N` days. Take `t`
to be the number of days the strategy rents before buying when it skis `N` days, or `N` if it never
buys. This reduces lower bounds over arbitrary deterministic strategies, such as the randomized
lower bound in `Complexity.DataStructure.Online.SkiRental.Randomized`, to threshold strategies. -/
theorem exists_rentThenBuy_cost_eq {B : Nat} (A : DetStrategy (problem B)) (N : Nat) :
    ∃ t, ∀ n ≤ N, A.cost false (List.replicate n ()) =
      (rentThenBuy B t).cost false (List.replicate n ()) := by
  have hlen : (A.states false (List.replicate N ())).length = N := by
    rw [DetStrategy.length_states, List.length_replicate]
  have htake : ∀ n ≤ N, A.states false (List.replicate n ()) =
      (A.states false (List.replicate N ())).take n := fun n hn => by
    rw [← DetStrategy.states_take, List.take_replicate, Nat.min_eq_left hn]
  have hrep : ∀ n, (problem B).scheduleCost false (List.replicate n ())
      (List.replicate n false) = n := fun n => by
    have := scheduleCost_replicate_false B (List.replicate n ())
    rwa [List.length_replicate] at this
  rcases bool_list_cases (A.states false (List.replicate N ())) with hall | ⟨d, tail, hsplit⟩
  · -- The strategy never buys within `N` days.
    refine ⟨N, fun n hn => ?_⟩
    rw [cost_rentThenBuy, List.length_replicate, ite_eq_left hn]
    change (problem B).scheduleCost false _ (A.states false _) = n
    rw [htake n hn, hall, hlen, List.take_replicate, Nat.min_eq_left hn, hrep]
  · -- The strategy buys on day `d + 1`.
    refine ⟨d, fun n hn => ?_⟩
    have hvn := A.validSchedule_states (s₀ := false) rfl (List.replicate n ())
    rw [cost_rentThenBuy, List.length_replicate]
    change (problem B).scheduleCost false _ (A.states false _) = _
    rw [htake n hn, hsplit] at hvn ⊢
    split_ifs with hnd
    · rw [List.take_append_of_le_length (by rw [List.length_replicate]; exact hnd),
        List.take_replicate, Nat.min_eq_left hnd, hrep]
    · rw [List.take_append, List.take_of_length_le (by rw [List.length_replicate]; omega),
        List.length_replicate, show n - d = (n - d - 1) + 1 by omega, List.take_succ_cons]
        at hvn ⊢
      exact scheduleCost_replicate_false_append_true_cons hvn

end Cslib.DataStructure.Online.SkiRental
