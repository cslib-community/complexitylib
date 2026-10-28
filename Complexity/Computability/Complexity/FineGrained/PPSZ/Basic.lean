/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.PPSZ.Defs
import Complexity.Probability.PMF.Event
import Mathlib.Analysis.MeanInequalities

/-!
# PPSZ with w-implication: the success probability

Let `σ` satisfy the formula `φ`. Along a run of PPSZ that agrees with `σ`, w-implied values are
the values of `σ` (`implied_eq`). A variable `x` is *forced* in the order `π` when the values of
`σ` on the variables before `x` w-imply a value on `x` (`Forced`). The run in the order `π`
outputs `σ` with probability exactly `2^{-u}`, where `u` counts the unforced variables
(`run_apply_restrict`). Averaging over the orders and applying the arithmetic–geometric mean
inequality, one round outputs `σ` with probability at least `2^{-n + ∑ₓ Pr_π[x forced]}`
(`round_apply_ge`).

A unit clause is a w-implication with `w = 1` (`wImplied_one_of_forced`), so for `w ≥ 1` PPSZ
outputs every satisfying assignment at least as often as PPZ (`ppz_round_apply_le`), and the PPZ
bound `2^{-(1 - 1/k) n}` carries over (`round_success_ppz`).

## Main definitions

* `Cslib.Complexity.PPSZ.unforcedCount`: the number of unforced variables along the run that
  agrees with `σ`.
* `Cslib.Complexity.PPSZ.Forced`: a variable is forced in an order.

## Main results

* `Cslib.Complexity.PPSZ.implied_eq`: w-implied values agree with every satisfying assignment that
  extends the partial assignment.
* `Cslib.Complexity.PPSZ.run_apply_restrict`: a run in a fixed order outputs `σ` with probability
  `2^{-u}`.
* `Cslib.Complexity.PPSZ.round_apply_eq`: the success probability is the average of `2^{-u}` over
  the orders.
* `Cslib.Complexity.PPSZ.round_apply_ge`: one round outputs `σ` with probability at least
  `2^{-n + ∑ₓ Pr_π[x forced]}`.
* `Cslib.Complexity.PPSZ.ppz_round_apply_le`: for `w ≥ 1`, PPSZ outputs each satisfying assignment
  at least as often as PPZ.
* `Cslib.Complexity.PPSZ.round_success_ppz`: for `w ≥ 1`, PPSZ finds the unique satisfying
  assignment of a k-CNF formula with probability at least `2^{-(1 - 1/k) n}`.

## References

* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
* [D. Scheder, *PPSZ is better than you think*][Scheder2021]
* [R. Paturi, P. Pudlák, F. Zane, *Satisfiability Coding Lemma*][PPZ1997]
-/

@[expose] public section

namespace Cslib.Complexity.PPZ

variable {n : ℕ}

/-- A restriction of `σ` agrees with `σ` where it is defined. -/
theorem eq_of_restrict_eq_some {σ : Fin n → Bool} {D : Finset (Fin n)} {y : Fin n} {b : Bool}
    (h : restrict σ D y = some b) : σ y = b := by
  simp only [restrict] at h
  split_ifs at h
  exact Option.some_injective _ h

/-- Once all `n` variables are processed, the restriction of `σ` is all of `σ`. -/
theorem restrict_prefixSet_self (σ : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    restrict σ (prefixSet π n) = fun x => some (σ x) := by
  funext y
  simp [restrict, mem_prefixSet]

end Cslib.Complexity.PPZ

namespace Cslib.Complexity.PPSZ

open Cslib.Logic.PL
open Finset hiding restrict
open Cslib.Complexity.PPZ (restrict prefixSet mem_prefixSet)

variable {n : ℕ}

/-! ### w-implication -/

/-- **w-implied values are correct.** If `σ` satisfies `φ` and agrees with `τ` where `τ` is
defined, then every value w-implied under `τ` is the value of `σ`. -/
theorem WImplied.eq {φ : CNF (Fin n)} {w : ℕ} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
    (h : WImplied φ w τ x b) {σ : Fin n → Bool} (hσ : φ.eval σ = true)
    (hτ : ∀ y c, τ y = some c → σ y = c) : σ x = b := by
  obtain ⟨ψ, hψ, -, himp⟩ := h
  exact himp σ hτ ((CNF.eval_eq_true_iff σ ψ).mpr fun c hc =>
    (CNF.eval_eq_true_iff σ φ).mp hσ c (hψ c hc))

/-- **Monotonicity of w-implication**: it survives adding clauses, raising the budget `w` and
extending the partial assignment. -/
theorem WImplied.mono {φ φ' : CNF (Fin n)} {w w' : ℕ} {τ τ' : Fin n → Option Bool} {x : Fin n}
    {b : Bool} (h : WImplied φ w τ x b) (hφ : ∀ c ∈ φ, c ∈ φ') (hw : w ≤ w')
    (hτ : ∀ y c, τ y = some c → τ' y = some c) : WImplied φ' w' τ' x b := by
  obtain ⟨ψ, hψ, hlen, himp⟩ := h
  exact ⟨ψ, fun c hc => hφ c (hψ c hc), hlen.trans hw,
    fun σ hσ => himp σ fun y c hy => hσ y c (hτ y c hy)⟩

/-- A value returned by `implied` is w-implied. -/
theorem wImplied_of_implied_eq_some {φ : CNF (Fin n)} {w : ℕ} {τ : Fin n → Option Bool}
    {x : Fin n} {b : Bool} (h : implied φ w τ x = some b) : WImplied φ w τ x b := by
  unfold implied at h
  split_ifs at h with h1 h2 <;> cases h <;> assumption

/-- `implied` returns a value exactly when some value is w-implied. -/
theorem implied_ne_none_iff {φ : CNF (Fin n)} {w : ℕ} {τ : Fin n → Option Bool} {x : Fin n} :
    implied φ w τ x ≠ none ↔ ∃ b, WImplied φ w τ x b := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
    exact ⟨b, wImplied_of_implied_eq_some hb⟩
  · rintro ⟨b, hb⟩
    unfold implied
    split_ifs with h1 h2
    · exact Option.some_ne_none _
    · exact Option.some_ne_none _
    · cases b
      · exact absurd hb h2
      · exact absurd hb h1

/-- **Implied values are correct**: if `σ` satisfies `φ` and agrees with `τ` where `τ` is defined,
then the value implied on `x` under `τ`, if any, is `σ x`. -/
theorem implied_eq {φ : CNF (Fin n)} {w : ℕ} {σ : Fin n → Bool} (hσ : φ.eval σ = true)
    {τ : Fin n → Option Bool} (hτ : ∀ y b, τ y = some b → σ y = b) {x : Fin n} {b : Bool}
    (h : implied φ w τ x = some b) : σ x = b :=
  (wImplied_of_implied_eq_some h).eq hσ hτ

/-- Under a partial assignment with a satisfying extension, `implied` returns every w-implied
value. -/
theorem implied_eq_some {φ : CNF (Fin n)} {w : ℕ} {σ : Fin n → Bool} (hσ : φ.eval σ = true)
    {τ : Fin n → Option Bool} (hτ : ∀ y b, τ y = some b → σ y = b) {x : Fin n} {b : Bool}
    (h : WImplied φ w τ x b) : implied φ w τ x = some b := by
  obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp (implied_ne_none_iff.mpr ⟨b, h⟩)
  rw [hb', ← implied_eq hσ hτ hb', h.eq hσ hτ]

/-! ### Runs -/

/-- A step on a variable with an implied value sets it to that value. -/
theorem step_of_implied_eq_some {φ : CNF (Fin n)} {w : ℕ} {τ : Fin n → Option Bool} {x : Fin n}
    {b : Bool} (h : implied φ w τ x = some b) : step φ w τ x = PMF.pure b := by
  simp only [step, h]

/-- A step on a variable without an implied value chooses a uniform bit. -/
theorem step_of_implied_eq_none {φ : CNF (Fin n)} {w : ℕ} {τ : Fin n → Option Bool} {x : Fin n}
    (h : implied φ w τ x = none) :
    step φ w τ x = Cslib.Probability.PMF.uniformOfFintype Bool := by
  simp only [step, h]

/-- A run of no steps assigns nothing. -/
theorem run_zero (φ : CNF (Fin n)) (w : ℕ) (π : Equiv.Perm (Fin n)) :
    run φ w π 0 = PMF.pure fun _ => none := by
  simp only [run]

/-- Step `i` of a run processes the variable `π i`. -/
theorem run_succ (φ : CNF (Fin n)) (w : ℕ) (π : Equiv.Perm (Fin n)) {i : ℕ} (h : i < n) :
    run φ w π (i + 1) = (run φ w π i).bind fun τ =>
      (step φ w τ (π ⟨i, h⟩)).map fun b => Function.update τ (π ⟨i, h⟩) (some b) := by
  simp only [run, h, ↓reduceDIte]

/-- A run stops after all `n` variables are processed. -/
theorem run_succ_of_le (φ : CNF (Fin n)) (w : ℕ) (π : Equiv.Perm (Fin n)) {i : ℕ} (h : n ≤ i) :
    run φ w π (i + 1) = run φ w π i := by
  simp only [run, show ¬ i < n by omega, ↓reduceDIte]

/-- A run only assigns the variables it has processed. -/
theorem eq_none_of_mem_support_run {φ : CNF (Fin n)} {w : ℕ} {π : Equiv.Perm (Fin n)} {i : ℕ}
    {τ : Fin n → Option Bool} (hτ : τ ∈ (run φ w π i).support) {y : Fin n}
    (hy : y ∉ prefixSet π i) : τ y = none := by
  induction i generalizing τ with
  | zero =>
    simp only [run, PMF.support_pure, Set.mem_singleton_iff] at hτ
    rw [hτ]
  | succ i ih =>
    simp only [run] at hτ
    split_ifs at hτ with h
    · rw [PMF.mem_support_bind_iff] at hτ
      obtain ⟨τ', hτ', hmap⟩ := hτ
      rw [PMF.support_map] at hmap
      obtain ⟨b, -, rfl⟩ := hmap
      have hyx : y ≠ π ⟨i, h⟩ := by
        intro e
        apply hy
        rw [mem_prefixSet, e, Equiv.symm_apply_apply]
        simp
      dsimp only
      rw [Function.update_of_ne hyx]
      exact ih hτ' fun hy' => hy (by rw [mem_prefixSet] at hy' ⊢; omega)
    · exact ih hτ fun hy' => hy (by rw [mem_prefixSet] at hy' ⊢; omega)

/-- The number of unforced variables among the first `i` steps of the run in the order `π` that
agrees with `σ`: at these steps PPSZ chooses a uniform bit. -/
noncomputable def unforcedCount (φ : CNF (Fin n)) (w : ℕ) (σ : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  (univ.filter fun j : Fin n =>
    (j : ℕ) < i ∧ implied φ w (restrict σ (prefixSet π j)) (π j) = none).card

private theorem unforcedCount_succ (φ : CNF (Fin n)) (w : ℕ) (σ : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) {i : ℕ} (h : i < n) :
    unforcedCount φ w σ π (i + 1) = unforcedCount φ w σ π i +
      if implied φ w (restrict σ (prefixSet π i)) (π ⟨i, h⟩) = none then 1 else 0 := by
  unfold unforcedCount
  have hsplit : (univ.filter fun j : Fin n =>
      (j : ℕ) < i + 1 ∧ implied φ w (restrict σ (prefixSet π j)) (π j) = none) =
      (univ.filter fun j : Fin n =>
        (j : ℕ) < i ∧ implied φ w (restrict σ (prefixSet π j)) (π j) = none) ∪
      (univ.filter fun j : Fin n =>
        (j : ℕ) = i ∧ implied φ w (restrict σ (prefixSet π j)) (π j) = none) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h3 : (j : ℕ) < i
      · exact Or.inl ⟨h3, h2⟩
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by omega, h2⟩
  rw [hsplit, card_union_of_disjoint (disjoint_filter.mpr fun j _ h1 h2 => by omega)]
  congr 1
  split_ifs with hU
  · rw [card_eq_one]
    refine ⟨⟨i, h⟩, ?_⟩
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hj, -⟩
      exact Fin.ext hj
    · rintro rfl
      exact ⟨rfl, hU⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro j - ⟨hj, hU'⟩
    obtain rfl : j = ⟨i, h⟩ := Fin.ext hj
    exact hU hU'

/-- **A run in a fixed order outputs the solution with probability `2^{-u}`** [Paturi, Pudlák,
Saks, Zane, Lemma 1][PaturiPudlakSaksZane2005] [Scheder, Observation 1.2][Scheder2021], where `u`
counts the unforced variables along the run that agrees with `σ`. -/
theorem run_apply_restrict {φ : CNF (Fin n)} {w : ℕ} {σ : Fin n → Bool} (hσ : φ.eval σ = true)
    (π : Equiv.Perm (Fin n)) {i : ℕ} (hi : i ≤ n) :
    run φ w π i (restrict σ (prefixSet π i)) = (2⁻¹ : ENNReal) ^ unforcedCount φ w σ π i := by
  induction i with
  | zero =>
    have : restrict σ (prefixSet π 0) = fun _ => none := by
      funext y
      simp [restrict, prefixSet]
    simp [run, this, unforcedCount]
  | succ i ih =>
    have h : i < n := by omega
    set x := π ⟨i, h⟩
    set T := restrict σ (prefixSet π i)
    set T' := restrict σ (prefixSet π (i + 1))
    have hxi : x ∉ prefixSet π i := by simp [mem_prefixSet, x]
    have hxi' : x ∈ prefixSet π (i + 1) := by simp [mem_prefixSet, x]
    have hT'x : T' = Function.update T x (some (σ x)) := by
      funext y
      by_cases hy : y = x
      · subst hy
        simp [T', restrict, hxi']
      · rw [Function.update_of_ne hy]
        simp only [T', T, restrict, mem_prefixSet]
        have : (π.symm y : ℕ) ≠ i := by
          intro e
          apply hy
          rw [show y = π (π.symm y) by simp]
          congr 1
          exact Fin.ext e
        congr 1
        exact propext ⟨fun h1 => by omega, fun h1 => by omega⟩
    simp only [run, h, ↓reduceDIte]
    rw [PMF.bind_apply, tsum_eq_single T]
    · rw [PMF.map_apply, tsum_eq_single (σ x)]
      · rw [ite_eq_left hT'x, ih (by omega), unforcedCount_succ φ w σ π h, pow_add]
        congr 1
        split_ifs with hU
        · rw [step_of_implied_eq_none hU]
          simp [Cslib.Probability.PMF.uniformOfFintype_apply]
        · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hU
          rw [step_of_implied_eq_some hb, implied_eq hσ (fun _ _ => PPZ.eq_of_restrict_eq_some) hb]
          simp
      · intro b hb
        rw [ite_eq_right]
        intro e
        have := congrFun e x
        rw [hT'x, Function.update_self, Function.update_self] at this
        exact hb (Option.some_injective _ this).symm
    · intro τ hτ
      by_cases hsupp : τ ∈ (run φ w π i).support
      · rw [PMF.map_apply]
        convert mul_zero _
        refine ENNReal.tsum_eq_zero.mpr fun b => ite_eq_right fun e => hτ ?_
        funext y
        by_cases hy : y = x
        · subst hy
          rw [eq_none_of_mem_support_run hsupp hxi]
          simp [T, restrict, hxi]
        · have := congrFun e y
          rw [Function.update_of_ne hy, hT'x, Function.update_of_ne hy] at this
          exact this.symm
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hsupp, zero_mul]

/-! ### Forced variables and the success probability -/

/-- `x` is **forced** in the order `π` [Scheder, Definition 1.1][Scheder2021]: along the run that
agrees with `σ`, the values of `σ` on the variables before `x` w-imply a value on `x`. -/
def Forced (φ : CNF (Fin n)) (w : ℕ) (σ : Fin n → Bool) (π : Equiv.Perm (Fin n)) (x : Fin n) :
    Prop :=
  implied φ w (restrict σ (prefixSet π (π.symm x))) x ≠ none

/-- `Forced` is decidable, classically through `implied`. -/
noncomputable instance instDecidableForced (φ : CNF (Fin n)) (w : ℕ) (σ : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) (x : Fin n) : Decidable (Forced φ w σ π x) := by
  unfold Forced
  infer_instance

/-- For a satisfying assignment `σ`, `x` is forced exactly when the values of `σ` before `x`
w-imply `x = σ x`, as in [Scheder, Definition 1.1][Scheder2021]. -/
theorem forced_iff_wImplied {φ : CNF (Fin n)} {w : ℕ} {σ : Fin n → Bool} (hσ : φ.eval σ = true)
    {π : Equiv.Perm (Fin n)} {x : Fin n} :
    Forced φ w σ π x ↔ WImplied φ w (restrict σ (prefixSet π (π.symm x))) x (σ x) := by
  unfold Forced
  rw [implied_ne_none_iff]
  constructor
  · rintro ⟨b, hb⟩
    rwa [hb.eq hσ fun _ _ => PPZ.eq_of_restrict_eq_some]
  · exact fun h => ⟨σ x, h⟩

/-- The unforced variables of a whole run are the variables that are not forced. -/
theorem unforcedCount_eq_card (φ : CNF (Fin n)) (w : ℕ) (σ : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) :
    unforcedCount φ w σ π n = (univ.filter fun x => ¬ Forced φ w σ π x).card := by
  unfold unforcedCount Forced
  refine card_bij' (fun j _ => π j) (fun x _ => π.symm x) (fun j hj => ?_) (fun x hx => ?_)
    (fun j _ => by simp) (fun x _ => by simp)
  · simp only [mem_filter, mem_univ, true_and, ne_eq, not_not] at hj ⊢
    rw [Equiv.symm_apply_apply]
    exact hj.2
  · simp only [mem_filter, mem_univ, true_and, ne_eq, not_not] at hx ⊢
    refine ⟨(π.symm x).isLt, ?_⟩
    rw [Equiv.apply_symm_apply]
    exact hx

/-- **The success probability is an average over the orders** [Paturi, Pudlák, Saks, Zane,
Lemma 2][PaturiPudlakSaksZane2005]: one round outputs a satisfying assignment `σ` with probability
`(1/n!) ∑_π 2^{-u(π)}`, where `u(π)` counts the unforced variables in the order `π`. -/
theorem round_apply_eq {φ : CNF (Fin n)} {w : ℕ} {σ : Fin n → Bool} (hσ : φ.eval σ = true) :
    ((round φ w) fun x => some (σ x)).toReal =
      ∑ π : Equiv.Perm (Fin n), ((n.factorial : ℝ))⁻¹ * (1 / 2 : ℝ) ^ unforcedCount φ w σ π n := by
  rw [round, PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum (fun π _ => ENNReal.mul_ne_top
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))]
  refine sum_congr rfl fun π _ => ?_
  rw [← PPZ.restrict_prefixSet_self σ π, run_apply_restrict hσ π le_rfl, ENNReal.toReal_mul,
    Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.card_perm, Fintype.card_fin, ENNReal.toReal_pow, ENNReal.toReal_inv]
  norm_num

/-- The arithmetic–geometric mean inequality for a uniform average of powers of `1/2`. -/
private theorem half_pow_avg_le {ι : Type*} [Fintype ι] {N : ℝ} (hN : 0 < N)
    (hcard : (Fintype.card ι : ℝ) = N) (f : ι → ℕ) :
    (1 / 2 : ℝ) ^ (∑ i, N⁻¹ * (f i : ℝ)) ≤ ∑ i, N⁻¹ * (1 / 2 : ℝ) ^ f i := by
  have hw : ∑ _i : ι, N⁻¹ = 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul, hcard]
    field_simp
  have hamgm := Real.geom_mean_le_arith_mean_weighted (univ : Finset ι) (fun _ => N⁻¹)
    (fun i => (1 / 2 : ℝ) ^ f i) (fun _ _ => inv_nonneg.mpr hN.le) hw (fun _ _ => by positivity)
  have hprod : ∏ i, ((1 / 2 : ℝ) ^ f i) ^ N⁻¹ = (1 / 2 : ℝ) ^ ∑ i, N⁻¹ * (f i : ℝ) := by
    rw [Real.rpow_sum_of_pos (by norm_num)]
    refine prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  exact hprod ▸ hamgm

/-- **The success probability in terms of forcing probabilities**, after
[Paturi, Pudlák, Saks, Zane, Lemma 3][PaturiPudlakSaksZane2005], in the w-implication form of
[Scheder, eq. (1)][Scheder2021]: one round outputs a satisfying assignment `σ` with probability
at least `2^{-n + ∑ₓ Pr_π[x forced]}`, where `Pr_π[x forced]` is the fraction of the `n!` orders
in which `x` is forced. -/
theorem round_apply_ge {φ : CNF (Fin n)} {w : ℕ} {σ : Fin n → Bool} (hσ : φ.eval σ = true) :
    (2 : ℝ) ^ (-(n : ℝ) + ∑ x : Fin n,
      ((univ.filter fun π : Equiv.Perm (Fin n) => Forced φ w σ π x).card : ℝ) / n.factorial) ≤
      ((round φ w) fun x => some (σ x)).toReal := by
  set N := n.factorial
  set c : Fin n → ℝ := fun x =>
    ((univ.filter fun π : Equiv.Perm (Fin n) => Forced φ w σ π x).card : ℝ)
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.factorial_pos n
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) = N := by
    rw [Fintype.card_perm, Fintype.card_fin]
  -- The average number of unforced variables is `n - ∑ₓ Pr_π[x forced]`.
  have hswap : ∑ π : Equiv.Perm (Fin n), (unforcedCount φ w σ π n : ℝ) =
      ∑ x : Fin n, ((N : ℝ) - c x) := by
    calc
      ∑ π : Equiv.Perm (Fin n), (unforcedCount φ w σ π n : ℝ) =
          ∑ π : Equiv.Perm (Fin n), ((univ.filter fun x => ¬ Forced φ w σ π x).card : ℝ) := by
        simp only [unforcedCount_eq_card]
      _ = ∑ x : Fin n,
          ((univ.filter fun π : Equiv.Perm (Fin n) => ¬ Forced φ w σ π x).card : ℝ) := by
        simp only [card_filter]
        push_cast
        rw [sum_comm]
      _ = ∑ x : Fin n, ((N : ℝ) - c x) := by
        refine sum_congr rfl fun x _ => ?_
        rw [eq_sub_iff_add_eq, ← Nat.cast_add, add_comm, card_filter_add_card_filter_not,
          card_univ, Fintype.card_perm, Fintype.card_fin]
  have havg : ∑ π : Equiv.Perm (Fin n), (N : ℝ)⁻¹ * (unforcedCount φ w σ π n : ℝ) =
      (n : ℝ) - ∑ x : Fin n, c x / N := by
    rw [← mul_sum, hswap, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← sum_div]
    field_simp
  rw [round_apply_eq hσ]
  calc
    (2 : ℝ) ^ (-(n : ℝ) + ∑ x : Fin n, c x / N) =
        (1 / 2 : ℝ) ^ ((n : ℝ) - ∑ x : Fin n, c x / N) := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow zero_le_two,
        ← Real.rpow_neg zero_le_two, neg_sub, neg_add_eq_sub]
    _ = (1 / 2 : ℝ) ^ ∑ π : Equiv.Perm (Fin n), (N : ℝ)⁻¹ * (unforcedCount φ w σ π n : ℝ) := by
      rw [havg]
    _ ≤ _ := half_pow_avg_le hN hcard _

/-- **A uniform forcing bound** [Paturi, Pudlák, Saks, Zane, Lemma 3][PaturiPudlakSaksZane2005]:
if every variable is forced in at least a `p` fraction of the orders, one round outputs a
satisfying assignment `σ` with probability at least `2^{-(1 - p) n}`. -/
theorem round_apply_ge_of_le {φ : CNF (Fin n)} {w : ℕ} {σ : Fin n → Bool} (hσ : φ.eval σ = true)
    {p : ℝ} (hp : ∀ x, p * n.factorial ≤
      ((univ.filter fun π : Equiv.Perm (Fin n) => Forced φ w σ π x).card : ℝ)) :
    (2 : ℝ) ^ (-((1 - p) * n)) ≤ ((round φ w) fun x => some (σ x)).toReal := by
  refine le_trans (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) (round_apply_ge hσ)
  have hN : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hsum : ∑ _x : Fin n, p ≤ ∑ x : Fin n,
      ((univ.filter fun π : Equiv.Perm (Fin n) => Forced φ w σ π x).card : ℝ) / n.factorial :=
    sum_le_sum fun x _ => (le_div_iff₀ hN).mpr (hp x)
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith

/-! ### PPZ as a special case -/

/-- **A unit clause is a 1-implication** (original): a value forced by a unit clause of `φ` is
w-implied with `w = 1`. -/
theorem wImplied_one_of_forced {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
    (h : PPZ.forced φ τ x = some b) : WImplied φ 1 τ x b := by
  have key : ∀ b, (∃ c ∈ φ, PPZ.IsUnitOn τ x b c) → WImplied φ 1 τ x b := by
    rintro b ⟨c, hc, -, hall⟩
    refine ⟨[c], by simpa using hc, by simp, fun σ hσ hψ => ?_⟩
    obtain ⟨l, hl, hls⟩ :=
      (Clause.eval_eq_true_iff σ c).mp ((CNF.eval_eq_true_iff σ [c]).mp hψ c (by simp))
    have := hall l hl
    split_ifs at this with hx
    · rw [← hx, hls, this]
    · have := hσ _ _ this
      rw [hls] at this
      cases l.2 <;> simp at this
  unfold PPZ.forced at h
  split_ifs at h with h1 h2
  · cases h
    exact key true h1
  · cases h
    exact key false h2

/-- For `w ≥ 1`, every variable forced by a unit clause has an implied value (original). -/
theorem implied_ne_none_of_forced {φ : CNF (Fin n)} {w : ℕ} (hw : 1 ≤ w)
    {τ : Fin n → Option Bool} {x : Fin n} (h : PPZ.forced φ τ x ≠ none) :
    implied φ w τ x ≠ none := by
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
  exact implied_ne_none_iff.mpr
    ⟨b, (wImplied_one_of_forced hb).mono (fun c hc => hc) hw fun y c hy => hy⟩

/-- For `w ≥ 1`, a run of PPSZ that agrees with `σ` has at most as many unforced variables as the
corresponding run of PPZ (original). -/
theorem unforcedCount_le_ppz {φ : CNF (Fin n)} {w : ℕ} (hw : 1 ≤ w) (σ : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) (i : ℕ) : unforcedCount φ w σ π i ≤ PPZ.unforcedCount φ σ π i :=
  card_le_card fun j hj => by
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    exact ⟨hj.1, not_not.mp fun h => implied_ne_none_of_forced hw h hj.2⟩

/-- **PPSZ dominates PPZ** (original): for `w ≥ 1`, one round of PPSZ outputs each satisfying
assignment with at least the probability that one round of PPZ does. -/
theorem ppz_round_apply_le {φ : CNF (Fin n)} {w : ℕ} (hw : 1 ≤ w) {σ : Fin n → Bool}
    (hσ : φ.eval σ = true) :
    PPZ.round φ (fun x => some (σ x)) ≤ round φ w (fun x => some (σ x)) := by
  rw [PPZ.round, round, PMF.bind_apply, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun π => mul_le_mul_right ?_ _
  rw [← PPZ.restrict_prefixSet_self σ π, PPZ.run_apply_restrict hσ π le_rfl,
    run_apply_restrict hσ π le_rfl]
  exact pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr one_le_two)
    (unforcedCount_le_ppz hw σ π n)

/-- **The PPZ bound for PPSZ** [Paturi, Pudlák, Zane][PPZ1997]: for `w ≥ 1`, if `σ` is the only
satisfying assignment of a CNF formula on `n` variables whose clauses have at most `k ≥ 1`
literals, one round of PPSZ outputs `σ` with probability at least `2^{-(1 - 1/k) n}`. -/
theorem round_success_ppz {k w : ℕ} (hk : 1 ≤ k) (hw : 1 ≤ w) {φ : CNF (Fin n)}
    {σ : Fin n → Bool} (hσ : φ.eval σ = true) (huniq : ∀ τ, φ.eval τ = true → τ = σ)
    (hlen : ∀ c ∈ φ, c.length ≤ k) :
    (2 : ℝ) ^ (-((1 - 1 / (k : ℝ)) * n)) ≤ ((round φ w) fun x => some (σ x)).toReal :=
  (PPZ.round_success hk hσ huniq hlen).trans
    (ENNReal.toReal_mono (PMF.apply_ne_top _ _) (ppz_round_apply_le hw hσ))

/-- **The PPZ bound for PPSZ on satisfiable formulas** [Paturi, Pudlák, Zane][PPZ1997]: for
`w ≥ 1` and every satisfiable CNF formula on `n` variables whose clauses have at most `k ≥ 1`
literals, one round of PPSZ outputs a satisfying assignment with probability at least
`2^{-(1 - 1/k) n}`. -/
theorem round_success_of_satisfiable_ppz {k w : ℕ} (hk : 1 ≤ k) (hw : 1 ≤ w) {φ : CNF (Fin n)}
    (hsat : φ.Satisfiable) (hlen : ∀ c ∈ φ, c.length ≤ k) :
    (2 : ℝ) ^ (-((1 - 1 / (k : ℝ)) * n)) ≤
      ((round φ w).toOuterMeasure
        {τ | ∃ σ, φ.eval σ = true ∧ τ = fun x => some (σ x)}).toReal := by
  refine (PPZ.round_success_of_satisfiable hk hsat hlen).trans ?_
  rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal,
    Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
  refine sum_le_sum fun τ _ => ?_
  split_ifs with hτ
  · obtain ⟨σ, hσ, rfl⟩ := hτ
    exact ENNReal.toReal_mono (PMF.apply_ne_top _ _) (ppz_round_apply_le hw hσ)
  · exact le_rfl

end Cslib.Complexity.PPSZ
