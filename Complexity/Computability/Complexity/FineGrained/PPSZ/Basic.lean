/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.PPSZ.Defs
import Complexity.Probability.PMF.Event

/-!
# PPSZ with w-implication: the success probability

Let `σ` satisfy the formula `φ`. Along a run of PPSZ that agrees with `σ`, w-implied values are
the values of `σ` (`implied_eq`). A variable `x` is *forced* in the order `π` when the values of
`σ` on the variables before `x` w-imply a value on `x` (`Forced`). The run in the order `π`
outputs `σ` with probability exactly `2^{-u}`, where `u` counts the unforced variables
(`run_apply_restrict`). Averaging over the orders and applying the arithmetic–geometric mean
inequality, one round outputs `σ` with probability at least `2^{-n + ∑ₓ Pr_π[x forced]}`
(`round_apply_ge`). PPSZ is the oracle round `Cslib.Complexity.PPZ.roundWith` with `implied` as the
oracle, so these follow from the oracle versions shared with PPZ (`PPZ.runWith_apply_restrict`,
`PPZ.roundWith_apply_eq`, `PPZ.roundWith_apply_ge`) once implied values are known to be correct.

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
* `Cslib.Complexity.PPSZ.forced_iff_wImplied`: for a satisfying assignment `σ`, a variable is
  forced exactly when the values of `σ` before it w-imply its value in `σ`.
* `Cslib.Complexity.PPSZ.round_apply_ge`: one round outputs `σ` with probability at least
  `2^{-n + ∑ₓ Pr_π[x forced]}`.
* `Cslib.Complexity.PPSZ.round_apply_ge_of_le`: if every variable is forced in at least a `p`
  fraction of the orders, one round outputs `σ` with probability at least `2^{-(1 - p) n}`.
* `Cslib.Complexity.PPSZ.ppz_round_apply_le`: for `w ≥ 1`, PPSZ outputs each satisfying assignment
  at least as often as PPZ.
* `Cslib.Complexity.PPSZ.round_success_ppz`: for `w ≥ 1`, PPSZ finds the unique satisfying
  assignment of a k-CNF formula with probability at least `2^{-(1 - 1/k) n}`.
* `Cslib.Complexity.PPSZ.round_success_of_satisfiable_ppz`: for `w ≥ 1`, PPSZ finds a satisfying
  assignment of a satisfiable k-CNF formula with probability at least `2^{-(1 - 1/k) n}`.

## References

* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
* [D. Scheder, *PPSZ is better than you think*][Scheder2021]
* [R. Paturi, P. Pudlák, F. Zane, *Satisfiability Coding Lemma*][PPZ1997]
-/

@[expose] public section

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

/-- Under a partial assignment with a satisfying extension `σ`, no value is implied on `x` exactly
when `x = σ x` is not w-implied. -/
theorem implied_eq_none_iff {φ : CNF (Fin n)} {w : ℕ} {σ : Fin n → Bool} (hσ : φ.eval σ = true)
    {τ : Fin n → Option Bool} (hτ : ∀ y b, τ y = some b → σ y = b) {x : Fin n} :
    implied φ w τ x = none ↔ ¬ WImplied φ w τ x (σ x) := by
  constructor
  · intro h hI
    rw [implied_eq_some hσ hτ hI] at h
    cases h
  · intro h
    by_contra hne
    obtain ⟨b, hb⟩ := implied_ne_none_iff.1 hne
    rw [hb.eq hσ hτ] at h
    exact h hb

/-! ### Runs -/

/-- The number of unforced variables among the first `i` steps of the run in the order `π` that
agrees with `σ`: at these steps PPSZ chooses a uniform bit. -/
noncomputable def unforcedCount (φ : CNF (Fin n)) (w : ℕ) (σ : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  PPZ.unforcedCountWith (implied φ w) σ π i

/-- **A run in a fixed order outputs the solution with probability `2^{-u}`**, after
[Paturi, Pudlák, Saks, Zane, Lemma 1][PaturiPudlakSaksZane2005] and as in
[Scheder, Observation 1.2][Scheder2021], where `u` counts the unforced variables along the run
that agrees with `σ`. [Paturi, Pudlák, Saks, Zane][PaturiPudlakSaksZane2005] draw the random bits
up front and characterise the bit strings for which the run outputs `σ`; here the bits are drawn
during the run, and the probability is computed directly (`PPZ.runWith_apply_restrict`). -/
theorem run_apply_restrict {φ : CNF (Fin n)} {w : ℕ} {σ : Fin n → Bool} (hσ : φ.eval σ = true)
    (π : Equiv.Perm (Fin n)) {i : ℕ} (hi : i ≤ n) :
    run φ w π i (restrict σ (prefixSet π i)) = (2⁻¹ : ENNReal) ^ unforcedCount φ w σ π i :=
  PPZ.runWith_apply_restrict (fun _ hτ _ _ h => implied_eq hσ hτ h) π hi

/-! ### Forced variables and the success probability -/

/-- `x` is **forced** in the order `π` [Scheder, Definition 1.1][Scheder2021]: along the run that
agrees with `σ`, the values of `σ` on the variables before `x` w-imply a value on `x`. -/
def Forced (φ : CNF (Fin n)) (w : ℕ) (σ : Fin n → Bool) (π : Equiv.Perm (Fin n)) (x : Fin n) :
    Prop :=
  implied φ w (restrict σ (prefixSet π (π.symm x))) x ≠ none

/-- `Forced` is decidable, classically through `implied`. -/
noncomputable instance instDecidableForced (φ : CNF (Fin n)) (w : ℕ) (σ : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) (x : Fin n) : Decidable (Forced φ w σ π x) :=
  inferInstanceAs (Decidable (implied φ w (restrict σ (prefixSet π (π.symm x))) x ≠ none))

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
  rw [unforcedCount, PPZ.unforcedCountWith_eq_card]
  simp only [Forced, ne_eq, not_not]

/-- **The success probability is an average over the orders** [Paturi, Pudlák, Saks, Zane,
Lemma 2][PaturiPudlakSaksZane2005]: one round outputs a satisfying assignment `σ` with probability
`(1/n!) ∑_π 2^{-u(π)}`, where `u(π)` counts the unforced variables in the order `π`. -/
theorem round_apply_eq {φ : CNF (Fin n)} {w : ℕ} {σ : Fin n → Bool} (hσ : φ.eval σ = true) :
    ((round φ w) fun x => some (σ x)).toReal =
      ∑ π : Equiv.Perm (Fin n), ((n.factorial : ℝ))⁻¹ * (1 / 2 : ℝ) ^ unforcedCount φ w σ π n :=
  PPZ.roundWith_apply_eq fun _ hτ _ _ h => implied_eq hσ hτ h

/-- **The success probability in terms of forcing probabilities**, after
[Paturi, Pudlák, Saks, Zane, Lemma 3][PaturiPudlakSaksZane2005], in the w-implication form of
[Scheder, eq. (1)][Scheder2021]: one round outputs a satisfying assignment `σ` with probability
at least `2^{-n + ∑ₓ Pr_π[x forced]}`, where `Pr_π[x forced]` is the fraction of the `n!` orders
in which `x` is forced. -/
theorem round_apply_ge {φ : CNF (Fin n)} {w : ℕ} {σ : Fin n → Bool} (hσ : φ.eval σ = true) :
    (2 : ℝ) ^ (-(n : ℝ) + ∑ x : Fin n,
      ((univ.filter fun π : Equiv.Perm (Fin n) => Forced φ w σ π x).card : ℝ) / n.factorial) ≤
      ((round φ w) fun x => some (σ x)).toReal :=
  PPZ.roundWith_apply_ge fun _ hτ _ _ h => implied_eq hσ hτ h

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
    (π : Equiv.Perm (Fin n)) (i : ℕ) : unforcedCount φ w σ π i ≤ PPZ.unforcedCount φ σ π i := by
  unfold unforcedCount PPZ.unforcedCount PPZ.unforcedCountWith
  refine card_le_card fun j hj => ?_
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  exact ⟨hj.1, not_not.mp fun h => implied_ne_none_of_forced hw h hj.2⟩

/-- **PPSZ dominates PPZ** (original): for `w ≥ 1`, one round of PPSZ outputs each satisfying
assignment with at least the probability that one round of PPZ does. -/
theorem ppz_round_apply_le {φ : CNF (Fin n)} {w : ℕ} (hw : 1 ≤ w) {σ : Fin n → Bool}
    (hσ : φ.eval σ = true) :
    PPZ.round φ (fun x => some (σ x)) ≤ round φ w (fun x => some (σ x)) := by
  rw [PPZ.round, round, PPZ.roundWith, PPZ.roundWith, PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun π => mul_le_mul_right ?_ _
  rw [← PPZ.restrict_prefixSet_self σ π]
  rw [PPZ.runWith_apply_restrict (O := PPZ.forced φ) (fun _ hτ _ _ h => PPZ.forced_eq hσ hτ h) π
    le_rfl, PPZ.runWith_apply_restrict (O := implied φ w) (fun _ hτ _ _ h => implied_eq hσ hτ h) π
    le_rfl]
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
