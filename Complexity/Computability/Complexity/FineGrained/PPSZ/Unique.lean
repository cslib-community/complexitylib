/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.PPSZ.Basic
public import Complexity.Computability.Complexity.FineGrained.PPSZ.CriticalTree
public import Complexity.Computability.Complexity.FineGrained.PPSZ.Placement

/-!
# PPSZ with w-implication: the bound for isolated and unique solutions

Let `σ` be an `h`-isolated satisfying assignment of a CNF formula `φ` whose clauses have at most
`k` literals, and let `w ≥ ∑ i < h, (k - 1) ^ i`. Fix a variable `x` and a critical clause tree
of height `h` for `x` (`exists_isCriticalTree`). When the variables other than `x` are included
independently with probability `r`, the event that every path from the root to depth `h` meets
the included set has probability at least `Q k h r` (`Q_le_bernoulliProb_cut`): this is the
depth recursion `Q_le_bernoulliProb` applied to the cut events of the subtrees, which are
increasing (`Cut.mono`), satisfy the recursion `cut_succ`, and do not depend on the label of
their own root (`cut_insert_of_mem`), while every node has at most `k - 1` children
(`card_children_le`). Integrating over `r`, the variables placed before `x` in a uniformly random
order contain such a cut with probability at least `qbar k h`; by the forcing lemma
(`wImplied_of_cut`), `x` is then forced. So every variable is forced with probability at least
`qbar k h` (`qbar_le_card_filter_forced_div_factorial`), and one round of PPSZ outputs `σ` with
probability at least `2^{-(1 - qbar k h) n}` (`round_success_of_isolated`).

This is the analogue, for w-implication, of the finite-depth bound of
[Paturi, Pudlák, Saks, Zane, Theorem 7][PaturiPudlakSaksZane2005] before its estimate of
`qbar k h` (Lemma 8 of the paper). A unique satisfying assignment is isolated for every `h`
(`round_success_of_unique`). For `k = 3` and depth `2`, where `qbar 3 2 = 31 / 70`, this gives
`2^{-(39/70) n}`, better than the PPZ bound `2^{-(2/3) n}` (`round_success_of_unique_three`).

## Main results

* `Cslib.Complexity.PPSZ.IsCriticalTreeAt.Q_le_bernoulliProb_cut`: the cut event of a rooted
  critical clause tree has probability at least `Q k h r` under independent inclusion.
* `Cslib.Complexity.PPSZ.Q_le_bernoulliProb_cut`: the same for a critical clause tree.
* `Cslib.Complexity.PPSZ.qbar_le_card_filter_forced_div_factorial`: every variable is forced in
  at least a `qbar k h` fraction of the orders.
* `Cslib.Complexity.PPSZ.round_success_of_isolated`: one round outputs an `h`-isolated satisfying
  assignment with probability at least `2^{-(1 - qbar k h) n}`.
* `Cslib.Complexity.PPSZ.round_success_of_unique`: the same for a unique satisfying assignment and
  every `h`.
* `Cslib.Complexity.PPSZ.round_success_of_unique_three`: for unique 3-SAT and `w ≥ 3`, one round
  succeeds with probability at least `2^{-(39/70) n}`.

## References

* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
* [D. Scheder, *PPSZ is better than you think*][Scheder2021]
-/

@[expose] public section

namespace Cslib.Complexity.PPSZ

open Cslib.Logic.PL Finset

variable {n : ℕ}

/-- **The cut probability of a rooted critical clause tree**
[Paturi, Pudlák, Saks, Zane, Lemma 7 and p. 351][PaturiPudlakSaksZane2005]. Let `C` label a
critical clause tree of height `h` rooted at `x` for a satisfying assignment `σ` of a formula whose
clauses have at most `k` literals. If every variable other than `x` is included independently with
probability `r`, then every path from the root `x` to depth `h` meets the included set with
probability at least `Q k h r`. -/
theorem IsCriticalTreeAt.Q_le_bernoulliProb_cut {k h : ℕ} {φ : CNF (Fin n)} {σ : Fin n → Bool}
    {x : Fin n} {C : List (Fin n) → Clause (Fin n)} (hC : IsCriticalTreeAt φ σ x h C)
    (hσ : φ.eval σ = true) (hlen : ∀ c ∈ φ, c.length ≤ k) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    Q k h r ≤ bernoulliProb (univ.erase x) r fun A => Cut C A h [x] := by
  refine Q_le_bernoulliProb hr (fun d p A => Cut C A d p)
    (fun d p => x ∈ p ∧ p.length + d ≤ h + 1) (children C) (fun p y => y :: p)
    (fun _ _ _ _ _ hAB => Cut.mono hAB) ?_ ?_ ?_ ?_ h [x]
    ⟨List.mem_singleton_self x, by rw [List.length_singleton]; omega⟩
  · rintro d p ⟨hxp, hp⟩
    exact ⟨fun y hy => mem_erase.mpr ⟨fun e => notMem_of_mem_children hy (e ▸ hxp), mem_univ y⟩,
      card_children_le hσ hC hlen hxp (by omega)⟩
  · rintro d p ⟨hxp, hp⟩ y -
    exact ⟨List.mem_cons_of_mem y hxp, by rw [List.length_cons]; omega⟩
  · rintro d p - y - S
    exact cut_insert_of_mem (List.mem_cons_self ..)
  · rintro d p - S -
    exact cut_succ C S d p

/-- **The cut probability of a critical clause tree**
[Paturi, Pudlák, Saks, Zane, Lemma 7 and p. 351][PaturiPudlakSaksZane2005]. Let `C` label a
critical clause tree of height `h` for a satisfying assignment `σ` of a formula whose clauses have
at most `k` literals. If every variable other than `x` is included independently with probability
`r`, then every path from the root `x` to depth `h` meets the included set with probability at
least `Q k h r`. -/
theorem Q_le_bernoulliProb_cut {k h : ℕ} {φ : CNF (Fin n)} {σ : Fin n → Bool}
    {C : List (Fin n) → Clause (Fin n)} (hσ : φ.eval σ = true) (hC : IsCriticalTree φ σ h C)
    (hlen : ∀ c ∈ φ, c.length ≤ k) (x : Fin n) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    Q k h r ≤ bernoulliProb (univ.erase x) r fun A => Cut C A h [x] :=
  (hC.isCriticalTreeAt x).Q_le_bernoulliProb_cut hσ hlen hr

/-- The variables placed before `x` are the variables PPZ and PPSZ have processed when they reach
`x`. (`placedBefore` is defined separately in the formula-free file
`Complexity.Computability.Complexity.FineGrained.PPSZ.Placement`.) -/
theorem placedBefore_eq_prefixSet (π : Equiv.Perm (Fin n)) (x : Fin n) :
    placedBefore π x = PPZ.prefixSet π (π.symm x) := by
  ext y
  rw [mem_placedBefore, PPZ.mem_prefixSet, Fin.lt_def]

/-- **Every variable is forced with probability at least `qbar k h`**
[Paturi, Pudlák, Saks, Zane, Lemmas 6 and 7 and p. 351][PaturiPudlakSaksZane2005], for PPSZ with
w-implication as in [Scheder, Lemma 3.2][Scheder2021]. Let `σ` be an `h`-isolated satisfying
assignment of a formula whose clauses have at most `k` literals, and let
`w ≥ ∑ i < h, (k - 1) ^ i`. Then every variable is forced in at least a `qbar k h` fraction of the
`n!` orders. The bound on `w`, the number of nodes of depth less than `h`, and the reduction from
random placements to random orders are original. -/
theorem qbar_le_card_filter_forced_div_factorial {k h w : ℕ} {φ : CNF (Fin n)}
    {σ : Fin n → Bool} (hσ : φ.eval σ = true) (hiso : IsIsolated φ σ h)
    (hlen : ∀ c ∈ φ, c.length ≤ k) (hw : ∑ i ∈ range h, (k - 1) ^ i ≤ w) (x : Fin n) :
    qbar k h ≤
      (#(univ.filter fun π : Equiv.Perm (Fin n) => Forced φ w σ π x) : ℝ) / n.factorial := by
  obtain ⟨C, hC⟩ := exists_isCriticalTree hiso
  refine (qbar_le_card_filter_placedBefore_div_factorial (E := fun A => Cut C A h [x])
    fun r hr => Q_le_bernoulliProb_cut hσ hC hlen x hr).trans ?_
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine Nat.cast_le.mpr (card_le_card fun π hπ => ?_)
  rw [mem_filter] at hπ ⊢
  refine ⟨hπ.1, (forced_iff_wImplied hσ).mpr ?_⟩
  rw [← placedBefore_eq_prefixSet]
  exact wImplied_of_cut hσ hC hlen hw hπ.2

/-- **PPSZ finds isolated solutions**, the analogue for w-implication of the finite-depth bound of
[Paturi, Pudlák, Saks, Zane, Theorem 7 (p. 344)][PaturiPudlakSaksZane2005] in the form
`Q_T ≥ qbar k h` of p. 351, before its estimate of `qbar k h` (Lemma 8 of the paper). Let `σ` be
an `h`-isolated satisfying assignment of a CNF formula on `n` variables whose clauses have at most
`k` literals, and let `w ≥ ∑ i < h, (k - 1) ^ i`. Then one round of PPSZ with w-implication
outputs `σ` with probability at least `2^{-(1 - qbar k h) n}`. The paper assumes `k ≥ 3` and uses
`s`-bounded resolution with `s ≥ k ^ h` in place of w-implication; only the bound on `w`, the
number of nodes of depth less than `h`, and the reduction from random placements to random orders
are original. -/
theorem round_success_of_isolated {k h w : ℕ} {φ : CNF (Fin n)} {σ : Fin n → Bool}
    (hσ : φ.eval σ = true) (hiso : IsIsolated φ σ h) (hlen : ∀ c ∈ φ, c.length ≤ k)
    (hw : ∑ i ∈ range h, (k - 1) ^ i ≤ w) :
    (2 : ℝ) ^ (-((1 - qbar k h) * n)) ≤ ((round φ w) fun x => some (σ x)).toReal :=
  round_apply_ge_of_le hσ fun x => (le_div_iff₀ (by exact_mod_cast Nat.factorial_pos n)).mp
    (qbar_le_card_filter_forced_div_factorial hσ hiso hlen hw x)

/-- **PPSZ finds unique solutions**, for every depth `h`, after
[Paturi, Pudlák, Saks, Zane, Theorem 7][PaturiPudlakSaksZane2005] and
[Scheder, Theorem 1.3][Scheder2021]. If `σ` is the only satisfying assignment of a CNF formula on
`n` variables whose clauses have at most `k` literals and `w ≥ ∑ i < h, (k - 1) ^ i`, one round
of PPSZ with w-implication outputs `σ` with probability at least `2^{-(1 - qbar k h) n}`. Like
[Paturi, Pudlák, Saks, Zane, Theorem 7 (p. 344)][PaturiPudlakSaksZane2005], this is a
finite-depth bound; the `qbar k h` form is the w-implication analogue of its chain
`Q_T ≥ qbar k h` on p. 351. Only the bound on `w` and the reduction from random placements to
random orders are original. -/
theorem round_success_of_unique {k h w : ℕ} {φ : CNF (Fin n)} {σ : Fin n → Bool}
    (hσ : φ.eval σ = true) (huniq : ∀ τ, φ.eval τ = true → τ = σ)
    (hlen : ∀ c ∈ φ, c.length ≤ k) (hw : ∑ i ∈ range h, (k - 1) ^ i ≤ w) :
    (2 : ℝ) ^ (-((1 - qbar k h) * n)) ≤ ((round φ w) fun x => some (σ x)).toReal :=
  round_success_of_isolated hσ (isIsolated_of_unique huniq h) hlen hw

/-- **PPSZ for unique 3-SAT at depth two** (original): for `w ≥ 3`, one round of PPSZ with
w-implication outputs the unique satisfying assignment of a 3-CNF formula on `n` variables with
probability at least `2^{-(39/70) n}`, since `qbar 3 2 = 31 / 70`. This improves the PPZ bound
`2^{-(2/3) n}` (`round_success_ppz`). -/
theorem round_success_of_unique_three {w : ℕ} (hw : 3 ≤ w) {φ : CNF (Fin n)} {σ : Fin n → Bool}
    (hσ : φ.eval σ = true) (huniq : ∀ τ, φ.eval τ = true → τ = σ)
    (hlen : ∀ c ∈ φ, c.length ≤ 3) :
    (2 : ℝ) ^ (-(39 / 70 * n : ℝ)) ≤ ((round φ w) fun x => some (σ x)).toReal := by
  have h := round_success_of_unique (h := 2) hσ huniq hlen (by simpa [sum_range_succ] using hw)
  rwa [qbar_three_two, show (1 : ℝ) - 31 / 70 = 39 / 70 by norm_num] at h

end Cslib.Complexity.PPSZ
