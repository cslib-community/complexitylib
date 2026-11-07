/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.List.MinMax
public import Mathlib.NumberTheory.Harmonic.Defs
import Complexity.Foundations.NumberTheory.Harmonic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The greedy algorithm for weighted set cover

This module formalizes the greedy algorithm for weighted set cover and Chvátal's harmonic bound on
its cost ([WilliamsonShmoys2011], Section 1.6, Algorithm 1.2, Theorems 1.11 and 1.12;
[Chvatal1979]).

## Model

An instance consists of a ground set `U : Finset α`, sets `S : ι → Finset α`, weights `w : ι → 𝕜`
in a linearly ordered field (`ℚ`, `ℝ`, …), and a list `J : List ι` of the candidate sets. The
weights of the candidates are assumed nonnegative where the bounds need it, as in
[WilliamsonShmoys2011], Section 1.2. A *cover* is a finite set `C` of candidates whose sets contain
every element of `U`; its cost is `∑ j ∈ C, w j`. A *fractional cover* gives each candidate `j ∈ C`
a weight `x j ≥ 0` such that the sets containing each element of `U` have total weight at least
`1`; a cover is the fractional cover with `x = 1`.

## Algorithm

`greedy S w J U` repeatedly chooses, among the candidates meeting the set `R` of elements not yet
covered, one minimizing the cost per newly covered element `w j / |S j ∩ R|`
(`costPerUncovered`), breaking ties toward the earliest candidate in `J` (`List.argmin`), and stops
when no candidate meets `R`. Each round covers at least one new element, so `U.card` rounds suffice
(`greedyLoop` is given that many rounds of fuel). The output is the list of chosen candidates, in
order. Ratios are compared exactly in `𝕜`.

## Source mapping

[WilliamsonShmoys2011], Algorithm 1.2, chooses `argmin_{j : Ŝ_j ≠ ∅} w_j / |Ŝ_j|` with `Ŝ_j` the
uncovered elements of `S_j`, and stops when the chosen sets cover the ground set; here the loop
also stops when no candidate meets the remaining elements, which only happens on infeasible inputs
(`greedy_covers`). The analysis follows Chvátal's: for every fractional cover `x`,
`∑_{i ∈ greedy} w i ≤ ∑_{j ∈ C} x j w j H(|S j ∩ U|)` (`sum_greedy_le_sum_harmonic`), proved by
induction on the rounds: the chosen set's weight `ρ |A|`, with `A` its newly covered elements and
`ρ` the minimal ratio, is at most the decrease `∑ x j w j (H(|S j ∩ R|) - H(|S j ∩ R \ A|))`, since
`w j / |S j ∩ R| ≥ ρ` and `(a - b) / a ≤ H a - H b`. This is the dual-fitting argument of
[WilliamsonShmoys2011], Theorem 1.12, with the dual feasibility step and weak duality composed into
one inequality against an arbitrary fractional cover, so no linear-programming API is needed. With
`d` bounding the sizes `|S j ∩ U|` this gives `cost ≤ H d · ∑ x j w j`, Chvátal's `H(d)` bound
against the fractional optimum (`sum_greedy_le_harmonic_mul_fractional`), hence against every
cover (`sum_greedy_le_harmonic_mul`, [WilliamsonShmoys2011], Theorem 1.12 with `g = d`); taking
`d = |U|` gives the `H_n` guarantee of [WilliamsonShmoys2011], Theorem 1.11
(`sum_greedy_le_harmonic_card_mul`). Over `ℝ`, Mathlib's `harmonic_le_one_add_log` gives
`cost ≤ (1 + log d) · w(C)` (`sum_greedy_le_one_add_log_mul`).

Earlier greedy analyses for unweighted set cover are due to Johnson and Lovász; see
[WilliamsonShmoys2011], Section 1.8.

## Limitations

The algorithm is a pure Lean function; no machine-level running time is certified here.

## Main definitions

* `Cslib.Algorithms.Lean.SetCover.costPerUncovered`: the ratio `w j / |S j ∩ R|`.
* `Cslib.Algorithms.Lean.SetCover.bestSet`: the candidate chosen in a round.
* `Cslib.Algorithms.Lean.SetCover.greedyLoop`, `Cslib.Algorithms.Lean.SetCover.greedy`: the
  greedy algorithm with explicit fuel, and with `U.card` rounds.

## Main results

* `bestSet_eq_none_iff`, `bestSet_spec`: the choice rule.
* `greedy_covers`, `greedy_subset`, `nodup_greedy`, `length_greedy_le`: the output is a cover by
  distinct candidates whenever the candidates cover `U`, with at most `U.card` sets.
* `sum_greedy_le_sum_harmonic`: Chvátal's charging bound against every fractional cover.
* `sum_greedy_le_harmonic_mul_fractional`, `sum_greedy_le_harmonic_mul`,
  `sum_greedy_le_harmonic_card_mul`: the `H d` and `H |U|` approximation guarantees.
* `sum_greedy_le_one_add_log_mul`: the `1 + log d` guarantee over `ℝ`.

## References

* [V. Chvátal, *A greedy heuristic for the set-covering problem*][Chvatal1979]
* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*][WilliamsonShmoys2011]
-/

public section

namespace Cslib.Algorithms.Lean.SetCover

variable {ι α 𝕜 : Type*} [DecidableEq α]

/-! ### The algorithm -/

/-- The cost per newly covered element of candidate `j` when the elements of `R` are uncovered:
`w j / |S j ∩ R|`. -/
@[expose] def costPerUncovered [Field 𝕜] (S : ι → Finset α) (w : ι → 𝕜) (R : Finset α)
    (j : ι) : 𝕜 :=
  w j / (S j ∩ R).card

/-- The candidate chosen by the greedy algorithm when the elements of `R` are uncovered: among the
candidates of `J` whose sets meet `R`, the first one minimizing `costPerUncovered`, or `none` if no
candidate meets `R`. -/
@[expose] def bestSet [Field 𝕜] [LinearOrder 𝕜] (S : ι → Finset α) (w : ι → 𝕜) (J : List ι)
    (R : Finset α) : Option ι :=
  (J.filter fun j => (S j ∩ R).Nonempty).argmin (costPerUncovered S w R)

/-- At most `k` rounds of the greedy algorithm on the uncovered elements `R`: choose
`bestSet S w J R`, remove its elements from `R`, and continue; stop when no candidate meets `R`.
Returns the chosen candidates in order. -/
@[expose] def greedyLoop [Field 𝕜] [LinearOrder 𝕜] (S : ι → Finset α) (w : ι → 𝕜) (J : List ι) :
    ℕ → Finset α → List ι
  | 0, _ => []
  | k + 1, R =>
    match bestSet S w J R with
    | none => []
    | some i => i :: greedyLoop S w J k (R \ S i)

/-- **The greedy algorithm for weighted set cover** ([WilliamsonShmoys2011], Algorithm 1.2): the
candidates of `J` chosen to cover `U`, with `U.card` rounds, each covering at least one new
element. -/
@[expose] def greedy [Field 𝕜] [LinearOrder 𝕜] (S : ι → Finset α) (w : ι → 𝕜) (J : List ι)
    (U : Finset α) : List ι :=
  greedyLoop S w J U.card U

section Basic

variable [Field 𝕜] [LinearOrder 𝕜] {S : ι → Finset α} {w : ι → 𝕜} {J : List ι}

/-- No candidate is chosen exactly when no candidate meets the uncovered elements. -/
theorem bestSet_eq_none_iff {R : Finset α} :
    bestSet S w J R = none ↔ ∀ j ∈ J, S j ∩ R = ∅ := by
  simp only [bestSet, List.argmin_eq_none, List.filter_eq_nil_iff, decide_eq_true_eq,
    Finset.not_nonempty_iff_eq_empty]

/-- The chosen candidate meets the uncovered elements and minimizes the cost per newly covered
element among the candidates that do. -/
theorem bestSet_spec {R : Finset α} {i : ι} (h : bestSet S w J R = some i) :
    i ∈ J ∧ (S i ∩ R).Nonempty ∧
      ∀ j ∈ J, (S j ∩ R).Nonempty → costPerUncovered S w R i ≤ costPerUncovered S w R j := by
  have hmem := List.argmin_mem h
  rw [List.mem_filter, decide_eq_true_eq] at hmem
  refine ⟨hmem.1, hmem.2, fun j hj hne => List.le_of_mem_argmin ?_ h⟩
  rw [List.mem_filter, decide_eq_true_eq]
  exact ⟨hj, hne⟩

/-- With at least `R.card` rounds, the greedy loop covers `R` whenever the candidates do. -/
theorem greedyLoop_covers {k : ℕ} {R : Finset α} (hR : R.card ≤ k)
    (hcov : ∀ a ∈ R, ∃ j ∈ J, a ∈ S j) :
    ∀ a ∈ R, ∃ i ∈ greedyLoop S w J k R, a ∈ S i := by
  induction k generalizing R with
  | zero =>
    rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hR)]
    simp
  | succ k ih =>
    unfold greedyLoop
    rcases h : bestSet S w J R with _ | i
    · rw [bestSet_eq_none_iff] at h
      intro a ha
      obtain ⟨j, hj, haj⟩ := hcov a ha
      have : a ∈ S j ∩ R := Finset.mem_inter.2 ⟨haj, ha⟩
      rw [h j hj] at this
      exact absurd this (Finset.notMem_empty a)
    · obtain ⟨-, hne, -⟩ := bestSet_spec h
      have hlt : (R \ S i).card ≤ k := by
        have h1 := Finset.card_sdiff_add_card_inter R (S i)
        have h2 : 0 < (R ∩ S i).card := by
          rw [Finset.inter_comm]
          exact hne.card_pos
        omega
      have ih' := ih hlt fun a ha => hcov a (Finset.mem_sdiff.1 ha).1
      intro a ha
      by_cases hai : a ∈ S i
      · exact ⟨i, List.mem_cons_self, hai⟩
      · obtain ⟨j, hj, haj⟩ := ih' a (Finset.mem_sdiff.2 ⟨ha, hai⟩)
        exact ⟨j, List.mem_cons_of_mem _ hj, haj⟩

/-- The greedy loop chooses only candidates. -/
theorem greedyLoop_subset {k : ℕ} {R : Finset α} : ∀ i ∈ greedyLoop S w J k R, i ∈ J := by
  induction k generalizing R with
  | zero => simp [greedyLoop]
  | succ k ih =>
    unfold greedyLoop
    rcases h : bestSet S w J R with _ | i
    · simp
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · exact (bestSet_spec h).1
      · exact ih j hj

/-- Every set chosen by the greedy loop meets the elements uncovered at the start. -/
theorem greedyLoop_inter_nonempty {k : ℕ} {R : Finset α} :
    ∀ i ∈ greedyLoop S w J k R, (S i ∩ R).Nonempty := by
  induction k generalizing R with
  | zero => simp [greedyLoop]
  | succ k ih =>
    unfold greedyLoop
    rcases h : bestSet S w J R with _ | i
    · simp
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · exact (bestSet_spec h).2.1
      · obtain ⟨a, ha⟩ := ih j hj
        exact ⟨a, Finset.mem_inter.2 ⟨(Finset.mem_inter.1 ha).1,
          (Finset.mem_sdiff.1 (Finset.mem_inter.1 ha).2).1⟩⟩

/-- The greedy loop never chooses a candidate twice. -/
theorem nodup_greedyLoop {k : ℕ} {R : Finset α} : (greedyLoop S w J k R).Nodup := by
  induction k generalizing R with
  | zero => simp [greedyLoop]
  | succ k ih =>
    unfold greedyLoop
    rcases h : bestSet S w J R with _ | i
    · simp
    · refine List.nodup_cons.2 ⟨fun hi => ?_, ih⟩
      obtain ⟨a, ha⟩ := greedyLoop_inter_nonempty i hi
      rw [Finset.mem_inter, Finset.mem_sdiff] at ha
      exact ha.2.2 ha.1

/-- The greedy loop runs at most its fuel many rounds. -/
theorem length_greedyLoop_le {k : ℕ} {R : Finset α} : (greedyLoop S w J k R).length ≤ k := by
  induction k generalizing R with
  | zero => simp [greedyLoop]
  | succ k ih =>
    unfold greedyLoop
    rcases h : bestSet S w J R with _ | i
    · simp
    · simpa using ih

/-- **Feasibility.** The greedy algorithm covers `U` whenever the candidates do. -/
theorem greedy_covers {U : Finset α} (hcov : ∀ a ∈ U, ∃ j ∈ J, a ∈ S j) :
    ∀ a ∈ U, ∃ i ∈ greedy S w J U, a ∈ S i :=
  greedyLoop_covers le_rfl hcov

/-- The greedy algorithm chooses only candidates. -/
theorem greedy_subset {U : Finset α} : ∀ i ∈ greedy S w J U, i ∈ J :=
  greedyLoop_subset

/-- The greedy algorithm never chooses a candidate twice. -/
theorem nodup_greedy {U : Finset α} : (greedy S w J U).Nodup :=
  nodup_greedyLoop

/-- The greedy algorithm chooses at most `U.card` sets. -/
theorem length_greedy_le {U : Finset α} : (greedy S w J U).length ≤ U.card :=
  length_greedyLoop_le

end Basic

/-! ### Chvátal's bound -/

section Cost

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {S : ι → Finset α} {w : ι → 𝕜} {J : List ι}

/-- The charging bound for the greedy loop on uncovered elements `R`, against every fractional
cover `x` of `R` by candidates. -/
theorem sum_greedyLoop_le_sum_harmonic {k : ℕ} {R : Finset α} {C : Finset ι}
    {x : ι → 𝕜} (hw : ∀ j ∈ J, 0 ≤ w j) (hCJ : ∀ j ∈ C, j ∈ J) (hx : ∀ j ∈ C, 0 ≤ x j)
    (hcov : ∀ a ∈ R, 1 ≤ ∑ j ∈ C with a ∈ S j, x j) :
    ((greedyLoop S w J k R).map w).sum ≤
      ∑ j ∈ C, x j * w j * (harmonic (S j ∩ R).card : 𝕜) := by
  induction k generalizing R with
  | zero =>
    exact Finset.sum_nonneg fun j hj => mul_nonneg (mul_nonneg (hx j hj) (hw j (hCJ j hj)))
      (Rat.cast_nonneg.2 (harmonic_nonneg _))
  | succ k ih =>
    unfold greedyLoop
    rcases h : bestSet S w J R with _ | i
    · exact Finset.sum_nonneg fun j hj => mul_nonneg (mul_nonneg (hx j hj) (hw j (hCJ j hj)))
        (Rat.cast_nonneg.2 (harmonic_nonneg _))
    obtain ⟨hiJ, hne, hmin⟩ := bestSet_spec h
    have ih' := ih (R := R \ S i) fun a ha => hcov a (Finset.mem_sdiff.1 ha).1
    rw [List.map_cons, List.sum_cons]
    set A := S i ∩ R with hA
    set ρ : 𝕜 := w i / A.card with hρ
    have hApos : (0 : 𝕜) < A.card := by exact_mod_cast hne.card_pos
    have hρ0 : 0 ≤ ρ := div_nonneg (hw i hiJ) hApos.le
    -- The chosen set costs `ρ * |A|`, which the fractional cover of `A` pays at rate `ρ`.
    have hwi : w i ≤ ∑ j ∈ C, x j * ρ * (S j ∩ A).card := by
      have hcount : ∑ j ∈ C, x j * (S j ∩ A).card = ∑ a ∈ A, ∑ j ∈ C with a ∈ S j, x j := by
        simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.mul_sum,
          mul_one, Finset.sum_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_filter]
        congr 1
        ext a
        simp only [Finset.mem_inter, Finset.mem_filter]
        tauto
      have hA1 : (A.card : 𝕜) ≤ ∑ a ∈ A, ∑ j ∈ C with a ∈ S j, x j := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
        exact Finset.sum_le_sum fun a ha => hcov a (Finset.mem_inter.1 ha).2
      calc w i = ρ * A.card := by rw [hρ, div_mul_cancel₀ _ hApos.ne']
        _ ≤ ρ * ∑ j ∈ C, x j * (S j ∩ A).card := by
          rw [hcount]
          exact mul_le_mul_of_nonneg_left hA1 hρ0
        _ = ∑ j ∈ C, x j * ρ * (S j ∩ A).card := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
    -- Each set of the cover pays its share at most from its harmonic budget.
    have hstep : ∀ j ∈ C, x j * ρ * (S j ∩ A).card ≤
        x j * w j * (harmonic (S j ∩ R).card : 𝕜) -
          x j * w j * (harmonic (S j ∩ (R \ S i)).card : 𝕜) := by
      intro j hj
      have hsplit : (S j ∩ R).card = (S j ∩ (R \ S i)).card + (S j ∩ A).card := by
        have := Finset.card_sdiff_add_card_inter (S j ∩ R) (S i)
        rw [Finset.inter_sdiff_assoc] at this
        rw [← this]
        congr 2
        ext a
        simp only [Finset.mem_inter, hA]
        tauto
      rcases (S j ∩ A).eq_empty_or_nonempty with hjA | hjA
      · have : (S j ∩ R).card = (S j ∩ (R \ S i)).card := by
          rw [hsplit, hjA, Finset.card_empty, add_zero]
        rw [hjA, this, Finset.card_empty, Nat.cast_zero, mul_zero, sub_self]
      set a := (S j ∩ R).card with ha
      set b := (S j ∩ (R \ S i)).card with hb
      have hjR : (S j ∩ R).Nonempty := by
        obtain ⟨y, hy⟩ := hjA
        exact ⟨y, by simp only [Finset.mem_inter, hA] at hy ⊢; tauto⟩
      have hρj : ρ ≤ w j / a := hmin j (hCJ j hj) hjR
      have hH : ((a : 𝕜) - b) / a ≤ (harmonic a : 𝕜) - harmonic b := by
        have := (Rat.cast_le (K := 𝕜)).2 (sub_div_le_harmonic_sub (a := a) (b := b) (by omega))
        push_cast at this
        exact this
      have hc : ((S j ∩ A).card : 𝕜) = a - b := by
        rw [hsplit]
        push_cast
        ring
      rw [hc, ← mul_sub]
      have hxw : 0 ≤ x j * w j := mul_nonneg (hx j hj) (hw j (hCJ j hj))
      calc x j * ρ * (a - b) ≤ x j * (w j / a) * (a - b) := by
            have hab : (0 : 𝕜) ≤ a - b := by
              rw [← hc]
              positivity
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρj (hx j hj)) hab
        _ = x j * w j * (((a : 𝕜) - b) / a) := by ring
        _ ≤ x j * w j * ((harmonic a : 𝕜) - harmonic b) :=
            mul_le_mul_of_nonneg_left hH hxw
    calc w i + ((greedyLoop S w J k (R \ S i)).map w).sum
        ≤ ∑ j ∈ C, x j * ρ * (S j ∩ A).card +
            ∑ j ∈ C, x j * w j * (harmonic (S j ∩ (R \ S i)).card : 𝕜) := add_le_add hwi ih'
      _ ≤ ∑ j ∈ C, (x j * w j * (harmonic (S j ∩ R).card : 𝕜) -
            x j * w j * (harmonic (S j ∩ (R \ S i)).card : 𝕜)) +
            ∑ j ∈ C, x j * w j * (harmonic (S j ∩ (R \ S i)).card : 𝕜) :=
          add_le_add_left (Finset.sum_le_sum hstep) _
      _ = ∑ j ∈ C, x j * w j * (harmonic (S j ∩ R).card : 𝕜) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => sub_add_cancel _ _

/-- **Chvátal's bound** ([Chvatal1979]; [WilliamsonShmoys2011], Theorem 1.12): against every
fractional cover `x` of `U` by candidates, the greedy cover costs at most
`∑ j ∈ C, x j * w j * H(|S j ∩ U|)`. -/
theorem sum_greedy_le_sum_harmonic {U : Finset α} {C : Finset ι} {x : ι → 𝕜}
    (hw : ∀ j ∈ J, 0 ≤ w j) (hCJ : ∀ j ∈ C, j ∈ J) (hx : ∀ j ∈ C, 0 ≤ x j)
    (hcov : ∀ a ∈ U, 1 ≤ ∑ j ∈ C with a ∈ S j, x j) :
    ((greedy S w J U).map w).sum ≤ ∑ j ∈ C, x j * w j * (harmonic (S j ∩ U).card : 𝕜) :=
  sum_greedyLoop_le_sum_harmonic hw hCJ hx hcov

/-- **The `H d` guarantee against fractional covers** ([Chvatal1979]; [WilliamsonShmoys2011],
Theorem 1.12): if every set of the fractional cover meets `U` in at most `d` elements, the greedy
cover costs at most `H d` times the cost `∑ j ∈ C, x j * w j` of the fractional cover. -/
theorem sum_greedy_le_harmonic_mul_fractional {U : Finset α} {C : Finset ι}
    {x : ι → 𝕜} {d : ℕ} (hw : ∀ j ∈ J, 0 ≤ w j) (hCJ : ∀ j ∈ C, j ∈ J)
    (hx : ∀ j ∈ C, 0 ≤ x j) (hcov : ∀ a ∈ U, 1 ≤ ∑ j ∈ C with a ∈ S j, x j)
    (hd : ∀ j ∈ C, (S j ∩ U).card ≤ d) :
    ((greedy S w J U).map w).sum ≤ (harmonic d : 𝕜) * ∑ j ∈ C, x j * w j := by
  refine (sum_greedy_le_sum_harmonic hw hCJ hx hcov).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [mul_comm (harmonic d : 𝕜)]
  exact mul_le_mul_of_nonneg_left (Rat.cast_le.2 (harmonic_mono (hd j hj)))
    (mul_nonneg (hx j hj) (hw j (hCJ j hj)))

/-- **The `H d` guarantee** ([Chvatal1979]; [WilliamsonShmoys2011], Theorem 1.12): if the
candidates `C` cover `U` and each of their sets meets `U` in at most `d` elements, the greedy cover
costs at most `H d` times the cost of `C`. Taking `C` optimal, the greedy algorithm is an
`H d`-approximation. -/
theorem sum_greedy_le_harmonic_mul {U : Finset α} {C : Finset ι} {d : ℕ}
    (hw : ∀ j ∈ J, 0 ≤ w j) (hCJ : ∀ j ∈ C, j ∈ J) (hcov : ∀ a ∈ U, ∃ j ∈ C, a ∈ S j)
    (hd : ∀ j ∈ C, (S j ∩ U).card ≤ d) :
    ((greedy S w J U).map w).sum ≤ (harmonic d : 𝕜) * ∑ j ∈ C, w j := by
  have h := sum_greedy_le_harmonic_mul_fractional (x := fun _ => 1) hw hCJ (fun _ _ => zero_le_one)
    (fun a ha => ?_) hd
  · simpa only [one_mul] using h
  obtain ⟨j, hj, haj⟩ := hcov a ha
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.one_le_cast]
  exact Finset.card_pos.2 ⟨j, Finset.mem_filter.2 ⟨hj, haj⟩⟩

/-- **The `H n` guarantee** ([WilliamsonShmoys2011], Theorem 1.11): if the candidates `C` cover
`U`, the greedy cover costs at most `H |U|` times the cost of `C`. -/
theorem sum_greedy_le_harmonic_card_mul {U : Finset α} {C : Finset ι}
    (hw : ∀ j ∈ J, 0 ≤ w j) (hCJ : ∀ j ∈ C, j ∈ J) (hcov : ∀ a ∈ U, ∃ j ∈ C, a ∈ S j) :
    ((greedy S w J U).map w).sum ≤ (harmonic U.card : 𝕜) * ∑ j ∈ C, w j :=
  sum_greedy_le_harmonic_mul hw hCJ hcov fun _ _ => Finset.card_le_card Finset.inter_subset_right

end Cost

/-- **The logarithmic guarantee**: over `ℝ`, if the candidates `C` cover `U` and each of their
sets meets `U` in at most `d` elements, the greedy cover costs at most `(1 + log d)` times the cost
of `C`, by `harmonic_le_one_add_log`. -/
theorem sum_greedy_le_one_add_log_mul {S : ι → Finset α} {w : ι → ℝ}
    {J : List ι} {U : Finset α} {C : Finset ι} {d : ℕ} (hw : ∀ j ∈ J, 0 ≤ w j)
    (hCJ : ∀ j ∈ C, j ∈ J) (hcov : ∀ a ∈ U, ∃ j ∈ C, a ∈ S j)
    (hd : ∀ j ∈ C, (S j ∩ U).card ≤ d) :
    ((greedy S w J U).map w).sum ≤ (1 + Real.log d) * ∑ j ∈ C, w j :=
  (sum_greedy_le_harmonic_mul hw hCJ hcov hd).trans
    (mul_le_mul_of_nonneg_right (harmonic_le_one_add_log d)
      (Finset.sum_nonneg fun j hj => hw j (hCJ j hj)))

end Cslib.Algorithms.Lean.SetCover
