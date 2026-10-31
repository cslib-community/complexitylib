/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.Query.Submodular.Greedy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# Adversarial Value-Oracle Lower Bounds for Submodular Maximization

This module proves worst-case deterministic value-oracle query lower bounds at budget `k = 1` for
cardinality-constrained normalized (`f ∅ = 0`) monotone submodular maximization:

1. For any approximation factor `c > 1 / 2` and any ground list `xs`, every deterministic
   `c`-approximate algorithm at budget `k = 1` must make at least `xs.toFinset.card - 1` value
   queries (`IsSubmodularCardMaxAlg.card_toFinset_sub_one_le_countQueries`).
2. For any approximation factor `c > 100 / 159` — in particular for the optimal greedy ratio
   `c = 1 - Real.exp (-1) > 0.6321 > 100 / 159 ≈ 0.6289` — and any ground list `xs` with
   `2 ≤ xs.toFinset.card`, every deterministic `c`-approximate algorithm at budget `k = 1` must
   make at least `xs.toFinset.card` value queries
   (`IsSubmodularCardMaxAlg.card_toFinset_le_countQueries` and
   `IsSubmodularCardMaxAlg.card_toFinset_le_countQueries_one_sub_exp_neg_one`).

   Note on `n ≤ 1`: when `xs.toFinset.card ≤ 1` and `k = 1`, returning `xs.toFinset` without
   issuing any value query is `1`-approximate on all monotone objectives, so `0` queries genuinely
   suffices at `n ≤ 1`, whereas `n` queries are both necessary and sufficient
   (`submodularGreedyQuery xs 1`) for every `n ≥ 2`.
3. On any `[Infinite α]`, this yields the uniform `Cslib.Query.LowerBound`
   `LowerBound (fun xs => alg xs 1) List.length (fun n => if n ≤ 1 then 0 else n)`, matching
   `submodularGreedyQuery_upperBound 1` (`1 * n = n`) with exact constant factor `1` for all
   `n ≥ 2`.

**Scope and relation to [NemhauserWolsey1978].** [NemhauserWolsey1978] (Section 4) proves an
asymptotic super-polynomial value-oracle query lower bound for beating `1 - 1 / e` across growing
cardinality budgets `K`; that general-`K` super-polynomial lower bound is out of scope here.
Instead, this module proves only the bounded `k = 1` linear (`n`-query) lower bound via an
original elementary `(59, 100, 159)` capped-modular adversary (and `(1, 2)` for `c > 1 / 2`),
using that any uniform `c`-approximate algorithm must achieve ratio `c` at `k = 1`.

## Proof technique

Given `E = xs.toFinset`, consider the capped modular family
`cappedModular E w cap S = min (∑ x ∈ S ∩ E, w x) cap`:
* Baseline `baseAdv E`: weight `100` on every `x ∈ E`, cap `159`.
* High perturbation `highAdv E e`: weight `159` on `e`, `100` on `E \ {e}`, cap `159`.
* Low perturbation `lowAdv E e`: weight `59` on `e`, `100` on `E \ {e}`, cap `159`.

Every member is nonnegative, monotone, and submodular (`IsSubmodular.min_const` applied to
`isSubmodular_modularSum`). Whenever `S ∩ E ≠ {e}`, either `e ∉ S ∩ E` (weights on `S ∩ E` are all
`100`) or `|S ∩ E| ≥ 2` (the sum on `S ∩ E` is at least `59 + 100 = 159`, saturating the cap), so
`baseAdv E S = highAdv E e S = lowAdv E e S` even if the algorithm queries sets `S` containing
elements outside `E`. Thus if `alg xs 1` fails to query any `S` with `S ∩ E = {e}`, it returns the
same output `out` under all three oracles: if `e ∉ out`, `highAdv E e` refutes `c`-approximation
(`100 < 159 * c`), while if `e ∈ out` (`out = {e}`), `lowAdv E e` refutes `c`-approximation against
any `x ∈ E \ {e}` (`59 < 100 * c`). Injectivity of `e ↦ {e}` inside `(queriedSets ...).image
(· ∩ E)` then yields `E.card ≤ countQueries`.

## Main definitions

* `Cslib.Query.IsSubmodularCardMaxAlg`: specification of a deterministic `c`-approximate
  cardinality-constrained monotone submodular maximization algorithm in `FreeM (ValueQuery α ℝ)`.
* `Cslib.Query.cappedModular`, `Cslib.Query.baseAdv`: adversarial capped-modular objectives.

## Main results

* `submodularGreedyQuery_isSubmodularCardMaxAlg`: `submodularGreedyQuery` satisfies
  `IsSubmodularCardMaxAlg` with `c = 1 - Real.exp (-1)`.
* `IsSubmodularCardMaxAlg.card_toFinset_sub_one_le_countQueries`: `xs.toFinset.card - 1` lower
  bound for every `c > 1 / 2`.
* `IsSubmodularCardMaxAlg.card_toFinset_le_countQueries`,
  `IsSubmodularCardMaxAlg.card_toFinset_le_countQueries_one_sub_exp_neg_one`: exact
  `xs.toFinset.card` lower bound for `2 ≤ xs.toFinset.card` and `c > 100 / 159` (including
  `1 - Real.exp (-1)`).
* `IsSubmodularCardMaxAlg.lowerBound_infinite`, `submodularGreedyQuery_lowerBound_one`: uniform
  `LowerBound` on `[Infinite α]`.

## References

* [NemhauserWolsey1978] George L. Nemhauser and Laurence A. Wolsey,
  *Best Algorithms for Approximating the Maximum of a Submodular Set Function*, 1978.
-/

public section

open Cslib.Algorithms.Lean.Submodular

namespace Cslib.Query

/-- Specification of a deterministic `c`-approximate value-oracle algorithm for
cardinality-constrained normalized (`f ∅ = 0`) monotone submodular maximization over `ℝ`. -/
structure IsSubmodularCardMaxAlg {α : Type} [DecidableEq α]
    (alg : List α → ℕ → FreeM (ValueQuery α ℝ) (Finset α)) (c : ℝ) : Prop where
  subset_toFinset : ∀ (f : Finset α → ℝ),
    IsSubmodular f → Monotone f → f ∅ = 0 →
    ∀ (xs : List α) (k : ℕ),
      (alg xs k).eval (ValueQuery.oracleOf f) ⊆ xs.toFinset
  card_le : ∀ (f : Finset α → ℝ),
    IsSubmodular f → Monotone f → f ∅ = 0 →
    ∀ (xs : List α) (k : ℕ),
      ((alg xs k).eval (ValueQuery.oracleOf f)).card ≤ k
  approx : ∀ (f : Finset α → ℝ),
    IsSubmodular f → Monotone f → f ∅ = 0 →
    ∀ (xs : List α) (k : ℕ) (OPT : Finset α),
      OPT ⊆ xs.toFinset → OPT.card ≤ k →
      c * f OPT ≤ f ((alg xs k).eval (ValueQuery.oracleOf f))

/-- `submodularGreedyQuery` is a `(1 - Real.exp (-1))`-approximate cardinality-constrained
monotone submodular maximization algorithm. -/
theorem submodularGreedyQuery_isSubmodularCardMaxAlg {α : Type} [DecidableEq α] :
    IsSubmodularCardMaxAlg (submodularGreedyQuery (α := α) (β := ℝ)) (1 - Real.exp (-1)) where
  subset_toFinset f _ _ _ xs k := by
    rw [eval_submodularGreedyQuery_oracleOf]
    exact submodularGreedy_subset_toFinset f xs k
  card_le f _ _ _ xs k := by
    rw [eval_submodularGreedyQuery_oracleOf]
    exact card_submodularGreedy_le f xs k
  approx _ hf hmono hf0 xs k _ hOPT_sub hOPT_card :=
    one_sub_exp_neg_one_mul_le_eval_submodularGreedyQuery hf hmono hf0.ge xs k hOPT_sub hOPT_card

/-! ## Capped modular adversary family -/

section Adversary

variable {α : Type} [DecidableEq α]

/-- Capped modular function `min (∑ x ∈ S ∩ E, w x) cap`, extended by zero outside `E`. -/
def cappedModular (E : Finset α) (w : α → ℝ) (cap : ℝ) (S : Finset α) : ℝ :=
  min (modularSum (fun x => if x ∈ E then w x else 0) S) cap

theorem cappedModular_eq_min_sum_inter (E : Finset α) (w : α → ℝ) (cap : ℝ) (S : Finset α) :
    cappedModular E w cap S = min (∑ x ∈ S ∩ E, w x) cap := by
  unfold cappedModular modularSum
  refine congrArg (min · cap) ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp [Finset.mem_inter]

theorem cappedModular_empty {E : Finset α} {w : α → ℝ} {cap : ℝ} (hcap : 0 ≤ cap) :
    cappedModular E w cap ∅ = 0 := by
  simp [cappedModular, hcap]

theorem monotone_cappedModular {E : Finset α} {w : α → ℝ}
    (hw : ∀ x ∈ E, 0 ≤ w x) (cap : ℝ) :
    Monotone (cappedModular E w cap) := by
  refine monotone_min_const (monotone_modularSum fun x => ?_) cap
  by_cases hx : x ∈ E
  · simp [hx, hw x hx]
  · simp [hx]

theorem isSubmodular_cappedModular {E : Finset α} {w : α → ℝ}
    (hw : ∀ x ∈ E, 0 ≤ w x) (cap : ℝ) :
    IsSubmodular (cappedModular E w cap) := by
  refine (isSubmodular_modularSum _).min_const (monotone_modularSum fun x => ?_) cap
  by_cases hx : x ∈ E
  · simp [hx, hw x hx]
  · simp [hx]

/-- Baseline `(1, 2)` capped-modular instance for the `c > 1 / 2` bound. -/
def halfBaseAdv (E : Finset α) : Finset α → ℝ :=
  cappedModular E (fun _ => 1) 2

private def halfHighAdv (E : Finset α) (e : α) : Finset α → ℝ :=
  cappedModular E (fun x => if x = e then 2 else 1) 2

/-- Baseline `(59, 100, 159)` capped-modular instance for the `c > 100 / 159` bound. -/
def baseAdv (E : Finset α) : Finset α → ℝ :=
  cappedModular E (fun _ => 100) 159

private def highAdv (E : Finset α) (e : α) : Finset α → ℝ :=
  cappedModular E (fun x => if x = e then 159 else 100) 159

private def lowAdv (E : Finset α) (e : α) : Finset α → ℝ :=
  cappedModular E (fun x => if x = e then 59 else 100) 159

omit [DecidableEq α] in
private theorem exists_other_of_mem_of_ne_singleton {I : Finset α} {e : α}
    (heI : e ∈ I) (hne : I ≠ {e}) : ∃ y ∈ I, y ≠ e := by
  by_contra h
  push Not at h
  apply hne
  ext y
  simp only [Finset.mem_singleton]
  exact ⟨fun hy => h y hy, fun hy => hy ▸ heI⟩

omit [DecidableEq α] in
private theorem sum_pair_le_of_nonneg {I : Finset α} {w : α → ℝ}
    (hw : ∀ x ∈ I, 0 ≤ w x) {e y : α} (he : e ∈ I) (hy : y ∈ I) (hne : y ≠ e) :
    w e + w y ≤ ∑ x ∈ I, w x := by
  classical
  have hsub : ({e, y} : Finset α) ⊆ I := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have he_not : e ∉ ({y} : Finset α) := by simp [hne.symm]
  calc
    w e + w y = ∑ x ∈ ({e, y} : Finset α), w x := by simp [Finset.sum_insert he_not]
    _ ≤ ∑ x ∈ I, w x := Finset.sum_le_sum_of_subset_of_nonneg hsub fun x hx _ => hw x hx

private theorem halfBaseAdv_eq_halfHighAdv_of_inter_ne {E S : Finset α} {e : α}
    (hne : S ∩ E ≠ {e}) :
    halfBaseAdv E S = halfHighAdv E e S := by
  rw [halfBaseAdv, halfHighAdv, cappedModular_eq_min_sum_inter, cappedModular_eq_min_sum_inter]
  by_cases he : e ∈ S ∩ E
  · obtain ⟨y, hy, hy_ne⟩ := exists_other_of_mem_of_ne_singleton he hne
    have h1 : (2 : ℝ) ≤ ∑ _x ∈ S ∩ E, (1 : ℝ) := by
      have hp := sum_pair_le_of_nonneg (w := fun _ => (1 : ℝ)) (fun _ _ => by norm_num) he hy hy_ne
      linarith
    have h2 : (2 : ℝ) ≤ ∑ x ∈ S ∩ E, (if x = e then (2 : ℝ) else 1) := by
      have hp := sum_pair_le_of_nonneg (w := fun x => if x = e then (2 : ℝ) else 1)
        (fun x _ => by split_ifs <;> norm_num) he hy hy_ne
      simp only [↓reduceIte, hy_ne] at hp
      linarith
    rw [min_eq_right h1, min_eq_right h2]
  · congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxe : x ≠ e := fun h => he (h ▸ hx)
    simp [hxe]

private theorem baseAdv_eq_highAdv_of_inter_ne {E S : Finset α} {e : α}
    (hne : S ∩ E ≠ {e}) :
    baseAdv E S = highAdv E e S := by
  rw [baseAdv, highAdv, cappedModular_eq_min_sum_inter, cappedModular_eq_min_sum_inter]
  by_cases he : e ∈ S ∩ E
  · obtain ⟨y, hy, hy_ne⟩ := exists_other_of_mem_of_ne_singleton he hne
    have h1 : (159 : ℝ) ≤ ∑ _x ∈ S ∩ E, (100 : ℝ) := by
      have hp := sum_pair_le_of_nonneg (w := fun _ => (100 : ℝ))
        (fun _ _ => by norm_num) he hy hy_ne
      linarith
    have h2 : (159 : ℝ) ≤ ∑ x ∈ S ∩ E, (if x = e then (159 : ℝ) else 100) := by
      have hp := sum_pair_le_of_nonneg (w := fun x => if x = e then (159 : ℝ) else 100)
        (fun x _ => by split_ifs <;> norm_num) he hy hy_ne
      simp only [↓reduceIte, hy_ne] at hp
      linarith
    rw [min_eq_right h1, min_eq_right h2]
  · congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxe : x ≠ e := fun h => he (h ▸ hx)
    simp [hxe]

private theorem baseAdv_eq_lowAdv_of_inter_ne {E S : Finset α} {e : α}
    (hne : S ∩ E ≠ {e}) :
    baseAdv E S = lowAdv E e S := by
  rw [baseAdv, lowAdv, cappedModular_eq_min_sum_inter, cappedModular_eq_min_sum_inter]
  by_cases he : e ∈ S ∩ E
  · obtain ⟨y, hy, hy_ne⟩ := exists_other_of_mem_of_ne_singleton he hne
    have h1 : (159 : ℝ) ≤ ∑ _x ∈ S ∩ E, (100 : ℝ) := by
      have hp := sum_pair_le_of_nonneg (w := fun _ => (100 : ℝ))
        (fun _ _ => by norm_num) he hy hy_ne
      linarith
    have h2 : (159 : ℝ) ≤ ∑ x ∈ S ∩ E, (if x = e then (59 : ℝ) else 100) := by
      have hp := sum_pair_le_of_nonneg (w := fun x => if x = e then (59 : ℝ) else 100)
        (fun x _ => by split_ifs <;> norm_num) he hy hy_ne
      simp only [↓reduceIte, hy_ne] at hp
      linarith
    rw [min_eq_right h1, min_eq_right h2]
  · congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxe : x ≠ e := fun h => he (h ▸ hx)
    simp [hxe]

/-! ## Lower-bound theorems -/

/-- Any deterministic `c`-approximate algorithm with `1 / 2 < c` must issue at least
`xs.toFinset.card - 1` value queries at budget `k = 1` on `halfBaseAdv xs.toFinset`. -/
theorem IsSubmodularCardMaxAlg.card_toFinset_sub_one_le_countQueries
    {alg : List α → ℕ → FreeM (ValueQuery α ℝ) (Finset α)} {c : ℝ}
    (halg : IsSubmodularCardMaxAlg alg c) (hc : (1 : ℝ) / 2 < c) (xs : List α) :
    xs.toFinset.card - 1 ≤
      (alg xs 1).countQueries (ValueQuery.oracleOf (halfBaseAdv xs.toFinset)) := by
  set E := xs.toFinset
  let o₀ : {ι : Type} → ValueQuery α ℝ ι → ι := ValueQuery.oracleOf (halfBaseAdv E)
  set Q := ValueQuery.queriedSets o₀ (alg xs 1)
  have hf₀_sub : IsSubmodular (halfBaseAdv E) :=
    isSubmodular_cappedModular (fun _ _ => by norm_num) 2
  have hf₀_mono : Monotone (halfBaseAdv E) :=
    monotone_cappedModular (fun _ _ => by norm_num) 2
  have hf₀_empty : halfBaseAdv E ∅ = 0 :=
    cappedModular_empty (by norm_num)
  set out := (alg xs 1).eval o₀
  have hout_sub : out ⊆ E := halg.subset_toFinset _ hf₀_sub hf₀_mono hf₀_empty xs 1
  have hout_card : out.card ≤ 1 := halg.card_le _ hf₀_sub hf₀_mono hf₀_empty xs 1
  have hmust_query : ∀ e ∈ E \ out, ∃ S ∈ Q, S ∩ E = {e} := by
    intro e he_diff
    rcases Finset.mem_sdiff.mp he_diff with ⟨heE, he_out⟩
    by_contra hno
    push Not at hno
    have hfe_sub : IsSubmodular (halfHighAdv E e) :=
      isSubmodular_cappedModular (fun x _ => by split_ifs <;> norm_num) 2
    have hfe_mono : Monotone (halfHighAdv E e) :=
      monotone_cappedModular (fun x _ => by split_ifs <;> norm_num) 2
    have hfe_empty : halfHighAdv E e ∅ = 0 :=
      cappedModular_empty (by norm_num)
    have hagree : ∀ S ∈ Q, o₀ (.value S) = ValueQuery.oracleOf (halfHighAdv E e) (.value S) :=
      fun S hS => halfBaseAdv_eq_halfHighAdv_of_inter_ne (hno S hS)
    have hout_eq : (alg xs 1).eval (ValueQuery.oracleOf (halfHighAdv E e)) = out :=
      (ValueQuery.eval_eq_of_agree_on_queriedSets (alg xs 1) hagree).symm
    have happrox := halg.approx (halfHighAdv E e) hfe_sub hfe_mono hfe_empty xs 1 {e}
      (Finset.singleton_subset_iff.mpr heE) (by simp)
    rw [hout_eq] at happrox
    have hopt_val : halfHighAdv E e {e} = 2 := by
      have hinter : ({e} : Finset α) ∩ E = {e} :=
        Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr heE)
      rw [halfHighAdv, cappedModular_eq_min_sum_inter, hinter]
      norm_num
    have hout_le : halfHighAdv E e out ≤ 1 := by
      rw [halfHighAdv, cappedModular_eq_min_sum_inter]
      have hinter : out ∩ E = out := Finset.inter_eq_left.mpr hout_sub
      rw [hinter]
      have hsum : (∑ x ∈ out, if x = e then (2 : ℝ) else 1) = (out.card : ℝ) := by
        have hcongr : (∑ x ∈ out, if x = e then (2 : ℝ) else 1) = ∑ _x ∈ out, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have hxe : x ≠ e := fun h => he_out (h ▸ hx)
          simp [hxe]
        rw [hcongr, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hcard_r : (out.card : ℝ) ≤ 1 := by exact_mod_cast hout_card
      exact (min_le_left _ _).trans (hsum.le.trans hcard_r)
    rw [hopt_val] at happrox
    linarith
  have himg_sub : (E \ out).image (fun e => ({e} : Finset α)) ⊆ Q.image (fun S => S ∩ E) := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨e, he, rfl⟩
    rcases hmust_query e he with ⟨S, hSQ, hSE⟩
    exact Finset.mem_image.mpr ⟨S, hSQ, hSE⟩
  have hcard_diff : E.card - 1 ≤ (E \ out).card := by
    have h1 : E.card - out.card ≤ (E \ out).card := Finset.le_card_sdiff out E
    omega
  have hinj : Function.Injective (fun e : α => ({e} : Finset α)) :=
    fun _ _ h => Finset.singleton_injective h
  calc
    E.card - 1 ≤ (E \ out).card := hcard_diff
    _ = ((E \ out).image (fun e => ({e} : Finset α))).card :=
        (Finset.card_image_of_injective (E \ out) hinj).symm
    _ ≤ (Q.image (fun S => S ∩ E)).card := Finset.card_le_card himg_sub
    _ ≤ Q.card := Finset.card_image_le
    _ ≤ (alg xs 1).countQueries o₀ := ValueQuery.card_queriedSets_le_countQueries o₀ (alg xs 1)

/-- **Exact `n`-Query Adversarial Lower Bound at `k = 1`**: for any `c > 100 / 159` and any ground
list `xs` with `2 ≤ xs.toFinset.card`, every deterministic `c`-approximate algorithm at budget
`k = 1` must make at least `xs.toFinset.card` value queries on the original `(59, 100, 159)`
capped-modular adversary `baseAdv xs.toFinset`. (Unlike [NemhauserWolsey1978], Section 4, which
proves a general-budget super-polynomial lower bound, this theorem establishes the tight linear
single-step bound matching `countQueries_submodularGreedyQuery_one`.) -/
theorem IsSubmodularCardMaxAlg.card_toFinset_le_countQueries
    {alg : List α → ℕ → FreeM (ValueQuery α ℝ) (Finset α)} {c : ℝ}
    (halg : IsSubmodularCardMaxAlg alg c) (hc : (100 : ℝ) / 159 < c)
    {xs : List α} (hcard : 2 ≤ xs.toFinset.card) :
    xs.toFinset.card ≤
      (alg xs 1).countQueries (ValueQuery.oracleOf (baseAdv xs.toFinset)) := by
  set E := xs.toFinset
  let o₀ : {ι : Type} → ValueQuery α ℝ ι → ι := ValueQuery.oracleOf (baseAdv E)
  set Q := ValueQuery.queriedSets o₀ (alg xs 1)
  have hf₀_sub : IsSubmodular (baseAdv E) :=
    isSubmodular_cappedModular (fun _ _ => by norm_num) 159
  have hf₀_mono : Monotone (baseAdv E) :=
    monotone_cappedModular (fun _ _ => by norm_num) 159
  have hf₀_empty : baseAdv E ∅ = 0 :=
    cappedModular_empty (by norm_num)
  set out := (alg xs 1).eval o₀
  have hout_sub : out ⊆ E := halg.subset_toFinset _ hf₀_sub hf₀_mono hf₀_empty xs 1
  have hout_card : out.card ≤ 1 := halg.card_le _ hf₀_sub hf₀_mono hf₀_empty xs 1
  have hmust_query : ∀ e ∈ E, ∃ S ∈ Q, S ∩ E = {e} := by
    intro e heE
    by_contra hno
    push Not at hno
    by_cases he_out : e ∈ out
    · have hout_eq_singleton : out = {e} := by
        have hsub_single : {e} ⊆ out := Finset.singleton_subset_iff.mpr he_out
        exact (Finset.eq_of_subset_of_card_le hsub_single (by simpa using hout_card)).symm
      have hex_other : ∃ y ∈ E, y ≠ e := by
        have hne : E ≠ {e} := by
          intro hEq
          rw [hEq, Finset.card_singleton] at hcard
          omega
        exact exists_other_of_mem_of_ne_singleton heE hne
      rcases hex_other with ⟨y, hyE, hye⟩
      have hlow_sub : IsSubmodular (lowAdv E e) :=
        isSubmodular_cappedModular (fun x _ => by split_ifs <;> norm_num) 159
      have hlow_mono : Monotone (lowAdv E e) :=
        monotone_cappedModular (fun x _ => by split_ifs <;> norm_num) 159
      have hlow_empty : lowAdv E e ∅ = 0 :=
        cappedModular_empty (by norm_num)
      have hagree : ∀ S ∈ Q, o₀ (.value S) = ValueQuery.oracleOf (lowAdv E e) (.value S) :=
        fun S hS => baseAdv_eq_lowAdv_of_inter_ne (hno S hS)
      have hout_eq : (alg xs 1).eval (ValueQuery.oracleOf (lowAdv E e)) = out :=
        (ValueQuery.eval_eq_of_agree_on_queriedSets (alg xs 1) hagree).symm
      have happrox := halg.approx (lowAdv E e) hlow_sub hlow_mono hlow_empty xs 1 {y}
        (Finset.singleton_subset_iff.mpr hyE) (by simp)
      rw [hout_eq, hout_eq_singleton] at happrox
      have hopt_val : lowAdv E e {y} = 100 := by
        have hinter : ({y} : Finset α) ∩ E = {y} :=
          Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hyE)
        rw [lowAdv, cappedModular_eq_min_sum_inter, hinter]
        simp only [Finset.sum_singleton, hye, ↓reduceIte]
        norm_num
      have hout_val : lowAdv E e {e} = 59 := by
        have hinter : ({e} : Finset α) ∩ E = {e} :=
          Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr heE)
        rw [lowAdv, cappedModular_eq_min_sum_inter, hinter]
        norm_num
      rw [hopt_val, hout_val] at happrox
      linarith
    · have hhigh_sub : IsSubmodular (highAdv E e) :=
        isSubmodular_cappedModular (fun x _ => by split_ifs <;> norm_num) 159
      have hhigh_mono : Monotone (highAdv E e) :=
        monotone_cappedModular (fun x _ => by split_ifs <;> norm_num) 159
      have hhigh_empty : highAdv E e ∅ = 0 :=
        cappedModular_empty (by norm_num)
      have hagree : ∀ S ∈ Q, o₀ (.value S) = ValueQuery.oracleOf (highAdv E e) (.value S) :=
        fun S hS => baseAdv_eq_highAdv_of_inter_ne (hno S hS)
      have hout_eq : (alg xs 1).eval (ValueQuery.oracleOf (highAdv E e)) = out :=
        (ValueQuery.eval_eq_of_agree_on_queriedSets (alg xs 1) hagree).symm
      have happrox := halg.approx (highAdv E e) hhigh_sub hhigh_mono hhigh_empty xs 1 {e}
        (Finset.singleton_subset_iff.mpr heE) (by simp)
      rw [hout_eq] at happrox
      have hopt_val : highAdv E e {e} = 159 := by
        have hinter : ({e} : Finset α) ∩ E = {e} :=
          Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr heE)
        rw [highAdv, cappedModular_eq_min_sum_inter, hinter]
        norm_num
      have hout_le : highAdv E e out ≤ 100 := by
        rw [highAdv, cappedModular_eq_min_sum_inter]
        have hinter : out ∩ E = out := Finset.inter_eq_left.mpr hout_sub
        rw [hinter]
        have hsum : (∑ x ∈ out, if x = e then (159 : ℝ) else 100) = 100 * (out.card : ℝ) := by
          have hcongr : (∑ x ∈ out, if x = e then (159 : ℝ) else 100) =
              ∑ _x ∈ out, (100 : ℝ) := by
            refine Finset.sum_congr rfl fun x hx => ?_
            have hxe : x ≠ e := fun h => he_out (h ▸ hx)
            simp [hxe]
          rw [hcongr, Finset.sum_const, nsmul_eq_mul, mul_comm]
        have hcard_r : (out.card : ℝ) ≤ 1 := by exact_mod_cast hout_card
        exact (min_le_left _ _).trans (by linarith)
      rw [hopt_val] at happrox
      linarith
  have himg_sub : E.image (fun e => ({e} : Finset α)) ⊆ Q.image (fun S => S ∩ E) := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨e, he, rfl⟩
    rcases hmust_query e he with ⟨S, hSQ, hSE⟩
    exact Finset.mem_image.mpr ⟨S, hSQ, hSE⟩
  have hinj : Function.Injective (fun e : α => ({e} : Finset α)) :=
    fun _ _ h => Finset.singleton_injective h
  calc
    E.card = (E.image (fun e => ({e} : Finset α))).card :=
        (Finset.card_image_of_injective E hinj).symm
    _ ≤ (Q.image (fun S => S ∩ E)).card := Finset.card_le_card himg_sub
    _ ≤ Q.card := Finset.card_image_le
    _ ≤ (alg xs 1).countQueries o₀ := ValueQuery.card_queriedSets_le_countQueries o₀ (alg xs 1)

/-- Numerical check: `100 / 159 < 1 - Real.exp (-1)`. -/
theorem hundred_div_159_lt_one_sub_exp_neg_one :
    (100 : ℝ) / 159 < 1 - Real.exp (-1) := by
  have hexp := Real.exp_neg_one_lt_d9
  linarith

/-- Specialization of `card_toFinset_le_countQueries` to `(1 - Real.exp (-1))`-approximate
algorithms: at budget `k = 1`, any deterministic `(1 - 1/e)`-approximate value-oracle algorithm
must issue at least `xs.toFinset.card` queries whenever `2 ≤ xs.toFinset.card`. -/
theorem IsSubmodularCardMaxAlg.card_toFinset_le_countQueries_one_sub_exp_neg_one
    {alg : List α → ℕ → FreeM (ValueQuery α ℝ) (Finset α)}
    (halg : IsSubmodularCardMaxAlg alg (1 - Real.exp (-1)))
    {xs : List α} (hcard : 2 ≤ xs.toFinset.card) :
    xs.toFinset.card ≤
      (alg xs 1).countQueries (ValueQuery.oracleOf (baseAdv xs.toFinset)) :=
  halg.card_toFinset_le_countQueries hundred_div_159_lt_one_sub_exp_neg_one hcard

/-- On duplicate-free ground lists of length `≥ 2`, any `(1 - Real.exp (-1))`-approximate
algorithm at budget `k = 1` must issue at least `xs.length` value queries. -/
theorem IsSubmodularCardMaxAlg.length_le_countQueries_one_sub_exp_neg_one
    {alg : List α → ℕ → FreeM (ValueQuery α ℝ) (Finset α)}
    (halg : IsSubmodularCardMaxAlg alg (1 - Real.exp (-1)))
    {xs : List α} (hnodup : xs.Nodup) (hlen : 2 ≤ xs.length) :
    xs.length ≤
      (alg xs 1).countQueries (ValueQuery.oracleOf (baseAdv xs.toFinset)) := by
  have hcard : xs.toFinset.card = xs.length := List.toFinset_card_of_nodup hnodup
  rw [← hcard]
  exact halg.card_toFinset_le_countQueries_one_sub_exp_neg_one (by omega)

/-- Uniform `Cslib.Query.LowerBound` on any infinite ground type: every deterministic
`c`-approximate algorithm (`c > 100 / 159`) at budget `k = 1` has worst-case value-query
complexity at least `if n ≤ 1 then 0 else n`. -/
theorem IsSubmodularCardMaxAlg.lowerBound_infinite [Infinite α]
    {alg : List α → ℕ → FreeM (ValueQuery α ℝ) (Finset α)} {c : ℝ}
    (halg : IsSubmodularCardMaxAlg alg c) (hc : (100 : ℝ) / 159 < c) :
    LowerBound (fun xs : List α => alg xs 1) List.length
      (fun n => if n ≤ 1 then 0 else n) := by
  intro n
  by_cases hn : n ≤ 1
  · refine ⟨[], by simp, ValueQuery.oracleOf (fun _ => 0), ?_⟩
    simp [hn]
  · have hn2 : 2 ≤ n := by omega
    let xs : List α := (List.range n).map (Infinite.natEmbedding α)
    have hlen : xs.length = n := by simp [xs]
    have hnodup : xs.Nodup := List.nodup_range.map (Infinite.natEmbedding α).injective
    have hcard : xs.toFinset.card = n :=
      (List.toFinset_card_of_nodup hnodup).trans hlen
    refine ⟨xs, hlen.le, ValueQuery.oracleOf (baseAdv xs.toFinset), ?_⟩
    simp only [hn, ↓reduceIte]
    rw [← hcard]
    exact halg.card_toFinset_le_countQueries hc (by omega)

/-- Instantiation at `submodularGreedyQuery · 1`: worst-case query complexity is at least
`if n ≤ 1 then 0 else n`, matching `submodularGreedyQuery_upperBound 1` (`1 * n = n`) for all
`n ≥ 2`. -/
theorem submodularGreedyQuery_lowerBound_one [Infinite α] :
    LowerBound (fun xs : List α => submodularGreedyQuery (β := ℝ) xs 1) List.length
      (fun n => if n ≤ 1 then 0 else n) :=
  submodularGreedyQuery_isSubmodularCardMaxAlg.lowerBound_infinite
    hundred_div_159_lt_one_sub_exp_neg_one

end Adversary

end Cslib.Query
