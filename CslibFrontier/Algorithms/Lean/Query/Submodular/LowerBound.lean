/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Query.Submodular.Greedy
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
* High perturbation `h_e`: weight `159` on `e`, `100` on `E \ {e}`, cap `159`.
* Low perturbation `l_e`: weight `59` on `e`, `100` on `E \ {e}`, cap `159`.

Every member is nonnegative, monotone, and submodular (`IsSubmodular.min_const` applied to
`isSubmodular_modularSum`). Whenever `S ∩ E ≠ {e}`, either `e ∉ S ∩ E` (weights on `S ∩ E` are all
`100`) or `|S ∩ E| ≥ 2` (the sum on `S ∩ E` is at least `59 + 100 = 159`, saturating the cap), so
`baseAdv E S = h_e S = l_e S` even if the algorithm queries sets `S` containing elements outside
`E`. Thus if `alg xs 1` fails to query any `S` with `S ∩ E = {e}`, it returns the same output `out`
under all three oracles: if `e ∉ out`, `h_e` refutes `c`-approximation (`100 < 159 * c`), while if
`e ∈ out` (`out = {e}`), `l_e` refutes `c`-approximation against
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

/-- Baseline `(59, 100, 159)` capped-modular instance for the `c > 100 / 159` bound. -/
def baseAdv (E : Finset α) : Finset α → ℝ :=
  cappedModular E (fun _ => 100) 159

/-- Two capped-modular functions whose weights differ only at `e` agree on every `S` whose
intersection with `E` is not `{e}`, once any two elements of `E` including `e` reach the cap under
both weightings. -/
private theorem cappedModular_eq_of_inter_ne {E S : Finset α} {e : α} {w w' : α → ℝ} {cap : ℝ}
    (hne : S ∩ E ≠ {e}) (hw : ∀ x, 0 ≤ w x) (hw' : ∀ x, 0 ≤ w' x) (hwe : ∀ x, x ≠ e → w x = w' x)
    (hcap : ∀ y, y ≠ e → cap ≤ w e + w y) (hcap' : ∀ y, y ≠ e → cap ≤ w' e + w' y) :
    cappedModular E w cap S = cappedModular E w' cap S := by
  rw [cappedModular_eq_min_sum_inter, cappedModular_eq_min_sum_inter]
  by_cases he : e ∈ S ∩ E
  · -- `S ∩ E` holds `e` and another element `y`, so both sums reach the cap.
    obtain ⟨y, hy, hye⟩ := ((Finset.nontrivial_iff_ne_singleton he).2 hne).exists_ne e
    rw [min_eq_right ((hcap y hye).trans
        (Finset.add_le_sum (fun x _ => hw x) he hy hye.symm)),
      min_eq_right ((hcap' y hye).trans
        (Finset.add_le_sum (fun x _ => hw' x) he hy hye.symm))]
  · congr 1
    exact Finset.sum_congr rfl fun x hx => hwe x fun h => he (h ▸ hx)

/-- A capped-modular function on a singleton of `E` is the capped weight. -/
private theorem cappedModular_singleton {E : Finset α} {w : α → ℝ} {cap : ℝ} {e : α}
    (he : e ∈ E) : cappedModular E w cap {e} = min (w e) cap := by
  rw [cappedModular_eq_min_sum_inter,
    Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr he), Finset.sum_singleton]

/-- A set of at most one element of `E`, avoiding `e`, has value at most the weight `b` of the
elements other than `e`. -/
private theorem cappedModular_ite_le {E out : Finset α} {e : α} {a b cap : ℝ} (hb : 0 ≤ b)
    (hout : out ⊆ E) (he : e ∉ out) (hcard : out.card ≤ 1) :
    cappedModular E (fun x => if x = e then a else b) cap out ≤ b := by
  have hsum : (∑ x ∈ out, if x = e then a else b) = ∑ _x ∈ out, b :=
    Finset.sum_congr rfl fun x hx => by simp [show x ≠ e from fun h => he (h ▸ hx)]
  rw [cappedModular_eq_min_sum_inter, Finset.inter_eq_left.mpr hout, hsum, Finset.sum_const,
    nsmul_eq_mul]
  have hcard_r : (out.card : ℝ) ≤ 1 := by exact_mod_cast hcard
  exact (min_le_left _ _).trans (by nlinarith)

/-- If a run of `alg xs 1` against the uniform capped-modular objective with weight `b` never
isolates `e` (no queried `S` has `S ∩ E = {e}`), then its output is `c`-approximate for the
adversary that reweights `e` to `a`, provided any two elements including `e` reach the cap. -/
private theorem IsSubmodularCardMaxAlg.approx_reweight_of_not_isolated
    {alg : List α → ℕ → FreeM (ValueQuery α ℝ) (Finset α)} {c : ℝ}
    (halg : IsSubmodularCardMaxAlg alg c) {xs : List α} {e : α} {a b cap : ℝ}
    {f : Finset α → ℝ} (hf : f = cappedModular xs.toFinset (fun _ => b) cap)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hcap : 0 ≤ cap) (hab : cap ≤ a + b) (hbb : cap ≤ b + b)
    (hno : ∀ S ∈ ValueQuery.queriedSets (ValueQuery.oracleOf f) (alg xs 1),
      S ∩ xs.toFinset ≠ {e})
    {OPT : Finset α} (hOPT : OPT ⊆ xs.toFinset) (hOPT_card : OPT.card ≤ 1) :
    c * cappedModular xs.toFinset (fun x => if x = e then a else b) cap OPT ≤
      cappedModular xs.toFinset (fun x => if x = e then a else b) cap
        ((alg xs 1).eval (ValueQuery.oracleOf f)) := by
  subst hf
  have hw : ∀ x, 0 ≤ if x = e then a else b := fun x => by split_ifs <;> assumption
  rw [ValueQuery.eval_eq_of_agree_on_queriedSets
    (o₂ := ValueQuery.oracleOf (cappedModular xs.toFinset (fun x => if x = e then a else b) cap))
    (alg xs 1) fun S hS =>
    cappedModular_eq_of_inter_ne (hno S hS) (fun _ => hb) hw (fun x hx => by simp [hx])
      (fun _ _ => hbb) (fun y hy => by simpa [hy] using hab)]
  exact halg.approx _ (isSubmodular_cappedModular (fun x _ => hw x) cap)
    (monotone_cappedModular (fun x _ => hw x) cap) (cappedModular_empty hcap) xs 1 OPT hOPT
    hOPT_card

/-- At budget `1`, the output of `alg` against a capped-modular objective is at most one element
of the ground set. -/
private theorem IsSubmodularCardMaxAlg.eval_cappedModular
    {alg : List α → ℕ → FreeM (ValueQuery α ℝ) (Finset α)} {c : ℝ}
    (halg : IsSubmodularCardMaxAlg alg c) (xs : List α) {w : α → ℝ} {cap : ℝ}
    (hw : ∀ x ∈ xs.toFinset, 0 ≤ w x) (hcap : 0 ≤ cap) :
    (alg xs 1).eval (ValueQuery.oracleOf (cappedModular xs.toFinset w cap)) ⊆ xs.toFinset ∧
      ((alg xs 1).eval (ValueQuery.oracleOf (cappedModular xs.toFinset w cap))).card ≤ 1 :=
  ⟨halg.subset_toFinset _ (isSubmodular_cappedModular hw cap) (monotone_cappedModular hw cap)
      (cappedModular_empty hcap) xs 1,
    halg.card_le _ (isSubmodular_cappedModular hw cap) (monotone_cappedModular hw cap)
      (cappedModular_empty hcap) xs 1⟩

/-- If every `e ∈ A` is isolated within `E` by a set that `p` queries, then `p` makes at least
`A.card` queries. -/
private theorem card_le_countQueries_of_isolated {γ : Type}
    (o : {ι : Type} → ValueQuery α ℝ ι → ι) (p : FreeM (ValueQuery α ℝ) γ) {A E : Finset α}
    (h : ∀ e ∈ A, ∃ S ∈ ValueQuery.queriedSets o p, S ∩ E = {e}) :
    A.card ≤ p.countQueries o :=
  calc
    A.card = (A.image fun e => ({e} : Finset α)).card :=
        (Finset.card_image_of_injective A fun _ _ h => Finset.singleton_injective h).symm
    _ ≤ ((ValueQuery.queriedSets o p).image fun S => S ∩ E).card :=
        Finset.card_le_card fun T hT => by
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hT
          obtain ⟨S, hS, hSE⟩ := h e he
          exact Finset.mem_image.mpr ⟨S, hS, hSE⟩
    _ ≤ (ValueQuery.queriedSets o p).card := Finset.card_image_le
    _ ≤ p.countQueries o := ValueQuery.card_queriedSets_le_countQueries o p

/-! ## Lower-bound theorems -/

/-- Any deterministic `c`-approximate algorithm with `1 / 2 < c` must issue at least
`xs.toFinset.card - 1` value queries at budget `k = 1` on `halfBaseAdv xs.toFinset`. -/
theorem IsSubmodularCardMaxAlg.card_toFinset_sub_one_le_countQueries
    {alg : List α → ℕ → FreeM (ValueQuery α ℝ) (Finset α)} {c : ℝ}
    (halg : IsSubmodularCardMaxAlg alg c) (hc : (1 : ℝ) / 2 < c) (xs : List α) :
    xs.toFinset.card - 1 ≤
      (alg xs 1).countQueries (ValueQuery.oracleOf (halfBaseAdv xs.toFinset)) := by
  set E := xs.toFinset
  set out := (alg xs 1).eval (ValueQuery.oracleOf (halfBaseAdv E))
  obtain ⟨hout_sub, hout_card⟩ : out ⊆ E ∧ out.card ≤ 1 :=
    halg.eval_cappedModular xs (w := fun _ => 1) (fun _ _ => by norm_num)
      (by norm_num : (0 : ℝ) ≤ 2)
  refine ((Nat.sub_le_sub_left hout_card _).trans (Finset.le_card_sdiff _ _)).trans
    (card_le_countQueries_of_isolated (E := E) _ _ fun e he_diff => ?_)
  obtain ⟨heE, he_out⟩ := Finset.mem_sdiff.mp he_diff
  by_contra hno
  push Not at hno
  -- Otherwise the run cannot tell `halfBaseAdv E` from the adversary favouring `e`.
  have happrox := halg.approx_reweight_of_not_isolated (f := halfBaseAdv E)
    (a := 2) (b := 1) (cap := 2) rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hno
    (Finset.singleton_subset_iff.mpr heE) (by simp)
  rw [cappedModular_singleton heE] at happrox
  have hout_le := cappedModular_ite_le (a := 2) (cap := 2) zero_le_one hout_sub he_out hout_card
  norm_num at happrox
  linarith

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
  set out := (alg xs 1).eval (ValueQuery.oracleOf (baseAdv E))
  obtain ⟨hout_sub, hout_card⟩ : out ⊆ E ∧ out.card ≤ 1 :=
    halg.eval_cappedModular xs (w := fun _ => 100) (fun _ _ => by norm_num)
      (by norm_num : (0 : ℝ) ≤ 159)
  refine card_le_countQueries_of_isolated (E := E) _ _ fun e heE => ?_
  by_contra hno
  push Not at hno
  by_cases he_out : e ∈ out
  · -- The run returns `{e}`, which the adversary penalizing `e` beats with another element.
    have hout_eq : out = {e} :=
      (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr he_out)
        (by simpa using hout_card)).symm
    have hne : E ≠ {e} := by
      intro hEq
      rw [hEq, Finset.card_singleton] at hcard
      omega
    obtain ⟨y, hyE, hye⟩ := ((Finset.nontrivial_iff_ne_singleton heE).2 hne).exists_ne e
    have happrox := halg.approx_reweight_of_not_isolated (f := baseAdv E)
      (a := 59) (b := 100) (cap := 159) rfl
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hno
      (Finset.singleton_subset_iff.mpr hyE) (by simp)
    rw [show (alg xs 1).eval (ValueQuery.oracleOf (baseAdv E)) = {e} from hout_eq,
      cappedModular_singleton hyE, cappedModular_singleton heE] at happrox
    simp only [hye, ↓reduceIte] at happrox
    norm_num at happrox
    linarith
  · -- The run misses `e`, which the adversary favouring `e` rewards.
    have happrox := halg.approx_reweight_of_not_isolated (f := baseAdv E)
      (a := 159) (b := 100) (cap := 159) rfl
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hno
      (Finset.singleton_subset_iff.mpr heE) (by simp)
    rw [cappedModular_singleton heE] at happrox
    have hout_le := cappedModular_ite_le (a := 159) (cap := 159) (by norm_num : (0 : ℝ) ≤ 100)
      hout_sub he_out hout_card
    norm_num at happrox
    linarith

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
