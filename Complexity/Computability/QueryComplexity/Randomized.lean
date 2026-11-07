/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Basic
public import Complexity.Probability.Minimax
public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Tactic.NormNum

/-!
# Randomized decision trees

A randomized decision tree tosses coins, uses them to pick a deterministic decision tree, and runs
it. We represent it by the distribution over decision trees that it draws from, a finitely
supported probability distribution `Convexity.StdSimplex ℝ (DecisionTree ι β)`
(`RandomizedDecisionTree`). Its depth is the largest depth of a tree it can draw: the number of
queries it makes in the worst case over the inputs and the coins (`RandomizedDecisionTree.depth`).
It computes `f` with error `ε` when on every input the tree it draws outputs a wrong value with
probability at most `ε` (`RandomizedDecisionTree.errorProb`, `RandomizedDecisionTree.Computes`).
The randomized decision tree complexity `R_ε(f)` is the least depth of a randomized decision tree
computing `f` with error `ε` (`QueryComplexity.randomizedComplexity`) [BuhrmanDeWolf2002]; the
bounded-error complexity `R(f)` of the literature is `R_{1/3}(f)`.

Deterministic trees are randomized trees that draw one tree, so `R_ε(f) ≤ D(f)` for `ε ≥ 0`
(`DecisionTree.randomizedComplexity_le_complexity`). With error `0` every tree that can be drawn
computes `f`, so `R_0(f) = D(f)` (`QueryComplexity.randomizedComplexity_zero`); zero-error
complexity in the literature usually counts the expected number of queries instead, which can be
smaller. A fair coin guesses a Boolean value correctly with probability `1/2`, so `R_ε(f) = 0` for
Boolean-valued `f` and `ε ≥ 1/2` (`QueryComplexity.randomizedComplexity_eq_zero_of_le`).

If a randomized tree computes `f` with error `ε`, then for every distribution `ν` on the inputs
some tree that it can draw errs with probability at most `ε` on inputs drawn from `ν`
(`RandomizedDecisionTree.Computes.exists_distributionalError_le`, from
`Convexity.StdSimplex.exists_mem_support_le_sum_mul` in `Complexity.Probability.Minimax`). This
averaging argument is the easy direction of Yao's principle [Yao1977]; the converse follows from
the minimax theorem (`QueryComplexity.exists_computes_of_forall_exists_distributionalError_le`).

Post-processing the output with a function `g` (`RandomizedDecisionTree.mapOutput`) makes no
further queries and errs against `g ∘ f` at most as often as the original tree errs against `f`
(`RandomizedDecisionTree.errorProb_mapOutput_le`); so lower bounds for computing `g ∘ f` are lower
bounds for computing `f`.

## Main definitions

* `Cslib.RandomizedDecisionTree`: randomized decision trees, as finitely supported distributions
  over decision trees, with `RandomizedDecisionTree.depth`, `RandomizedDecisionTree.errorProb` and
  `RandomizedDecisionTree.Computes`.
* `Cslib.RandomizedDecisionTree.mapOutput`: post-processing the output.
* `Cslib.DecisionTree.distributionalError`: the error of a decision tree on inputs drawn from a
  distribution.
* `Cslib.QueryComplexity.randomizedComplexity`: the randomized decision tree complexity `R_ε(f)`.

## Main results

* `Cslib.RandomizedDecisionTree.Computes.exists_distributionalError_le`: the averaging argument.
* `Cslib.RandomizedDecisionTree.depth_mapOutput_le`,
  `Cslib.RandomizedDecisionTree.errorProb_mapOutput_le`: post-processing adds no queries and no
  error.
* `Cslib.DecisionTree.randomizedComplexity_le_complexity`: `R_ε(f) ≤ D(f)` for `ε ≥ 0`.
* `Cslib.QueryComplexity.randomizedComplexity_zero`: `R_0(f) = D(f)`.
* `Cslib.QueryComplexity.randomizedComplexity_antitone`: `R_ε(f)` decreases as `ε` grows.
* `Cslib.QueryComplexity.randomizedComplexity_eq_zero_of_le`: `R_ε(f) = 0` for Boolean-valued `f`
  and `ε ≥ 1/2`.

## References

* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
-/

@[expose] public section

namespace Cslib

open Convexity

/-- A randomized decision tree over Boolean variables indexed by `ι`, with outputs in `β`: a
finitely supported probability distribution over decision trees. It draws a tree from this
distribution and runs it. -/
abbrev RandomizedDecisionTree (ι β : Type*) : Type _ :=
  StdSimplex ℝ (DecisionTree ι β)

namespace DecisionTree

variable {ι β : Type*}

open Classical in
/-- The error of a decision tree `t` on inputs drawn from `ν`: the probability that on an input `x`
drawn from `ν` it outputs a value other than `f x`. -/
noncomputable def distributionalError (t : DecisionTree ι β) (ν : StdSimplex ℝ (ι → Bool))
    (f : (ι → Bool) → β) : ℝ :=
  ν.weights.sum fun x w => w * if t.eval x = f x then 0 else 1

/-- `distributionalError` with any decidable equality on the outputs. -/
theorem distributionalError_eq_sum [DecidableEq β] (t : DecisionTree ι β)
    (ν : StdSimplex ℝ (ι → Bool)) (f : (ι → Bool) → β) :
    t.distributionalError ν f = ν.weights.sum fun x w => w * if t.eval x = f x then 0 else 1 := by
  unfold distributionalError
  congr!

variable {t : DecisionTree ι β} {ν : StdSimplex ℝ (ι → Bool)} {f : (ι → Bool) → β}

theorem distributionalError_nonneg : 0 ≤ t.distributionalError ν f := by
  classical
  refine Finset.sum_nonneg fun x _ => mul_nonneg (ν.weights_nonneg x) ?_
  split_ifs <;> norm_num

/-- A decision tree computing `f` has error `0` on every distribution. -/
theorem Computes.distributionalError_eq_zero (ht : t.Computes f) :
    t.distributionalError ν f = 0 := by
  classical
  exact Finset.sum_eq_zero fun x _ => by simp [ht x]

end DecisionTree

namespace RandomizedDecisionTree

variable {ι β : Type*}

/-- The depth of a randomized decision tree: the largest depth of a tree that it can draw, so the
number of queries it makes in the worst case over the inputs and the coins. -/
def depth (μ : RandomizedDecisionTree ι β) : ℕ :=
  μ.weights.support.sup DecisionTree.depth

open Classical in
/-- The probability that the tree drawn from `μ` outputs on `x` a value other than `f x`. -/
noncomputable def errorProb (μ : RandomizedDecisionTree ι β) (f : (ι → Bool) → β)
    (x : ι → Bool) : ℝ :=
  μ.weights.sum fun t w => w * if t.eval x = f x then 0 else 1

/-- A randomized decision tree `μ` computes `f` with error `ε` when on every input the tree drawn
from `μ` outputs a wrong value with probability at most `ε`. -/
def Computes (μ : RandomizedDecisionTree ι β) (ε : ℝ) (f : (ι → Bool) → β) : Prop :=
  ∀ x, μ.errorProb f x ≤ ε

/-- `errorProb` with any decidable equality on the outputs. -/
theorem errorProb_eq_sum [DecidableEq β] (μ : RandomizedDecisionTree ι β) (f : (ι → Bool) → β)
    (x : ι → Bool) :
    μ.errorProb f x = μ.weights.sum fun t w => w * if t.eval x = f x then 0 else 1 := by
  unfold errorProb
  congr!

variable {μ : RandomizedDecisionTree ι β} {f : (ι → Bool) → β} {t : DecisionTree ι β}
  {ε ε' : ℝ} {d : ℕ} {x : ι → Bool}

theorem depth_le_iff : μ.depth ≤ d ↔ ∀ t ∈ μ.weights.support, t.depth ≤ d :=
  Finset.sup_le_iff

theorem depth_le_depth (ht : t ∈ μ.weights.support) : t.depth ≤ μ.depth :=
  Finset.le_sup ht

@[simp] theorem depth_single (t : DecisionTree ι β) :
    depth (StdSimplex.single t : RandomizedDecisionTree ι β) = t.depth := by
  simp [depth]

private theorem ite_nonneg' {p : Prop} {_ : Decidable p} : (0 : ℝ) ≤ if p then 0 else 1 := by
  split_ifs <;> norm_num

private theorem ite_le_one' {p : Prop} {_ : Decidable p} : (if p then 0 else 1 : ℝ) ≤ 1 := by
  split_ifs <;> norm_num

theorem errorProb_nonneg : 0 ≤ μ.errorProb f x :=
  Finset.sum_nonneg fun t _ => mul_nonneg (μ.weights_nonneg t) ite_nonneg'

theorem errorProb_le_one : μ.errorProb f x ≤ 1 :=
  StdSimplex.sum_mul_le_of_forall_le fun _ _ => ite_le_one'

theorem errorProb_eq_zero_iff :
    μ.errorProb f x = 0 ↔ ∀ t ∈ μ.weights.support, t.eval x = f x := by
  classical
  rw [errorProb, Finsupp.sum, Finset.sum_eq_zero_iff_of_nonneg fun t _ =>
    mul_nonneg (μ.weights_nonneg t) ite_nonneg']
  refine forall₂_congr fun t ht => ?_
  rw [mul_eq_zero, or_iff_right (Finsupp.mem_support_iff.mp ht)]
  split_ifs with h <;> simp [h]

private theorem errorProb_single_of_eq (h : t.eval x = f x) :
    errorProb (StdSimplex.single t : RandomizedDecisionTree ι β) f x = 0 := by
  simp [errorProb, h]

private theorem errorProb_single_of_ne (h : t.eval x ≠ f x) :
    errorProb (StdSimplex.single t : RandomizedDecisionTree ι β) f x = 1 := by
  simp [errorProb, h]

theorem Computes.mono (h : μ.Computes ε f) (hε : ε ≤ ε') : μ.Computes ε' f :=
  fun x => (h x).trans hε

/-- A randomized decision tree can only compute with nonnegative error. -/
theorem Computes.nonneg (h : μ.Computes ε f) : 0 ≤ ε :=
  errorProb_nonneg.trans (h fun _ => false)

/-- A deterministic decision tree computing `f` computes it with any nonnegative error. -/
theorem computes_single (ht : t.Computes f) (hε : 0 ≤ ε) :
    Computes (StdSimplex.single t : RandomizedDecisionTree ι β) ε f :=
  fun x => (errorProb_single_of_eq (ht x)).trans_le hε

/-- A randomized decision tree computes `f` with error `0` exactly when every tree it can draw
computes `f`. -/
theorem computes_zero_iff : μ.Computes 0 f ↔ ∀ t ∈ μ.weights.support, t.Computes f :=
  ⟨fun h t ht x => errorProb_eq_zero_iff.mp ((h x).antisymm errorProb_nonneg) t ht,
    fun h x => (errorProb_eq_zero_iff.mpr fun t ht => h t ht x).le⟩

/-- **The averaging argument**, the easy direction of Yao's principle: if `μ` computes `f` with
error `ε`, then for every distribution `ν` on the inputs some tree that `μ` can draw errs with
probability at most `ε` on inputs drawn from `ν`. -/
theorem Computes.exists_distributionalError_le (h : μ.Computes ε f)
    (ν : StdSimplex ℝ (ι → Bool)) : ∃ t ∈ μ.weights.support, t.distributionalError ν f ≤ ε := by
  classical
  obtain ⟨t, ht, hle⟩ :=
    StdSimplex.exists_mem_support_le_sum_mul μ fun t => t.distributionalError ν f
  refine ⟨t, ht, hle.trans ?_⟩
  -- the average over `μ` of the error over `ν` is the average over `ν` of the error over `μ`
  have hswap : (μ.weights.sum fun t w => w * t.distributionalError ν f) =
      ν.weights.sum fun x w => w * μ.errorProb f x := by
    simp only [DecisionTree.distributionalError, errorProb, Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun t _ => mul_left_comm _ _ _
  rw [hswap]
  exact StdSimplex.sum_mul_le_of_forall_le fun x _ => h x

/-! ### Post-processing the output -/

/-- Post-process the output of a randomized decision tree with `g`: draw a tree from `μ` and
relabel its leaves with `g` (`DecisionTree.map`). -/
noncomputable def mapOutput {γ : Type*} (g : β → γ) (μ : RandomizedDecisionTree ι β) :
    RandomizedDecisionTree ι γ :=
  StdSimplex.map (DecisionTree.map g) μ

/-- Post-processing makes no further queries. -/
theorem depth_mapOutput_le {γ : Type*} (g : β → γ) (μ : RandomizedDecisionTree ι β) :
    (mapOutput g μ).depth ≤ μ.depth := by
  classical
  refine depth_le_iff.mpr fun t ht => ?_
  obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp
    (Finsupp.mapDomain_support (by simpa [mapOutput, StdSimplex.weights_map] using ht))
  rw [DecisionTree.depth_map]
  exact depth_le_depth ht'

/-- **Post-processing does not increase the error**: the tree drawn from `mapOutput g μ` errs
against `g ∘ f` at most as often as the tree drawn from `μ` errs against `f`. -/
theorem errorProb_mapOutput_le {γ : Type*} (g : β → γ) (μ : RandomizedDecisionTree ι β)
    (f : (ι → Bool) → β) (x : ι → Bool) :
    (mapOutput g μ).errorProb (g ∘ f) x ≤ μ.errorProb f x := by
  classical
  rw [errorProb_eq_sum, errorProb_eq_sum, mapOutput, StdSimplex.weights_map,
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _]
  refine Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left ?_ (μ.weights_nonneg t)
  by_cases h : t.eval x = f x
  · simp [h]
  · split_ifs <;> norm_num

end RandomizedDecisionTree

namespace QueryComplexity

open RandomizedDecisionTree

variable {ι β : Type*} {f : (ι → Bool) → β} {μ : RandomizedDecisionTree ι β} {ε ε' : ℝ} {d : ℕ}

/-- The randomized decision tree complexity `R_ε(f)`: the least depth of a randomized decision tree
computing `f` with error `ε`. It is `0` when no randomized decision tree computes `f` with error
`ε`, which over finitely many variables happens exactly for `ε < 0`. -/
noncomputable def randomizedComplexity (ε : ℝ) (f : (ι → Bool) → β) : ℕ :=
  sInf {d | ∃ μ : RandomizedDecisionTree ι β, μ.Computes ε f ∧ μ.depth ≤ d}

theorem randomizedComplexity_le_depth (h : μ.Computes ε f) : randomizedComplexity ε f ≤ μ.depth :=
  Nat.sInf_le ⟨μ, h, le_rfl⟩

/-- `R_ε(f) = 0` for `ε < 0`, where no randomized decision tree qualifies. -/
theorem randomizedComplexity_of_neg (hε : ε < 0) : randomizedComplexity ε f = 0 :=
  Nat.sInf_eq_zero.mpr <| Or.inr <| Set.eq_empty_of_forall_notMem fun _ ⟨_, h, _⟩ =>
    (not_le.mpr hε) h.nonneg

section Finite

variable [Finite ι]

/-- For `ε ≥ 0` the randomized complexity is attained: some randomized decision tree of depth
`R_ε(f)` computes `f` with error `ε`. -/
theorem exists_computes_depth_eq_randomizedComplexity (hε : 0 ≤ ε) (f : (ι → Bool) → β) :
    ∃ μ : RandomizedDecisionTree ι β, μ.Computes ε f ∧ μ.depth = randomizedComplexity ε f := by
  obtain ⟨t, ht, -⟩ := DecisionTree.exists_computes_depth_eq_complexity f
  obtain ⟨μ, hμ, hd⟩ := Nat.sInf_mem (s := {d | ∃ μ : RandomizedDecisionTree ι β,
    μ.Computes ε f ∧ μ.depth ≤ d}) ⟨_, _, computes_single ht hε, le_rfl⟩
  exact ⟨μ, hμ, le_antisymm hd (randomizedComplexity_le_depth hμ)⟩

theorem randomizedComplexity_le_iff (hε : 0 ≤ ε) :
    randomizedComplexity ε f ≤ d ↔ ∃ μ : RandomizedDecisionTree ι β, μ.Computes ε f ∧ μ.depth ≤ d :=
  ⟨fun h => (exists_computes_depth_eq_randomizedComplexity hε f).imp fun _ ⟨hμ, hd⟩ =>
    ⟨hμ, hd.trans_le h⟩, fun ⟨_, hμ, hd⟩ => (randomizedComplexity_le_depth hμ).trans hd⟩

/-- Lower bounds on `R_ε(f)` are lower bounds on the depth of every randomized decision tree
computing `f` with error `ε`. -/
theorem le_randomizedComplexity_iff (hε : 0 ≤ ε) :
    d ≤ randomizedComplexity ε f ↔ ∀ μ : RandomizedDecisionTree ι β, μ.Computes ε f → d ≤ μ.depth :=
  ⟨fun h _ hμ => h.trans (randomizedComplexity_le_depth hμ), fun h =>
    let ⟨_, hμ, hd⟩ := exists_computes_depth_eq_randomizedComplexity hε f
    (h _ hμ).trans_eq hd⟩

/-- `R_ε(f)` decreases as `ε` grows. -/
theorem randomizedComplexity_antitone (hε : 0 ≤ ε) (hεε' : ε ≤ ε') :
    randomizedComplexity ε' f ≤ randomizedComplexity ε f :=
  let ⟨_, hμ, hd⟩ := exists_computes_depth_eq_randomizedComplexity hε f
  (randomizedComplexity_le_depth (hμ.mono hεε')).trans_eq hd

/-- With error `0` randomness does not help: `R_0(f) = D(f)`. The cost here is the worst case over
the coins, unlike the expected number of queries of zero-error (Las Vegas) complexity. -/
theorem randomizedComplexity_zero (f : (ι → Bool) → β) :
    randomizedComplexity 0 f = DecisionTree.complexity f := by
  obtain ⟨t, ht, hd⟩ := DecisionTree.exists_computes_depth_eq_complexity f
  obtain ⟨μ, hμ, hμd⟩ := exists_computes_depth_eq_randomizedComplexity le_rfl f
  obtain ⟨s, hs⟩ := μ.support_weights_nonempty
  refine le_antisymm ((randomizedComplexity_le_depth (computes_single ht le_rfl)).trans_eq
    (by rw [depth_single, hd])) ?_
  rw [← hμd]
  exact (DecisionTree.complexity_le_depth (computes_zero_iff.mp hμ s hs)).trans (depth_le_depth hs)

end Finite

/-- From `ε = 1/2` on, a fair coin computes every Boolean-valued function: `R_ε(f) = 0`. -/
theorem randomizedComplexity_eq_zero_of_le (hε : 1 / 2 ≤ ε) (f : (ι → Bool) → Bool) :
    randomizedComplexity ε f = 0 := by
  classical
  set μ : RandomizedDecisionTree ι Bool := StdSimplex.duple (.leaf false) (.leaf true)
    (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hsupp : μ.weights.support ⊆ {DecisionTree.leaf false, DecisionTree.leaf true} := by
    simp only [μ, StdSimplex.weights_duple]
    exact Finsupp.support_add.trans (Finset.union_subset_union Finsupp.support_single_subset
      Finsupp.support_single_subset)
  have hdepth : μ.depth = 0 := Nat.le_zero.mp <| depth_le_iff.mpr fun t ht => by
    rcases Finset.mem_insert.mp (hsupp ht) with rfl | ht
    · rfl
    · rw [Finset.mem_singleton.mp ht]
      rfl
  refine Nat.le_zero.mp ((randomizedComplexity_le_depth (μ := μ) fun x => ?_).trans_eq hdepth)
  refine le_trans (le_of_eq ?_) hε
  simp only [errorProb, μ, StdSimplex.weights_duple]
  rw [Finsupp.sum_add_index' (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _,
    Finsupp.sum_single_index (zero_mul _), Finsupp.sum_single_index (zero_mul _)]
  cases f x <;> simp

end QueryComplexity

namespace DecisionTree

/-- Randomness does not hurt: `R_ε(f) ≤ D(f)` for `ε ≥ 0`. -/
theorem randomizedComplexity_le_complexity {ι β : Type*} [Finite ι] {ε : ℝ} (hε : 0 ≤ ε)
    (f : (ι → Bool) → β) : QueryComplexity.randomizedComplexity ε f ≤ complexity f :=
  QueryComplexity.randomizedComplexity_zero f ▸
    QueryComplexity.randomizedComplexity_antitone le_rfl hε

/-- `R_ε(f)` is at most the number of variables for `ε ≥ 0`. -/
theorem randomizedComplexity_le_card {ι β : Type*} [Fintype ι] {ε : ℝ} (hε : 0 ≤ ε)
    (f : (ι → Bool) → β) : QueryComplexity.randomizedComplexity ε f ≤ Fintype.card ι :=
  (randomizedComplexity_le_complexity hε f).trans (complexity_le_card f)

end DecisionTree

end Cslib
