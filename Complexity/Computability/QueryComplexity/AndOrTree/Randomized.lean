/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Composition
public import Complexity.Computability.QueryComplexity.AndOrTree
public import Complexity.Computability.QueryComplexity.Randomized.ZeroError
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Evaluating the AND–OR tree with zero error in `n ^ (log₄ 3)` expected queries

The *directional* algorithm evaluates a NAND node by evaluating a uniformly random child first,
and stops if that child is `false`, the node then being `true`; otherwise it evaluates the other
child and outputs its negation. Fixing all coin tosses, one per internal node
(`QueryComplexity.NandTree.DirectionalCoins`), gives a deterministic decision tree
(`QueryComplexity.NandTree.directionalTree`) computing the NAND tree, and the algorithm is the
uniform mixture of these trees (`QueryComplexity.NandTree.directional`). It is always correct
(`QueryComplexity.NandTree.directional_computes`).

Its expected cost on an input satisfies an exact recurrence over the two subtrees
(`QueryComplexity.NandTree.expectedCost_directional_succ`): with `E₀`, `E₁` the expected costs on
the subtrees and `v₀`, `v₁` their values, it is `(E₀ + E₁ + [v₀] E₁ + [v₁] E₀) / 2`. By the joint
induction on `0`- and `1`-valued subtrees, the expected cost is at most `3 ^ k` at depth `2k`, and
at depth `2k + 1` at most `(3 / 2) 3 ^ k` on value `true` and `2 · 3 ^ k` on value `false`
(`QueryComplexity.NandTree.expectedCost_directional_le`)
[Motwani and Raghavan, Theorem 2.1][MotwaniRaghavan95].

The same recurrence gives the sharp rate of the directional algorithm, due to Snir
[Snir][Snir1985]. Let `α = (1 + √33) / 4 ≈ 1.6861` be the positive root of `2 α² = α + 4`
(`QueryComplexity.NandTree.directionalRate`). By a single induction, the expected cost at depth
`d` is at most `α ^ d` on value `true` and `(α - 1 / 2) α ^ d` on value `false`
(`QueryComplexity.NandTree.expectedCost_directional_le_cond_rate`). So the NAND tree on `n = 2 ^ d`
leaves has `R₀ ≤ (α - 1 / 2) n ^ (log₂ α)`, with `log₂ α ≈ 0.7537`
(`QueryComplexity.zeroErrorComplexity_nandTree_le_rate`).

The OR–AND tree of depth `2k` is the NAND tree, and the AND–OR tree `T_{2,k}` of Motwani and
Raghavan, with AND at the root, is its dual, evaluated by the dual trees
(`DecisionTree.dual`) with the same costs on complemented inputs. So on `T_{2,k}` with `n = 4 ^ k`
leaves the zero-error randomized complexity is at most `3 ^ k = n ^ (log₄ 3) ≈ n ^ 0.793`
(`QueryComplexity.zeroErrorComplexity_andOrTree_le`,
`QueryComplexity.zeroErrorComplexity_andOrTree_le_rpow`), below the deterministic complexity `n`
(`QueryComplexity.zeroErrorComplexity_andOrTree_lt_complexity`). The sharp rate gives
`R₀(T_{2,k}) ≤ (α - 1 / 2) n ^ (log₂ α)`
(`QueryComplexity.zeroErrorComplexity_andOrTree_le_rpow_rate`).

Saks and Wigderson [Saks and Wigderson][SaksWigderson1986] proved the matching lower bound
`R₀ = Ω(n ^ (log₂ α))` for the NAND tree, so the directional algorithm is optimal up to a
constant factor. That lower bound is not formalized here.

## Main definitions

* `Cslib.QueryComplexity.NandTree.directionalTree`: the directional algorithm for fixed coins.
* `Cslib.QueryComplexity.NandTree.directional`: the randomized directional algorithm.

## Main results

* `Cslib.QueryComplexity.NandTree.expectedCost_directional_succ`: the expected-cost recurrence.
* `Cslib.QueryComplexity.NandTree.expectedCost_directional_le`: the `3 ^ k` bound.
* `Cslib.QueryComplexity.NandTree.expectedCost_directional_le_cond_rate`: the sharp `α ^ d` bound.
* `Cslib.QueryComplexity.zeroErrorComplexity_nandTree_le_rate`: `R₀ ≤ (α - 1 / 2) α ^ d` for the
  NAND tree of depth `d`.
* `Cslib.QueryComplexity.exists_computes_zero_expectedCost_andOrTree_le`: an always-correct
  randomized decision tree for `T_{2,k}` with at most `3 ^ k` expected queries on every input.
* `Cslib.QueryComplexity.zeroErrorComplexity_andOrTree_lt_complexity`: `R₀(T_{2,k}) < D(T_{2,k})`
  for `k ≥ 1`.

## References

* [R. Motwani, P. Raghavan, *Randomized Algorithms*][MotwaniRaghavan95]
* [M. Snir, *Lower bounds on probabilistic linear decision trees*][Snir1985]
* [M. Saks, A. Wigderson, *Probabilistic Boolean decision trees and the complexity of evaluating
  game trees*][SaksWigderson1986]
-/

public section

namespace Cslib.QueryComplexity

open Finset RandomizedDecisionTree
open scoped BigOperators


namespace NandTree

/-- The coin tosses of the directional algorithm on the NAND tree of depth `d`: at depth `d + 1`,
which child to evaluate first, and the coin tosses for the two subtrees. -/
@[expose] def DirectionalCoins : ℕ → Type
  | 0 => Unit
  | d + 1 => Bool × DirectionalCoins d × DirectionalCoins d

instance instFintypeDirectionalCoins : (d : ℕ) → Fintype (DirectionalCoins d)
  | 0 => inferInstanceAs (Fintype Unit)
  | d + 1 =>
    letI := instFintypeDirectionalCoins d
    inferInstanceAs (Fintype (Bool × DirectionalCoins d × DirectionalCoins d))

instance instInhabitedDirectionalCoins : (d : ℕ) → Inhabited (DirectionalCoins d)
  | 0 => inferInstanceAs (Inhabited Unit)
  | d + 1 =>
    letI := instInhabitedDirectionalCoins d
    inferInstanceAs (Inhabited (Bool × DirectionalCoins d × DirectionalCoins d))

/-- The coins at depth `d + 1`: which child goes first, and the coins of the two subtrees. -/
@[expose] def coinsEquiv (d : ℕ) :
    DirectionalCoins (d + 1) ≃ Bool × DirectionalCoins d × DirectionalCoins d :=
  Equiv.refl _

/-- Run `l`; if it outputs `false`, output `true`, and otherwise run `r` and output its negation.
This computes the NAND of `l` and `r`, short-circuiting on a `false` first argument. -/
def nandThen {ι : Type*} (l r : DecisionTree ι Bool) : DecisionTree ι Bool :=
  l.bind fun b => cond b (r.bind fun c => .leaf !c) (.leaf true)

@[simp] theorem eval_nandThen {ι : Type*} (l r : DecisionTree ι Bool) (x : ι → Bool) :
    (nandThen l r).eval x = !(l.eval x && r.eval x) := by
  simp only [nandThen, DecisionTree.eval_bind]
  cases l.eval x <;> simp

theorem cost_nandThen {ι : Type*} (l r : DecisionTree ι Bool) (x : ι → Bool) :
    (nandThen l r).cost x = l.cost x + cond (l.eval x) (r.cost x) 0 := by
  simp only [nandThen, DecisionTree.cost, DecisionTree.weightedCost_bind]
  cases l.eval x <;> simp [DecisionTree.weightedCost_bind]

/-- The directional algorithm on the NAND tree of depth `d` for fixed coin tosses: at a node,
evaluate the left child first if the node's coin is `false`, and the right child first
otherwise. -/
@[expose] def directionalTree : (d : ℕ) → DirectionalCoins d → DecisionTree (Fin d → Bool) Bool
  | 0, _ => .node Fin.elim0 (.leaf false) (.leaf true)
  | d + 1, ω =>
    let t₀ := (directionalTree d (coinsEquiv d ω).2.1).mapQueries (Fin.cons false)
    let t₁ := (directionalTree d (coinsEquiv d ω).2.2).mapQueries (Fin.cons true)
    cond (coinsEquiv d ω).1 (nandThen t₁ t₀) (nandThen t₀ t₁)

theorem directionalTree_succ (d : ℕ) (b : Bool) (ω₀ ω₁ : DirectionalCoins d) :
    directionalTree (d + 1) ((coinsEquiv d).symm (b, ω₀, ω₁)) =
      cond b
        (nandThen ((directionalTree d ω₁).mapQueries (Fin.cons true))
          ((directionalTree d ω₀).mapQueries (Fin.cons false)))
        (nandThen ((directionalTree d ω₀).mapQueries (Fin.cons false))
          ((directionalTree d ω₁).mapQueries (Fin.cons true))) :=
  rfl

/-- For every choice of coins the directional algorithm computes the NAND tree. -/
theorem directionalTree_computes (d : ℕ) (ω : DirectionalCoins d) :
    (directionalTree d ω).Computes (nandTree d) := by
  induction d with
  | zero =>
    intro x
    simp only [directionalTree, DecisionTree.eval_node, nandTree_zero]
    cases x Fin.elim0 <;> rfl
  | succ d ih =>
    obtain ⟨⟨b, ω₀, ω₁⟩, rfl⟩ := (coinsEquiv d).symm.surjective ω
    intro x
    have h₀ := ih ω₀ fun p => x (Fin.cons false p)
    have h₁ := ih ω₁ fun p => x (Fin.cons true p)
    rw [directionalTree_succ, nandTree_succ, ← h₀, ← h₁]
    cases b
    · simp only [Bool.cond_false, eval_nandThen, DecisionTree.eval_mapQueries, Function.comp_def]
    · simp only [Bool.cond_true, eval_nandThen, DecisionTree.eval_mapQueries, Function.comp_def,
        Bool.and_comm]

@[simp] theorem eval_directionalTree (d : ℕ) (ω : DirectionalCoins d)
    (x : (Fin d → Bool) → Bool) : (directionalTree d ω).eval x = nandTree d x :=
  directionalTree_computes d ω x

/-- The cost of the directional algorithm at depth `d + 1` for fixed coins: the cost on the subtree
evaluated first, plus the cost on the other subtree if the first one is `true`. -/
theorem cost_directionalTree_succ (d : ℕ) (b : Bool) (ω₀ ω₁ : DirectionalCoins d)
    (x : (Fin (d + 1) → Bool) → Bool) :
    ((directionalTree (d + 1) ((coinsEquiv d).symm (b, ω₀, ω₁))).cost x : ℝ) =
      cond b
        ((directionalTree d ω₁).cost (fun p => x (Fin.cons true p)) +
          cond (nandTree d fun p => x (Fin.cons true p))
            ((directionalTree d ω₀).cost (fun p => x (Fin.cons false p)) : ℝ) 0)
        ((directionalTree d ω₀).cost (fun p => x (Fin.cons false p)) +
          cond (nandTree d fun p => x (Fin.cons false p))
            ((directionalTree d ω₁).cost (fun p => x (Fin.cons true p)) : ℝ) 0) := by
  rw [directionalTree_succ]
  cases b <;>
  · simp only [Bool.cond_false, Bool.cond_true, cost_nandThen, DecisionTree.cost_mapQueries,
      DecisionTree.eval_mapQueries, eval_directionalTree, Function.comp_def]
    cases nandTree d (fun p => x (Fin.cons false p)) <;>
      cases nandTree d (fun p => x (Fin.cons true p)) <;> simp

/-- The **directional algorithm**: evaluate a uniformly random child first and short-circuit. -/
noncomputable def directional (d : ℕ) : RandomizedDecisionTree (Fin d → Bool) Bool :=
  uniformMixture (directionalTree d)

/-- The directional algorithm is always correct. -/
theorem directional_computes (d : ℕ) : (directional d).Computes 0 (nandTree d) :=
  computes_uniformMixture (directionalTree_computes d)

/-- At depth `0` the directional algorithm reads the single leaf. -/
theorem expectedCost_directional_zero (x : (Fin 0 → Bool) → Bool) :
    (directional 0).expectedCost x = 1 := by
  rw [directional, expectedCost_uniformMixture]
  simp [directionalTree]

private theorem expect_bool (g : Bool → ℝ) : 𝔼 b, g b = (g false + g true) / 2 := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.sum_bool, Fintype.card_bool, add_comm]
  norm_num

private theorem expect_coins_succ (d : ℕ) (g : DirectionalCoins (d + 1) → ℝ) :
    𝔼 ω, g ω = 𝔼 b, 𝔼 ω₀, 𝔼 ω₁, g ((coinsEquiv d).symm (b, ω₀, ω₁)) := by
  rw [Fintype.expect_equiv (coinsEquiv d) g (fun bω => g ((coinsEquiv d).symm bω))
      fun ω => by rw [Equiv.symm_apply_apply], ← univ_product_univ, expect_product,
    ← univ_product_univ]
  simp only [expect_product]

/-- **The expected-cost recurrence** of the directional algorithm: with `E₀`, `E₁` the expected
costs on the left and right subtrees and `v₀`, `v₁` their values, the expected cost at depth
`d + 1` is `(E₀ + E₁ + [v₀] E₁ + [v₁] E₀) / 2`. -/
theorem expectedCost_directional_succ (d : ℕ) (x : (Fin (d + 1) → Bool) → Bool) :
    (directional (d + 1)).expectedCost x =
      ((directional d).expectedCost (fun p => x (Fin.cons false p)) +
        (directional d).expectedCost (fun p => x (Fin.cons true p)) +
        cond (nandTree d fun p => x (Fin.cons false p))
          ((directional d).expectedCost fun p => x (Fin.cons true p)) 0 +
        cond (nandTree d fun p => x (Fin.cons true p))
          ((directional d).expectedCost fun p => x (Fin.cons false p)) 0) / 2 := by
  simp only [directional, expectedCost_uniformMixture]
  rw [expect_coins_succ, expect_bool]
  simp only [cost_directionalTree_succ, Bool.cond_false, Bool.cond_true]
  cases nandTree d (fun p => x (Fin.cons false p)) <;>
    cases nandTree d (fun p => x (Fin.cons true p)) <;>
    simp only [Bool.cond_false, Bool.cond_true, add_zero, expect_add_distrib,
      Fintype.expect_const] <;>
    ring

/-- **The `3 ^ k` bound** [Motwani and Raghavan, Theorem 2.1][MotwaniRaghavan95], by joint
induction over the values of the subtrees: the directional algorithm makes at most `3 ^ k` queries
in expectation at depth `2k`, and at depth `2k + 1` at most `(3 / 2) 3 ^ k` if the value is `true`
and `2 · 3 ^ k` if it is `false`. -/
theorem expectedCost_directional_le (k : ℕ) :
    (∀ x, (directional (2 * k)).expectedCost x ≤ 3 ^ k) ∧
      ∀ x, (directional (2 * k + 1)).expectedCost x ≤
        cond (nandTree (2 * k + 1) x) (3 / 2 * 3 ^ k) (2 * 3 ^ k) := by
  induction k with
  | zero =>
    have h0 (y : (Fin (2 * 0) → Bool) → Bool) : (directional (2 * 0)).expectedCost y = 1 :=
      expectedCost_directional_zero y
    refine ⟨fun x => by rw [h0, pow_zero], fun x => ?_⟩
    rw [expectedCost_directional_succ, nandTree_succ, h0, h0]
    cases nandTree (2 * 0) (fun p => x (Fin.cons false p)) <;>
      cases nandTree (2 * 0) (fun p => x (Fin.cons true p)) <;> norm_num
  | succ k ih =>
    obtain ⟨-, hodd⟩ := ih
    have heven (x : (Fin (2 * (k + 1)) → Bool) → Bool) :
        (directional (2 * (k + 1))).expectedCost x ≤ 3 ^ (k + 1) := by
      change (directional (2 * k + 1 + 1)).expectedCost x ≤ 3 ^ (k + 1)
      rw [expectedCost_directional_succ, pow_succ]
      have h₀ := hodd fun p => x (Fin.cons false p)
      have h₁ := hodd fun p => x (Fin.cons true p)
      have hM : (0 : ℝ) ≤ 3 ^ k := by positivity
      revert h₀ h₁
      cases nandTree (2 * k + 1) (fun p => x (Fin.cons false p)) <;>
        cases nandTree (2 * k + 1) (fun p => x (Fin.cons true p)) <;>
        simp only [Bool.cond_false, Bool.cond_true] <;> intro h₀ h₁ <;> linarith
    refine ⟨heven, fun x => ?_⟩
    rw [expectedCost_directional_succ, nandTree_succ (2 * (k + 1)) x, pow_succ]
    have h₀ := heven fun p => x (Fin.cons false p)
    have h₁ := heven fun p => x (Fin.cons true p)
    rw [pow_succ] at h₀ h₁
    have hM : (0 : ℝ) ≤ 3 ^ k := by positivity
    cases nandTree (2 * (k + 1)) (fun p => x (Fin.cons false p)) <;>
      cases nandTree (2 * (k + 1)) (fun p => x (Fin.cons true p)) <;>
      simp only [Bool.cond_false, Bool.cond_true, Bool.and_false, Bool.and_true, Bool.not_false,
        Bool.not_true, add_zero] <;> linarith

/-! ### The sharp rate -/

/-- The growth rate `α = (1 + √33) / 4 ≈ 1.6861` per level of the directional algorithm on the
NAND tree: the positive root of `2 α² = α + 4`. -/
noncomputable def directionalRate : ℝ := (1 + √33) / 4

private theorem five_lt_sqrt_33 : 5 < √(33 : ℝ) :=
  (Real.lt_sqrt (by norm_num)).2 (by norm_num)

private theorem sqrt_33_lt_six : √(33 : ℝ) < 6 :=
  (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

/-- `2 α² = α + 4`. -/
theorem two_mul_directionalRate_sq : 2 * directionalRate ^ 2 = directionalRate + 4 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 33 by norm_num)
  rw [directionalRate]
  linear_combination h / 8

theorem three_halves_lt_directionalRate : 3 / 2 < directionalRate := by
  rw [directionalRate]
  linarith [five_lt_sqrt_33]

theorem directionalRate_lt_seven_fourths : directionalRate < 7 / 4 := by
  rw [directionalRate]
  linarith [sqrt_33_lt_six]

/-- `α ^ 2 < 3`, so the sharp rate improves on the `3 ^ k` bound at even depth `2k`. -/
theorem directionalRate_sq_lt_three : directionalRate ^ 2 < 3 := by
  linarith [two_mul_directionalRate_sq, directionalRate_lt_seven_fourths]

/-- **The sharp bound for the directional algorithm**, after Snir [Snir][Snir1985]: with
`α = directionalRate`, the expected cost at depth `d` is at most `α ^ d` on value `true` and
`(α - 1 / 2) α ^ d` on value `false`. With `A = α ^ d`, the induction step needs
`α A ≥ (α - 1 / 2) A` when both subtrees are `false`, `α A = (α - 1 / 2) A + A / 2` when one
subtree is `false`, and `(α - 1 / 2) α A = 2 A` when both are `true` (`2 α² = α + 4`). -/
theorem expectedCost_directional_le_cond_rate (d : ℕ) (x : (Fin d → Bool) → Bool) :
    (directional d).expectedCost x ≤
      cond (nandTree d x) (directionalRate ^ d)
        ((directionalRate - 1 / 2) * directionalRate ^ d) := by
  have hα := three_halves_lt_directionalRate
  have hα2 := two_mul_directionalRate_sq
  induction d with
  | zero =>
    rw [expectedCost_directional_zero, nandTree_zero, pow_zero]
    cases x Fin.elim0
    · simp only [Bool.cond_false, mul_one]
      linarith
    · simp only [Bool.cond_true, le_refl]
  | succ d ih =>
    rw [expectedCost_directional_succ, nandTree_succ, pow_succ]
    have h₀ := ih fun p => x (Fin.cons false p)
    have h₁ := ih fun p => x (Fin.cons true p)
    have hA : (0 : ℝ) ≤ directionalRate ^ d := pow_nonneg (by linarith) d
    have hTT : (directionalRate - 1 / 2) * (directionalRate ^ d * directionalRate) =
        2 * directionalRate ^ d := by
      linear_combination (directionalRate ^ d / 2) * hα2
    have hFF : (directionalRate - 1 / 2) * directionalRate ^ d ≤
        directionalRate ^ d * directionalRate := by
      nlinarith
    revert h₀ h₁
    cases nandTree d (fun p => x (Fin.cons false p)) <;>
      cases nandTree d (fun p => x (Fin.cons true p)) <;>
      simp only [Bool.cond_false, Bool.cond_true, Bool.false_and, Bool.and_false, Bool.true_and,
        Bool.not_false, Bool.not_true, add_zero] <;> intro h₀ h₁ <;> nlinarith

/-- The sharp bound on every input: at most `(α - 1 / 2) α ^ d` expected queries at depth `d`. -/
theorem expectedCost_directional_le_rate (d : ℕ) (x : (Fin d → Bool) → Bool) :
    (directional d).expectedCost x ≤ (directionalRate - 1 / 2) * directionalRate ^ d := by
  have h := expectedCost_directional_le_cond_rate d x
  have hα := three_halves_lt_directionalRate
  have hA : (0 : ℝ) ≤ directionalRate ^ d := pow_nonneg (by linarith) d
  cases hv : nandTree d x <;> rw [hv] at h
  · exact h
  · rw [Bool.cond_true] at h
    nlinarith

end NandTree

open NandTree

/-- The OR–AND tree of depth `2k` has a zero-error randomized decision tree making at most `3 ^ k`
queries in expectation on every input: the directional algorithm. -/
theorem exists_computes_zero_expectedCost_orAndTree_le (k : ℕ) :
    ∃ μ : RandomizedDecisionTree (Fin (2 * k) → Bool) Bool,
      μ.Computes 0 (orAndTree k) ∧ ∀ x, μ.expectedCost x ≤ 3 ^ k :=
  ⟨directional (2 * k), orAndTree_eq_nandTree k ▸ directional_computes (2 * k),
    (expectedCost_directional_le k).1⟩

/-- The directional algorithm run on the dual trees (`DecisionTree.dual`), which evaluates AND at
the root, computes `T_{2,k}` without error, with the expected cost of the directional algorithm on
the complemented input. -/
private theorem exists_computes_zero_andOrTree_of_directional {k : ℕ} {c : ℝ}
    (hc : ∀ x, (directional (2 * k)).expectedCost x ≤ c) :
    ∃ μ : RandomizedDecisionTree (Fin (2 * k) → Bool) Bool,
      μ.Computes 0 (andOrTree k) ∧ ∀ x, μ.expectedCost x ≤ c := by
  refine ⟨uniformMixture fun ω => (directionalTree (2 * k) ω).dual,
    computes_uniformMixture fun ω x => ?_, fun x => ?_⟩
  · rw [DecisionTree.eval_dual, eval_directionalTree, andOrTree_eq_not_orAndTree,
      orAndTree_eq_nandTree]
  · have h := hc fun p => !x p
    rw [directional, expectedCost_uniformMixture] at h
    rw [expectedCost_uniformMixture]
    simpa only [DecisionTree.cost_dual] using h

/-- **The AND–OR tree has a zero-error randomized decision tree with `3 ^ k` expected queries**
[Motwani and Raghavan, Theorem 2.1][MotwaniRaghavan95]: the directional algorithm, run on the dual
trees (`DecisionTree.dual`) to evaluate AND at the root, computes `T_{2,k}` without error and makes
at most `3 ^ k` queries in expectation on every input. -/
theorem exists_computes_zero_expectedCost_andOrTree_le (k : ℕ) :
    ∃ μ : RandomizedDecisionTree (Fin (2 * k) → Bool) Bool,
      μ.Computes 0 (andOrTree k) ∧ ∀ x, μ.expectedCost x ≤ 3 ^ k :=
  exists_computes_zero_andOrTree_of_directional (expectedCost_directional_le k).1

/-- `R₀(T_{2,k}) ≤ 3 ^ k`. -/
theorem zeroErrorComplexity_andOrTree_le (k : ℕ) : zeroErrorComplexity (andOrTree k) ≤ 3 ^ k :=
  let ⟨_, hμ, hc⟩ := exists_computes_zero_expectedCost_andOrTree_le k
  zeroErrorComplexity_le hμ hc

/-- `R₀(T_{2,k}) ≤ n ^ (log₄ 3) ≈ n ^ 0.793` for the AND–OR tree `T_{2,k}` on `n = 4 ^ k`
leaves. -/
theorem zeroErrorComplexity_andOrTree_le_rpow (k : ℕ) :
    zeroErrorComplexity (andOrTree k) ≤ ((4 : ℝ) ^ k) ^ Real.logb 4 3 := by
  have h : ((4 : ℝ) ^ k) ^ Real.logb 4 3 = 3 ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
      Real.rpow_natCast]
  rw [h]
  exact zeroErrorComplexity_andOrTree_le k

/-- **Randomness helps for the AND–OR tree**: `R₀(T_{2,k}) < D(T_{2,k})` for `k ≥ 1`. -/
theorem zeroErrorComplexity_andOrTree_lt_complexity {k : ℕ} (hk : k ≠ 0) :
    zeroErrorComplexity (andOrTree k) < DecisionTree.complexity (andOrTree k) := by
  rw [complexity_andOrTree, Nat.cast_pow]
  exact (zeroErrorComplexity_andOrTree_le k).trans_lt
    (pow_lt_pow_left₀ (by norm_num) (by norm_num) hk)

/-- `R₀ ≤ 3 ^ k` for the OR–AND tree of depth `2k`. -/
theorem zeroErrorComplexity_orAndTree_le (k : ℕ) : zeroErrorComplexity (orAndTree k) ≤ 3 ^ k :=
  let ⟨_, hμ, hc⟩ := exists_computes_zero_expectedCost_orAndTree_le k
  zeroErrorComplexity_le hμ hc

/-- **The sharp rate for the NAND tree** [Snir][Snir1985]: `R₀ ≤ (α - 1 / 2) α ^ d` on the NAND tree
of depth `d`, that is `(α - 1 / 2) n ^ (log₂ α) ≈ n ^ 0.7537` on `n = 2 ^ d` leaves. -/
theorem zeroErrorComplexity_nandTree_le_rate (d : ℕ) :
    zeroErrorComplexity (nandTree d) ≤ (directionalRate - 1 / 2) * directionalRate ^ d :=
  zeroErrorComplexity_le (directional_computes d) (expectedCost_directional_le_rate d)

/-- The sharp rate for the AND–OR tree: `R₀(T_{2,k}) ≤ (α - 1 / 2) α ^ (2k)`. -/
theorem zeroErrorComplexity_andOrTree_le_rate (k : ℕ) :
    zeroErrorComplexity (andOrTree k) ≤ (directionalRate - 1 / 2) * directionalRate ^ (2 * k) :=
  let ⟨_, hμ, hc⟩ :=
    exists_computes_zero_andOrTree_of_directional (expectedCost_directional_le_rate (2 * k))
  zeroErrorComplexity_le hμ hc

/-- The sharp rate for `T_{2,k}` on `n = 4 ^ k` leaves: `R₀ ≤ (α - 1 / 2) n ^ (log₂ α)`, where
`log₂ α ≈ 0.7537`. -/
theorem zeroErrorComplexity_andOrTree_le_rpow_rate (k : ℕ) :
    zeroErrorComplexity (andOrTree k) ≤
      (directionalRate - 1 / 2) * ((4 : ℝ) ^ k) ^ Real.logb 2 directionalRate := by
  have hα : 0 < directionalRate := by linarith [three_halves_lt_directionalRate]
  have h : ((4 : ℝ) ^ k) ^ Real.logb 2 directionalRate = directionalRate ^ (2 * k) := by
    rw [show (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) by rw [pow_mul]; norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hα, Real.rpow_natCast]
  rw [h]
  exact zeroErrorComplexity_andOrTree_le_rate k

end Cslib.QueryComplexity
