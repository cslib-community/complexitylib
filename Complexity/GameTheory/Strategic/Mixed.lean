/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.GameTheory.Strategic.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Mixed strategies and product distributions

A *mixed strategy* of player `i` in a finite game is a probability vector `p i : S i → ℝ`. When the
players randomize independently, the outcome distribution is the product distribution, with weight
`productWeight p s = ∏ i, p i (s i)` on the profile `s` (`productDist`). The *expected cost vector*
of player `i` assigns to each of its strategies `a` the expected cost
`deviationCost G p i a = E_{s ∼ p}[cost i (update s i a)]` of playing `a` while the others play
according to `p` ([Roughgarden2013CS364A], Lecture 17, §3). The coordinate `s i` is overwritten,
so this expectation depends on `p i` only through its total mass. For a probability vector `p i`
it is the expectation over the opponents' strategies alone.

The basic identity is `sum_mul_deviationCost`: averaging the expected cost vector of player `i`
against its own mixed strategy `p i` gives its expected cost under the product distribution. So a
learner that faces the expected cost vectors has the same regret as the player in the game.

## Main definitions

* `Cslib.GameTheory.productWeight`: the weight `∏ i, p i (s i)` of a profile.
* `Cslib.GameTheory.productDist`: the product distribution, a point of
  `Convexity.StdSimplex ℝ (∀ i, S i)`.
* `Cslib.GameTheory.CostGame.deviationCost`: the expected cost vector of player `i`.

## Main results

* `Cslib.GameTheory.sum_productWeight`: the product weights of probability vectors sum to `1`.
* `Cslib.GameTheory.productDist_sum`: expectations under `productDist` are sums over profiles.
* `Cslib.GameTheory.CostGame.sum_mul_deviationCost`: averaging the expected cost vector against
  the player's own mixed strategy gives its expected cost.
* `Cslib.GameTheory.CostGame.abs_deviationCost_le`: expected costs inherit bounds on the costs.

## References

* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
-/

public section

namespace Cslib.GameTheory

open Finset

variable {ι : Type*} {S : ι → Type*} [Fintype ι]

/-- The weight `∏ i, p i (s i)` of the profile `s` under the product of the mixed strategies
`p i`. -/
def productWeight (p : ∀ i, S i → ℝ) (s : ∀ i, S i) : ℝ :=
  ∏ i, p i (s i)

/-- Product weights of nonnegative vectors are nonnegative. -/
theorem productWeight_nonneg {p : ∀ i, S i → ℝ} (hp : ∀ i a, 0 ≤ p i a) (s : ∀ i, S i) :
    0 ≤ productWeight p s :=
  prod_nonneg fun i _ => hp i (s i)

variable [DecidableEq ι]

/-- Changing coordinate `i` of a profile from `s i` to `a` changes its product weight by the factor
`p i a / p i (s i)`, written without division. -/
theorem productWeight_update (p : ∀ i, S i → ℝ) (s : ∀ i, S i) (i : ι) (a : S i) :
    p i (s i) * productWeight p (Function.update s i a) = p i a * productWeight p s := by
  unfold productWeight
  rw [prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ i)
      (fun j => p j (Function.update s i a j)),
    prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ i) (fun j => p j (s j))]
  have h : ∏ j ∈ univ \ {i}, p j (Function.update s i a j) = ∏ j ∈ univ \ {i}, p j (s j) :=
    prod_congr rfl fun j hj => by rw [Function.update_of_ne (by simpa using hj)]
  rw [h, Function.update_self]
  ring

variable [∀ i, Fintype (S i)]

/-- The product weights of probability vectors sum to `1`. -/
theorem sum_productWeight {p : ∀ i, S i → ℝ} (hp : ∀ i, ∑ a, p i a = 1) :
    ∑ s, productWeight p s = 1 := by
  unfold productWeight
  rw [← Fintype.prod_sum]
  exact prod_eq_one fun i _ => hp i

/-- The **product distribution** of the mixed strategies `p i`, as a finitely supported
distribution on profiles. -/
noncomputable def productDist {p : ∀ i, S i → ℝ} (hp0 : ∀ i a, 0 ≤ p i a)
    (hp1 : ∀ i, ∑ a, p i a = 1) : Convexity.StdSimplex ℝ (∀ i, S i) where
  weights := Finsupp.equivFunOnFinite.symm (productWeight p)
  nonneg s := by
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_equivFunOnFinite_symm]
    exact productWeight_nonneg hp0 s
  total := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl]
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    exact sum_productWeight hp1

/-- Expectations under the product distribution are sums over all profiles. -/
theorem productDist_sum {p : ∀ i, S i → ℝ} (hp0 : ∀ i a, 0 ≤ p i a) (hp1 : ∀ i, ∑ a, p i a = 1)
    (f : (∀ i, S i) → ℝ) :
    (productDist hp0 hp1).weights.sum (fun s w => w * f s) = ∑ s, productWeight p s * f s := by
  rw [Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp only [productDist, Finsupp.coe_equivFunOnFinite_symm]

/-- Resampling coordinate `i` from `p i` preserves the product distribution: if `p i` has total
mass `1`, then `∑ a, p i a * E_{s ∼ p}[f (update s i a)] = E_{s ∼ p}[f s]`. The proof is the
change of variables `(a, s) ↦ (s i, update s i a)` on `S i × ∀ j, S j`. -/
theorem sum_mul_sum_productWeight_update (p : ∀ i, S i → ℝ) {i : ι} (hp : ∑ a, p i a = 1)
    (f : (∀ j, S j) → ℝ) :
    ∑ a, p i a * ∑ s, productWeight p s * f (Function.update s i a)
      = ∑ s, productWeight p s * f s := by
  calc ∑ a, p i a * ∑ s, productWeight p s * f (Function.update s i a)
      = ∑ x : S i × (∀ j, S j),
          p i x.1 * (productWeight p x.2 * f (Function.update x.2 i x.1)) := by
        rw [Fintype.sum_prod_type]
        simp only [mul_sum]
    _ = ∑ x : S i × (∀ j, S j), p i x.1 * (productWeight p x.2 * f x.2) :=
        Fintype.sum_equiv
          ⟨fun x => (x.2 i, Function.update x.2 i x.1),
            fun x => (x.2 i, Function.update x.2 i x.1), fun x => by simp, fun x => by simp⟩
          _ _ fun x => by
            simp only [Equiv.coe_fn_mk]
            rw [← mul_assoc, ← mul_assoc, productWeight_update]
    _ = ∑ s, productWeight p s * f s := by
        rw [Fintype.sum_prod_type]
        simp only [← mul_sum]
        rw [← sum_mul, hp, one_mul]

namespace CostGame

/-- The **expected cost vector** of player `i` against the mixed strategies `p`
([Roughgarden2013CS364A], Lecture 17, §3): the expected cost of strategy `a` when every player
`j` samples `s j` from `p j` and player `i` then replaces `s i` by `a`. -/
def deviationCost (G : CostGame ι S) (p : ∀ i, S i → ℝ) (i : ι) (a : S i) : ℝ :=
  ∑ s, productWeight p s * G.cost i (Function.update s i a)

/-- Unfolding equation for `deviationCost`, whose body is not exposed. -/
theorem deviationCost_def (G : CostGame ι S) (p : ∀ i, S i → ℝ) (i : ι) (a : S i) :
    G.deviationCost p i a = ∑ s, productWeight p s * G.cost i (Function.update s i a) := by
  rw [deviationCost]

/-- Averaging the expected cost vector of player `i` against its own mixed strategy gives its
expected cost under the product distribution. -/
theorem sum_mul_deviationCost (G : CostGame ι S) (p : ∀ i, S i → ℝ) {i : ι}
    (hp : ∑ a, p i a = 1) :
    ∑ a, p i a * G.deviationCost p i a = ∑ s, productWeight p s * G.cost i s :=
  sum_mul_sum_productWeight_update p hp (G.cost i)

/-- If the costs of player `i` are bounded by `M` in absolute value, so are its expected costs
against mixed strategies. -/
theorem abs_deviationCost_le (G : CostGame ι S) {p : ∀ i, S i → ℝ} (hp0 : ∀ j b, 0 ≤ p j b)
    (hp1 : ∀ j, ∑ b, p j b = 1) {i : ι} {M : ℝ} (hc : ∀ s, |G.cost i s| ≤ M) (a : S i) :
    |G.deviationCost p i a| ≤ M := by
  calc |∑ s, productWeight p s * G.cost i (Function.update s i a)|
      ≤ ∑ s, |productWeight p s * G.cost i (Function.update s i a)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, productWeight p s * M := sum_le_sum fun s _ => by
        rw [abs_mul, abs_of_nonneg (productWeight_nonneg hp0 s)]
        exact mul_le_mul_of_nonneg_left (hc _) (productWeight_nonneg hp0 s)
    _ = M := by rw [← sum_mul, sum_productWeight hp1, one_mul]

end CostGame

end Cslib.GameTheory
