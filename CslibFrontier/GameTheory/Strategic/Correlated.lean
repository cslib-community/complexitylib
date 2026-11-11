/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Nash
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Correlated equilibria

A *correlated equilibrium* of a cost-minimization game is a distribution `σ` on profiles under
which no player can lower its expected cost by applying a switching function `δ : S i → S i` to
its own strategy while the others keep theirs ([Roughgarden2013CS364A], Lecture 18, §1). A
trusted party samples `s ∼ σ` and privately recommends `s i` to each player `i`; the condition
says that following the recommendation is optimal given what the recommendation reveals about
the others'. Equivalently (`isCorrelatedEquilibrium_iff`), for every recommendation `a` and
deviation `b`, the expected cost of `i` on the event `s i = a` does not exceed its expected cost
there after switching to `b`. This is Definition 3.3 of [Roughgarden2013CS364A], Lecture 13, with
both sides multiplied by the probability of the event, so that the condition is meaningful when
that probability vanishes.

Distributions are finitely supported, as for coarse correlated equilibria, so expectations are
finite sums. The equilibrium concepts are nested ([Roughgarden2013CS364A], Lecture 13, §3):
a pure Nash equilibrium is a correlated equilibrium as a point mass, the product distribution of a
mixed Nash equilibrium is a correlated equilibrium, and a correlated equilibrium is a coarse
correlated equilibrium, because a constant switching function is a fixed deviation. By Nash's
theorem, every finite game has a correlated equilibrium.

## Main definitions

* `Cslib.GameTheory.CostGame.IsCorrelatedEquilibrium`: correlated equilibria, by switching
  functions.

## Main results

* `Cslib.GameTheory.CostGame.isCorrelatedEquilibrium_iff`: the conditional form.
* `Cslib.GameTheory.CostGame.IsCorrelatedEquilibrium.isCoarseCorrelatedEquilibrium`: a correlated
  equilibrium is a coarse correlated equilibrium.
* `Cslib.GameTheory.CostGame.IsPureNash.isCorrelatedEquilibrium`: a pure Nash equilibrium is a
  correlated equilibrium as a point mass.
* `Cslib.GameTheory.CostGame.IsMixedNash.isCorrelatedEquilibrium`: the product distribution of a
  mixed Nash equilibrium is a correlated equilibrium.
* `Cslib.GameTheory.CostGame.exists_isCorrelatedEquilibrium`: every finite game has a correlated
  equilibrium.

## References

* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
-/

public section

namespace Cslib.GameTheory.CostGame

open Finset Function

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] (G : CostGame ι S)

/-- A finitely supported distribution `σ` on profiles is a **correlated equilibrium**
([Roughgarden2013CS364A], Lecture 18, §1): for every player `i` and switching function
`δ : S i → S i`, the expected cost of `i` under `σ` is at most its expected cost when it replaces
its recommended strategy `s i` by `δ (s i)` while the others play according to `σ`. -/
@[expose] def IsCorrelatedEquilibrium (σ : Convexity.StdSimplex ℝ (∀ i, S i)) : Prop :=
  ∀ i (δ : S i → S i), σ.weights.sum (fun s w => w * G.cost i s)
    ≤ σ.weights.sum (fun s w => w * G.cost i (update s i (δ (s i))))

/-- A finitely supported distribution `σ` on profiles is an **approximate correlated equilibrium**
([Roughgarden2013CS364A], Lecture 18, Proposition 1.3): for every player `i` and switching function
`δ : S i → S i`, the expected cost of `i` under `σ` exceeds its expected cost under the deviation
`δ` by at most the additive slack `ε i`. -/
@[expose] def IsApproxCorrelatedEquilibrium (ε : ι → ℝ)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) : Prop :=
  ∀ i (δ : S i → S i), σ.weights.sum (fun s w => w * G.cost i s)
    ≤ σ.weights.sum (fun s w => w * G.cost i (update s i (δ (s i)))) + ε i


omit [DecidableEq ι] in
/-- Grouping a sum over the support of `σ` by the recommendation `s i`. -/
private theorem sum_eq_sum_image_sum_ite (σ : Convexity.StdSimplex ℝ (∀ i, S i)) (i : ι)
    [DecidableEq (S i)] (f : (∀ j, S j) → S i → ℝ) :
    σ.weights.sum (fun s w => w * f s (s i)) = ∑ a ∈ σ.weights.support.image (fun s => s i),
      σ.weights.sum (fun s w => w * if s i = a then f s a else 0) := by
  simp only [Finsupp.sum]
  rw [sum_comm]
  refine sum_congr rfl fun s hs => ?_
  simp only [mul_ite, mul_zero]
  rw [sum_ite_eq (σ.weights.support.image fun s => s i) (s i) fun a => σ.weights s * f s a,
    ite_eq_left (mem_image_of_mem _ hs)]

omit [DecidableEq ι] in
private theorem sum_eq_sum_univ_sum_ite (σ : Convexity.StdSimplex ℝ (∀ i, S i)) (i : ι)
    [Fintype (S i)] [DecidableEq (S i)] (f : (∀ j, S j) → S i → ℝ) :
    σ.weights.sum (fun s w => w * f s (s i)) = ∑ a,
      σ.weights.sum (fun s w => w * if s i = a then f s a else 0) := by
  rw [sum_eq_sum_image_sum_ite σ i f]
  refine Finset.sum_subset (Finset.subset_univ (σ.weights.support.image fun s => s i))
    (fun a _ ha => ?_)
  simp only [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro s hs
  have : s i ≠ a := fun hs_eq => ha (hs_eq ▸ Finset.mem_image_of_mem (fun s => s i) hs)
  split_ifs with hs_eq
  · exact (this hs_eq).elim
  · rw [mul_zero]

variable {G}

/-- An approximate correlated equilibrium with zero slack is a correlated equilibrium. -/
theorem isApproxCorrelatedEquilibrium_zero_iff {σ : Convexity.StdSimplex ℝ (∀ i, S i)} :
    G.IsApproxCorrelatedEquilibrium 0 σ ↔ G.IsCorrelatedEquilibrium σ := by
  dsimp [IsApproxCorrelatedEquilibrium, IsCorrelatedEquilibrium]
  simp only [add_zero]


/-- The conditional form of approximate correlated equilibria. -/
theorem isApproxCorrelatedEquilibrium_iff [∀ i, DecidableEq (S i)] [∀ i, Fintype (S i)]
    {ε : ι → ℝ} {σ : Convexity.StdSimplex ℝ (∀ i, S i)} :
    G.IsApproxCorrelatedEquilibrium ε σ ↔ ∀ i (δ : S i → S i),
      (∑ a, σ.weights.sum (fun s w => w * if s i = a then G.cost i s else 0))
        ≤ (∑ a, σ.weights.sum (fun s w =>
            w * if s i = a then G.cost i (update s i (δ a)) else 0)) + ε i := by
  have H (i : ι) (δ : S i → S i) :
      σ.weights.sum (fun s w => w * G.cost i (update s i (δ (s i)))) =
        ∑ a, σ.weights.sum (fun s w =>
          w * if s i = a then G.cost i (update s i (δ a)) else 0) :=
    sum_eq_sum_univ_sum_ite σ i fun s a => G.cost i (update s i (δ a))
  have H0 (i : ι) : σ.weights.sum (fun s w => w * G.cost i s) =
      ∑ a, σ.weights.sum (fun s w => w * if s i = a then G.cost i s else 0) :=
    sum_eq_sum_univ_sum_ite σ i fun s _ => G.cost i s
  constructor
  · intro h i δ
    rw [← H0 i, ← H i δ]
    exact h i δ
  · intro h i δ
    rw [H0 i, H i δ]
    exact h i δ


/-- The **conditional form** of correlated equilibria ([Roughgarden2013CS364A], Lecture 13,
Definition 3.3): for every player `i`, recommendation `a` and deviation `b`, the expected cost of
`i` on the event `s i = a` is at most its expected cost there when it plays `b` instead. Both sides
carry the probability of the event, so no division is needed. -/
theorem isCorrelatedEquilibrium_iff [∀ i, DecidableEq (S i)]
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} :
    G.IsCorrelatedEquilibrium σ ↔ ∀ i (a b : S i),
      σ.weights.sum (fun s w => w * if s i = a then G.cost i s else 0)
        ≤ σ.weights.sum (fun s w => w * if s i = a then G.cost i (update s i b) else 0) := by
  constructor
  · intro h i a b
    have key := h i fun c => if c = a then b else c
    have hL : σ.weights.sum (fun s w => w * G.cost i s)
        = σ.weights.sum (fun s w => w * if s i = a then G.cost i s else 0)
          + σ.weights.sum (fun s w => w * if s i = a then 0 else G.cost i s) := by
      rw [← Finsupp.sum_add]
      refine Finsupp.sum_congr fun s _ => ?_
      split_ifs <;> ring
    have hR : σ.weights.sum (fun s w => w * G.cost i (update s i (if s i = a then b else s i)))
        = σ.weights.sum (fun s w => w * if s i = a then G.cost i (update s i b) else 0)
          + σ.weights.sum (fun s w => w * if s i = a then 0 else G.cost i s) := by
      rw [← Finsupp.sum_add]
      refine Finsupp.sum_congr fun s _ => ?_
      split_ifs with hs
      · ring
      · rw [update_eq_self]
        ring
    linarith
  · intro h i δ
    have hL := sum_eq_sum_image_sum_ite σ i fun s _ => G.cost i s
    have hR := sum_eq_sum_image_sum_ite σ i fun s c => G.cost i (update s i (δ c))
    rw [hL, hR]
    exact sum_le_sum fun a _ => h i a (δ a)

/-- A correlated equilibrium is a coarse correlated equilibrium: a fixed deviation `a` is the
constant switching function. -/
theorem IsCorrelatedEquilibrium.isCoarseCorrelatedEquilibrium
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} (h : G.IsCorrelatedEquilibrium σ) :
    G.IsCoarseCorrelatedEquilibrium σ :=
  fun i a => h i fun _ => a

/-- A pure Nash equilibrium, viewed as a point mass, is a correlated equilibrium. -/
theorem IsPureNash.isCorrelatedEquilibrium {s : ∀ i, S i} (hs : G.IsPureNash s) :
    G.IsCorrelatedEquilibrium (Convexity.StdSimplex.single s) := by
  intro i δ
  simp only [Convexity.StdSimplex.weights_single, Finsupp.sum_single_index, zero_mul, one_mul]
  exact hs i (δ (s i))

section Mixed

variable [Fintype ι] [∀ i, Fintype (S i)]

/-- Under the product distribution of `p`, the expected cost of `i` after switching to `b`, on the
event that `i` is recommended `a`, is `p i a` times the expected cost of playing `b` against the
others' mixed strategies. -/
theorem sum_ite_productWeight [∀ i, DecidableEq (S i)] (G : CostGame ι S)
    (p : ∀ i, S i → ℝ) {i : ι} (hp : ∑ c, p i c = 1) (a b : S i) :
    ∑ s, productWeight p s * (if s i = a then G.cost i (update s i b) else 0)
      = p i a * G.deviationCost p i b := by
  have hsum : ∑ c, (Pi.single a 1 : S i → ℝ) c = ∑ c, p i c := by
    rw [hp]
    simp
  rw [← G.deviationCost_update_self p hsum b, deviationCost_def, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [productWeight_def, productWeight_def,
    ← mul_prod_erase univ (fun j => p j (s j)) (mem_univ i),
    ← mul_prod_erase univ (fun j => update p i (Pi.single a 1) j (s j)) (mem_univ i)]
  have herase : ∏ j ∈ univ.erase i, update p i (Pi.single a 1) j (s j)
      = ∏ j ∈ univ.erase i, p j (s j) :=
    prod_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  rw [herase, update_self]
  split_ifs with hs
  · subst hs
    rw [Pi.single_eq_same]
    ring
  · rw [Pi.single_eq_of_ne hs]
    ring

/-- The product distribution of a mixed Nash equilibrium is a correlated equilibrium: conditioned
on its own recommendation, a player still faces the others' independent mixed strategies. -/
theorem IsMixedNash.isCorrelatedEquilibrium {p : ∀ i, S i → ℝ} (h : G.IsMixedNash p) :
    G.IsCorrelatedEquilibrium
      (productDist (fun i => (h.1 i).nonneg) (fun i => (h.1 i).sum_eq_one)) := by
  classical
  refine isCorrelatedEquilibrium_iff.2 fun i a b => ?_
  have hp := (h.1 i).sum_eq_one
  have hL : ∑ s, productWeight p s * (if s i = a then G.cost i s else 0)
      = p i a * G.deviationCost p i a := by
    rw [← sum_ite_productWeight G p hp a a]
    refine sum_congr rfl fun s _ => ?_
    split_ifs with hs
    · rw [← hs, update_eq_self]
    · rfl
  rw [productDist_sum, productDist_sum, hL, sum_ite_productWeight G p hp a b]
  rcases ((h.1 i).nonneg a).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, zero_mul]
  · rw [h.deviationCost_eq_of_pos i hpos]
    exact mul_le_mul_of_nonneg_left (h.2 i b) hpos.le

end Mixed

/-- Every finite game with nonempty strategy sets has a correlated equilibrium: the product
distribution of a mixed Nash equilibrium. -/
theorem exists_isCorrelatedEquilibrium [Finite ι] [∀ i, Finite (S i)] [∀ i, Nonempty (S i)]
    (G : CostGame ι S) : ∃ σ, G.IsCorrelatedEquilibrium σ := by
  have := Fintype.ofFinite ι
  have := fun i => Fintype.ofFinite (S i)
  obtain ⟨_, h⟩ := G.exists_isMixedNash
  exact ⟨_, h.isCorrelatedEquilibrium⟩

end Cslib.GameTheory.CostGame
