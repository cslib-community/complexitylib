/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.MixedStrategy
public import CslibFrontier.GameTheory.Strategic.Mixed
public import CslibFrontier.GameTheory.Strategic.Smooth
public import Mathlib.Dynamics.FixedPoints.Defs
import CslibFrontier.Foundations.Analysis.Brouwer.Simplex
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Monoid

/-!
# Mixed Nash equilibria and Nash's theorem

A *mixed Nash equilibrium* of a finite cost-minimization game is a profile `p` of mixed strategies
`p i : S i → ℝ` under which no player can lower its expected cost by deviating to a pure strategy
([Roughgarden2013CS364A], Lecture 13, Definition 3.2). The expected cost
`expectedCost G p i = E_{s ∼ p}[cost i s]` is taken over the product distribution of the `p i`, and
the cost of the deviation to `a` is `deviationCost G p i a` from
`CslibFrontier.GameTheory.Strategic.Mixed`.

**Nash's theorem** ([Nash1951], Theorem 1) says that every finite game has a mixed Nash
equilibrium. Nash's proof applies Brouwer's fixed-point theorem to the map that shifts each mixed
strategy towards the pure strategies that would lower the player's cost: with
`nashGain G p i a = max 0 (expectedCost G p i - deviationCost G p i a)`,
`nashMap G p i a = (p i a + nashGain G p i a) / (1 + ∑ b, nashGain G p i b)`.
It maps the product of simplices continuously into itself, and its fixed points are exactly the
mixed Nash equilibria (`isFixedPt_nashMap_iff`). Brouwer's theorem for products of simplices is
`Cslib.Brouwer.exists_isFixedPt_pi_simplex`.

Pure Nash equilibria are exactly the mixed Nash equilibria in which every player uses a point
mass (`isMixedNash_single_iff`). Deviations to mixed strategies gain nothing either
(`IsMixedNash.expectedCost_le_update`), and the product distribution of a mixed Nash equilibrium
is a coarse correlated equilibrium (`IsMixedNash.isCoarseCorrelatedEquilibrium`).

## Main definitions

* `Cslib.GameTheory.CostGame.expectedCost`: the expected cost of a player under the product
  distribution.
* `Cslib.GameTheory.CostGame.IsMixedNash`: mixed Nash equilibria.
* `Cslib.GameTheory.CostGame.nashMap`: Nash's map on mixed strategy profiles.

## Main results

* `Cslib.GameTheory.CostGame.exists_isMixedNash`: **Nash's theorem**.
* `Cslib.GameTheory.CostGame.isFixedPt_nashMap_iff`: the fixed points of Nash's map are the mixed
  Nash equilibria.
* `Cslib.GameTheory.CostGame.isMixedNash_single_iff`: pure Nash equilibria are the mixed Nash
  equilibria made of point masses.
* `Cslib.GameTheory.CostGame.IsMixedNash.deviationCost_eq_of_pos`: the pure strategies in the
  support of an equilibrium strategy attain the expected cost.
* `Cslib.GameTheory.CostGame.IsMixedNash.expectedCost_le_update`: mixed deviations gain nothing.
* `Cslib.GameTheory.CostGame.IsMixedNash.isCoarseCorrelatedEquilibrium`: a mixed Nash
  equilibrium induces a coarse correlated equilibrium.

## References

* [J. Nash, *Non-Cooperative Games*][Nash1951]
* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
-/

public section

namespace Cslib.GameTheory.CostGame

open Finset Function

variable {ι : Type*} {S : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)]
  (G : CostGame ι S)

/-- The **expected cost** `E_{s ∼ p}[cost i s]` of player `i` when every player `j` samples its
strategy independently from `p j`. -/
def expectedCost (p : ∀ i, S i → ℝ) (i : ι) : ℝ :=
  ∑ s, productWeight p s * G.cost i s

/-- Unfolding equation for `expectedCost`, whose body is not exposed. -/
theorem expectedCost_def (p : ∀ i, S i → ℝ) (i : ι) :
    G.expectedCost p i = ∑ s, productWeight p s * G.cost i s := by
  rw [expectedCost]

omit [DecidableEq ι] [∀ i, Fintype (S i)] in
private theorem continuous_productWeight (s : ∀ i, S i) :
    Continuous fun p : ∀ i, S i → ℝ => productWeight p s := by
  simp only [productWeight_def]
  exact continuous_finsetProd _ fun i _ => (continuous_apply (s i)).comp (continuous_apply i)

private theorem continuous_expectedCost (i : ι) :
    Continuous fun p : ∀ i, S i → ℝ => G.expectedCost p i := by
  simp only [expectedCost_def]
  exact continuous_finsetSum _ fun s _ => (continuous_productWeight s).mul continuous_const

private theorem continuous_deviationCost (i : ι) (a : S i) :
    Continuous fun p : ∀ i, S i → ℝ => G.deviationCost p i a := by
  simp only [deviationCost_def]
  exact continuous_finsetSum _ fun s _ => (continuous_productWeight s).mul continuous_const

/-- Averaging the expected cost vector of player `i` against its own mixed strategy gives its
expected cost. -/
theorem sum_mul_deviationCost_eq_expectedCost (p : ∀ i, S i → ℝ) {i : ι}
    (hp : ∑ a, p i a = 1) : ∑ a, p i a * G.deviationCost p i a = G.expectedCost p i := by
  rw [sum_mul_deviationCost G p hp, expectedCost_def]

/-- A **mixed Nash equilibrium** ([Roughgarden2013CS364A], Lecture 13, Definition 3.2): every
player uses a mixed strategy, and no player can lower its expected cost by deviating to a pure
strategy while the others keep theirs. -/
@[expose] def IsMixedNash (p : ∀ i, S i → ℝ) : Prop :=
  (∀ i, IsMixedStrategy (p i)) ∧ ∀ i a, G.expectedCost p i ≤ G.deviationCost p i a

/-- The gain `max 0 (E_p[cost i] - E_p[cost i | i plays a])` of player `i` from deviating to the
pure strategy `a`. -/
noncomputable def nashGain (p : ∀ i, S i → ℝ) (i : ι) (a : S i) : ℝ :=
  max 0 (G.expectedCost p i - G.deviationCost p i a)

/-- **Nash's map** ([Nash1951], proof of Theorem 1): each player moves probability towards the
pure strategies that would lower its cost, in proportion to the gain, and renormalizes. -/
noncomputable def nashMap (p : ∀ i, S i → ℝ) (i : ι) (a : S i) : ℝ :=
  (p i a + G.nashGain p i a) / (1 + ∑ b, G.nashGain p i b)

private theorem nashGain_nonneg (p : ∀ i, S i → ℝ) (i : ι) (a : S i) : 0 ≤ G.nashGain p i a :=
  le_max_left _ _

private theorem nashGain_eq_zero_iff (p : ∀ i, S i → ℝ) (i : ι) (a : S i) :
    G.nashGain p i a = 0 ↔ G.expectedCost p i ≤ G.deviationCost p i a := by
  unfold nashGain
  constructor
  · intro h
    have := le_max_right 0 (G.expectedCost p i - G.deviationCost p i a)
    linarith
  · intro h
    exact max_eq_left (by linarith)

private theorem nashDenom_pos (p : ∀ i, S i → ℝ) (i : ι) :
    0 < 1 + ∑ b, G.nashGain p i b :=
  add_pos_of_pos_of_nonneg one_pos (sum_nonneg fun b _ => G.nashGain_nonneg p i b)

private theorem continuous_nashGain (i : ι) (a : S i) :
    Continuous fun p : ∀ i, S i → ℝ => G.nashGain p i a :=
  continuous_const.max ((G.continuous_expectedCost i).sub (G.continuous_deviationCost i a))

private theorem continuous_nashMap : Continuous G.nashMap := by
  refine continuous_pi fun i => continuous_pi fun a => ?_
  unfold nashMap
  exact (((continuous_apply a).comp (continuous_apply i)).add (G.continuous_nashGain i a)).div₀
    (continuous_const.add (continuous_finsetSum _ fun b _ => G.continuous_nashGain i b))
    fun p => (G.nashDenom_pos p i).ne'

private theorem isMixedStrategy_nashMap {p : ∀ i, S i → ℝ} (hp : ∀ i, IsMixedStrategy (p i))
    (i : ι) : IsMixedStrategy (G.nashMap p i) := by
  refine isMixedStrategy_iff.2 ⟨fun a => ?_, ?_⟩
  · exact div_nonneg (add_nonneg ((hp i).nonneg a) (G.nashGain_nonneg p i a))
      (G.nashDenom_pos p i).le
  · unfold nashMap
    rw [← sum_div, sum_add_distrib, (hp i).sum_eq_one]
    exact div_self (G.nashDenom_pos p i).ne'

/-- The fixed points of Nash's map are exactly the mixed Nash equilibria. -/
theorem isFixedPt_nashMap_iff {p : ∀ i, S i → ℝ} (hp : ∀ i, IsMixedStrategy (p i)) :
    IsFixedPt G.nashMap p ↔ G.IsMixedNash p := by
  constructor
  · intro h
    refine ⟨hp, fun i => ?_⟩
    have hg : ∀ b, G.nashGain p i b = p i b * ∑ c, G.nashGain p i c := by
      intro b
      have hb : G.nashMap p i b = p i b := congrFun (congrFun h i) b
      unfold nashMap at hb
      rw [div_eq_iff (G.nashDenom_pos p i).ne'] at hb
      linear_combination hb
    -- Some pure strategy in the support of `p i` does not beat the mixed strategy `p i`.
    obtain ⟨c, hc, hEc⟩ : ∃ c, 0 < p i c ∧ G.expectedCost p i ≤ G.deviationCost p i c := by
      by_contra hne
      push Not at hne
      obtain ⟨c, hc⟩ := (hp i).exists_pos
      have hlt : ∑ b, p i b * G.deviationCost p i b < ∑ b, p i b * G.expectedCost p i := by
        refine sum_lt_sum (fun b _ => ?_) ⟨c, mem_univ c, ?_⟩
        · rcases ((hp i).nonneg b).lt_or_eq with hb | hb
          · exact (mul_lt_mul_of_pos_left (hne b hb) hb).le
          · simp [← hb]
        · exact mul_lt_mul_of_pos_left (hne c hc) hc
      rw [← sum_mul, (hp i).sum_eq_one, one_mul,
        G.sum_mul_deviationCost_eq_expectedCost p (hp i).sum_eq_one] at hlt
      exact lt_irrefl _ hlt
    have hT : ∑ b, G.nashGain p i b = 0 := by
      have h0 := hg c
      rw [(G.nashGain_eq_zero_iff p i c).2 hEc] at h0
      exact (mul_eq_zero.1 h0.symm).resolve_left hc.ne'
    intro a
    refine (G.nashGain_eq_zero_iff p i a).1 ?_
    rw [hg a, hT, mul_zero]
  · intro h
    have hg : ∀ i a, G.nashGain p i a = 0 := fun i a => (G.nashGain_eq_zero_iff p i a).2 (h.2 i a)
    funext i a
    simp only [nashMap, hg, add_zero, sum_const_zero, div_one]

/-- **Nash's theorem** ([Nash1951], Theorem 1; [Roughgarden2013CS364A], Lecture 13, §3.3): every
finite game has a mixed Nash equilibrium. -/
theorem exists_isMixedNash [∀ i, Nonempty (S i)] : ∃ p, G.IsMixedNash p := by
  obtain ⟨p, hp, hfix⟩ := Cslib.Brouwer.exists_isFixedPt_pi_simplex (f := G.nashMap)
    (fun p hp i => isMixedStrategy_iff.1 (G.isMixedStrategy_nashMap
      (fun j => isMixedStrategy_iff.2 (hp j)) i))
    G.continuous_nashMap.continuousOn
  have hp' : ∀ i, IsMixedStrategy (p i) := fun i => isMixedStrategy_iff.2 (hp i)
  exact ⟨p, (G.isFixedPt_nashMap_iff hp').1 hfix⟩

section Pure

variable [∀ i, DecidableEq (S i)]

/-- The expected cost under the point masses at the coordinates of `s` is the cost at `s`. -/
theorem expectedCost_single (s : ∀ i, S i) (i : ι) :
    G.expectedCost (fun j => Pi.single (s j) 1) i = G.cost i s := by
  simp [expectedCost_def, productWeight_single]

/-- The expected cost vector under the point masses at the coordinates of `s` is the vector of
costs of unilateral deviations from `s`. -/
theorem deviationCost_single (s : ∀ i, S i) (i : ι) (a : S i) :
    G.deviationCost (fun j => Pi.single (s j) 1) i a = G.cost i (update s i a) := by
  simp [deviationCost_def, productWeight_single]

/-- Pure Nash equilibria are exactly the mixed Nash equilibria in which every player uses a point
mass. -/
theorem isMixedNash_single_iff (s : ∀ i, S i) :
    G.IsMixedNash (fun i => Pi.single (s i) 1) ↔ G.IsPureNash s := by
  simp only [IsMixedNash, IsPureNash, expectedCost_single, deviationCost_single]
  exact ⟨fun h => h.2, fun h => ⟨fun i => isMixedStrategy_single (s i), h⟩⟩

variable {G}

/-- A pure Nash equilibrium, played as point masses, is a mixed Nash equilibrium. -/
theorem IsPureNash.isMixedNash {s : ∀ i, S i} (h : G.IsPureNash s) :
    G.IsMixedNash fun i => Pi.single (s i) 1 :=
  (G.isMixedNash_single_iff s).2 h

end Pure

variable {G}

/-- In a mixed Nash equilibrium, deviations to mixed strategies do not lower the expected cost
either. -/
theorem IsMixedNash.expectedCost_le_update {p : ∀ i, S i → ℝ} (h : G.IsMixedNash p) (i : ι)
    {q : S i → ℝ} (hq : IsMixedStrategy q) :
    G.expectedCost p i ≤ G.expectedCost (update p i q) i := by
  have hq' : ∑ b, update p i q i b = 1 := by rw [update_self]; exact hq.sum_eq_one
  rw [← G.sum_mul_deviationCost_eq_expectedCost (update p i q) hq']
  calc G.expectedCost p i
      = ∑ b, q b * G.expectedCost p i := by rw [← sum_mul, hq.sum_eq_one, one_mul]
    _ ≤ ∑ b, q b * G.deviationCost p i b :=
        sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (h.2 i b) (hq.nonneg b)
    _ = ∑ b, update p i q i b * G.deviationCost (update p i q) i b := by
        refine sum_congr rfl fun b _ => ?_
        rw [update_self, G.deviationCost_update_self p
          (by rw [hq.sum_eq_one, (h.1 i).sum_eq_one]) b]

/-- In a mixed Nash equilibrium, every pure strategy that a player uses with positive probability
attains its expected cost. -/
theorem IsMixedNash.deviationCost_eq_of_pos {p : ∀ i, S i → ℝ} (h : G.IsMixedNash p) (i : ι)
    {a : S i} (ha : 0 < p i a) : G.deviationCost p i a = G.expectedCost p i := by
  refine le_antisymm (not_lt.1 fun hlt => ?_) (h.2 i a)
  have hsum : ∑ b, p i b * G.expectedCost p i < ∑ b, p i b * G.deviationCost p i b :=
    sum_lt_sum (fun b _ => mul_le_mul_of_nonneg_left (h.2 i b) ((h.1 i).nonneg b))
      ⟨a, mem_univ a, mul_lt_mul_of_pos_left hlt ha⟩
  rw [← sum_mul, (h.1 i).sum_eq_one, one_mul,
    G.sum_mul_deviationCost_eq_expectedCost p (h.1 i).sum_eq_one] at hsum
  exact lt_irrefl _ hsum

/-- The product distribution of a mixed Nash equilibrium is a coarse correlated equilibrium. -/
theorem IsMixedNash.isCoarseCorrelatedEquilibrium {p : ∀ i, S i → ℝ} (h : G.IsMixedNash p) :
    G.IsCoarseCorrelatedEquilibrium
      (productDist (fun i => (h.1 i).nonneg) (fun i => (h.1 i).sum_eq_one)) := by
  intro i a
  rw [productDist_sum, productDist_sum, ← expectedCost_def, ← deviationCost_def]
  exact h.2 i a

end Cslib.GameTheory.CostGame
