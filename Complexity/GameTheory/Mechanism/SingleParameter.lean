/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Single-parameter mechanism design

A *single-parameter environment* has bidders `i : ι`, each with a private valuation `vᵢ` per unit
of "stuff", and a feasible set `X` of allocation vectors `ι → ℝ`. A sealed-bid mechanism collects a
bid profile `b : ι → ℝ` and chooses an allocation `x(b)` and payments `p(b)`; bidder `i` with
valuation `v` has quasilinear utility `v · xᵢ(b) − pᵢ(b)`.

We work over real bids and quantify incentive constraints over *nonnegative* bid profiles and
valuations, as in [Roughgarden2013CS364A], Lecture 3. Truthfulness (`IsDSIC`) and individual
rationality (`IsIR`) are separate predicates; Roughgarden's "DSIC" bundles both (Lecture 2,
Theorem 5.1 (1)). Values of a rule on profiles with a negative entry are irrelevant to every
definition here.

## Main definitions

* `SingleParameter.Mechanism`: an allocation rule and a payment rule.
* `SingleParameter.Mechanism.utility`: quasilinear utility `v · xᵢ(b) − pᵢ(b)`.
* `SingleParameter.Mechanism.IsDSIC`: truthful bidding is a dominant strategy.
* `SingleParameter.Mechanism.IsIR`: truthful bidders get nonnegative utility.
* `SingleParameter.Mechanism.IsNormalized`: a bidder who bids `0` pays `0`.
* `SingleParameter.IsMonotone`: each `xᵢ(z, b₋ᵢ)` is nondecreasing in the own bid `z ≥ 0`
  ([Roughgarden2013CS364A], Lecture 3, Definition 4.2).
* `SingleParameter.IsImplementable`: some payment rule makes the allocation rule DSIC
  (Lecture 3, Definition 4.1).
* `SingleParameter.IsWelfareMaximizing`: on every nonnegative bid profile the rule picks a feasible
  allocation maximizing the reported welfare `∑ bᵢ xᵢ`.

## Main results

* `SingleParameter.Mechanism.IsDSIC.isMonotone`: DSIC allocation rules are monotone (the "payment
  difference sandwich", Lecture 3 (4)); `IsImplementable.isMonotone` restates it.
* `SingleParameter.IsWelfareMaximizing.isMonotone`: every welfare-maximizing allocation rule, with
  any tie-breaking, is monotone.
* `SingleParameter.exists_isWelfareMaximizing`: a welfare-maximizing rule exists for every finite
  nonempty feasible set.

The converse direction of Myerson's Lemma and the payment formula are in
`Complexity.GameTheory.Mechanism.Myerson`.

## References

* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
* [T. Roughgarden, *Twenty Lectures on Algorithmic Game Theory*][Roughgarden2016]
* [R. B. Myerson, *Optimal auction design*][Myerson1981]
-/

public section

namespace Cslib.GameTheory.SingleParameter

/-- A sealed-bid mechanism in a single-parameter environment with bidders `ι`: on the bid profile
`b`, bidder `i` receives `allocation b i` units and pays `payment b i`. -/
structure Mechanism (ι : Type*) where
  /-- The allocation rule `x`: `allocation b i` is the amount allocated to bidder `i`. -/
  allocation : (ι → ℝ) → ι → ℝ
  /-- The payment rule `p`: `payment b i` is the amount charged to bidder `i`. -/
  payment : (ι → ℝ) → ι → ℝ

namespace Mechanism

variable {ι : Type*}

/-- The quasilinear utility `v · xᵢ(b) − pᵢ(b)` of bidder `i` with valuation `v` on the bid
profile `b`. -/
@[expose] def utility (M : Mechanism ι) (i : ι) (v : ℝ) (b : ι → ℝ) : ℝ :=
  v * M.allocation b i - M.payment b i

/-- Dominant-strategy incentive compatibility: for every bidder `i`, nonnegative valuation `v`
and nonnegative bid profile `b`, replacing `i`'s bid by `v` does not lower `i`'s utility. Since
`b` is arbitrary, this quantifies over all bids `b₋ᵢ` of the others and all deviations `bᵢ`.
Individual rationality is the separate predicate `IsIR`. -/
@[expose] def IsDSIC [DecidableEq ι] (M : Mechanism ι) : Prop :=
  ∀ (i : ι) (b : ι → ℝ) (v : ℝ), 0 ≤ b → 0 ≤ v →
    M.utility i v b ≤ M.utility i v (Function.update b i v)

/-- Individual rationality: on every nonnegative bid profile, a truthful bidder (whose valuation
is its bid `b i`) receives nonnegative utility. -/
@[expose] def IsIR (M : Mechanism ι) : Prop :=
  ∀ (i : ι) (b : ι → ℝ), 0 ≤ b → 0 ≤ M.utility i (b i) b

/-- The normalization of Myerson's Lemma (b): a bidder who bids `0` pays `0`, whatever the
nonnegative bids of the others. -/
@[expose] def IsNormalized [DecidableEq ι] (M : Mechanism ι) : Prop :=
  ∀ (i : ι) (b : ι → ℝ), 0 ≤ b → M.payment (Function.update b i 0) i = 0

end Mechanism

variable {ι : Type*}

section DecidableEq

variable [DecidableEq ι]

/-- Replacing one entry of a nonnegative bid profile by a nonnegative bid keeps it nonnegative. -/
theorem update_nonneg {b : ι → ℝ} (hb : 0 ≤ b) (i : ι) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ Function.update b i z := by
  intro j
  rcases eq_or_ne j i with rfl | hj
  · rw [Pi.zero_apply, Function.update_self]
    exact hz
  · rw [Pi.zero_apply, Function.update_of_ne hj]
    exact hb j

/-- An allocation rule is *monotone* if, for every bidder `i` and nonnegative bids of the others,
`i`'s allocation is nondecreasing in its own nonnegative bid ([Roughgarden2013CS364A], Lecture 3,
Definition 4.2). -/
@[expose] def IsMonotone (x : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ (i : ι) (b : ι → ℝ), 0 ≤ b →
    MonotoneOn (fun z => x (Function.update b i z) i) (Set.Ici 0)

/-- An allocation rule is *implementable* if some payment rule makes it DSIC
([Roughgarden2013CS364A], Lecture 3, Definition 4.1). -/
@[expose] def IsImplementable (x : (ι → ℝ) → ι → ℝ) : Prop :=
  ∃ p : (ι → ℝ) → ι → ℝ, (Mechanism.mk x p).IsDSIC

/-- The allocation and payment curves of a DSIC mechanism along one bidder's own bid satisfy
both swap inequalities of Myerson's proof ([Roughgarden2013CS364A], Lecture 3, (2) and (3)). -/
theorem Mechanism.IsDSIC.utility_update_le {M : Mechanism ι} (hM : M.IsDSIC) (i : ι)
    {b : ι → ℝ} (hb : 0 ≤ b) {v z : ℝ} (hv : 0 ≤ v) (hz : 0 ≤ z) :
    v * M.allocation (Function.update b i z) i - M.payment (Function.update b i z) i ≤
      v * M.allocation (Function.update b i v) i - M.payment (Function.update b i v) i := by
  have := hM i (Function.update b i z) v (update_nonneg hb i hz) hv
  simpa only [Mechanism.utility, Function.update_idem] using this

/-- **Myerson's Lemma, necessity** ([Roughgarden2013CS364A], Lecture 3, Theorem 4.3 (a), "only
if"): the allocation rule of a DSIC mechanism is monotone. Adding the two swap inequalities for
bids `z ≤ y` gives `(y − z)(x(y) − x(z)) ≥ 0`. -/
theorem Mechanism.IsDSIC.isMonotone {M : Mechanism ι} (hM : M.IsDSIC) :
    IsMonotone M.allocation := by
  intro i b hb z hz y hy hzy
  have h1 := hM.utility_update_le i hb hy hz
  have h2 := hM.utility_update_le i hb hz hy
  by_contra hlt'
  have hlt := not_le.1 hlt'
  rcases hzy.lt_or_eq with hzy' | rfl
  · nlinarith
  · exact lt_irrefl _ hlt

/-- Implementable allocation rules are monotone. -/
theorem IsImplementable.isMonotone {x : (ι → ℝ) → ι → ℝ} (hx : IsImplementable x) :
    IsMonotone x :=
  let ⟨_, hp⟩ := hx
  Mechanism.IsDSIC.isMonotone (M := ⟨x, _⟩) hp

end DecidableEq

section Welfare

variable [Fintype ι]

/-- An allocation rule is *welfare-maximizing* for the feasible set `X` if on every nonnegative
bid profile `b` it chooses some `x(b) ∈ X` maximizing the reported welfare `∑ᵢ bᵢ xᵢ` over `X`
([Roughgarden2013CS364A], Lecture 2, Theorem 5.1 (2), and Lecture 4, (1)). Ties may be broken
arbitrarily. -/
@[expose] def IsWelfareMaximizing (X : Set (ι → ℝ)) (x : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ b, 0 ≤ b → x b ∈ X ∧ ∀ y ∈ X, ∑ i, b i * y i ≤ ∑ i, b i * x b i

/-- Changing bidder `i`'s bid to `z` changes the welfare of a fixed allocation `y` by
`(z − bᵢ) yᵢ`. -/
theorem sum_update_mul [DecidableEq ι] (b y : ι → ℝ) (i : ι) (z : ℝ) :
    ∑ j, Function.update b i z j * y j = ∑ j, b j * y j + (z - b i) * y i := by
  have h : (fun j => Function.update b i z j * y j) =
      Function.update (fun j => b j * y j) i (z * y i) := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  rw [h, Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.add_sum_erase _ _
    (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  ring

/-- Every welfare-maximizing allocation rule is monotone, whatever its tie-breaking: optimality
of `x(z, b₋ᵢ)` and of `x(z', b₋ᵢ)` against each other gives
`(z' − z)(xᵢ(z', b₋ᵢ) − xᵢ(z, b₋ᵢ)) ≥ 0`. With Myerson's Lemma this makes welfare maximization
implementable in every single-parameter environment ([Roughgarden2013CS364A], Lecture 4, §1.2–1.3,
for knapsack auctions). -/
theorem IsWelfareMaximizing.isMonotone [DecidableEq ι] {X : Set (ι → ℝ)}
    {x : (ι → ℝ) → ι → ℝ} (hx : IsWelfareMaximizing X x) : IsMonotone x := by
  intro i b hb z hz z' hz' hzz'
  change x (Function.update b i z) i ≤ x (Function.update b i z') i
  set B := Function.update b i z
  set B' := Function.update b i z'
  obtain ⟨hmem, hmax⟩ := hx B (update_nonneg hb i hz)
  obtain ⟨hmem', hmax'⟩ := hx B' (update_nonneg hb i hz')
  have h1 := hmax _ hmem'
  have h2 := hmax' _ hmem
  have e1 := sum_update_mul B (x B') i z'
  have e2 := sum_update_mul B (x B) i z'
  have hB' : Function.update B i z' = B' := by
    simp only [B, B', Function.update_idem]
  have hBi : B i = z := Function.update_self i z b
  rw [hB', hBi] at e1 e2
  rcases hzz'.lt_or_eq with hlt | rfl
  · by_contra hcon
    have := not_le.1 hcon
    nlinarith
  · exact le_rfl

/-- A welfare-maximizing allocation rule exists for every finite nonempty feasible set. -/
theorem exists_isWelfareMaximizing {X : Set (ι → ℝ)} (hX : X.Finite) (hne : X.Nonempty) :
    ∃ x, IsWelfareMaximizing X x := by
  have : ∀ b : ι → ℝ, ∃ y ∈ X, ∀ y' ∈ X, ∑ i, b i * y' i ≤ ∑ i, b i * y i := by
    intro b
    obtain ⟨y, hy, hmax⟩ := hX.toFinset.exists_max_image (fun y => ∑ i, b i * y i)
      (hX.toFinset_nonempty.2 hne)
    exact ⟨y, hX.mem_toFinset.1 hy, fun y' hy' => hmax y' (hX.mem_toFinset.2 hy')⟩
  choose x hxX hxmax using this
  exact ⟨x, fun b _ => ⟨hxX b, hxmax b⟩⟩

end Welfare

end Cslib.GameTheory.SingleParameter
