/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Monotone.Basic
import CslibFrontier.Foundations.Data.Finset.ApplyUpdate
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

General valuations and the VCG mechanism use the separate structure `Cslib.GameTheory.Mechanism`
in `CslibFrontier.GameTheory.Mechanism.VCG`. Its incentive predicates range over all real
valuation functions, whereas the ones here range over the restricted domain `v · xᵢ`. No bridge
between the two models is proved yet.

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
* `SingleParameter.IsTruthfulOn X P s`: one-dimensional incentive compatibility of an allocation
  curve `X` and a payment curve `P` on a set of types `s`.
* `SingleParameter.IsWelfareMaximizing`: on every nonnegative bid profile the rule picks a feasible
  allocation maximizing the reported welfare `∑ bᵢ xᵢ`.
* `SingleParameter.IsVirtualWelfareMaximizing`: the same for the virtual welfare `∑ φᵢ(bᵢ) xᵢ`
  (Lecture 5, §3.1); welfare maximization is the case `φᵢ = id`.

## Main results

* `SingleParameter.IsTruthfulOn.monotoneOn`: incentive-compatible allocation curves are monotone
  (the "payment difference sandwich", Lecture 3 (4)).
* `SingleParameter.Mechanism.IsDSIC.isTruthfulOn`, `SingleParameter.Mechanism.IsDSIC.isMonotone`:
  along one bidder's own bid a DSIC mechanism is incentive compatible on `[0, ∞)`, so DSIC
  allocation rules are monotone; `IsImplementable.isMonotone` restates it.
* `SingleParameter.IsVirtualWelfareMaximizing.isMonotone`: when every `φᵢ` is strictly increasing,
  every virtual-welfare-maximizing allocation rule, with any tie-breaking, is monotone.
* `SingleParameter.IsWelfareMaximizing.isMonotone`: every welfare-maximizing allocation rule, with
  any tie-breaking, is monotone.
* `SingleParameter.exists_isWelfareMaximizing`: a welfare-maximizing rule exists for every finite
  nonempty feasible set.

The converse direction of Myerson's Lemma and the payment formula are in
`CslibFrontier.GameTheory.Mechanism.Myerson`.

## References

* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
* [T. Roughgarden, *Twenty Lectures on Algorithmic Game Theory*][Roughgarden2016]
* [R. B. Myerson, *Optimal auction design*][Myerson1981]
* [J. D. Hartline, *Mechanism Design and Approximation*][Hartline2021]
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

/-- One-dimensional incentive compatibility on `s`: a type `v ∈ s` facing the allocation curve `X`
and payment curve `P` prefers its own outcome to that of any other type `w ∈ s`,
`v X(w) − P(w) ≤ v X(v) − P(v)`. With `s = Ici 0` and the curves of one bidder's own bid this is
DSIC (`Mechanism.IsDSIC.isTruthfulOn`); for interim rules it is the condition of [Hartline2021],
Proposition 2.4.1. -/
@[expose] def IsTruthfulOn (X P : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ v ∈ s, ∀ w ∈ s, v * X w - P w ≤ v * X v - P v

/-- Incentive-compatible allocation curves are monotone: adding the constraints for `v` and `w`
gives `(v − w)(X(v) − X(w)) ≥ 0` (the "payment difference sandwich", [Roughgarden2013CS364A],
Lecture 3, (4)). -/
theorem IsTruthfulOn.monotoneOn {X P : ℝ → ℝ} {s : Set ℝ} (hT : IsTruthfulOn X P s) :
    MonotoneOn X s := by
  intro w hw v hv hwv
  have h1 := hT v hv w hw
  have h2 := hT w hw v hv
  by_contra hlt'
  have hlt := not_le.1 hlt'
  rcases hwv.lt_or_eq with hwv' | rfl
  · nlinarith
  · exact lt_irrefl _ hlt

variable {ι : Type*}

section DecidableEq

variable [DecidableEq ι]

/-- Replacing one entry of a nonnegative bid profile by a nonnegative bid keeps it nonnegative. -/
theorem update_nonneg {b : ι → ℝ} (hb : 0 ≤ b) (i : ι) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ Function.update b i z :=
  le_update_iff.2 ⟨hz, fun j _ => hb j⟩

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

/-- Along one bidder's own bid, with the others' nonnegative bids fixed, the allocation and payment
curves of a DSIC mechanism are incentive compatible on `[0, ∞)`. -/
theorem Mechanism.IsDSIC.isTruthfulOn {M : Mechanism ι} (hM : M.IsDSIC) (i : ι) {b : ι → ℝ}
    (hb : 0 ≤ b) :
    IsTruthfulOn (fun z => M.allocation (Function.update b i z) i)
      (fun z => M.payment (Function.update b i z) i) (Set.Ici 0) :=
  fun _ hv _ hz => hM.utility_update_le i hb hv hz

/-- **Myerson's Lemma, necessity** ([Roughgarden2013CS364A], Lecture 3, Theorem 4.3 (a), "only
if"): the allocation rule of a DSIC mechanism is monotone. Adding the two swap inequalities for
bids `z ≤ y` gives `(y − z)(x(y) − x(z)) ≥ 0` (`IsTruthfulOn.monotoneOn`). -/
theorem Mechanism.IsDSIC.isMonotone {M : Mechanism ι} (hM : M.IsDSIC) :
    IsMonotone M.allocation :=
  fun i _ hb => (hM.isTruthfulOn i hb).monotoneOn

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

/-- `x` maximizes **virtual welfare** `∑ᵢ φᵢ(bᵢ) yᵢ` over the feasible allocations `X` at every
nonnegative bid profile ([Roughgarden2013CS364A], Lecture 5, §3.1). Ties may be broken
arbitrarily. Welfare maximization (`IsWelfareMaximizing`) is the case `φᵢ = id`. -/
@[expose] def IsVirtualWelfareMaximizing (φ : ι → ℝ → ℝ) (X : Set (ι → ℝ))
    (x : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ b, 0 ≤ b → x b ∈ X ∧ ∀ y ∈ X, ∑ i, φ i (b i) * y i ≤ ∑ i, φ i (b i) * x b i

/-- Changing bidder `i`'s bid to `z` only changes the `i`-th term of the virtual welfare of a fixed
allocation `y`. -/
private theorem sum_update_weight [DecidableEq ι] (φ : ι → ℝ → ℝ) (b y : ι → ℝ) (i : ι) (z : ℝ) :
    ∑ j, φ j (Function.update b i z j) * y j =
      φ i z * y i + ∑ j ∈ Finset.univ.erase i, φ j (b j) * y j :=
  Finset.sum_apply_update_of_mem (Finset.mem_univ i) (fun j c => φ j c * y j) b z

/-- **Virtual-welfare maximization is monotone** when every `φᵢ` is strictly increasing on
`[0, ∞)`, whatever the tie-breaking ([Roughgarden2013CS364A], Lecture 5, §3.1). Comparing the
optimality of `x(z, b₋ᵢ)` and of `x(z', b₋ᵢ)` against each other gives
`(φᵢ(z') − φᵢ(z))(xᵢ(z', b₋ᵢ) − xᵢ(z, b₋ᵢ)) ≥ 0`. -/
theorem IsVirtualWelfareMaximizing.isMonotone [DecidableEq ι] {φ : ι → ℝ → ℝ}
    {X : Set (ι → ℝ)} {x : (ι → ℝ) → ι → ℝ} (hx : IsVirtualWelfareMaximizing φ X x)
    (hφ : ∀ i, StrictMonoOn (φ i) (Set.Ici 0)) : IsMonotone x := by
  intro i b hb z hz z' hz' hzz'
  change x (Function.update b i z) i ≤ x (Function.update b i z') i
  rcases hzz'.lt_or_eq with hlt | rfl
  · have h1 := (hx _ (update_nonneg hb i hz)).2 _ (hx _ (update_nonneg hb i hz')).1
    have h2 := (hx _ (update_nonneg hb i hz')).2 _ (hx _ (update_nonneg hb i hz)).1
    simp only [sum_update_weight φ b _ i] at h1 h2
    have hφlt := hφ i hz hz' hlt
    by_contra hcon
    have := lt_of_not_ge hcon
    nlinarith
  · exact le_rfl

/-- Every welfare-maximizing allocation rule is monotone, whatever its tie-breaking: this is
`IsVirtualWelfareMaximizing.isMonotone` with `φᵢ = id`, i.e. optimality of `x(z, b₋ᵢ)` and of
`x(z', b₋ᵢ)` against each other gives `(z' − z)(xᵢ(z', b₋ᵢ) − xᵢ(z, b₋ᵢ)) ≥ 0`. With Myerson's
Lemma this makes welfare maximization implementable in every single-parameter environment
([Roughgarden2013CS364A], Lecture 4, §1.2–1.3, for knapsack auctions). -/
theorem IsWelfareMaximizing.isMonotone [DecidableEq ι] {X : Set (ι → ℝ)}
    {x : (ι → ℝ) → ι → ℝ} (hx : IsWelfareMaximizing X x) : IsMonotone x :=
  IsVirtualWelfareMaximizing.isMonotone (φ := fun _ => id) hx fun _ => strictMono_id.strictMonoOn _

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
