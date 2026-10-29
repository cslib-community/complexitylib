/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.PartialAssignment
public import Complexity.Logics.Propositional.CNF
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# The random process AssignSL

Hertli's analysis of PPSZ on general satisfiable formulas weights the satisfying assignments of a
formula by the output distribution of a random process, AssignSL
[Hertli, Definition 12 (p. 6)][Hertli2011]: starting from a partial assignment `τ`, repeatedly
pick a uniformly random *satisfying literal* `x = b`, one whose addition still leaves a
satisfying extension, and add it, until every variable is assigned. This file defines the satisfying
literals and the output distribution, and proves the properties used by the cost-function
induction of [Hertli, §3][Hertli2011]. Nothing here depends on PPSZ itself.

The process starts from the partial assignment `τ`. Its output probability `assignProb φ τ α` of
a total assignment `α` is defined by recursion on the number of unassigned variables
(`assignProb_of_free_eq_empty`, `assignProb_eq_sum`). It is a probability distribution on
the satisfying extensions of `τ` (`assignProb_nonneg`, `sum_assignProb`, `assignProb_pos_iff`).
The recursion can be rewritten as a sum over the unassigned variables
[Hertli, Observation 13 (p. 7)][Hertli2011] (`card_satLits_mul_assignProb`), and adding a literal
of `α` never lowers the probability of `α`, the first statement of
[Hertli, Lemma 16 (p. 7)][Hertli2011] (`assignProb_le_assignProb_update`).

The unassigned variables of `τ` are its free coordinates `Cslib.BitString.PartialAssignment.free`,
and the extension condition is `Cslib.BitString.PartialAssignment.Agrees`.

## Main definitions

* `Cslib.Complexity.PPSZ.IsSatExtension`: a total assignment extends a partial one and satisfies
  the formula.
* `Cslib.Complexity.PPSZ.SatLit`, `Cslib.Complexity.PPSZ.satLits`: the satisfying literals.
* `Cslib.Complexity.PPSZ.assignProb`: the output distribution of AssignSL.

## Main results

* `Cslib.Complexity.PPSZ.card_free_le_card_satLits`: with a satisfying extension, there are
  at least as many satisfying literals as unassigned variables (and at most twice as many,
  `card_satLits_le`).
* `Cslib.Complexity.PPSZ.sum_assignProb`: AssignSL is a probability distribution.
* `Cslib.Complexity.PPSZ.assignProb_pos_iff`: its support is the set of satisfying extensions.
* `Cslib.Complexity.PPSZ.card_satLits_mul_assignProb`: Observation 13 of Hertli.
* `Cslib.Complexity.PPSZ.assignProb_le_assignProb_update`: the first statement of Lemma 16 of
  Hertli.

## Implementation notes

[Hertli][Hertli2011] restricts the formula by each chosen literal, so that the process runs on a
shrinking set of variables, and lets `p(F, α)` ignore the values of `α` outside the variables of
`F`. Here the formula stays fixed and the process extends a partial assignment
`τ : Fin n → Option Bool`, as PPSZ does (`Cslib.Complexity.PPZ.runWith`). Accordingly
`assignProb φ τ α` is the probability that the process outputs exactly the total assignment `α`,
which is `0` unless `α` extends `τ`; the literals of `α` in [Hertli][Hertli2011] are the updates
of `τ` by `α` on its unassigned variables.

## References

* [T. Hertli, *3-SAT faster and simpler*][Hertli2011]
-/

@[expose] public section

namespace Cslib.Complexity.PPSZ

open Cslib.Logic.PL Finset Function
open Cslib.BitString.PartialAssignment (Agrees free mem_free free_update)

variable {n : ℕ}

/-! ### Satisfying extensions and satisfying literals -/

/-- `σ` is a **satisfying extension** of the partial assignment `τ`: it agrees with `τ` wherever
`τ` is defined (`Cslib.BitString.PartialAssignment.Agrees`) and satisfies `φ`. -/
def IsSatExtension (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (σ : Fin n → Bool) : Prop :=
  Agrees τ σ ∧ φ.eval σ = true

instance (φ : CNF (Fin n)) (τ : Fin n → Option Bool) : DecidablePred (IsSatExtension φ τ) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The literal `y = b` is a **satisfying literal** under `τ`
[Hertli, Definition 8 (p. 5)][Hertli2011]: `y` is unassigned and some satisfying extension of `τ`
sets `y` to `b`. Equivalently, `τ` updated by `y = b` has a satisfying extension
(`satLit_iff_update`). -/
def SatLit (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (y : Fin n) (b : Bool) : Prop :=
  τ y = none ∧ ∃ σ, IsSatExtension φ τ σ ∧ σ y = b

instance (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (y : Fin n) (b : Bool) :
    Decidable (SatLit φ τ y b) :=
  inferInstanceAs (Decidable (_ ∧ ∃ _ : Fin n → Bool, _ ∧ _))

/-- The **satisfying literals** under `τ` [Hertli, Definition 8 (p. 5)][Hertli2011], as pairs of a
variable and a value. -/
def satLits (φ : CNF (Fin n)) (τ : Fin n → Option Bool) : Finset (Fin n × Bool) :=
  univ.filter fun l => SatLit φ τ l.1 l.2

@[simp]
theorem mem_satLits {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {l : Fin n × Bool} :
    l ∈ satLits φ τ ↔ SatLit φ τ l.1 l.2 := by
  simp [satLits]

/-- Assigning an unassigned variable lowers the number of unassigned variables by one. -/
theorem card_free_update {τ : Fin n → Option Bool} {y : Fin n} (hy : τ y = none) (b : Bool) :
    (free (update τ y (some b))).card + 1 = (free τ).card := by
  rw [free_update, card_erase_add_one (mem_free.mpr hy)]

/-- Satisfying extensions of `τ` updated by an unassigned `y = b` are the satisfying extensions of
`τ` that set `y` to `b`. -/
theorem isSatExtension_update_iff {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {y : Fin n}
    (hy : τ y = none) {b : Bool} {σ : Fin n → Bool} :
    IsSatExtension φ (update τ y (some b)) σ ↔ IsSatExtension φ τ σ ∧ σ y = b := by
  constructor
  · rintro ⟨hext, hsat⟩
    refine ⟨⟨fun z c hz => hext z c ?_, hsat⟩, hext y b (update_self y _ τ)⟩
    rwa [update_of_ne (by rintro rfl; rw [hy] at hz; cases hz)]
  · rintro ⟨⟨hext, hsat⟩, hσy⟩
    refine ⟨fun z c hz => ?_, hsat⟩
    by_cases hzy : z = y
    · subst hzy
      rw [update_self, Option.some.injEq] at hz
      rw [hσy, hz]
    · rw [update_of_ne hzy] at hz
      exact hext z c hz

/-- `y = b` is a satisfying literal exactly when `y` is unassigned and `τ` updated by `y = b` has
a satisfying extension, the form of [Hertli, Definition 8 (p. 5)][Hertli2011]. -/
theorem satLit_iff_update {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {y : Fin n} {b : Bool} :
    SatLit φ τ y b ↔ τ y = none ∧ ∃ σ, IsSatExtension φ (update τ y (some b)) σ := by
  constructor
  · rintro ⟨hy, σ, hσ, hσy⟩
    exact ⟨hy, σ, (isSatExtension_update_iff hy).mpr ⟨hσ, hσy⟩⟩
  · rintro ⟨hy, σ, hσ⟩
    exact ⟨hy, σ, (isSatExtension_update_iff hy).mp hσ⟩

/-- After setting a satisfying literal, a satisfying extension remains. -/
theorem SatLit.update_isSatExtension {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {y : Fin n}
    {b : Bool} (h : SatLit φ τ y b) : ∃ σ, IsSatExtension φ (update τ y (some b)) σ :=
  (satLit_iff_update.mp h).2

/-- There are at most two satisfying literals per unassigned variable. -/
theorem card_satLits_le (φ : CNF (Fin n)) (τ : Fin n → Option Bool) :
    (satLits φ τ).card ≤ 2 * (free τ).card := by
  calc (satLits φ τ).card ≤ (free τ ×ˢ (univ : Finset Bool)).card :=
        card_le_card fun l hl =>
          mem_product.mpr ⟨mem_free.mpr (mem_satLits.mp hl).1, mem_univ _⟩
    _ = 2 * (free τ).card := by rw [card_product, card_univ, Fintype.card_bool, mul_comm]

/-- **At least one satisfying literal per unassigned variable**, after
[Hertli, p. 5][Hertli2011]: if `τ` has a satisfying extension `σ`, every unassigned `y = σ y` is
a satisfying literal. -/
theorem card_free_le_card_satLits {φ : CNF (Fin n)} {τ : Fin n → Option Bool}
    (h : ∃ σ, IsSatExtension φ τ σ) : (free τ).card ≤ (satLits φ τ).card := by
  obtain ⟨σ, hσ⟩ := h
  refine card_le_card_of_injOn (fun y => (y, σ y)) (fun y hy => ?_)
    fun _ _ _ _ h => congrArg Prod.fst h
  exact mem_satLits.mpr ⟨mem_free.mp hy, σ, hσ, rfl⟩

/-- With a satisfying extension and an unassigned variable, there is a satisfying literal. -/
theorem card_satLits_pos {φ : CNF (Fin n)} {τ : Fin n → Option Bool}
    (h : ∃ σ, IsSatExtension φ τ σ) (hne : (free τ).Nonempty) :
    0 < (satLits φ τ).card :=
  (card_pos.mpr hne).trans_le (card_free_le_card_satLits h)

/-- Assigning an unassigned variable only removes satisfying literals, among them the literals on
that variable. -/
theorem satLits_update_subset {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {y : Fin n}
    (hy : τ y = none) (b : Bool) :
    satLits φ (update τ y (some b)) ⊆ (satLits φ τ).erase (y, b) := by
  intro l hl
  obtain ⟨hl1, σ, hσ, hσl⟩ := mem_satLits.mp hl
  have hne : l.1 ≠ y := by
    rintro h
    rw [h, update_self] at hl1
    cases hl1
  rw [update_of_ne hne] at hl1
  exact mem_erase.mpr ⟨fun h => hne (congrArg Prod.fst h),
    mem_satLits.mpr ⟨hl1, σ, ((isSatExtension_update_iff hy).mp hσ).1, hσl⟩⟩

/-- Setting a satisfying literal removes at least that literal from the satisfying literals. -/
theorem card_satLits_update_lt {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {y : Fin n} {b : Bool}
    (h : SatLit φ τ y b) : (satLits φ (update τ y (some b))).card < (satLits φ τ).card :=
  (card_le_card (satLits_update_subset h.1 b)).trans_lt
    (card_erase_lt_of_mem (mem_satLits.mpr h))

/-- **Induction on the unassigned variables**: a property holds for every partial assignment if it
holds when no variable is unassigned, and holds for `τ` whenever it holds for every update of `τ`
on an unassigned variable. -/
theorem free_induction {P : (Fin n → Option Bool) → Prop}
    (base : ∀ τ, free τ = ∅ → P τ)
    (step : ∀ τ, (free τ).Nonempty → (∀ y b, τ y = none → P (update τ y (some b))) → P τ)
    (τ : Fin n → Option Bool) : P τ := by
  obtain ⟨k, hk⟩ : ∃ k, (free τ).card = k := ⟨_, rfl⟩
  induction k generalizing τ with
  | zero => exact base τ (card_eq_zero.mp hk)
  | succ k ih =>
    refine step τ (card_pos.mp (by omega)) fun y b hy => ih _ ?_
    have := card_free_update hy b
    omega

/-! ### The output distribution of AssignSL -/

/-- `assignProb` with an explicit bound `k` on the recursion depth; `assignProb` takes `k` to be
the number of unassigned variables. -/
noncomputable def assignProbAux (φ : CNF (Fin n)) :
    ℕ → (Fin n → Option Bool) → (Fin n → Bool) → ℝ
  | 0, τ, α => if IsSatExtension φ τ α then 1 else 0
  | k + 1, τ, α => ((satLits φ τ).card : ℝ)⁻¹ *
      ∑ l ∈ satLits φ τ, assignProbAux φ k (update τ l.1 (some l.2)) α

/-- **The output distribution of AssignSL** [Hertli, Definition 12 (p. 6)][Hertli2011]: the
probability that the process started at `τ`, which repeatedly sets a uniformly random satisfying
literal until no variable is unassigned, outputs the total assignment `α`. When no variable is
unassigned, it is `1` if `α` is a satisfying extension of `τ` and `0` otherwise; when some
variable is unassigned and `τ` has no satisfying extension, there are no satisfying literals and
it is `0`. -/
noncomputable def assignProb (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (α : Fin n → Bool) : ℝ :=
  assignProbAux φ (free τ).card τ α

/-- When no variable is unassigned, AssignSL outputs `α` exactly when `α` is a satisfying
extension. -/
theorem assignProb_of_free_eq_empty {φ : CNF (Fin n)} {τ : Fin n → Option Bool}
    (h : free τ = ∅) (α : Fin n → Bool) :
    assignProb φ τ α = if IsSatExtension φ τ α then 1 else 0 := by
  rw [assignProb, h, card_empty, assignProbAux]

/-- **One step of AssignSL** [Hertli, Definition 12 (p. 6)][Hertli2011]: while some variable is
unassigned, the process sets a uniformly random satisfying literal. -/
theorem assignProb_eq_sum {φ : CNF (Fin n)} {τ : Fin n → Option Bool}
    (h : (free τ).Nonempty) (α : Fin n → Bool) :
    assignProb φ τ α = ((satLits φ τ).card : ℝ)⁻¹ *
      ∑ l ∈ satLits φ τ, assignProb φ (update τ l.1 (some l.2)) α := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (card_ne_zero.mpr h)
  rw [assignProb, hk, assignProbAux]
  refine congrArg _ (sum_congr rfl fun l hl => ?_)
  have := card_free_update (mem_satLits.mp hl).1 l.2
  rw [assignProb, show (free (update τ l.1 (some l.2))).card = k by omega]

/-- Output probabilities are nonnegative. -/
theorem assignProb_nonneg (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (α : Fin n → Bool) :
    0 ≤ assignProb φ τ α := by
  induction τ using free_induction with
  | base τ hτ =>
    rw [assignProb_of_free_eq_empty hτ]
    split_ifs <;> norm_num
  | step τ hne ih =>
    rw [assignProb_eq_sum hne]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (sum_nonneg fun l hl => ih _ _ (mem_satLits.mp hl).1)

/-- **AssignSL outputs satisfying extensions** [Hertli, Observation 13 (p. 7)][Hertli2011]. -/
theorem isSatExtension_of_assignProb_ne_zero {φ : CNF (Fin n)} {τ : Fin n → Option Bool}
    {α : Fin n → Bool} (h : assignProb φ τ α ≠ 0) : IsSatExtension φ τ α := by
  induction τ using free_induction with
  | base τ hτ =>
    rw [assignProb_of_free_eq_empty hτ] at h
    by_contra hc
    exact h (ite_eq_right hc)
  | step τ hne ih =>
    rw [assignProb_eq_sum hne] at h
    obtain ⟨l, hl, hl0⟩ := exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h)
    have hy := (mem_satLits.mp hl).1
    exact ((isSatExtension_update_iff hy).mp (ih _ _ hy hl0)).1

/-- AssignSL never outputs an assignment that is not a satisfying extension. -/
theorem assignProb_eq_zero {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {α : Fin n → Bool}
    (h : ¬ IsSatExtension φ τ α) : assignProb φ τ α = 0 :=
  not_not.mp fun h' => h (isSatExtension_of_assignProb_ne_zero h')

/-- **The support of AssignSL** [Hertli, Observation 13 (p. 7)][Hertli2011]: the process started
at `τ` outputs `α` with positive probability exactly when `α` is a satisfying extension of `τ`. -/
theorem assignProb_pos_iff {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {α : Fin n → Bool} :
    0 < assignProb φ τ α ↔ IsSatExtension φ τ α := by
  refine ⟨fun h => isSatExtension_of_assignProb_ne_zero h.ne', fun h => ?_⟩
  induction τ using free_induction with
  | base τ hτ =>
    rw [assignProb_of_free_eq_empty hτ, ite_eq_left h]
    exact one_pos
  | step τ hne ih =>
    rw [assignProb_eq_sum hne]
    obtain ⟨y, hy⟩ := hne
    have hy' := mem_free.mp hy
    refine mul_pos (inv_pos.mpr (Nat.cast_pos.mpr (card_satLits_pos ⟨α, h⟩ ⟨y, hy⟩)))
      (sum_pos' (fun l hl => assignProb_nonneg _ _ _) ⟨(y, α y), ?_, ?_⟩)
    · exact mem_satLits.mpr ⟨hy', α, h, rfl⟩
    · exact ih y (α y) hy' ((isSatExtension_update_iff hy').mpr ⟨h, rfl⟩)

/-- **AssignSL is a probability distribution** [Hertli, Observation 13 (p. 7)][Hertli2011]: if
`τ` has a satisfying extension, the output probabilities sum to `1`. -/
theorem sum_assignProb {φ : CNF (Fin n)} {τ : Fin n → Option Bool}
    (h : ∃ σ, IsSatExtension φ τ σ) : ∑ α, assignProb φ τ α = 1 := by
  induction τ using free_induction with
  | base τ hτ =>
    obtain ⟨σ, hσ⟩ := h
    have key : ∀ α, IsSatExtension φ τ α → α = σ := fun α hα => funext fun x => by
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp fun hx =>
        notMem_empty x (hτ ▸ mem_free.mpr hx)
      rw [hα.1 x c hc, hσ.1 x c hc]
    rw [sum_eq_single σ (fun α _ hα => ?_) (fun h => absurd (mem_univ σ) h),
      assignProb_of_free_eq_empty hτ, ite_eq_left hσ]
    rw [assignProb_of_free_eq_empty hτ, ite_eq_right fun h => hα (key α h)]
  | step τ hne ih =>
    have hs : ((satLits φ τ).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (card_satLits_pos h hne).ne'
    rw [sum_congr rfl fun α _ => assignProb_eq_sum hne α, ← mul_sum, sum_comm,
      sum_congr rfl fun l hl =>
        ih _ _ (mem_satLits.mp hl).1 (mem_satLits.mp hl).update_isSatExtension,
      sum_const, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hs]

/-- **Observation 13 of [Hertli, p. 7][Hertli2011]**, multiplied out: `s · R(τ)(α)` is the sum of
`R(τ[y ↦ α y])(α)` over the unassigned variables `y`, where `R` is the output distribution of
AssignSL and `s` the number of satisfying literals. -/
theorem card_satLits_mul_assignProb (φ : CNF (Fin n)) (τ : Fin n → Option Bool)
    (α : Fin n → Bool) :
    ((satLits φ τ).card : ℝ) * assignProb φ τ α =
      ∑ y ∈ free τ, assignProb φ (update τ y (some (α y))) α := by
  by_cases hα : IsSatExtension φ τ α
  swap
  · rw [assignProb_eq_zero hα, mul_zero]
    exact (sum_eq_zero fun y hy => assignProb_eq_zero fun h =>
      hα ((isSatExtension_update_iff (mem_free.mp hy)).mp h).1).symm
  rcases (free τ).eq_empty_or_nonempty with hτ | hne
  · have : (satLits φ τ).card = 0 := by
      have := card_satLits_le φ τ
      rw [hτ, card_empty] at this
      omega
    rw [hτ, sum_empty, this, Nat.cast_zero, zero_mul]
  have hs : ((satLits φ τ).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (card_satLits_pos ⟨α, hα⟩ hne).ne'
  let e : Fin n ↪ Fin n × Bool := ⟨fun y => (y, α y), fun _ _ h => congrArg Prod.fst h⟩
  rw [assignProb_eq_sum hne, mul_inv_cancel_left₀ hs]
  refine Eq.trans ?_ (sum_map (free τ) e fun l => assignProb φ (update τ l.1 (some l.2)) α)
  refine (sum_subset (fun l hl => ?_) fun l hl hl' => ?_).symm
  · obtain ⟨y, hy, rfl⟩ := mem_map.mp hl
    exact mem_satLits.mpr ⟨mem_free.mp hy, α, hα, rfl⟩
  · refine assignProb_eq_zero fun h => hl' (mem_map.mpr ⟨l.1, ?_, ?_⟩)
    · exact mem_free.mpr (mem_satLits.mp hl).1
    · exact Prod.ext rfl ((isSatExtension_update_iff (mem_satLits.mp hl).1).mp h).2

/-- **Observation 13 of [Hertli, p. 7][Hertli2011]**: while some variable is unassigned,
`R(τ)(α) = (1/s) ∑_y R(τ[y ↦ α y])(α)` over the unassigned variables `y`, where `R` is the output
distribution of AssignSL and `s` the number of satisfying literals. -/
theorem assignProb_eq_inv_mul_sum {φ : CNF (Fin n)} {τ : Fin n → Option Bool}
    (h : (free τ).Nonempty) (α : Fin n → Bool) :
    assignProb φ τ α = ((satLits φ τ).card : ℝ)⁻¹ *
      ∑ y ∈ free τ, assignProb φ (update τ y (some (α y))) α := by
  rw [← card_satLits_mul_assignProb]
  rcases eq_or_ne ((satLits φ τ).card : ℝ) 0 with hs | hs
  · rw [assignProb_eq_sum h, hs, inv_zero, zero_mul, zero_mul]
  · rw [inv_mul_cancel_left₀ hs]

/-- The first statement of Lemma 16 of [Hertli, p. 7][Hertli2011] for an unassigned variable. -/
private theorem assignProb_le_assignProb_update_of_eq_none (φ : CNF (Fin n))
    (τ : Fin n → Option Bool) (α : Fin n → Bool) :
    ∀ y, τ y = none → assignProb φ τ α ≤ assignProb φ (update τ y (some (α y))) α := by
  induction τ using free_induction with
  | base τ hτ =>
    intro y hy
    exact absurd (hτ ▸ mem_free.mpr hy) (notMem_empty y)
  | step τ hne ih =>
    intro y hy
    set τ' := update τ y (some (α y))
    by_cases hα : IsSatExtension φ τ α
    swap
    · rw [assignProb_eq_zero hα]
      exact assignProb_nonneg _ _ _
    have hs : (0 : ℝ) < (satLits φ τ).card := Nat.cast_pos.mpr (card_satLits_pos ⟨α, hα⟩ hne)
    have hlt : ((satLits φ τ').card : ℝ) + 1 ≤ (satLits φ τ).card := by
      exact_mod_cast card_satLits_update_lt (b := α y) ⟨hy, α, hα, rfl⟩
    have h13 := card_satLits_mul_assignProb φ τ α
    rw [← insert_erase (mem_free.mpr hy), sum_insert (notMem_erase y _)] at h13
    have h13' := card_satLits_mul_assignProb φ τ' α
    rw [free_update] at h13'
    have hle : ∑ z ∈ (free τ).erase y, assignProb φ (update τ z (some (α z))) α ≤
        ∑ z ∈ (free τ).erase y, assignProb φ (update τ' z (some (α z))) α := by
      refine sum_le_sum fun z hz => ?_
      have hzy := ne_of_mem_erase hz
      have := ih z (α z) (mem_free.mp (mem_of_mem_erase hz)) y
        (by rw [update_of_ne (Ne.symm hzy)]; exact hy)
      rwa [update_comm hzy] at this
    have hR' := assignProb_nonneg φ τ' α
    refine le_of_mul_le_mul_left ?_ hs
    nlinarith [mul_nonneg (sub_nonneg.mpr hlt) hR']

/-- **Lemma 16 of [Hertli, p. 7][Hertli2011]**, its first statement: setting a variable to its
value in `α` does not lower the probability that AssignSL outputs `α`. Its second statement, the
equality of the probabilities and the cost inequality for a literal on a frozen variable, is not
formalized; the cost-function induction (`Cslib.Complexity.PPSZ.factorial_mul_le_succSum`) uses
only the first.

The proof is an induction on the number of unassigned variables (original). By Observation 13
(`card_satLits_mul_assignProb`), `s · R(τ)(α)` is `R(τ[y ↦ α y])(α)` plus the sum of
`R(τ[z ↦ α z])(α)` over the other unassigned `z`; by induction each of these is at most
`R(τ[y ↦ α y][z ↦ α z])(α)`, and these sum to `s' · R(τ[y ↦ α y])(α)` by Observation 13 again,
where `s' < s` (`card_satLits_update_lt`). [Hertli][Hertli2011] argues instead through the
sampling process. -/
theorem assignProb_le_assignProb_update (φ : CNF (Fin n)) (τ : Fin n → Option Bool)
    (α : Fin n → Bool) (y : Fin n) :
    assignProb φ τ α ≤ assignProb φ (update τ y (some (α y))) α := by
  rcases hy : τ y with _ | c
  · exact assignProb_le_assignProb_update_of_eq_none φ τ α y hy
  · by_cases hc : α y = c
    · rw [hc, ← hy, update_eq_self]
    · rw [assignProb_eq_zero fun h => hc (h.1 y c hy)]
      exact assignProb_nonneg _ _ _

end Cslib.Complexity.PPSZ
