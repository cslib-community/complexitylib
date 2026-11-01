/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.Asymptotics.Ring

/-!
# Asymptotic cost bounds

`Cslib.CostIsBigO l g size cost` says that the cost of every input is bounded by one cost
function of its size, chosen before the input: some monotone, nonnegative `f` with `f =O[l] g`
satisfies `cost a ≤ f (size a)` for all `a`. This is the form of asymptotic cost specification
used by Guéneau, Charguéraud and Pottier [GueneauChargueraudPottier2018]. Because `f` is chosen
once, the statement is `∃ f, ∀ a`. Inductive reasoning with "`O(1) + O(1) = O(1)`" proves
`∀ a, ∃ c` instead, which is unsound as a cost claim. The filter makes multivariate bounds
explicit: for example, `atTop` on `ℕ × ℕ` for a bound in two size parameters.

Exact constants are proved internally and exported in this form: `CostIsBigO.of_le_nat` turns an
exact natural-number bound into an asymptotic one.

## Main definitions

* `Cslib.CostIsBigO`: a cost bounded by a monotone, nonnegative function that is `O(g)` along a
  filter.

## Main results

* `Cslib.CostIsBigO.of_le_nat`: export an exact monotone natural-number bound.
* `Cslib.CostIsBigO.mono`: a smaller cost has the same bound.
* `Cslib.CostIsBigO.trans_isBigO`: weaken the comparison function.

## References

* [A. Guéneau, A. Charguéraud and F. Pottier, *A Fistful of Dollars: Formalizing Asymptotic
  Complexity Claims via Deductive Program Verification*][GueneauChargueraudPottier2018]
-/

@[expose] public section

open Asymptotics

namespace Cslib

variable {α ι : Type*} [Preorder ι]

/-- The cost of every input `a` is at most `f (size a)` for one monotone, nonnegative cost
function `f` with `f =O[l] g`. -/
def CostIsBigO (l : Filter ι) (g : ι → ℝ) (size : α → ι) (cost : α → ℕ) : Prop :=
  ∃ f : ι → ℝ, Monotone f ∧ 0 ≤ f ∧ f =O[l] g ∧ ∀ a, (cost a : ℝ) ≤ f (size a)

namespace CostIsBigO

variable {l : Filter ι} {g : ι → ℝ} {size : α → ι} {cost : α → ℕ}

/-- An exact monotone natural-number bound that is `O(g)` gives an asymptotic cost bound. -/
theorem of_le_nat {F : ι → ℕ} (hF : Monotone F) (hO : (fun n => (F n : ℝ)) =O[l] g)
    (h : ∀ a, cost a ≤ F (size a)) : CostIsBigO l g size cost :=
  ⟨fun n => F n, fun _ _ hab => Nat.cast_le.mpr (hF hab), fun _ => Nat.cast_nonneg _, hO,
    fun a => Nat.cast_le.mpr (h a)⟩

/-- A cost below a bounded cost has the same bound. -/
theorem mono {cost' : α → ℕ} (h : CostIsBigO l g size cost) (hle : ∀ a, cost' a ≤ cost a) :
    CostIsBigO l g size cost' := by
  obtain ⟨f, hf, hf0, hO, hb⟩ := h
  exact ⟨f, hf, hf0, hO, fun a => (Nat.cast_le.mpr (hle a)).trans (hb a)⟩

/-- A cost that is `O(g)` is `O(g')` whenever `g =O[l] g'`. -/
theorem trans_isBigO {g' : ι → ℝ} (h : CostIsBigO l g size cost) (hg : g =O[l] g') :
    CostIsBigO l g' size cost := by
  obtain ⟨f, hf, hf0, hO, hb⟩ := h
  exact ⟨f, hf, hf0, hO.trans hg, hb⟩

end CostIsBigO

end Cslib
