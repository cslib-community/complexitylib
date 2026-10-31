/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Complexity.Foundations.Data.List.Boole
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Fintype.BigOperators

/-!
# Partition functions of weighted constraint satisfaction problems

A weighting `wt : Rel → List D → ℕ` reads each relation symbol as a function from local
assignments to natural numbers. The partition function of a CSP instance `F : CSP Rel V`
sums, over the assignments of the variables occurring in `F` to the finite domain `D`, the product
of the weights of the constraints at their scopes:
`F.partitionFunction wt = ∑ σ, ∏ (R, vs) ∈ F, wt R (vs.map σ)`.

With `0/1` weights this is the model count of the relation semantics
(`CSP.partitionFunction_boole`). Weighted counting problems such as the hard-core model, or the
number of perfect matchings as a Holant problem with edge variables, are instances with other
weightings.

## Main definitions

* `Cslib.Logic.PL.CSP.weight`: the product of the constraint weights at an assignment.
* `Cslib.Logic.PL.CSP.partitionFunction`: the sum of the weights over the assignments of the
  occurring variables.

## Main results

* `Cslib.Logic.PL.CSP.partitionFunction_boole`: with `0/1` weights it is `CSP.modelCount`.
* `Cslib.Logic.PL.CSP.partitionFunction_le`: it is at most `|D| ^ n * W ^ m` when every weight is
  at most `W`, for `n` variables and `m` constraints.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V D : Type*}

/-- The weight of an assignment `σ`: the product over the constraints `(R, vs)` of `F` of
`wt R (vs.map σ)`. -/
@[expose] def weight (wt : Rel → List D → ℕ) (F : CSP Rel V) (σ : V → D) : ℕ :=
  (F.map fun c => wt c.1 (c.2.map σ)).prod

variable [DecidableEq V] [Fintype D] [Inhabited D]

/-- **The partition function** of a weighted CSP instance: the sum of `F.weight wt σ` over the
assignments `σ` of the variables occurring in `F` (extended by `default` elsewhere). -/
@[expose] def partitionFunction (wt : Rel → List D → ℕ) (F : CSP Rel V) : ℕ :=
  ∑ σ : F.vars.toFinset → D,
    F.weight wt fun v => if h : v ∈ F.vars.toFinset then σ ⟨v, h⟩ else default

/-- **With `0/1` weights the partition function is the model count** of the relation
semantics. -/
theorem partitionFunction_boole (sem : Rel → List D → Bool) (F : CSP Rel V) :
    F.partitionFunction (fun R w => if sem R w then 1 else 0) = F.modelCount sem := by
  rw [partitionFunction, modelCount, modelCountOn, Finset.card_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [weight, List.prod_map_boole]
  exact if_congr List.all_eq_true.symm rfl rfl

/-- **The partition function is at most `|D| ^ n * W ^ m`** when every weight at a local
assignment of the right length is at most `W`. -/
theorem partitionFunction_le {wt : Rel → List D → ℕ} {F : CSP Rel V} {W : ℕ}
    (hW : ∀ c ∈ F, ∀ w : List D, w.length = c.2.length → wt c.1 w ≤ W) :
    F.partitionFunction wt ≤ Fintype.card D ^ F.numVars * W ^ F.length := by
  rw [partitionFunction]
  refine (Finset.sum_le_card_nsmul _ _ (W ^ F.length) fun σ _ => ?_).trans ?_
  · rw [weight]
    refine (List.prod_le_pow_length _ W fun x hx => ?_).trans_eq (by rw [List.length_map])
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact hW c hc _ (List.length_map _)
  · rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, numVars, nsmul_eq_mul, Nat.cast_id]

end Cslib.Logic.PL.CSP
