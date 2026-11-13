/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.QueryCount
public import CslibFrontier.Languages.Probabilistic.Sum

/-!
# Call budgets of programs over one side of a sum

A program over `spec₁`, embedded in `spec₁ ⊕ₒ spec₂` by `OracleComp.liftLeft`, makes only left
calls. A budget for its calls therefore bounds the embedded program under any cost on the sum
that charges each left call at most its original cost (`IsCostBounded.liftLeft`); in particular,
the embedded program makes no call that a cost charging nothing on the left counts. The same
holds on the right (`IsCostBounded.liftRight`).

## Main results

* `Cslib.OracleComp.IsCostBounded.liftLeft`, `Cslib.OracleComp.IsCostBounded.liftRight`: budgets
  transfer to embedded programs.
* `Cslib.OracleComp.IsCostBounded.liftLeft_of_cost_inl_eq_zero`,
  `Cslib.OracleComp.IsCostBounded.liftRight_of_cost_inr_eq_zero`: an embedded program has zero
  cost on the other side.
-/

public section

namespace Cslib.OracleComp.IsCostBounded

universe u v

variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, v} ι₁} {spec₂ : OracleSpec.{u, v} ι₂}
  {α : Type v}

/-- A budget `n` for a left program under `cost₁` is a budget for its embedding under every cost
on the sum charging each left call `.inl q` at most `cost₁ q`. -/
theorem liftLeft {cost₁ : ι₁ → ℕ} {cost : ι₁ ⊕ ι₂ → ℕ} {program : OracleComp spec₁ α} {n : ℕ}
    (h : IsCostBounded cost₁ program n) (hcost : ∀ q, cost (.inl q) ≤ cost₁ q) :
    IsCostBounded cost (OracleComp.liftLeft (spec₂ := spec₂) program) n :=
  IsCostBounded.interpret
    (fun q => (IsCostBounded.query (spec := spec₁ ⊕ₒ spec₂) (cost := cost) (.inl q)).mono
      (hcost q)) h

/-- A budget `n` for a right program under `cost₂` is a budget for its embedding under every cost
on the sum charging each right call `.inr q` at most `cost₂ q`. -/
theorem liftRight {cost₂ : ι₂ → ℕ} {cost : ι₁ ⊕ ι₂ → ℕ} {program : OracleComp spec₂ α} {n : ℕ}
    (h : IsCostBounded cost₂ program n) (hcost : ∀ q, cost (.inr q) ≤ cost₂ q) :
    IsCostBounded cost (OracleComp.liftRight (spec₁ := spec₁) program) n :=
  IsCostBounded.interpret
    (fun q => (IsCostBounded.query (spec := spec₁ ⊕ₒ spec₂) (cost := cost) (.inr q)).mono
      (hcost q)) h

/-- A left program makes no call that a cost charging nothing on the left counts. -/
theorem liftLeft_of_cost_inl_eq_zero {cost : ι₁ ⊕ ι₂ → ℕ} (hcost : ∀ q, cost (.inl q) = 0)
    (program : OracleComp spec₁ α) :
    IsCostBounded cost (OracleComp.liftLeft (spec₂ := spec₂) program) 0 :=
  (of_forall_cost_eq_zero (cost := fun _ => 0) (fun _ => rfl) program).liftLeft
    fun q => (hcost q).le

/-- A right program makes no call that a cost charging nothing on the right counts. -/
theorem liftRight_of_cost_inr_eq_zero {cost : ι₁ ⊕ ι₂ → ℕ} (hcost : ∀ q, cost (.inr q) = 0)
    (program : OracleComp spec₂ α) :
    IsCostBounded cost (OracleComp.liftRight (spec₁ := spec₁) program) 0 :=
  (of_forall_cost_eq_zero (cost := fun _ => 0) (fun _ => rfl) program).liftRight
    fun q => (hcost q).le

end Cslib.OracleComp.IsCostBounded
