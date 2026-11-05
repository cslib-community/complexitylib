/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Maximin share through complete partitions

The goods max-min and chores min-max benchmarks of [EzraGarbuz2027],
Section 1.1 (PDF pp. 3–5), expressed by comparison with every complete partition.
An allocation assigns every item to one agent; empty fibers are allowed.
For finite nonempty agent sets, the partition-comparison predicates mean exactly
that the received value is at least goods MMS, or the cost is at most chores MMS.
Existence budgets range over all nonnegative real additive instances with a fixed
agent population and an upper item-count bound.

## Main definitions

- `bundleValue`: additive value of a complete allocation's fiber.
- `GoodsMMSAllocation`: exact goods MMS through all competing partitions.
- `ChoresMMSAllocation`: exact chores MMS through all competing partitions.
- `GoodsExistenceBudget`: universal existence for nonnegative real additive goods.
- `ChoresExistenceBudget`: universal existence for nonnegative real additive chores.
-/

public section

open scoped BigOperators

namespace Cslib.FairDivision

/-- Additive value of the complete fiber assigned to an agent. -/
@[expose] noncomputable def bundleValue {Item Agent : Type*} [Fintype Item] [DecidableEq Agent]
    (v : Item → ℝ) (a : Item → Agent) (i : Agent) : ℝ :=
  ∑ g ∈ Finset.univ.filter (fun g => a g = i), v g

/-- Every competing partition has a bundle worth at most the recipient's bundle;
this is exactly the goods MMS condition, quantified over all partitions. -/
@[expose] def GoodsMMSAllocation {Item Agent : Type*} [Fintype Item] [DecidableEq Agent]
    (v : Agent → Item → ℝ) (a : Item → Agent) : Prop :=
  ∀ i (p : Item → Agent), ∃ j, bundleValue (v i) p j ≤ bundleValue (v i) a i

/-- Every competing partition has a bundle costing at least the recipient's bundle;
this is exactly the chores MMS condition, quantified over all partitions. -/
@[expose] def ChoresMMSAllocation {Item Agent : Type*} [Fintype Item] [DecidableEq Agent]
    (v : Agent → Item → ℝ) (a : Item → Agent) : Prop :=
  ∀ i (p : Item → Agent), ∃ j, bundleValue (v i) a i ≤ bundleValue (v i) p j

/-- A universal goods MMS existence guarantee with at most m items and exactly
n agents, over nonnegative real additive values. -/
@[expose] def GoodsExistenceBudget (n m : ℕ) : Prop :=
  ∀ (Item Agent : Type) [Fintype Item] [Fintype Agent] [DecidableEq Agent],
    Fintype.card Agent = n → Fintype.card Item ≤ m →
    ∀ v : Agent → Item → ℝ, (∀ i g, 0 ≤ v i g) → ∃ a, GoodsMMSAllocation v a

/-- The corresponding universal existence guarantee for nonnegative real costs. -/
@[expose] def ChoresExistenceBudget (n m : ℕ) : Prop :=
  ∀ (Item Agent : Type) [Fintype Item] [Fintype Agent] [DecidableEq Agent],
    Fintype.card Agent = n → Fintype.card Item ≤ m →
    ∀ v : Agent → Item → ℝ, (∀ i g, 0 ≤ v i g) → ∃ a, ChoresMMSAllocation v a

end Cslib.FairDivision
