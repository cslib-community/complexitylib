/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, next to `MeasureTheory/Group/FundamentalDomain`)

public import Complexity.Init
public import Mathlib.Algebra.Group.Subgroup.MulOpposite
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Fundamental domains of opposite subgroups

A subgroup `Γ` of a group `G` acts on `G` by left multiplication, and its opposite `Γ.op` acts by
right multiplication. Mathlib's quotient `G ⧸ Γ` and its Haar measure API use the opposite action,
while the `ZLattice` covolume API uses the subgroup itself. In a commutative group the two actions
coincide, so they have the same fundamental domains.

## Main results

* `MeasureTheory.isFundamentalDomain_op_iff`: in a commutative group, `s` is a fundamental domain
  for `Γ.op` if and only if it is one for `Γ`.
* `MeasureTheory.isAddFundamentalDomain_op_iff`: the additive version.
-/

public section

namespace MeasureTheory

variable {G : Type*} [CommGroup G] [MeasurableSpace G] {Γ : Subgroup G} {s : Set G}
  {μ : Measure G}

/-- In a commutative group, a subgroup and its opposite act by the same multiplications, so they
have the same fundamental domains. -/
@[to_additive isAddFundamentalDomain_op_iff /-- In a commutative additive group, a subgroup and its
opposite act by the same translations, so they have the same fundamental domains. -/]
theorem isFundamentalDomain_op_iff :
    IsFundamentalDomain Γ.op s μ ↔ IsFundamentalDomain Γ s μ :=
  ⟨fun h => h.preimage_of_equiv (.id μ) (Subgroup.equivOp Γ).symm.bijective fun _ _ => mul_comm _ _,
    fun h => h.preimage_of_equiv (.id μ) (Subgroup.equivOp Γ).bijective fun _ _ => mul_comm _ _⟩

end MeasureTheory
