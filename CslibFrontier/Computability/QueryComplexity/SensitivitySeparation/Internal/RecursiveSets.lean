/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveFlips
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Superquadratic sensitivity separation: recursive sets

This file packages the sensitive coordinates of individual children as finite sets of raw
coordinates, so that the sensitivity of a next-level predicate can be bounded by the size of a union
of such sets. It also proves the joint version of the flip analysis: a flip that changes the clause
of row `i` at two indices changes its target condition, or changes both gate conditions on the same
labeled edge.

## Main definitions

* `childLift`: the embedding of a set `A` of coordinates into the component `j` of `J × I`.
* `childChanges`: the raw coordinates of the child `(j, c)` whose flip changes `F q` on that child.
* `childJointChanges`: the raw coordinates of the child `(j, c)` whose flip changes both `F q` and
  `F q'` on that child.

## Main results

* `childChanges_card`: `childChanges F q x j c` has as many elements as the sensitivity of `F q` at
  the child `(j, c)`.
* `childJointChanges_card`: `childJointChanges F q q' x j c` has as many elements as the joint
  sensitivity of `F q` and `F q'` at the child `(j, c)`.
* `card_biUnion_le_mul`: a union of `A.card` sets of size at most `n` has at most `A.card * n`
  elements.
* `rowClause_joint_flip_change`: a flip changing a row clause at two indices changes its target
  condition or both gate conditions on one labeled edge.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/RecursiveSets.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- Embed a coordinate block into a specified child of a product. -/
def childLift {J I : Type} (j : J) (A : Finset I) : Finset (J × I) :=
  A.map ⟨fun a => (j, a), fun _ _ h => congrArg (fun p : J × I => p.2) h⟩

/-- A pair `p` lies in `childLift j A` iff `p.1 = j` and `p.2 ∈ A`. -/
@[simp] theorem mem_childLift {J I : Type} (j : J) (A : Finset I) (p : J × I) :
    p ∈ childLift j A ↔ p.1 = j ∧ p.2 ∈ A := by
  rcases p with ⟨k, a⟩
  unfold childLift
  rw [Finset.mem_map]
  constructor
  · rintro ⟨b, hb, hp⟩
    change (j, b) = (k, a) at hp
    cases hp
    exact ⟨rfl, hb⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩

/-- `childLift j A` has the same cardinality as `A`. -/
@[simp] theorem childLift_card {J I : Type} (j : J) (A : Finset I) :
    (childLift j A).card = A.card := Finset.card_map _

open scoped Classical in
/-- Lift the individually sensitive coordinates of a child predicate. -/
def childChanges {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    Finset ((Fin k × Fin r) × I) :=
  childLift (j, c) (Finset.univ.filter fun a =>
    F q (BitString.flipOn {a} (recursiveChild x j c)) ≠ F q (recursiveChild x j c))

open scoped Classical in
/-- Lift coordinates that simultaneously change two predicates in one child. -/
def childJointChanges {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q q' : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    Finset ((Fin k × Fin r) × I) :=
  childLift (j, c) (Finset.univ.filter fun a =>
    F q (BitString.flipOn {a} (recursiveChild x j c)) ≠ F q (recursiveChild x j c) ∧
    F q' (BitString.flipOn {a} (recursiveChild x j c)) ≠ F q' (recursiveChild x j c))

/-- The cardinality of `childChanges F q x j c` is `sensitivityAt (F q) (recursiveChild x j c)`. -/
@[simp] theorem childChanges_card {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    (childChanges F q x j c).card = sensitivityAt (F q) (recursiveChild x j c) := by
  simp [childChanges, sensitivityAt]

/-- The cardinality of `childJointChanges F q q' x j c` is
`jointSensitivityAt (F q) (F q') (recursiveChild x j c)`. -/
@[simp] theorem childJointChanges_card {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q q' : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    (childJointChanges F q q' x j c).card =
      jointSensitivityAt (F q) (F q') (recursiveChild x j c) := by
  simp [childJointChanges, jointSensitivityAt]

/-- If `(B j).card ≤ n` for every `j ∈ A`, then `(A.biUnion B).card ≤ A.card * n`. -/
theorem card_biUnion_le_mul {J I : Type} [DecidableEq I] (A : Finset J) (B : J → Finset I) (n : ℕ)
    (hn : ∀ j ∈ A, (B j).card ≤ n) : (A.biUnion B).card ≤ A.card * n := by
  calc
    (A.biUnion B).card ≤ ∑ j ∈ A, (B j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ A, n := Finset.sum_le_sum hn
    _ = A.card * n := by simp

open scoped Classical in
/-- If flipping `((j, c), a)` changes the clause of row `i` both at index `q` and at index `q'`,
then either `j = i` and the flip changes the target value of the child at `(j, c)`, or `T.Adj i j`,
`c = label i j` and the flip changes both gate values `F (gateIndex q)` and `F (gateIndex q')` of
that child. -/
theorem rowClause_joint_flip_change {k r h : ℕ} {I : Type} [DecidableEq ((Fin k × Fin r) × I)]
    (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q q' : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (c : Fin r) (a : I)
    (hc : rowClause T label F q (BitString.flipOn {((j, c), a)} x) i ≠
      rowClause T label F q x i)
    (hc' : rowClause T label F q' (BitString.flipOn {((j, c), a)} x) i ≠
      rowClause T label F q' x i) :
    (j = i ∧ F (Fin.last h) (BitString.flipOn {a} (recursiveChild x j c)) ≠
      F (Fin.last h) (recursiveChild x j c)) ∨
    (T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (BitString.flipOn {a} (recursiveChild x j c)) ≠
        F (gateIndex q) (recursiveChild x j c) ∧
      F (gateIndex q') (BitString.flipOn {a} (recursiveChild x j c)) ≠
        F (gateIndex q') (recursiveChild x j c)) := by
  rcases rowClause_flip_change T label F q x i j c a hc with ht | ⟨hij, hcl, hq⟩
  · exact Or.inl ht
  · rcases rowClause_flip_change T label F q' x i j c a hc' with ht | hg
    · exact False.elim ((T.ne_of_adj hij) ht.1.symm)
    · exact Or.inr ⟨hij, hcl, hq, hg.2.2⟩

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
