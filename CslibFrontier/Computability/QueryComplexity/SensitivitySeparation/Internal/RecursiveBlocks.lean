/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveDefinitions

/-!
# Superquadratic sensitivity separation: recursive blocks

This file lifts sensitive blocks of the all-false child input to the next level. A block `B` of
child coordinates is copied into every column of a row `i`, giving `rowLift i B`. If the child
predicates reject the all-false input but accept it after flipping `B`, then every next-level
predicate accepts the all-false input after flipping `rowLift i B`. Lifting preserves pairwise
disjointness, which yields the block sensitivity lower bound.

## Main definitions

* `rowLift`: the copies of a child block `B` in all `r` columns of row `i`.

## Main results

* `rowLift_family_disjoint`: pairwise disjoint child blocks lift to pairwise disjoint blocks indexed
  by `Fin k × K`.
* `recursiveFamily_rowLift`: flipping a lifted block in the all-false input makes every next-level
  predicate accept.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/RecursiveBlocks.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- Lift a sensitive block to every column of the specified row. -/
def rowLift {k r : ℕ} {I : Type} (i : Fin k) (B : Finset I) :
    Finset ((Fin k × Fin r) × I) :=
  (Finset.univ.product B).map
    ⟨fun p : Fin r × I => ((i, p.1), p.2), by
      intro p q hpq
      exact Prod.ext (congrArg (fun z => z.1.2) hpq)
        (congrArg (fun z : (Fin k × Fin r) × I => z.2) hpq)⟩

/-- A coordinate `p` lies in `rowLift i B` iff its row is `i` and its child coordinate lies in `B`.
-/
@[simp] private theorem mem_rowLift {k r : ℕ} {I : Type} (i : Fin k) (B : Finset I)
    (p : (Fin k × Fin r) × I) : p ∈ rowLift (r := r) i B ↔ p.1.1 = i ∧ p.2 ∈ B := by
  rcases p with ⟨⟨j, c⟩, a⟩
  unfold rowLift
  rw [Finset.mem_map]
  constructor
  · rintro ⟨⟨c', b⟩, hb, hp⟩
    change ((i, c'), b) = ((j, c), a) at hp
    cases hp
    exact ⟨rfl, (Finset.mem_product.mp hb).2⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨(c, a), Finset.mem_product.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩

/-- If `0 < r` and `B` is nonempty, then `rowLift i B` is nonempty. -/
theorem rowLift_nonempty {k r : ℕ} {I : Type} (i : Fin k) (B : Finset I)
    (hr : 0 < r) (hB : B.Nonempty) : (rowLift (r := r) i B).Nonempty := by
  obtain ⟨a, ha⟩ := hB
  exact ⟨((i, ⟨0, hr⟩), a), (mem_rowLift i B _).mpr ⟨rfl, ha⟩⟩

/-- Blocks lifted to distinct rows are disjoint. -/
private theorem rowLift_disjoint_of_ne {k r : ℕ} {I : Type} (i j : Fin k)
    (B C : Finset I) (hij : i ≠ j) : Disjoint (rowLift (r := r) i B) (rowLift j C) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hij (((mem_rowLift i B p).mp hp).1.symm.trans ((mem_rowLift j C p).mp hq).1)

/-- Lifts of disjoint child blocks are disjoint, whichever rows they are lifted to. -/
private theorem rowLift_disjoint {k r : ℕ} {I : Type} (i j : Fin k) (B C : Finset I)
    (hBC : Disjoint B C) : Disjoint (rowLift (r := r) i B) (rowLift j C) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp hBC ((mem_rowLift i B p).mp hp).2
    ((mem_rowLift j C p).mp hq).2

/-- If the blocks `blocks a` are pairwise disjoint, then the lifts `rowLift a.1 (blocks a.2)`
indexed by `a : Fin k × K` are pairwise disjoint. -/
theorem rowLift_family_disjoint {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (hB : Pairwise fun a b => Disjoint (blocks a) (blocks b)) :
    Pairwise fun a b : Fin k × K =>
      Disjoint (rowLift (r := r) a.1 (blocks a.2)) (rowLift b.1 (blocks b.2)) := by
  intro a b hab
  by_cases hrow : a.1 = b.1
  · apply rowLift_disjoint
    apply hB
    intro hcol
    exact hab (Prod.ext hrow hcol)
  · exact rowLift_disjoint_of_ne _ _ _ _ hrow

open scoped Classical in
/-- After flipping `rowLift i B` in the all-false input, every child of row `i` is the all-false
child input with `B` flipped. -/
private theorem recursiveChild_rowLift_same {k r : ℕ} {I : Type}
    [DecidableEq ((Fin k × Fin r) × I)]
    (i : Fin k) (B : Finset I) (c : Fin r) :
    recursiveChild (BitString.flipOn (rowLift (r := r) i B) (fun _ => false)) i c =
      BitString.flipOn B (fun _ => false) := by
  funext a
  simp [recursiveChild, BitString.flipOn_apply]

/-- After flipping `rowLift i B` in the all-false input, every child outside row `i` is still
all-false. -/
private theorem recursiveChild_rowLift_other {k r : ℕ} {I : Type}
    [DecidableEq ((Fin k × Fin r) × I)]
    (i j : Fin k) (B : Finset I) (c : Fin r) (hji : j ≠ i) :
    recursiveChild (BitString.flipOn (rowLift (r := r) i B) (fun _ => false)) j c =
      fun _ => false := by
  funext a
  simp [recursiveChild, BitString.flipOn_apply, hji]

open scoped Classical in
/-- If every member of `F` rejects the all-false input and accepts the all-false input with `B`
flipped, then every next-level predicate accepts the all-false input with `rowLift i B` flipped. -/
theorem recursiveFamily_rowLift {k r h : ℕ} {I : Type} [DecidableEq ((Fin k × Fin r) × I)]
    (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hzero : ∀ q, F q (fun _ => false) = false) (B : Finset I)
    (hB : ∀ q, F q (BitString.flipOn B (fun _ => false)) = true) (i : Fin k) (q : Fin h) :
    recursiveFamily T label F q
      (BitString.flipOn (rowLift i B) (fun _ => false)) = true := by
  apply (recursiveFamily_eq_true_iff _ _ _ _ _).mpr
  refine ⟨i, (rowClause_eq_true_iff _ _ _ _ _ _).mpr ⟨?_, ?_⟩⟩
  · intro c
    rw [recursiveChild_rowLift_same]
    exact hB _
  · intro j hij
    rw [recursiveChild_rowLift_other _ _ _ _ (T.ne_of_adj hij).symm]
    exact hzero _

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
