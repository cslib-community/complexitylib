/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.Mobius
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# The subset zeta transform and Yates's algorithm

The **subset zeta transform** of `f : Finset ι → M` is `subsetZeta f S = ∑_{T ⊆ S} f T`. It is
inverse to the subset Möbius transform `subsetMobius` of
`Complexity.Foundations.BooleanAnalysis.Mobius`: `subsetZeta_subsetMobius` and
`subsetMobius_subsetZeta`.

**Yates's algorithm** computes both transforms by one pass per coordinate. The pass in coordinate
`i` with coefficient `c` (`yatesPass`) replaces `f S` by `f S + c • f (S \ {i})` when `i ∈ S` and
leaves it unchanged otherwise. After the passes in the coordinates of a duplicate-free list `l`
(`yatesTransform`), the value at `S` is `∑_{U ⊆ S ∩ l} c ^ #U • f (S \ U)` (`yatesTransform_apply`).
With coefficient `1` this is Williams's invariant for the dynamic program in [Williams2014],
Lemma 4.2, Proof 1, and once every coordinate of `S` is processed it is the zeta transform
(`yatesTransform_one_apply`); with coefficient `-1` it is the Möbius transform
(`yatesTransform_neg_one_apply`). The algorithm goes back to Yates (1937); see
[BjorklundHusfeldtKoivisto2009], Section 2.2. Passes with coefficient `-c` in reverse order undo
passes with coefficient `c` (`yatesTransform_neg_reverse`); this gives the second inversion
formula `subsetMobius_subsetZeta`.

The cost of a table implementation on `Fin n` (`n` passes over `2 ^ n` cells) is in
`Complexity.Algorithms.Lean.Yates`.

## Main definitions

* `Cslib.BitString.subsetZeta`: the subset zeta transform.
* `Cslib.BitString.yatesPass`, `Cslib.BitString.yatesTransform`: Yates's passes.

## Main results

* `Cslib.BitString.yatesTransform_apply`: the closed form of the passes over a duplicate-free list.
* `Cslib.BitString.yatesTransform_one_apply`, `yatesTransform_one_eq_subsetZeta`: coefficient `1`
  gives the zeta transform.
* `Cslib.BitString.yatesTransform_neg_one_apply`: coefficient `-1` gives the Möbius transform.
* `Cslib.BitString.yatesTransform_neg_reverse`: reversed passes with the negated coefficient are
  inverse.
* `Cslib.BitString.subsetZeta_subsetMobius`, `subsetMobius_subsetZeta`: Möbius inversion on the
  subsets of a set, in both directions.

## References

* [A. Björklund, T. Husfeldt, M. Koivisto, *Set Partitioning via
  Inclusion–Exclusion*][BjorklundHusfeldtKoivisto2009]
* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
-/

public section

open Finset

namespace Cslib.BitString

section Zeta

variable {ι M : Type*} [AddCommMonoid M]

/-- The **subset zeta transform**: the value at `S` is `∑_{T ⊆ S} f T`. -/
@[expose] def subsetZeta (f : Finset ι → M) (S : Finset ι) : M :=
  ∑ T ∈ S.powerset, f T

/-- One pass of Yates's algorithm in coordinate `i` with coefficient `c`: the value at `S` becomes
`f S + c • f (S \ {i})` when `i ∈ S`, and stays `f S` otherwise. -/
@[expose] def yatesPass {R : Type*} [Monoid R] [DistribMulAction R M] [DecidableEq ι] (c : R)
    (i : ι) (f : Finset ι → M) (S : Finset ι) : M :=
  if i ∈ S then f S + c • f (S.erase i) else f S

/-- The passes of Yates's algorithm with coefficient `c` in the coordinates of `l`, in order. -/
@[expose] def yatesTransform {R : Type*} [Monoid R] [DistribMulAction R M] [DecidableEq ι]
    (c : R) (l : List ι) (f : Finset ι → M) : Finset ι → M :=
  l.foldl (fun g i => yatesPass c i g) f

variable {R : Type*} [Monoid R] [DistribMulAction R M] [DecidableEq ι]

@[simp] theorem yatesTransform_nil (c : R) (f : Finset ι → M) : yatesTransform c [] f = f := rfl

theorem yatesTransform_cons (c : R) (i : ι) (l : List ι) (f : Finset ι → M) :
    yatesTransform c (i :: l) f = yatesTransform c l (yatesPass c i f) := rfl

theorem yatesTransform_append (c : R) (l₁ l₂ : List ι) (f : Finset ι → M) :
    yatesTransform c (l₁ ++ l₂) f = yatesTransform c l₂ (yatesTransform c l₁ f) :=
  List.foldl_append

/-- **The passes in closed form.** After the passes in the coordinates of a duplicate-free list
`l`, the value at `S` is `∑_{U ⊆ S ∩ l} c ^ #U • f (S \ U)`. For `c = 1` this is the invariant of
[Williams2014], Lemma 4.2, Proof 1: the sum of `f T` over the `T ⊆ S` that agree with `S` outside
the processed coordinates. -/
theorem yatesTransform_apply (c : R) {l : List ι} (hl : l.Nodup) (f : Finset ι → M)
    (S : Finset ι) :
    yatesTransform c l f S = ∑ U ∈ (S ∩ l.toFinset).powerset, c ^ #U • f (S \ U) := by
  induction l generalizing f with
  | nil => simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    rw [yatesTransform_cons, ih hl.2]
    have hU : ∀ U ∈ (S ∩ l.toFinset).powerset, i ∉ U := fun U hU hiU =>
      hl.1 (List.mem_toFinset.mp (mem_inter.mp (mem_powerset.mp hU hiU)).2)
    by_cases hi : i ∈ S
    · have hins : S ∩ (i :: l).toFinset = insert i (S ∩ l.toFinset) := by
        rw [List.toFinset_cons, inter_insert_of_mem hi]
      have hni : i ∉ S ∩ l.toFinset := fun h =>
        hl.1 (List.mem_toFinset.mp (mem_inter.mp h).2)
      rw [hins, sum_powerset_insert hni, ← sum_add_distrib]
      refine sum_congr rfl fun U hUm => ?_
      rw [yatesPass, ite_eq_left (mem_sdiff.mpr ⟨hi, hU U hUm⟩), smul_add,
        card_insert_of_notMem (hU U hUm), pow_succ, mul_smul, sdiff_insert]
    · have hins : S ∩ (i :: l).toFinset = S ∩ l.toFinset := by
        rw [List.toFinset_cons, inter_insert_of_notMem hi]
      rw [hins]
      refine sum_congr rfl fun U _ => ?_
      have : i ∉ S \ U := fun h => hi (mem_sdiff.mp h).1
      rw [yatesPass, ite_eq_right this]

/-- Once every coordinate of `S` has been processed, the value at `S` is
`∑_{T ⊆ S} c ^ #(S \ T) • f T`. -/
theorem yatesTransform_apply_of_subset (c : R) {l : List ι} (hl : l.Nodup) (f : Finset ι → M)
    {S : Finset ι} (hS : S ⊆ l.toFinset) :
    yatesTransform c l f S = ∑ T ∈ S.powerset, c ^ #(S \ T) • f T := by
  rw [yatesTransform_apply c hl, inter_eq_left.mpr hS]
  refine sum_nbij' (S \ ·) (S \ ·) ?_ ?_ ?_ ?_ ?_
  · intro U _
    exact mem_powerset.mpr sdiff_subset
  · intro T _
    exact mem_powerset.mpr sdiff_subset
  · intro U hU
    exact Finset.sdiff_sdiff_eq_self (mem_powerset.mp hU)
  · intro T hT
    exact Finset.sdiff_sdiff_eq_self (mem_powerset.mp hT)
  · intro U hU
    rw [Finset.sdiff_sdiff_eq_self (mem_powerset.mp hU)]

end Zeta

section ZetaOne

variable {ι M : Type*} [AddCommMonoid M] [DecidableEq ι]

/-- **Yates's algorithm computes the zeta transform**: with coefficient `1`, once every coordinate
of `S` has been processed, the value at `S` is `subsetZeta f S`. -/
theorem yatesTransform_one_apply {l : List ι} (hl : l.Nodup) (f : Finset ι → M)
    {S : Finset ι} (hS : S ⊆ l.toFinset) :
    yatesTransform (1 : ℕ) l f S = subsetZeta f S := by
  rw [yatesTransform_apply_of_subset _ hl f hS, subsetZeta]
  simp only [one_pow, one_smul]

/-- The passes in every coordinate, once each, compute the zeta transform. -/
theorem yatesTransform_one_eq_subsetZeta {l : List ι} (hl : l.Nodup)
    (hall : ∀ i, i ∈ l) (f : Finset ι → M) : yatesTransform (1 : ℕ) l f = subsetZeta f := by
  funext S
  exact yatesTransform_one_apply hl f fun i _ => List.mem_toFinset.mpr (hall i)

end ZetaOne

section Inverse

variable {ι M R : Type*} [AddCommGroup M] [Ring R] [Module R M] [DecidableEq ι]

/-- The pass with coefficient `-c` undoes the pass with coefficient `c` in the same coordinate. -/
theorem yatesPass_neg_yatesPass (c : R) (i : ι) (f : Finset ι → M) :
    yatesPass (-c) i (yatesPass c i f) = f := by
  funext S
  by_cases hi : i ∈ S
  · simp only [yatesPass, ite_eq_left hi, ite_eq_right (notMem_erase i S), neg_smul]
    abel
  · simp only [yatesPass, ite_eq_right hi]

/-- The passes with coefficient `-c` in reverse order undo the passes with coefficient `c`. -/
theorem yatesTransform_neg_reverse (c : R) (l : List ι) (f : Finset ι → M) :
    yatesTransform (-c) l.reverse (yatesTransform c l f) = f := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    rw [List.reverse_cons, yatesTransform_append, yatesTransform_cons c i l f, ih]
    exact yatesPass_neg_yatesPass c i f

end Inverse

section Mobius

variable {ι M : Type*} [AddCommGroup M]

/-- **Möbius inversion**: the zeta transform of the Möbius transform is the identity. -/
theorem subsetZeta_subsetMobius (f : Finset ι → M) : subsetZeta (subsetMobius f) = f :=
  funext (sum_powerset_subsetMobius f)

/-- The Möbius transform at `S` reads only the values at subsets of `S`. -/
theorem subsetMobius_congr {f g : Finset ι → M} {S : Finset ι}
    (h : ∀ T ⊆ S, f T = g T) : subsetMobius f S = subsetMobius g S :=
  sum_congr rfl fun T hT => by rw [h T (mem_powerset.mp hT)]

/-- **Yates's algorithm computes the Möbius transform**: with coefficient `-1`, once every
coordinate of `S` has been processed, the value at `S` is `subsetMobius f S`. -/
theorem yatesTransform_neg_one_apply [DecidableEq ι] {l : List ι} (hl : l.Nodup)
    (f : Finset ι → M) {S : Finset ι} (hS : S ⊆ l.toFinset) :
    yatesTransform (-1 : ℤ) l f S = subsetMobius f S := by
  rw [yatesTransform_apply_of_subset _ hl f hS, subsetMobius]
  refine sum_congr rfl fun T hT => ?_
  rw [card_sdiff_of_subset (mem_powerset.mp hT)]

/-- **Möbius inversion, the other direction**: the Möbius transform of the zeta transform is the
identity. The proof runs Yates's passes forwards with coefficient `1` and backwards with
coefficient `-1`. -/
theorem subsetMobius_subsetZeta (f : Finset ι → M) : subsetMobius (subsetZeta f) = f := by
  classical
  funext S
  set l := S.toList
  have hl : l.Nodup := S.nodup_toList
  have hS : S ⊆ l.toFinset := by rw [toList_toFinset]
  have hS' : S ⊆ l.reverse.toFinset := by rw [List.toFinset_reverse, toList_toFinset]
  calc subsetMobius (subsetZeta f) S
      = subsetMobius (yatesTransform (1 : ℤ) l f) S := by
        refine subsetMobius_congr fun T hT => ?_
        rw [yatesTransform_apply_of_subset _ hl f (hT.trans hS), subsetZeta]
        simp only [one_pow, one_smul]
    _ = yatesTransform (-1 : ℤ) l.reverse (yatesTransform (1 : ℤ) l f) S :=
        (yatesTransform_neg_one_apply (List.nodup_reverse.mpr hl) _ hS').symm
    _ = f S := by rw [yatesTransform_neg_reverse]

end Mobius

end Cslib.BitString
