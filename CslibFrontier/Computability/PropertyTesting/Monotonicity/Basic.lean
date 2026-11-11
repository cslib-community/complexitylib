/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Pi.Interval
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Violated edges and the distance to monotone Boolean functions

A Boolean function `f : (ι → Bool) → Bool` on the cube is monotone (Mathlib's `Monotone`, for the
coordinatewise order with `false < true`) exactly when it does not decrease along any edge of the
cube, the edge in direction `i` joining `update x i false` to `update x i true`
(`BitString.monotone_iff_forall_update_le`). The *violated edges* of `f` in direction `i`
(`BitString.violatedEdges f i`) are those along which `f` decreases, listed by their lower
endpoints; `f` is monotone exactly when it has none (`monotone_iff_forall_violatedEdges_eq_empty`).
`BitString.distMonotone f` is the least Hamming distance from `f` to a monotone function, and
`BitString.relDistMonotone f` that distance divided by the `2 ^ n` points of the cube, `n` being
the number of coordinates; `f` is `ε`-far from monotone in the sense of [Goldreich, Goldwasser,
Lehman, Ron and Samorodnitsky][GoldreichGoldwasserLehmanRonSamorodnitsky2000] when
`ε ≤ relDistMonotone f` (`BitString.le_relDistMonotone_iff`).

`BitString.sortAlong i f` sorts the values of `f` along every edge in direction `i`: the lower
endpoint gets the smaller value and the upper endpoint the larger. This is the operator that swaps
the values at the endpoints of every violated edge of the `i`-th slice
[Roughgarden, §8.3.1][Roughgarden2015CC]. It changes `f` at exactly the `2 |A_i|` endpoints of
the violated edges in direction `i` (`BitString.hammingDist_sortAlong`), it leaves none in that
direction (`BitString.violatedEdges_sortAlong_self`), and, the *Key Claim* of the source's proof,
it does not increase the number of violated edges in any direction
(`BitString.card_violatedEdges_sortAlong_le`). Its proof compares, on every square spanned by the
directions `i` and `j`, the violations of the two `j`-edges before and after sorting along `i`; this
is a check of the 16 labellings of the square. Sorting along every direction in turn therefore
gives a monotone function within Hamming distance `2 Σ_i |A_i|` of `f`
(`BitString.exists_monotone_hammingDist_le`, `BitString.distMonotone_le_two_mul_sum`). Conversely
every violated edge has an endpoint on which `f` differs from a nearest monotone function, and the
violated edges in one direction are disjoint, so `|A_i| ≤ distMonotone f`
(`BitString.card_violatedEdges_le_distMonotone`).

Normalized by the `n 2 ^ (n - 1)` edges of the cube (`BitString.violatedEdgeFraction`), this is the
combinatorial core of the edge tester's analysis [Roughgarden, Theorem 8.2][Roughgarden2015CC]:
the relative distance to monotone is at most `n` times the fraction of violated edges
(`BitString.relDistMonotone_le_card_mul_violatedEdgeFraction`), so a function `ε`-far from monotone
has at least an `ε / n` fraction of violated edges
(`BitString.div_card_le_violatedEdgeFraction`). The tester itself is in
`CslibFrontier.Computability.PropertyTesting.Monotonicity.EdgeTester`.

The results are stated for any finite index type `ι`, in particular for `Fin n`.

## Main definitions

* `Cslib.BitString.violatedEdges`: the violated edges in a direction, by their lower endpoints.
* `Cslib.BitString.violatedEdgeFraction`: the fraction of the edges of the cube that are violated.
* `Cslib.BitString.distMonotone`, `Cslib.BitString.relDistMonotone`: the absolute and relative
  Hamming distance to the monotone functions.
* `Cslib.BitString.sortAlong`: sorting the values along the edges in one direction.

## Main results

* `Cslib.BitString.monotone_iff_forall_update_le`,
  `Cslib.BitString.monotone_iff_forall_violatedEdges_eq_empty`: monotonicity along edges.
* `Cslib.BitString.card_endpoints_violatedEdges`: the violated edges in direction `i` have
  `2 |A_i|` endpoints.
* `Cslib.BitString.hammingDist_sortAlong`, `Cslib.BitString.violatedEdges_sortAlong_self`,
  `Cslib.BitString.card_violatedEdges_sortAlong_le`,
  `Cslib.BitString.violatedEdges_sortAlong_eq_empty`: sorting along a direction, with the Key
  Claim.
* `Cslib.BitString.exists_monotone_hammingDist_le`, `Cslib.BitString.distMonotone_le_two_mul_sum`:
  every function is within `2 Σ_i |A_i|` of a monotone function.
* `Cslib.BitString.card_violatedEdges_le_distMonotone`: `|A_i| ≤ distMonotone f`.
* `Cslib.BitString.distMonotone_eq_zero_iff`, `Cslib.BitString.relDistMonotone_of_monotone`,
  `Cslib.BitString.le_relDistMonotone_iff`: the distance to monotone.
* `Cslib.BitString.relDistMonotone_le_card_mul_violatedEdgeFraction`,
  `Cslib.BitString.div_card_le_violatedEdgeFraction`: an `ε`-far function has at least an `ε / n`
  fraction of violated edges.

## References

* [O. Goldreich, S. Goldwasser, E. Lehman, D. Ron, A. Samorodnitsky, *Testing
  monotonicity*][GoldreichGoldwasserLehmanRonSamorodnitsky2000]
* [T. Roughgarden, *Communication Complexity (for Algorithm Designers)*][Roughgarden2015CC]
-/

public section

namespace Cslib.BitString

open Finset Function

variable {ι : Type*}

/-! ### Monotonicity along edges -/

/-- A function on a finite cube is monotone exactly when it does not decrease along any edge: for
every point `x` and direction `i`, its value at `update x i false` is at most its value at
`update x i true`. -/
theorem monotone_iff_forall_update_le [Finite ι] [DecidableEq ι] {β : Type*} [Preorder β]
    {f : (ι → Bool) → β} :
    Monotone f ↔ ∀ x i, f (update x i false) ≤ f (update x i true) := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun hf x i => hf (update_le_update_iff'.2 (Bool.false_le true)), fun h => ?_⟩
  let _ : LocallyFiniteOrder (ι → Bool) := Fintype.toLocallyFiniteOrder
  rw [monotone_iff_forall_covBy]
  intro a b hab
  obtain ⟨i, c, hc, rfl⟩ := Pi.covBy_iff_exists_right_eq.1 hab
  have hlt := hc.lt
  have ha : a i = false := by revert hlt; cases a i <;> cases c <;> decide
  have hc' : c = true := by revert hlt; cases a i <;> cases c <;> decide
  subst hc'
  have := h a i
  rwa [update_eq_self_iff.2 ha.symm] at this

variable [DecidableEq ι]

/-! ### Violated edges -/

section ViolatedEdges

variable [Fintype ι]

/-- The **violated edges** of `f` in direction `i`, listed by their lower endpoints: the points `x`
with `x i = false` such that `f x = true` and `f (update x i true) = false`. The edges in
direction `i` are the `2 ^ (n - 1)` pairs `(x, update x i true)` with `x i = false`. -/
@[expose]
def violatedEdges (f : (ι → Bool) → Bool) (i : ι) : Finset (ι → Bool) :=
  {x | x i = false ∧ f x = true ∧ f (update x i true) = false}

theorem mem_violatedEdges {f : (ι → Bool) → Bool} {i : ι} {x : ι → Bool} :
    x ∈ violatedEdges f i ↔ x i = false ∧ f x = true ∧ f (update x i true) = false := by
  simp only [violatedEdges, mem_filter, mem_univ, true_and]

/-- A Boolean function is monotone exactly when it has no violated edge in any direction. -/
theorem monotone_iff_forall_violatedEdges_eq_empty {f : (ι → Bool) → Bool} :
    Monotone f ↔ ∀ i, violatedEdges f i = ∅ := by
  rw [monotone_iff_forall_update_le]
  constructor
  · intro h i
    ext x
    simp only [mem_violatedEdges, Finset.notMem_empty, iff_false, not_and]
    intro hx h1 h2
    have := h x i
    rw [update_eq_self_iff.2 hx.symm, h1, h2] at this
    exact absurd this (by decide)
  · intro h x i
    by_contra hlt
    have h1 : f (update x i false) = true ∧ f (update x i true) = false := by
      revert hlt; cases f (update x i false) <;> cases f (update x i true) <;> decide
    have hmem : update x i false ∈ violatedEdges f i := by
      rw [mem_violatedEdges, update_self, update_idem]
      exact ⟨rfl, h1⟩
    rw [h i] at hmem
    exact Finset.notMem_empty _ hmem

end ViolatedEdges

/-- `f` decreases along the edge in direction `i` through `x`; this does not depend on `x i`. -/
private def Viol (f : (ι → Bool) → Bool) (i : ι) (x : ι → Bool) : Prop :=
  f (update x i false) = true ∧ f (update x i true) = false

private instance (f : (ι → Bool) → Bool) (i : ι) : DecidablePred (Viol f i) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

private theorem viol_update (f : (ι → Bool) → Bool) (i : ι) (x : ι → Bool) (b : Bool) :
    Viol f i (update x i b) ↔ Viol f i x := by
  simp only [Viol, update_idem]

/-- Flip the coordinate `i`. -/
private def flipAt (i : ι) (x : ι → Bool) : ι → Bool := update x i (!x i)

private theorem flipAt_flipAt (i : ι) (x : ι → Bool) : flipAt i (flipAt i x) = x := by
  simp only [flipAt, update_self, update_idem, Bool.not_not, update_eq_self]

private theorem update_false_add_update_true {M : Type*} [AddCommMonoid M] (i : ι)
    (h : (ι → Bool) → M) (y : ι → Bool) :
    h (update y i false) + h (update y i true) = h y + h (flipAt i y) := by
  unfold flipAt
  cases hy : y i
  · have e : update y i false = y := update_eq_self_iff.2 hy.symm
    rw [e, Bool.not_false]
  · have e : update y i true = y := update_eq_self_iff.2 hy.symm
    rw [e, Bool.not_true, add_comm]

/-! ### Sorting along a direction -/

/-- **Sorting along direction `i`**: on every edge in direction `i`, the lower endpoint gets the
smaller and the upper endpoint the larger of the two values of `f`. On a violated edge this swaps
the two values, and elsewhere it changes nothing [Roughgarden, §8.3.1][Roughgarden2015CC]. -/
def sortAlong (i : ι) (f : (ι → Bool) → Bool) (x : ι → Bool) : Bool :=
  if x i then f (update x i false) || f (update x i true)
  else f (update x i false) && f (update x i true)

/-- At the lower endpoint of an edge, sorting takes the smaller value. -/
@[simp]
theorem sortAlong_update_false (i : ι) (f : (ι → Bool) → Bool) (x : ι → Bool) :
    sortAlong i f (update x i false) = (f (update x i false) && f (update x i true)) := by
  simp only [sortAlong, update_self, update_idem, Bool.false_eq_true, ite_false]

/-- At the upper endpoint of an edge, sorting takes the larger value. -/
@[simp]
theorem sortAlong_update_true (i : ι) (f : (ι → Bool) → Bool) (x : ι → Bool) :
    sortAlong i f (update x i true) = (f (update x i false) || f (update x i true)) := by
  simp only [sortAlong, update_self, update_idem, ite_true]

/-- Sorting along `i` changes `f` exactly at the endpoints of its violated edges in direction
`i`. -/
private theorem ne_sortAlong_iff (f : (ι → Bool) → Bool) (i : ι) (x : ι → Bool) :
    f x ≠ sortAlong i f x ↔ Viol f i x := by
  unfold sortAlong Viol
  cases hx : x i
  · have e : update x i false = x := update_eq_self_iff.2 hx.symm
    rw [e]
    cases f x <;> cases f (update x i true) <;> simp
  · have e : update x i true = x := update_eq_self_iff.2 hx.symm
    rw [e]
    cases f x <;> cases f (update x i false) <;> simp

/-- On a square spanned by the directions `i ≠ j`, sorting along `i` does not increase the number
of violated `j`-edges: this is the case analysis of the Key Claim, over the 16 labellings of the
square. -/
private theorem viol_sortAlong_square (f : (ι → Bool) → Bool) {i j : ι} (hij : i ≠ j)
    (y : ι → Bool) :
    ((if Viol (sortAlong i f) j (update y i false) then 1 else 0) +
      (if Viol (sortAlong i f) j (update y i true) then 1 else 0) : ℕ) ≤
    (if Viol f j (update y i false) then 1 else 0) +
      (if Viol f j (update y i true) then 1 else 0) := by
  simp only [Viol]
  simp only [update_comm hij, sortAlong_update_false, sortAlong_update_true]
  generalize f (update (update y j false) i false) = a
  generalize f (update (update y j false) i true) = b
  generalize f (update (update y j true) i false) = c
  generalize f (update (update y j true) i true) = d
  revert a b c d
  decide

variable [Fintype ι]

private theorem sum_update_false_add_update_true {M : Type*} [AddCommMonoid M] (i : ι)
    (h : (ι → Bool) → M) :
    ∑ y, (h (update y i false) + h (update y i true)) = ∑ y, h y + ∑ y, h y := by
  simp only [update_false_add_update_true, sum_add_distrib]
  congr 1
  exact Equiv.sum_comp (Function.Involutive.toPerm _ (flipAt_flipAt i)) h

private theorem mem_violatedEdges_iff_viol {f : (ι → Bool) → Bool} {i : ι} {x : ι → Bool} :
    x ∈ violatedEdges f i ↔ x i = false ∧ Viol f i x := by
  rw [mem_violatedEdges, Viol]
  constructor
  · rintro ⟨hx, h0, h1⟩
    exact ⟨hx, by rwa [update_eq_self_iff.2 hx.symm], h1⟩
  · rintro ⟨hx, h0, h1⟩
    exact ⟨hx, by rwa [update_eq_self_iff.2 hx.symm] at h0, h1⟩

/-- Each violated edge has two endpoints. -/
private theorem card_viol (f : (ι → Bool) → Bool) (i : ι) :
    #{x | Viol f i x} = 2 * #(violatedEdges f i) := by
  have h := sum_update_false_add_update_true i
    (fun x => if x i = false ∧ Viol f i x then (1 : ℕ) else 0)
  simp only [update_self, viol_update, true_and, Bool.true_eq_false, false_and,
    ↓reduceIte, add_zero] at h
  have he : violatedEdges f i = univ.filter fun x => x i = false ∧ Viol f i x := by
    ext x
    rw [mem_violatedEdges_iff_viol, mem_filter]
    simp only [mem_univ, true_and]
  rw [he, card_filter, card_filter, h, two_mul]

/-- The endpoints of the violated edges in direction `i`, the points `x` such that `f` decreases
along the edge in direction `i` through `x`, number `2 |A_i|`. -/
theorem card_endpoints_violatedEdges (f : (ι → Bool) → Bool) (i : ι) :
    #{x | f (update x i false) = true ∧ f (update x i true) = false} =
      2 * #(violatedEdges f i) :=
  card_viol f i

/-- Sorting along `i` changes `f` at exactly the `2 |A_i|` endpoints of its violated edges in
direction `i`. -/
theorem hammingDist_sortAlong (f : (ι → Bool) → Bool) (i : ι) :
    hammingDist f (sortAlong i f) = 2 * #(violatedEdges f i) := by
  rw [← card_viol, hammingDist]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, ne_sortAlong_iff]

/-- After sorting along `i`, no edge in direction `i` is violated. -/
theorem violatedEdges_sortAlong_self (f : (ι → Bool) → Bool) (i : ι) :
    violatedEdges (sortAlong i f) i = ∅ := by
  ext x
  simp only [mem_violatedEdges, Finset.notMem_empty, iff_false, not_and]
  intro hx h1
  have hx' : update x i false = x := update_eq_self_iff.2 hx.symm
  rw [← hx', sortAlong_update_false] at h1
  rw [← hx', update_idem, sortAlong_update_true]
  simp only [Bool.and_eq_true] at h1
  simp [h1.1]

/-- **The Key Claim** [Roughgarden, §8.3.1][Roughgarden2015CC]: sorting along any direction `i`
does not increase the number of violated edges in any direction `j`. -/
theorem card_violatedEdges_sortAlong_le (f : (ι → Bool) → Bool) (i j : ι) :
    #(violatedEdges (sortAlong i f) j) ≤ #(violatedEdges f j) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [violatedEdges_sortAlong_self, card_empty]
    exact Nat.zero_le _
  · have key : ∀ g : (ι → Bool) → Bool,
        ∑ y, ((if Viol g j (update y i false) then 1 else 0) +
          (if Viol g j (update y i true) then 1 else 0) : ℕ) =
          2 * (2 * #(violatedEdges g j)) := by
      intro g
      rw [sum_update_false_add_update_true i (fun x => if Viol g j x then 1 else 0),
        ← two_mul, ← card_viol, card_filter]
    have h := sum_le_sum fun y (_ : y ∈ univ) => viol_sortAlong_square f hij y
    rw [key, key] at h
    omega

/-- Sorting along one direction keeps every direction without violated edges free of them; in
particular it keeps a monotone function monotone. -/
theorem violatedEdges_sortAlong_eq_empty {f : (ι → Bool) → Bool} {j : ι}
    (h : violatedEdges f j = ∅) (i : ι) : violatedEdges (sortAlong i f) j = ∅ := by
  have := card_violatedEdges_sortAlong_le f i j
  rwa [h, card_empty, Nat.le_zero, card_eq_zero] at this

/-- Sorting along the directions of `s` in turn. -/
private theorem exists_sorted (f : (ι → Bool) → Bool) (s : Finset ι) :
    ∃ g : (ι → Bool) → Bool, (∀ i ∈ s, violatedEdges g i = ∅) ∧
      (∀ j, #(violatedEdges g j) ≤ #(violatedEdges f j)) ∧
      hammingDist f g ≤ 2 * ∑ i ∈ s, #(violatedEdges f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨f, by simp, fun _ => le_rfl, by simp⟩
  | insert a s has ih =>
    obtain ⟨g, hs, hle, hd⟩ := ih
    refine ⟨sortAlong a g, fun i hi => ?_, fun j => ?_, ?_⟩
    · rcases mem_insert.1 hi with rfl | hi
      · exact violatedEdges_sortAlong_self g i
      · exact violatedEdges_sortAlong_eq_empty (hs i hi) a
    · exact (card_violatedEdges_sortAlong_le g a j).trans (hle j)
    · rw [sum_insert has]
      calc hammingDist f (sortAlong a g)
          ≤ hammingDist f g + hammingDist g (sortAlong a g) := hammingDist_triangle _ _ _
        _ ≤ 2 * ∑ i ∈ s, #(violatedEdges f i) + 2 * #(violatedEdges f a) := by
          rw [hammingDist_sortAlong]
          exact Nat.add_le_add hd (Nat.mul_le_mul_left 2 (hle a))
        _ = _ := by ring

/-- **Every Boolean function is within `2 Σ_i |A_i|` of a monotone function**, where `A_i` are its
violated edges in direction `i` [Roughgarden, proof of Theorem 8.2][Roughgarden2015CC]: sort along
every direction in turn. -/
theorem exists_monotone_hammingDist_le (f : (ι → Bool) → Bool) :
    ∃ g : (ι → Bool) → Bool, Monotone g ∧
      hammingDist f g ≤ 2 * ∑ i, #(violatedEdges f i) := by
  obtain ⟨g, hg, -, hd⟩ := exists_sorted f univ
  exact ⟨g, monotone_iff_forall_violatedEdges_eq_empty.2 fun i => hg i (mem_univ i), hd⟩

/-! ### Distance to monotone -/

/-- The **distance to monotone** of `f`: the least Hamming distance from `f` to a monotone Boolean
function, that is, the least number of points at which `f` must be changed to make it monotone. -/
noncomputable def distMonotone (f : (ι → Bool) → Bool) : ℕ :=
  sInf ((fun g => hammingDist f g) '' {g | Monotone g})

/-- The distance to monotone is at most the distance to any monotone function. -/
theorem distMonotone_le {f g : (ι → Bool) → Bool} (hg : Monotone g) :
    distMonotone f ≤ hammingDist f g :=
  Nat.sInf_le ⟨g, hg, rfl⟩

/-- The distance to monotone is attained by a monotone function. -/
theorem exists_monotone_hammingDist_eq_distMonotone (f : (ι → Bool) → Bool) :
    ∃ g : (ι → Bool) → Bool, Monotone g ∧ hammingDist f g = distMonotone f := by
  have hne : ((fun g => hammingDist f g) '' {g : (ι → Bool) → Bool | Monotone g}).Nonempty :=
    ⟨_, (fun _ => false), monotone_const, rfl⟩
  obtain ⟨g, hg, h⟩ := Nat.sInf_mem hne
  exact ⟨g, hg, h⟩

/-- The distance to monotone vanishes exactly on monotone functions. -/
theorem distMonotone_eq_zero_iff {f : (ι → Bool) → Bool} : distMonotone f = 0 ↔ Monotone f := by
  constructor
  · intro h
    obtain ⟨g, hg, hfg⟩ := exists_monotone_hammingDist_eq_distMonotone f
    rw [h, hammingDist_eq_zero] at hfg
    rwa [hfg]
  · intro hf
    exact Nat.le_zero.1 ((distMonotone_le hf).trans (hammingDist_self f).le)

/-- The distance to monotone is at most twice the number of violated edges. -/
theorem distMonotone_le_two_mul_sum (f : (ι → Bool) → Bool) :
    distMonotone f ≤ 2 * ∑ i, #(violatedEdges f i) := by
  obtain ⟨g, hg, hd⟩ := exists_monotone_hammingDist_le f
  exact (distMonotone_le hg).trans hd

/-- The violated edges in one direction are at most as many as the distance to monotone: they are
disjoint, and each has an endpoint at which `f` differs from a nearest monotone function. -/
theorem card_violatedEdges_le_distMonotone (f : (ι → Bool) → Bool) (i : ι) :
    #(violatedEdges f i) ≤ distMonotone f := by
  obtain ⟨g, hg, hfg⟩ := exists_monotone_hammingDist_eq_distMonotone f
  rw [← hfg, hammingDist]
  refine card_le_card_of_injOn (fun x => if f x ≠ g x then x else update x i true) ?_ ?_
  · intro x hx
    rw [mem_coe, mem_violatedEdges] at hx
    obtain ⟨hxi, h1, h2⟩ := hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    split_ifs with h
    · exact h
    · push Not at h
      have hmono := hg (update_le_update_iff'.2 (Bool.false_le true) :
        update x i false ≤ update x i true)
      rw [update_eq_self_iff.2 hxi.symm] at hmono
      intro heq
      rw [← h, h1, ← heq, h2] at hmono
      exact absurd hmono (by decide)
  · intro x hx y hy hxy
    rw [mem_coe, mem_violatedEdges] at hx hy
    simp only at hxy
    split_ifs at hxy with h1 h2 h2
    · exact hxy
    · have := congrFun hxy i
      rw [update_self, hx.1] at this
      exact absurd this (by decide)
    · have := congrFun hxy i
      rw [update_self, hy.1] at this
      exact absurd this (by decide)
    · have := congrArg (fun z => update z i false) hxy
      simp only [update_idem] at this
      rwa [update_eq_self_iff.2 hx.1.symm, update_eq_self_iff.2 hy.1.symm] at this

/-- The **relative distance to monotone** of `f`: the distance to monotone divided by the
`2 ^ n` points of the cube. A function is `ε`-far from monotone when `ε ≤ relDistMonotone f`. -/
noncomputable def relDistMonotone (f : (ι → Bool) → Bool) : ℝ :=
  distMonotone f / 2 ^ Fintype.card ι

theorem relDistMonotone_eq (f : (ι → Bool) → Bool) :
    relDistMonotone f = distMonotone f / 2 ^ Fintype.card ι := by
  rw [relDistMonotone]

/-- `ε ≤ relDistMonotone f` says that `f` is `ε`-far from monotone: every monotone function
differs from `f` on at least an `ε` fraction of the cube. -/
theorem le_relDistMonotone_iff {f : (ι → Bool) → Bool} {ε : ℝ} :
    ε ≤ relDistMonotone f ↔
      ∀ g : (ι → Bool) → Bool, Monotone g → ε ≤ hammingDist f g / 2 ^ Fintype.card ι := by
  constructor
  · intro h g hg
    refine h.trans ?_
    rw [relDistMonotone]
    gcongr
    exact_mod_cast distMonotone_le hg
  · intro h
    obtain ⟨g, hg, hfg⟩ := exists_monotone_hammingDist_eq_distMonotone f
    have := h g hg
    rwa [hfg] at this

/-- Monotone functions are at relative distance `0` from monotone. -/
theorem relDistMonotone_of_monotone {f : (ι → Bool) → Bool} (hf : Monotone f) :
    relDistMonotone f = 0 := by
  rw [relDistMonotone, distMonotone_eq_zero_iff.2 hf, Nat.cast_zero, zero_div]

/-! ### The fraction of violated edges -/

/-- The **fraction of violated edges** of `f`: the number of violated edges divided by the
`n 2 ^ (n - 1)` edges of the cube, written `2 Σ_i |A_i| / (n 2 ^ n)`. It is `0` for `n = 0`. -/
noncomputable def violatedEdgeFraction (f : (ι → Bool) → Bool) : ℝ :=
  2 * (∑ i, #(violatedEdges f i) : ℝ) / (Fintype.card ι * 2 ^ Fintype.card ι)

theorem violatedEdgeFraction_eq (f : (ι → Bool) → Bool) :
    violatedEdgeFraction f =
      2 * (∑ i, #(violatedEdges f i) : ℝ) / (Fintype.card ι * 2 ^ Fintype.card ι) := by
  rw [violatedEdgeFraction]

theorem violatedEdgeFraction_nonneg (f : (ι → Bool) → Bool) : 0 ≤ violatedEdgeFraction f := by
  rw [violatedEdgeFraction]
  exact div_nonneg (mul_nonneg zero_le_two (sum_nonneg fun _ _ => Nat.cast_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg zero_le_two _))

/-- **The relative distance to monotone is at most `n` times the fraction of violated edges**
[Roughgarden, proof of Theorem 8.2][Roughgarden2015CC]. -/
theorem relDistMonotone_le_card_mul_violatedEdgeFraction (f : (ι → Bool) → Bool) :
    relDistMonotone f ≤ Fintype.card ι * violatedEdgeFraction f := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [relDistMonotone_of_monotone (Subsingleton.monotone f), Fintype.card_eq_zero,
      Nat.cast_zero, zero_mul]
  · have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hd : (distMonotone f : ℝ) ≤ 2 * ∑ i, (#(violatedEdges f i) : ℝ) := by
      exact_mod_cast distMonotone_le_two_mul_sum f
    rw [relDistMonotone, violatedEdgeFraction, mul_div_assoc', mul_div_mul_left _ _ hn.ne']
    gcongr

/-- **An `ε`-far function has at least an `ε / n` fraction of violated edges**
[Roughgarden, proof of Theorem 8.2][Roughgarden2015CC]. For `n = 0` both sides are `0`. -/
theorem div_card_le_violatedEdgeFraction {f : (ι → Bool) → Bool} {ε : ℝ}
    (hε : ε ≤ relDistMonotone f) : ε / Fintype.card ι ≤ violatedEdgeFraction f := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Fintype.card_eq_zero, Nat.cast_zero, div_zero]
    exact violatedEdgeFraction_nonneg f
  · have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    rw [div_le_iff₀ hn, mul_comm]
    exact hε.trans (relDistMonotone_le_card_mul_violatedEdgeFraction f)

end Cslib.BitString
