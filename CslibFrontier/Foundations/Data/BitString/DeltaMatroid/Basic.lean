/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Flip
public import CslibFrontier.Foundations.Data.BitString.Parity

/-!
# Relational delta-matroids on Boolean tuples

`IsDeltaMatroid R` is the nonempty, one-sided symmetric exchange axiom of
[Kazda, Kolmogorov and Rolínek, Definition 5, p. 4][KazdaKolmogorovRolinek2018]
(arXiv:1602.03124v6). Coordinates are arbitrary types; `Fin n` gives the usual tuples.
The set `{i, j}` is a singleton when `i = j`, allowing a one-coordinate exchange.
No simultaneous exchange at both feasible tuples is assumed.

`IsEvenDeltaMatroid R` additionally requires common parity, of either value, over a finite
coordinate type. Empty relations are excluded, including on the empty coordinate type.

## Main definitions

* `IsDeltaMatroid`: nonempty one-sided symmetric exchange.
* `IsEvenDeltaMatroid`: a delta-matroid with common parity of either value.

## Main results

* `IsEvenDeltaMatroid.not_mem_flipOn_singleton`: a one-coordinate flip is infeasible.
* `IsEvenDeltaMatroid.exchange`: exchange uses two distinct disagreeing coordinates.
-/

public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [DecidableEq ι] {R : Set (ι → Bool)} {x y : ι → Bool}

/-- A nonempty Boolean relation satisfying one-sided symmetric exchange.
This is Definition 5 of [KazdaKolmogorovRolinek2018], with set flips as in Definition 4. -/
structure IsDeltaMatroid (R : Set (ι → Bool)) : Prop where
  nonempty : R.Nonempty
  exchange : ∀ ⦃x y⦄, x ∈ R → y ∈ R → ∀ ⦃i⦄, x i ≠ y i →
    ∃ j, x j ≠ y j ∧ flipOn {i, j} x ∈ R

/-- A delta-matroid whose feasible tuples have common parity (possibly odd).
This is the evenness condition in Definition 5 of [KazdaKolmogorovRolinek2018]. -/
structure IsEvenDeltaMatroid [Fintype ι] (R : Set (ι → Bool)) : Prop where
  isDeltaMatroid : IsDeltaMatroid R
  parity_eq : ∀ ⦃x y⦄, x ∈ R → y ∈ R → parityOn univ x = parityOn univ y

/-- Empty relations are not delta-matroids under the nonempty convention. -/
@[simp] theorem not_isDeltaMatroid_empty : ¬ IsDeltaMatroid (∅ : Set (ι → Bool)) :=
  fun h => Set.not_nonempty_empty h.nonempty

/-- A singleton relation is a delta-matroid. -/
theorem isDeltaMatroid_singleton (x : ι → Bool) : IsDeltaMatroid {x} where
  nonempty := Set.singleton_nonempty x
  exchange := by
    intro u v hu hv i hi
    obtain rfl := Set.mem_singleton_iff.mp hu
    obtain rfl := Set.mem_singleton_iff.mp hv
    exact (hi rfl).elim

/-- The full Boolean cube is a delta-matroid, using a single-coordinate exchange. -/
theorem isDeltaMatroid_univ : IsDeltaMatroid (Set.univ : Set (ι → Bool)) where
  nonempty := ⟨fun _ => false, Set.mem_univ _⟩
  exchange := by
    intro x y hx hy i hi
    exact ⟨i, hi, Set.mem_univ _⟩

variable [Fintype ι]

/-- A singleton relation is even, including a singleton of odd parity. -/
theorem isEvenDeltaMatroid_singleton (x : ι → Bool) : IsEvenDeltaMatroid {x} where
  isDeltaMatroid := isDeltaMatroid_singleton x
  parity_eq := by
    intro u v hu hv
    obtain rfl := Set.mem_singleton_iff.mp hu
    obtain rfl := Set.mem_singleton_iff.mp hv
    rfl

/-- Flipping one coordinate negates total parity. -/
theorem parityOn_univ_flipOn_singleton (x : ι → Bool) (i : ι) :
    parityOn univ (flipOn {i} x) = !parityOn univ x := by
  rw [flipOn_singleton, parityOn_update_not (mem_univ i)]

/-- Flipping two distinct coordinates preserves total parity. -/
theorem parityOn_univ_flipOn_pair (x : ι → Bool) {i j : ι} (hij : i ≠ j) :
    parityOn univ (flipOn {i, j} x) = parityOn univ x := by
  rw [flipOn_insert (by simpa using hij), parityOn_univ_flipOn_singleton,
    parityOn_univ_flipOn_singleton, Bool.not_not]

/-- Evenness rules out feasible one-coordinate flips. -/
theorem IsEvenDeltaMatroid.not_mem_flipOn_singleton (hR : IsEvenDeltaMatroid R)
    (hx : x ∈ R) (i : ι) : flipOn {i} x ∉ R := by
  intro hf
  have h := hR.parity_eq hf hx
  rw [parityOn_univ_flipOn_singleton] at h
  exact Bool.not_ne_self _ h

/-- In an even delta-matroid, exchange flips two distinct coordinates on which the tuples differ. -/
theorem IsEvenDeltaMatroid.exchange (hR : IsEvenDeltaMatroid R)
    (hx : x ∈ R) (hy : y ∈ R) {i : ι} (hi : x i ≠ y i) :
    ∃ j, j ≠ i ∧ x j ≠ y j ∧ flipOn {i, j} x ∈ R := by
  obtain ⟨j, hj, hf⟩ := hR.isDeltaMatroid.exchange hx hy hi
  refine ⟨j, ?_, hj, hf⟩
  intro hji
  subst j
  exact hR.not_mem_flipOn_singleton hx i (by simpa using hf)

omit [DecidableEq ι] in
/-- Tuples of equal parity cannot disagree at just one coordinate. -/
theorem exists_ne_disagree_of_parity_eq
    (h : parityOn univ x = parityOn univ y) {i : ι} (hi : x i ≠ y i) :
    ∃ j, j ≠ i ∧ x j ≠ y j := by
  classical
  by_contra hn
  push Not at hn
  have hy : y = flipOn {i} x := by
    funext j
    by_cases hj : j = i
    · subst j
      rw [flipOn_singleton_self]
      cases hx : x i <;> cases hy : y i <;> simp_all
    · rw [flipOn_singleton_of_ne hj, hn j hj]
  rw [hy, parityOn_univ_flipOn_singleton] at h
  exact Bool.not_ne_self _ h.symm

/-- Every nonempty total-parity fiber is an even delta-matroid.
The witness is necessary: the odd fiber on the empty coordinate type is empty. -/
theorem isEvenDeltaMatroid_parityOn_fiber (b : Bool)
    (hne : ∃ x : ι → Bool, parityOn univ x = b) :
    IsEvenDeltaMatroid {x : ι → Bool | parityOn univ x = b} where
  isDeltaMatroid := {
    nonempty := hne
    exchange := by
      intro x y hx hy i hi
      obtain ⟨j, hji, hj⟩ := exists_ne_disagree_of_parity_eq (hx.trans hy.symm) hi
      exact ⟨j, hj, by simpa only [Set.mem_ofPred_eq,
        parityOn_univ_flipOn_pair x hji.symm] using hx⟩ }
  parity_eq := by
    intro x y hx hy
    exact hx.trans hy.symm

end Cslib.BitString
