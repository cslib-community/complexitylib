/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Immune
import CslibFrontier.Computability.Complexity.Classes.P.Countable

/-!
# Complexity cores

A set `X` is a **complexity core** of `A` for a class `C` of sets
(`Cslib.Complexity.IsComplexityCore`) when every member of `C` that lies inside `A`, or inside its
complement, meets `X` in a finite set.
A member of `C` that accepts only instances in `A`, or only instances outside `A`, accepts only
finitely many instances of `X`. For `C = P` and decidable `A`, these are the polynomial complexity
cores of [Lynch][Lynch1975]: every machine deciding `A` runs in superpolynomial time on all but
finitely many instances of `X`. The machine form, with binary machines as in `P` where Lynch allows
any machine (a polynomially robust choice), is in
`CslibFrontier.Computability.Complexity.Classes.Immune.PolyTimeCore`. Cores were studied further by
[Orponen and Schöning][OrponenSchoening1986].

A set is bi-immune to `C` exactly when it and its complement are infinite and the universe is a
core (`Cslib.Complexity.isBiImmune_iff_isComplexityCore_univ`). Problems in a class closed under
complement have only finite cores (`Cslib.Complexity.IsComplexityCore.finite_of_mem`).

[Lynch, Lemma 1][Lynch1975] shows that a recursive set outside `P` has an infinite recursive
polynomial complexity core, a subset of all words. A standard diagonal argument gives a
class-generic form with a *proper* core, one inside the set: for every countable class `C` that
contains the finite sets and is closed under union, a set not in `C` has an infinite core inside it
(`Cslib.Complexity.exists_infinite_isComplexityCore_subset`). Enumerate
`C` as `e₀, e₁, …`, and let `Dₙ` be the union of the `eᵢ` with `i < n` that lie inside `A`. Then
`A \ Dₙ` is infinite, since otherwise `A` would be the union of `Dₙ` and a finite set. Choosing
`xₙ ∈ A \ Dₙ` gives an infinite set `{xₙ}` that meets each `eᵢ` inside `A` only at indices
`n ≤ i`. `P` is such a class (`Cslib.Complexity.countable_P`), so problems outside `P` have
infinite cores inside them (`Cslib.Complexity.exists_infinite_isComplexityCore_P_subset`). Compared
with Lynch's lemma, the core is proper, which is stronger, but it is chosen without regard to
decidability. For decidable problems on bit strings, a delayed diagonalization chooses it decidable
(`Cslib.Complexity.exists_infinite_isDecidable_isPolyTimeCore`, in `Immune.RecursiveCore`).

## Main definitions

* `Cslib.Complexity.IsComplexityCore`: a complexity core of a set for a class.

## Main results

* `Cslib.Complexity.IsComplexityCore.subset`, `.union`, `.mono`, `Set.Finite.isComplexityCore`,
  `Cslib.Complexity.isComplexityCore_compl`: cores are closed under subsets and finite unions,
  finite sets are cores, and `A` and its complement have the same cores.
* `Cslib.Complexity.IsComplexityCore.finite_of_mem`: if `A` and its complement are in the class,
  every core of `A` is finite.
* `Cslib.Complexity.isBiImmune_iff_isComplexityCore_univ`: bi-immunity is a core condition.
* `Cslib.Complexity.exists_infinite_isComplexityCore_subset`: the class-generic core theorem,
  generalizing [Lynch, Lemma 1][Lynch1975] to countable classes containing the finite sets and
  closed under union, with a proper core.
* `Cslib.Complexity.exists_infinite_isComplexityCore_P_subset`,
  `Cslib.Complexity.notMem_P_iff_exists_infinite_isComplexityCore`: a problem is outside `P`
  exactly when it has an infinite core for `P`.

## References

* [N. Lynch, *On reducibility to complex or sparse sets*][Lynch1975]
* [P. Orponen, U. Schöning, *The density and complexity of polynomial cores for intractable
  sets*][OrponenSchoening1986]
-/

public section

namespace Cslib.Complexity

variable {α : Type*}

/-- `X` is a complexity core of `A` for the class `C`: every member of `C` contained in `A` or in
its complement meets `X` in a finite set. -/
def IsComplexityCore (C : Set (Set α)) (A X : Set α) : Prop :=
  ∀ B ∈ C, (B ⊆ A ∨ B ⊆ Aᶜ) → (B ∩ X).Finite

variable {C D : Set (Set α)} {A X Y : Set α}

theorem isComplexityCore_iff :
    IsComplexityCore C A X ↔ ∀ B ∈ C, (B ⊆ A ∨ B ⊆ Aᶜ) → (B ∩ X).Finite := Iff.rfl

/-- Subsets of cores are cores. -/
theorem IsComplexityCore.subset (h : IsComplexityCore C A X) (hYX : Y ⊆ X) :
    IsComplexityCore C A Y :=
  fun B hB hBA => (h B hB hBA).subset (Set.inter_subset_inter_right B hYX)

/-- Unions of two cores are cores. -/
theorem IsComplexityCore.union (hX : IsComplexityCore C A X) (hY : IsComplexityCore C A Y) :
    IsComplexityCore C A (X ∪ Y) := fun B hB hBA => by
  rw [Set.inter_union_distrib_left]
  exact (hX B hB hBA).union (hY B hB hBA)

/-- Finite sets are cores. -/
theorem _root_.Set.Finite.isComplexityCore (hX : X.Finite) : IsComplexityCore C A X :=
  fun _ _ _ => hX.subset Set.inter_subset_right

theorem isComplexityCore_empty : IsComplexityCore C A ∅ :=
  Set.finite_empty.isComplexityCore

/-- A core for a class is a core for every subclass. -/
theorem IsComplexityCore.mono (h : IsComplexityCore C A X) (hDC : D ⊆ C) :
    IsComplexityCore D A X :=
  fun B hB hBA => h B (hDC hB) hBA

/-- A set and its complement have the same cores. -/
@[simp]
theorem isComplexityCore_compl : IsComplexityCore C Aᶜ X ↔ IsComplexityCore C A X := by
  simp only [IsComplexityCore, compl_compl, or_comm]

/-- If `A` and its complement are in the class, every core of `A` is finite. -/
theorem IsComplexityCore.finite_of_mem (h : IsComplexityCore C A X) (hA : A ∈ C)
    (hAc : Aᶜ ∈ C) : X.Finite := by
  have := (h A hA (.inl le_rfl)).union (h Aᶜ hAc (.inr le_rfl))
  rwa [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter] at this

/-- The universe is a core of `A` when every member of the class inside `A` or its complement is
finite. -/
theorem isComplexityCore_univ_iff :
    IsComplexityCore C A Set.univ ↔ ∀ B ∈ C, (B ⊆ A ∨ B ⊆ Aᶜ) → B.Finite := by
  simp only [IsComplexityCore, Set.inter_univ]

/-- **Bi-immunity is a core condition**: `A` is bi-immune to `C` exactly when `A` and its
complement are infinite and the universe is a core of `A`. -/
theorem isBiImmune_iff_isComplexityCore_univ :
    IsBiImmune C A ↔ A.Infinite ∧ Aᶜ.Infinite ∧ IsComplexityCore C A Set.univ := by
  rw [isComplexityCore_univ_iff, isBiImmune_iff, isImmune_iff, isImmune_iff]
  exact ⟨fun ⟨⟨h₁, h₂⟩, h₃, h₄⟩ => ⟨h₁, h₃, fun B hB hBA => hBA.elim (h₂ B hB) (h₄ B hB)⟩,
    fun ⟨h₁, h₃, h⟩ => ⟨⟨h₁, fun B hB hBA => h B hB (.inl hBA)⟩, h₃,
      fun B hB hBA => h B hB (.inr hBA)⟩⟩

/-- **Class-generic core theorem**, generalizing [Lynch, Lemma 1][Lynch1975] by a standard diagonal
argument: if `C` is countable, contains the finite sets and is closed under union, every set not in
`C` has an infinite core inside it. -/
theorem exists_infinite_isComplexityCore_subset (hC : C.Countable)
    (hfin : ∀ F : Set α, F.Finite → F ∈ C) (hunion : ∀ B ∈ C, ∀ B' ∈ C, B ∪ B' ∈ C)
    (hA : A ∉ C) : ∃ X ⊆ A, X.Infinite ∧ IsComplexityCore C A X := by
  classical
  obtain ⟨e, he⟩ := hC.exists_eq_range ⟨∅, hfin ∅ Set.finite_empty⟩
  -- the members of the enumeration contained in `A`, and the unions of the first `n` of them
  let g : ℕ → Set α := fun i => if e i ⊆ A then e i else ∅
  have hg (i : ℕ) : g i ∈ C := by
    by_cases h : e i ⊆ A
    · simpa only [g, h, ↓reduceIte] using he ▸ Set.mem_range_self i
    · simpa only [g, h, ↓reduceIte] using hfin ∅ Set.finite_empty
  have hgA (i : ℕ) : g i ⊆ A := by
    by_cases h : e i ⊆ A
    · simp only [g, h, ↓reduceIte]
    · simp only [g, h, ↓reduceIte, Set.empty_subset]
  let D : ℕ → Set α := fun n => ⋃ i ∈ Finset.range n, g i
  have hD (n : ℕ) : D n ∈ C := by
    induction n with
    | zero => simpa [D] using hfin ∅ Set.finite_empty
    | succ n ih =>
      have : D (n + 1) = D n ∪ g n := by
        simp only [D, Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm]
      rw [this]
      exact hunion _ ih _ (hg n)
  have hDA (n : ℕ) : D n ⊆ A := Set.iUnion₂_subset fun i _ => hgA i
  have hsub {i n : ℕ} (hi : i < n) (hiA : e i ⊆ A) : e i ⊆ D n := by
    have : g i = e i := by simp only [g, hiA, ↓reduceIte]
    exact this ▸ Set.subset_biUnion_of_mem (u := g) (Finset.mem_coe.mpr (Finset.mem_range.mpr hi))
  -- what is left of `A` is infinite, since `A` is not in `C`
  have hinf (n : ℕ) : (A \ D n).Infinite := by
    intro hfin'
    apply hA
    rw [← Set.union_sdiff_cancel (hDA n)]
    exact hunion _ (hD n) _ (hfin _ hfin')
  choose x hx using fun n => (hinf n).nonempty
  refine ⟨Set.range x, Set.range_subset_iff.mpr fun n => (hx n).1, ?_, ?_⟩
  · -- a finite range would be some `e i` inside `A`, which `x (i + 1)` avoids
    intro hfr
    obtain ⟨i, hi⟩ : Set.range x ∈ Set.range e := he ▸ hfin _ hfr
    have hiA : e i ⊆ A := hi ▸ Set.range_subset_iff.mpr fun n => (hx n).1
    have hmem : x (i + 1) ∈ e i := hi ▸ Set.mem_range_self (i + 1)
    exact (hx (i + 1)).2 (hsub (Nat.lt_succ_self i) hiA hmem)
  · rintro B hB (hBA | hBA)
    · -- `B = e i` meets the range only at indices `n ≤ i`
      obtain ⟨i, rfl⟩ : B ∈ Set.range e := he ▸ hB
      refine ((Set.finite_lt_nat (i + 1)).image x).subset ?_
      rintro _ ⟨hy, n, rfl⟩
      refine ⟨n, ?_, rfl⟩
      by_contra hn
      exact (hx n).2 (hsub (by simp only [Set.mem_ofPred_eq] at hn; omega) hBA hy)
    · refine Set.finite_empty.subset ?_
      rintro _ ⟨hy, n, rfl⟩
      exact hBA hy (hx n).1

section P

variable {β : Type} {enc : β ↪ List Bool} {A X : Set β}

/-- **Problems outside `P` have infinite cores** ([Lynch, Lemma 1][Lynch1975], proper-core
strengthening): a problem outside `P` has an infinite core for `P` inside it. Unlike Lynch's core,
this one is not claimed to be recursive; for a decidable core of a decidable problem on bit strings,
see `Cslib.Complexity.exists_infinite_isDecidable_isPolyTimeCore`. -/
theorem exists_infinite_isComplexityCore_P_subset (hA : A ∉ P enc) :
    ∃ X ⊆ A, X.Infinite ∧ IsComplexityCore (P enc) A X :=
  exists_infinite_isComplexityCore_subset (countable_P enc) (fun _ hF => hF.mem_P)
    (fun _ hB _ hB' => union_mem_P hB hB') hA

/-- A problem in `P` has only finite cores for `P`. -/
theorem IsComplexityCore.finite_of_mem_P (h : IsComplexityCore (P enc) A X) (hA : A ∈ P enc) :
    X.Finite :=
  h.finite_of_mem hA (compl_mem_P hA)

/-- **A problem is outside `P` exactly when it has an infinite core for `P`.** -/
theorem notMem_P_iff_exists_infinite_isComplexityCore :
    A ∉ P enc ↔ ∃ X ⊆ A, X.Infinite ∧ IsComplexityCore (P enc) A X :=
  ⟨exists_infinite_isComplexityCore_P_subset, fun ⟨_, _, hX, h⟩ hA => hX (h.finite_of_mem_P hA)⟩

end P

end Cslib.Complexity
