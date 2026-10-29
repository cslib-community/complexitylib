/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.LowDegree.Dimension
public import Complexity.Foundations.BooleanAnalysis.LowDegree.Addition
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Small representative sets for Boolean sumsets

For arbitrary subsets `A` and `B` of the Boolean cube, choose `A₀ ⊆ A` and `B₀ ⊆ B` such that
`A + B = (A₀ + B) ∪ (A + B₀)` and `|A₀| + |B₀| ≤ 3 ∑_{j ≤ n/3} binom(n,j)`.
Here addition of bit strings is coordinatewise XOR. There is no degree or circuit-size
assumption on `A` and `B`.

This is the case `q = 2` (the field `𝔽₂`) of [Ellenberg2017Sumsets, Theorem 1, pp. 1–2]. The proof
uses the general image-sparsification theorem with restricted low-degree evaluation spaces.
Its input is the common slice-space containment of the polynomial pullbacks; we do not use or
formalize the theorem of Meshulam used in the published proof. All choices are nonuniform.

## Main results

* `Cslib.BitString.exists_add_cover_of_degree`: an asymmetric, degree-parameterized bound.
* `Cslib.BitString.exists_add_cover`: the `3` times low-degree monomial-count bound.

## References

* [J. S. Ellenberg, *Sumsets as unions of sumsets of subsets*][Ellenberg2017Sumsets],
  arXiv:1612.01929v2, Theorem 1 and its proof, pp. 1–3.
-/

public section

namespace Cslib.BitString

open Finset Module ImageSparsification
open scoped Pointwise

variable {ι : Type*} [Fintype ι]

/-- Restricting the degree-`p` and degree-`q` evaluation spaces to the two summands yields an
exact sumset cover with budget `D(p) + D(q) + 2^n - D(p+q+1)`. Parentheses around the
codimension keep the subtraction in natural numbers local to that term. -/
theorem exists_add_cover_of_degree (A B : Finset (ι → Bool)) (p q : ℕ) :
    ∃ A₀ B₀, A₀ ⊆ A ∧ B₀ ⊆ B ∧ A + B = (A₀ + B) ∪ (A + B₀) ∧
      #A₀ + #B₀ ≤ #{S : Finset ι | #S ≤ p} + #{S : Finset ι | #S ≤ q} +
        (2 ^ Fintype.card ι - #{S : Finset ι | #S ≤ p + q + 1}) := by
  classical
  let restrictA := LinearMap.funLeft (ZMod 2) (ZMod 2) (fun a : A => a.1)
  let restrictB := LinearMap.funLeft (ZMod 2) (ZMod 2) (fun b : B => b.1)
  have hdecomp := (hasSliceDecomposition_add (K := ZMod 2) (ι := ι) p q).comp
    (fun a : A => a.1) (fun b : B => b.1)
  obtain ⟨s, t, hcard, hcover⟩ := exists_image_cover hdecomp
  refine ⟨s.image Subtype.val, t.image Subtype.val, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨a', _, rfl⟩ := mem_image.mp ha
    exact a'.2
  · intro b hb
    obtain ⟨b', _, rfl⟩ := mem_image.mp hb
    exact b'.2
  · ext x
    constructor
    · intro hx
      obtain ⟨a, ha, b, hb, hab⟩ := mem_add.mp hx
      rcases hcover ⟨a, ha⟩ ⟨b, hb⟩ with hleft | hright
      · obtain ⟨a', ha', b', hab'⟩ := hleft
        exact mem_union_left _ (mem_add.mpr
          ⟨a'.1, mem_image.mpr ⟨a', ha', rfl⟩, b'.1, b'.2, hab'.trans hab⟩)
      · obtain ⟨b', hb', a', hab'⟩ := hright
        exact mem_union_right _ (mem_add.mpr
          ⟨a'.1, a'.2, b'.1, mem_image.mpr ⟨b', hb', rfl⟩, hab'.trans hab⟩)
    · intro hx
      rcases mem_union.mp hx with hx | hx
      · obtain ⟨a, ha, b, hb, hab⟩ := mem_add.mp hx
        obtain ⟨a', _, rfl⟩ := mem_image.mp ha
        exact mem_add.mpr ⟨a'.1, a'.2, b, hb, hab⟩
      · obtain ⟨a, ha, b, hb, hab⟩ := mem_add.mp hx
        obtain ⟨b', _, rfl⟩ := mem_image.mp hb
        exact mem_add.mpr ⟨a, ha, b'.1, b'.2, hab⟩
  · have hA := Submodule.finrank_map_le restrictA (lowDegree (ZMod 2) ι p)
    have hB := Submodule.finrank_map_le restrictB (lowDegree (ZMod 2) ι q)
    rw [finrank_lowDegree] at hA hB
    have hX : Fintype.card (ι → Bool) = 2 ^ Fintype.card ι := by simp
    rw [finrank_lowDegree, hX] at hcard
    exact (Nat.add_le_add card_image_le card_image_le).trans
      (hcard.trans (Nat.add_le_add_right (Nat.add_le_add hA hB) _))

/-- **Ellenberg's sumset cover on the Boolean cube.** At most three times the number of
degree-`⌊n/3⌋` monomials suffice to generate the whole sumset using translates of the original
summands. This includes empty summands and the zero-dimensional cube. -/
theorem exists_add_cover (A B : Finset (ι → Bool)) :
    ∃ A₀ B₀, A₀ ⊆ A ∧ B₀ ⊆ B ∧ A + B = (A₀ + B) ∪ (A + B₀) ∧
      #A₀ + #B₀ ≤ 3 * #{S : Finset ι | #S ≤ Fintype.card ι / 3} := by
  obtain ⟨A₀, B₀, hA, hB, hcover, hcard⟩ :=
    exists_add_cover_of_degree A B (Fintype.card ι / 3) (Fintype.card ι / 3)
  refine ⟨A₀, B₀, hA, hB, hcover, ?_⟩
  have hcodim := card_sub_finrank_lowDegree_le (K := ZMod 2) (ι := ι)
    (D := Fintype.card ι / 3 + Fintype.card ι / 3 + 1) (E := Fintype.card ι / 3)
    (by omega)
  rw [finrank_lowDegree] at hcodim
  omega

end Cslib.BitString
