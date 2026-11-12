/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.SetMultilinear
public import CslibFrontier.Foundations.Data.MvPolynomial.Shift

/-!
# Set-partitioned polynomials

The variables `σ` of a polynomial are split into blocks by a map `blk : σ → ι`. A polynomial is
*set-partitioned* (`MvPolynomial.IsSetPartitioned`) if each of its monomials has at most one
variable of each block, to the first power. A set-multilinear polynomial is set-partitioned
(`MvPolynomial.IsSetMultilinear.isSetPartitioned`). Unlike set-multilinear polynomials,
set-partitioned polynomials are closed under shifts `f ↦ f (X + a)`
(`MvPolynomial.IsSetPartitioned.shift`), because every monomial of a shift divides a monomial of
the polynomial (`MvPolynomial.exists_le_of_mem_support_shift`). When every block is a single
variable, set-partitioned means multilinear (`MvPolynomial.isSetPartitioned_id_iff`).

## Main definitions

* `MvPolynomial.IsSetPartitioned`: every monomial has at most one variable of each block, to the
  first power.

## Main results

* `MvPolynomial.exists_le_of_mem_support_shift`: a monomial of `f (X + a)` divides a monomial
  of `f`.
* `MvPolynomial.IsSetPartitioned.shift`: shifts of set-partitioned polynomials are
  set-partitioned.
* `MvPolynomial.IsSetPartitioned.totalDegree_le`: the degree is at most the number of blocks.

## References

* [A. Shpilka, *Polynomial-size hitting sets for multilinear any-order read-once algebraic
  branching programs and for set-multilinear depth-3 circuits with constant-size variable
  sets*][Shpilka2026], §2, where a polynomial that "respects" a partition is called
  set-partitioned (unrefereed preprint)
-/

@[expose] public section

namespace MvPolynomial

variable {σ ι R A : Type*} [CommSemiring R]

/-- A monomial of `f (X + a)` divides a monomial of `f`. -/
theorem exists_le_of_mem_support_shift [CommSemiring A] [Algebra R A] (a : σ → A)
    {f : MvPolynomial σ R} {m : σ →₀ ℕ} (hm : m ∈ (shift a f).support) :
    ∃ m' ∈ f.support, m ≤ m' := by
  classical
  rw [f.as_sum, map_sum] at hm
  obtain ⟨m', hm', hmm'⟩ := Finset.mem_biUnion.1 (support_sum hm)
  refine ⟨m', hm', fun j => ?_⟩
  refine (monomial_le_degreeOf j hmm').trans ((degreeOf_shift_le a _ j).trans ?_)
  exact degreeOf_le_iff.2 fun d hd => by rw [Finset.mem_singleton.1 (support_monomial_subset hd)]

/-- Every monomial of `f` has at most one variable of each block of `blk`, to the first
power. -/
def IsSetPartitioned (blk : σ → ι) (f : MvPolynomial σ R) : Prop :=
  ∀ m ∈ f.support, (∀ v, m v ≤ 1) ∧ Set.InjOn blk (m.support : Set σ)

/-- A set-multilinear polynomial is set-partitioned. -/
theorem IsSetMultilinear.isSetPartitioned {d : ℕ} {blk : σ → Fin d} {S : Finset (Fin d)}
    {f : MvPolynomial σ R} (hf : IsSetMultilinear blk S f) : IsSetPartitioned blk f := by
  classical
  intro m hm
  obtain ⟨x, rfl⟩ := hf m hm
  have h1 (v : σ) : blockMonomial blk S x v ≠ 0 →
      ∃ h : blk v ∈ S, (x ⟨blk v, h⟩ : σ) = v := fun hv => by
    rw [blockMonomial_apply] at hv
    by_contra hcon
    push Not at hcon
    split_ifs at hv with h hx
    exacts [hcon h hx, hv rfl, hv rfl]
  refine ⟨fun v => ?_, fun u hu v hv huv => ?_⟩
  · rw [blockMonomial_apply]
    split_ifs <;> simp
  · obtain ⟨hu', hxu⟩ := h1 u (Finsupp.mem_support_iff.1 hu)
    obtain ⟨hv', hxv⟩ := h1 v (Finsupp.mem_support_iff.1 hv)
    exact hxu.symm.trans ((congrArg (fun i : S => (x i : σ)) (Subtype.ext huv)).trans hxv)

namespace IsSetPartitioned

variable {blk : σ → ι} {f : MvPolynomial σ R}

/-- A shift of a set-partitioned polynomial is set-partitioned. -/
protected theorem shift [CommSemiring A] [Algebra R A] (hf : IsSetPartitioned blk f)
    (a : σ → A) : IsSetPartitioned blk (shift a f) := fun m hm => by
  obtain ⟨m', hm', hle⟩ := exists_le_of_mem_support_shift a hm
  exact ⟨fun v => (hle v).trans ((hf m' hm').1 v),
    (hf m' hm').2.mono (Finset.coe_subset.2 (Finsupp.support_mono hle))⟩

/-- A set-partitioned polynomial has degree at most the number of blocks. -/
theorem totalDegree_le [Fintype ι] (hf : IsSetPartitioned blk f) :
    f.totalDegree ≤ Fintype.card ι := by
  classical
  refine Finset.sup_le fun m hm => ?_
  calc (m.sum fun _ e => e) ≤ ∑ _v ∈ m.support, 1 := Finset.sum_le_sum fun v _ => (hf m hm).1 v
    _ = (m.support.image blk).card := by
      rw [Finset.card_image_of_injOn (hf m hm).2, Finset.card_eq_sum_ones]
    _ ≤ Fintype.card ι := Finset.card_le_univ _

end IsSetPartitioned

/-- When every block is one variable, set-partitioned means multilinear. -/
theorem isSetPartitioned_id_iff {f : MvPolynomial σ R} :
    IsSetPartitioned id f ↔ ∀ i, f.degreeOf i ≤ 1 :=
  ⟨fun h i => degreeOf_le_iff.2 fun m hm => (h m hm).1 i,
    fun h _ hm => ⟨fun v => (monomial_le_degreeOf v hm).trans (h v), Set.injOn_id _⟩⟩

end MvPolynomial
