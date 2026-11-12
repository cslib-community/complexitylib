/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Basic
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ColorPartDerivative
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ColorPartEval
public import CslibFrontier.Foundations.Combinatorics.PerfectHashFamily.Basic
public import CslibFrontier.Foundations.Data.MvPolynomial.SetPartitioned

/-!
# From support-concentrating shifts to hitting sets, for set-partitioned polynomials

The variables `σ` are split into `n` blocks by `blk : σ → Fin n`. Let `f` be a set-partitioned
polynomial (`MvPolynomial.IsSetPartitioned`) of split rank at most `w` across every union of
blocks, over a field of characteristic zero. If a shift `f (X + a)` has a monomial with at most
`L` variables, then `f` is nonzero at a point of an explicit set built from `a`
(`exists_mem_setPartitionedHittingSet_eval_ne_zero`). So a set `A` of shifts, one of which
works for every nonzero polynomial of the class, gives the hitting set
`setPartitionedHittingSet F blk A L w`, of size `|A|` times a polynomial in `n`, `|σ|`, `w` and
`2 ^ L` (`card_setPartitionedHittingSet_le`). This is Lemma 3.4 of Shpilka [Shpilka2026], in
characteristic zero.

## Proof

Let `G = f (X + a)` and let `m` be a monomial of `G` with `r ≤ L` variables. If `r = 0` then
`f a ≠ 0`. Otherwise the variables of `m` lie in `r` distinct blocks, so some colouring `h` of
the blocks with `r` colours, from `Cslib.perfectHashFamily`, is injective on them. The colour
part `g = colorPart (h ∘ blk) G` contains `m` (`colorPart_ne_zero`, the source's Lemma 3.1) and
lies in a space of dimension at most `2 ^ r * w` closed under partial derivatives
(`exists_pderiv_closed_colorPart`, Lemma 3.3), so it is nonzero at a point `b` of
`logHittingSetOn`. Finally `g b` is a combination of values of `G` at the points `t • b`
restricted to the variables with colours outside a set `J`
(`exists_eval_ne_zero_of_eval_colorPart_ne_zero`, Lemma 3.2).

## Main definitions

* `logHittingSetOn`: `logHittingSet` for variables indexed by a finite type.
* `setPartitionedHittingSet`: the points built from a set of shifts.

## Main results

* `isHittingSet_logHittingSetOn`, `card_logHittingSetOn_le`.
* `exists_mem_setPartitionedHittingSet_eval_ne_zero`: [Shpilka2026, Lemma 3.4].
* `card_setPartitionedHittingSet_le`: the size of the set.

## References

* [A. Shpilka, *Polynomial-size hitting sets for multilinear any-order read-once algebraic
  branching programs and for set-multilinear depth-3 circuits with constant-size variable
  sets*][Shpilka2026], §3, eq. (7) and Lemma 3.4 (unrefereed preprint)
-/

public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

variable (F : Type*) [Field F] [CharZero F] (σ : Type*) [Fintype σ]

/-- The hitting set `logHittingSet` for polynomials in a derivative-closed space of dimension at
most `r`, for variables indexed by a finite type `σ` through `Fintype.equivFin σ`. -/
noncomputable def logHittingSetOn (r d : ℕ) : Finset (σ → F) :=
  (logHittingSet F (Fintype.card σ) r d).map
    ⟨fun b => b ∘ Fintype.equivFin σ, (Fintype.equivFin σ).surjective.injective_comp_right⟩

variable {F σ}

theorem card_logHittingSetOn_le (r d : ℕ) :
    (logHittingSetOn F σ r d).card ≤ d * (Fintype.card σ * r ^ 2 + r) + 1 :=
  (card_map _).trans_le (card_logHittingSet_le r d)

/-- `logHittingSetOn F σ r d` hits every polynomial of degree at most `d` in the variables `σ`
that lies in a space of dimension at most `r` closed under all partial derivatives. -/
theorem isHittingSet_logHittingSetOn (r d : ℕ) :
    IsHittingSet (logHittingSetOn F σ r d)
      {f | f.totalDegree ≤ d ∧ ∃ V : Submodule F (MvPolynomial σ F),
        (∀ i, ∀ p ∈ V, pderiv i p ∈ V) ∧ Module.Finite F V ∧
          Module.finrank F V ≤ r ∧ f ∈ V} := by
  classical
  rintro f ⟨hd, V, hV, hfin, hr, hf⟩ hf0
  set e := Fintype.equivFin σ
  have hinj := rename_injective e e.injective (R := F)
  have hV' : ∀ i, ∀ p ∈ V.map (rename e).toLinearMap,
      pderiv i p ∈ V.map (rename e).toLinearMap := by
    rintro i _ ⟨p, hp, rfl⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    exact ⟨pderiv j p, hV j p hp, (pderiv_rename e.injective j p).symm⟩
  obtain ⟨b, hb, hbf⟩ := isHittingSet_logHittingSet r d (rename e f)
    ⟨(totalDegree_rename_le e f).trans hd, V.map (rename e).toLinearMap, hV',
      Module.Finite.map V _, (Submodule.finrank_map_le _ V).trans hr,
      Submodule.mem_map_of_mem hf⟩ fun h => hf0 (hinj (h.trans (map_zero _).symm))
  exact ⟨b ∘ e, mem_map_of_mem _ hb, by rwa [eval_rename] at hbf⟩

variable (F) {n : ℕ}

open scoped Classical in
/-- The points of [Shpilka2026, eq. (7)] built from a set `A` of shifts: the shifts `a`, together
with the points `a + t • b` restricted to the variables whose block has a colour outside `J`,
for a colouring `h` of the `n` blocks with `r ≤ L` colours from the perfect hash family, a set
`J` of colours, a point `b` of the hitting set for derivative-closed spaces of dimension
`2 ^ r * w` and `t = 0, …, n`. -/
noncomputable def setPartitionedHittingSet (blk : σ → Fin n) (A : Finset (σ → F)) (L w : ℕ) :
    Finset (σ → F) :=
  A ∪ (range (L + 1)).biUnion fun r =>
    (A ×ˢ perfectHashFamily n r ×ˢ (univ : Finset (Finset (Fin r))) ×ˢ
      logHittingSetOn F σ (2 ^ r * w) n ×ˢ range (n + 1)).image
      fun ⟨a, h, J, b, t⟩ v => a v + if h (blk v) ∈ J then 0 else (t : F) * b v

variable {F}

omit [CharZero F] [Fintype σ] in
private theorem support_colorPart_subset {r : ℕ} (c : σ → Fin r) (G : MvPolynomial σ F) :
    (colorPart c G).support ⊆ G.support := fun d hd => by
  classical
  rw [colorPart, support_weightedHomogeneousComponent] at hd
  exact Finset.mem_of_mem_filter d hd

/-- **From a shift to a point** ([Shpilka2026, Lemma 3.4], in characteristic zero). Let `f` be
set-partitioned for the blocks `blk`, of split rank at most `w` across every union of blocks.
If `f (X + a)` has a monomial with at most `L` variables for a shift `a` of `A`, then `f` is
nonzero at a point of `setPartitionedHittingSet F blk A L w`. -/
theorem exists_mem_setPartitionedHittingSet_eval_ne_zero {blk : σ → Fin n}
    {A : Finset (σ → F)} {L w : ℕ} {f : MvPolynomial σ F} (hpart : IsSetPartitioned blk f)
    (hsplit : ∀ I : Finset (Fin n), SplitRankLE (blk ⁻¹' (I : Set (Fin n))) w f)
    {a : σ → F} (ha : a ∈ A) {m : σ →₀ ℕ} (hm : m ∈ (shift a f).support)
    (hmL : m.support.card ≤ L) :
    ∃ x ∈ setPartitionedHittingSet F blk A L w, eval x f ≠ 0 := by
  classical
  set G := shift a f with hG
  have hGpart : IsSetPartitioned blk G := hpart.shift a
  have hGdeg : G.totalDegree ≤ n := hGpart.totalDegree_le.trans_eq (Fintype.card_fin n)
  rcases Nat.eq_zero_or_pos m.support.card with h0 | hpos
  · refine ⟨a, mem_union_left _ ha, ?_⟩
    rw [← coeff_zero_shift]
    exact Finsupp.support_eq_empty.1 (card_eq_zero.1 h0) ▸ mem_support_iff.1 hm
  · obtain ⟨h, hh, hinj⟩ := isPerfectHashFamily_perfectHashFamily n _ hpos
      (m.support.image blk) (card_image_of_injOn (hGpart m hm).2)
    have hinj' : Set.InjOn (h ∘ blk) (m.support : Set σ) := by
      refine Set.InjOn.comp (by rwa [coe_image] at hinj) (hGpart m hm).2 (Set.mapsTo_image _ _)
    have hg0 : colorPart (h ∘ blk) G ≠ 0 :=
      colorPart_ne_zero (h ∘ blk) hm (hGpart m hm).1 hinj' rfl
    obtain ⟨V, hV, hfin, hrank, hgV⟩ := exists_pderiv_closed_colorPart (h ∘ blk) (w := w)
      (G := G) fun I => by
        have hI := (hsplit (univ.filter fun j => h j ∈ I)).shift a
        have hset : blk ⁻¹' ((univ.filter fun j => h j ∈ I : Finset (Fin n)) : Set (Fin n)) =
            h ∘ blk ⁻¹' (I : Set (Fin m.support.card)) := by
          ext v
          simp
        rwa [hset] at hI
    have hgdeg : (colorPart (h ∘ blk) G).totalDegree ≤ n :=
      (totalDegree_le_of_support_subset (support_colorPart_subset _ G)).trans hGdeg
    obtain ⟨b, hb, hbg⟩ := isHittingSet_logHittingSetOn (2 ^ m.support.card * w) n
      (colorPart (h ∘ blk) G) ⟨hgdeg, V, hV, hfin, hrank, hgV⟩ hg0
    obtain ⟨t, ht, J, hJ⟩ := exists_eval_ne_zero_of_eval_colorPart_ne_zero (h ∘ blk)
      (Λ := (range (n + 1)).image Nat.cast)
      (by
        rw [card_image_of_injective _ Nat.cast_injective, card_range]
        exact Nat.lt_succ_of_le hGdeg) hbg
    obtain ⟨t', ht', rfl⟩ := mem_image.1 ht
    rw [eval_shift] at hJ
    refine ⟨fun v => a v + if h (blk v) ∈ J then 0 else (t' : F) * b v, mem_union_right _
      (mem_biUnion.2 ⟨m.support.card, mem_range.2 (Nat.lt_succ_of_le hmL), mem_image.2
        ⟨(a, h, J, b, t'), ?_, rfl⟩⟩), ?_⟩
    · simp only [mem_product, mem_univ, true_and]
      exact ⟨ha, hh, hb, ht'⟩
    · have hpt : (fun v => a v + if h (blk v) ∈ J then 0 else (t' : F) * b v) =
          fun i => (if (h ∘ blk) i ∈ J then 0 else (t' : F) * b i) + a i :=
        funext fun v => add_comm _ _
      rw [hpt]
      exact hJ

/-- The set has at most `|A| (1 + ∑ r ≤ L, n 2 ^ (25 r) 2 ^ r (n (N (2 ^ r w)² + 2 ^ r w) + 1)
(n + 1))` points, where `N` is the number of variables. -/
theorem card_setPartitionedHittingSet_le (blk : σ → Fin n) (A : Finset (σ → F)) (L w : ℕ) :
    (setPartitionedHittingSet F blk A L w).card ≤
      A.card * (1 + ∑ r ∈ range (L + 1), n * 2 ^ (25 * r) *
        (2 ^ r * ((n * (Fintype.card σ * (2 ^ r * w) ^ 2 + 2 ^ r * w) + 1) * (n + 1)))) := by
  classical
  unfold setPartitionedHittingSet
  rw [mul_add, mul_one, mul_sum]
  refine (card_union_le _ _).trans (add_le_add_right (card_biUnion_le.trans
    (sum_le_sum fun r _ => card_image_le.trans ?_)) _)
  simp only [card_product, card_univ, Fintype.card_finset, Fintype.card_fin, card_range]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (card_perfectHashFamily_le n r)
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (card_logHittingSetOn_le _ _))))

end Cslib.Circuits.Arithmetic
