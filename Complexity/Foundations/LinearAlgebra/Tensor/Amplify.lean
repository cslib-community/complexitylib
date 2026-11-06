/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, bilinear complexity: amplification of shared-left packings)

public import Complexity.Foundations.LinearAlgebra.Tensor.Degeneration
public import Complexity.Foundations.LinearAlgebra.Tensor.Polynomial
import Mathlib.Combinatorics.Pigeonhole

/-!
# Amplification of a shared-left packing

A shared-left degeneration of `n` copies of a source `S` to `m` targets `F i` tensors with its
dual (the exchange of the right input and the output, which keeps the left leg) and with itself
`d` times, giving a shared-left degeneration of `n ^ (2 d)` copies of
`tpow d S ⊗ tpow d (swap23 S)` to the shared-left sum, over all pairs of words
`w w' : Fin d → Fin m`, of the targets `tprodPi (F ∘ w) ⊗ tprodPi (swap23 ∘ F ∘ w')`
(`IsSLDegen.amplify`; [Pass][Pass2026], Lemma 3.2, first half). The order multiplies by `2 d`.

When the targets are full and middle products `full a b` and `mid a b`, the word tensors whose
total numbers of full and middle factors are both `d` are reindexings of the canonical tensor
`tprod (tpow d (full a b)) (tpow d (mid a b))` (`exists_reindex_eq_canonical`): a word `w` with
exactly `h` middle letters paired with a word `w'` with exactly `h` middle letters, since the
dual of a middle product is a full product. Counting such words ([Pass][Pass2026], Claim 3.3):
the words with exactly `h` middle letters, `h = 0, …, d`, partition the `m ^ d` words, so some
`h` has at least `m ^ d / (d + 1)` of them (`exists_card_filter_count_ge`); squaring gives the
`m ^ (2 d) / (d + 1) ^ 2` retained pairs, which loses only a factor polynomial in `d` compared
with the Cauchy–Schwarz count of the source.

## Main results

* `Cslib.Tensor.IsSLDegen.amplify`: tensoring with the dual and taking the `d`-th power.
* `Cslib.Tensor.exists_card_filter_count_ge`: a fibre of the count of middle letters is large.
* `Cslib.Tensor.exists_reindex_eq_canonical`: balanced word tensors are reindexings of the
  canonical tensor.

## References

* [R. Pass, *Matrix Multiplication from Polynomial Packings*][Pass2026], Lemma 3.2 and
  Claim 3.3
-/

@[expose] public section

namespace Cslib.Tensor

open Finset

variable {K : Type*} [CommRing K] {X Y Z X' Y' Z' : Type*}

/-- **Amplification** ([Pass][Pass2026], Lemma 3.2): tensor a shared-left degeneration with its
dual and take the `d`-th tensor power. The targets are indexed by pairs of words. -/
theorem IsSLDegen.amplify [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X'] {m n h : ℕ}
    {f : X → X'} {F : Fin m → Tensor K X Y Z} {S : Tensor K X' Y' Z'}
    (hF : IsSLDegen f h (Tensor.slSum F) (Tensor.slSum fun _ : Fin n => S)) (d : ℕ) :
    IsSLDegen (Prod.map (fun x i => f (x i)) (fun x i => f (x i))) (2 * d * h)
      (Tensor.slSum fun w : (Fin d → Fin m) × (Fin d → Fin m) =>
        Tensor.tprod (Tensor.tprodPi (F ∘ w.1)) (Tensor.tprodPi (Tensor.swap23 ∘ F ∘ w.2)))
      (Tensor.slSum fun _ : Fin (n ^ (2 * d)) =>
        Tensor.tprod (Tensor.tpow d S) (Tensor.tpow d (Tensor.swap23 S))) := by
  classical
  -- the dual packing
  have hF' : IsSLDegen f h (slSum fun i => Tensor.swap23 (F i))
      (slSum fun _ : Fin n => Tensor.swap23 S) := by
    have := hF.swap23
    rwa [swap23_slSum, swap23_slSum] at this
  -- the `d`-th powers, as shared-left sums over words
  have h₁ := hF.tpow d
  have h₂ := hF'.tpow d
  rw [tpow_slSum, tpow_slSum] at h₁ h₂
  have h₁' := h₁.of_reindex_target.of_reindex_source
  have h₂' := h₂.of_reindex_target.of_reindex_source
  simp only [Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, Function.id_comp] at h₁' h₂'
  -- their tensor product, as a shared-left sum over pairs of words
  have h₃ := h₁'.tprod h₂'
  rw [tprod_slSum, tprod_slSum] at h₃
  have h₄ := h₃.of_reindex_target.of_reindex_source
  simp only [Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, Function.id_comp] at h₄
  rw [show 2 * d * h = d * h + d * h by ring]
  -- number the sources
  refine IsSLDegen.slSum_source_comp (G := fun _ : Fin (n ^ (2 * d)) =>
    Tensor.tprod (Tensor.tpow d S) (Tensor.tpow d (Tensor.swap23 S)))
    (Fintype.equivFinOfCardEq (by simp [Fintype.card_prod, two_mul, pow_add]) :
      (Fin d → Fin n) × (Fin d → Fin n) ≃ Fin (n ^ (2 * d)))
    (Equiv.injective _) ?_
  exact h₄

/-- **Counting words by type** ([Pass][Pass2026], Claim 3.3, in the form used here): the words
`Fin d → Fin m` with exactly `h` letters in `M`, for `h = 0, …, d`, partition all `m ^ d` words,
so for some `h` there are at least `m ^ d / (d + 1)` of them. -/
theorem exists_card_filter_count_ge (m d : ℕ) (M : Finset (Fin m)) :
    ∃ h ≤ d, m ^ d ≤ (d + 1) *
      (univ.filter fun w : Fin d → Fin m => (univ.filter fun i => w i ∈ M).card = h).card := by
  classical
  obtain ⟨h, hh, hcard⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := (univ : Finset (Fin d → Fin m))) (t := Finset.range (d + 1))
    (f := fun w => (univ.filter fun i => w i ∈ M).card) (b := (m ^ d : ℚ) / (d + 1))
    (fun w _ => Finset.mem_range.2 (Nat.lt_succ_of_le
      ((Finset.card_filter_le _ _).trans (by simp))))
    ⟨0, Finset.mem_range.2 (Nat.succ_pos d)⟩ (by
      rw [Finset.card_range, nsmul_eq_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin]
      push_cast
      rw [mul_div_cancel₀ _ (by positivity)])
  refine ⟨h, Nat.lt_succ_iff.1 (Finset.mem_range.1 hh), ?_⟩
  rw [div_le_iff₀ (by positivity), mul_comm] at hcard
  exact_mod_cast hcard

/-- The canonical balanced tensor: `d` full products tensored with `d` middle products. -/
def canonical (d a b : ℕ) :
    Tensor K ((Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1)))
      ((Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1)))
      ((Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1))) :=
  tprod (tpow d (full a b)) (tpow d (mid a b))

/-- The full-or-middle targets of the primal packing, by the set `M` of middle positions. -/
def fullOrMid (a b : ℕ) {m : ℕ} (M : Finset (Fin m)) (i : Fin m) :
    Tensor K (Fin (a + b - 1)) (Fin (a + b - 1)) (Fin (a + b - 1)) :=
  if i ∈ M then mid a b else full a b

/-- **Balanced words are canonical** ([Pass][Pass2026], proof of Lemma 3.2): if `w` and `w'`
each have exactly `h` middle letters, the word tensor
`tprodPi (fullOrMid ∘ w) ⊗ tprodPi (swap23 ∘ fullOrMid ∘ w')` has `d` full and `d` middle
factors, so it is the canonical tensor reindexed along one permutation of the `2 d`
coordinates, applied to all three legs. -/
theorem exists_reindex_eq_canonical (a b : ℕ) {m d h : ℕ} (M : Finset (Fin m))
    (w w' : Fin d → Fin m) (hw : (univ.filter fun i => w i ∈ M).card = h)
    (hw' : (univ.filter fun i => w' i ∈ M).card = h) :
    ∃ e : (Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1)) ≃
        (Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1)),
      tprod (tprodPi (fullOrMid a b M ∘ w)) (tprodPi (swap23 ∘ fullOrMid a b M ∘ w')) =
        reindex e e e (canonical d a b : Tensor K _ _ _) := by
  classical
  -- the `2 d` factors, and the set of positions carrying a full product
  let g : Fin d ⊕ Fin d → Tensor K (Fin (a + b - 1)) (Fin (a + b - 1)) (Fin (a + b - 1)) :=
    Sum.elim (fullOrMid a b M ∘ w) (swap23 ∘ fullOrMid a b M ∘ w')
  let P : Finset (Fin d ⊕ Fin d) :=
    (univ.filter fun i => w i ∉ M).disjSum (univ.filter fun i => w' i ∈ M)
  have hg : ∀ p, g p = if p ∈ P then full a b else mid a b := by
    rintro (i | i)
    · by_cases hi : w i ∈ M <;> simp [g, P, fullOrMid, hi]
    · by_cases hi : w' i ∈ M <;> simp [g, P, fullOrMid, mid, hi]
  -- exactly `d` positions carry a full product
  have hle : h ≤ d := by
    rw [← hw]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hneg : (univ.filter fun i => w i ∉ M).card = d - h := by
    have := Finset.card_filter_add_card_filter_not (s := univ) (p := fun i => w i ∈ M)
    rw [hw, Finset.card_univ, Fintype.card_fin] at this
    omega
  have hcard : Fintype.card {p // p ∈ P} = d := by
    rw [Fintype.card_coe, Finset.card_disjSum, hneg, hw']
    omega
  have hcard' : Fintype.card {p // ¬ p ∈ P} = d := by
    rw [Fintype.card_subtype_compl, hcard, Fintype.card_sum, Fintype.card_fin]
    omega
  -- the permutation of positions sending the first half onto the full positions
  let σ : Fin d ⊕ Fin d ≃ Fin d ⊕ Fin d :=
    (Equiv.sumCongr (Fintype.equivFinOfCardEq hcard).symm
      (Fintype.equivFinOfCardEq hcard').symm).trans (Equiv.sumCompl (· ∈ P))
  have hσl : ∀ i, σ (Sum.inl i) ∈ P := fun i => by
    simp only [σ, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact ((Fintype.equivFinOfCardEq hcard).symm i).2
  have hσr : ∀ i, ¬ σ (Sum.inr i) ∈ P := fun i => by
    simp only [σ, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact ((Fintype.equivFinOfCardEq hcard').symm i).2
  -- the induced reindexing of the legs
  let e' : (Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1)) ≃
      (Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1)) :=
    (Equiv.sumArrowEquivProdArrow _ _ _).symm.trans
      ((Equiv.arrowCongr σ (Equiv.refl _)).symm.trans (Equiv.sumArrowEquivProdArrow _ _ _))
  have he' : ∀ p : (Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1)),
      e' p = (fun i => Sum.elim p.1 p.2 (σ (Sum.inl i)),
        fun i => Sum.elim p.1 p.2 (σ (Sum.inr i))) :=
    fun p => rfl
  refine ⟨e'.symm, ?_⟩
  funext x y z
  simp only [reindex_apply, Equiv.symm_symm, he', canonical, tprod_apply, tpow_apply, tprodPi_apply,
    Function.comp_apply]
  calc (∏ i, fullOrMid a b M (w i) (x.1 i) (y.1 i) (z.1 i)) *
        ∏ i, swap23 (fullOrMid a b M (w' i)) (x.2 i) (y.2 i) (z.2 i)
      = ∏ p, g p (Sum.elim x.1 x.2 p) (Sum.elim y.1 y.2 p) (Sum.elim z.1 z.2 p) := by
        rw [Fintype.prod_sum_type]
        rfl
    _ = ∏ p, g (σ p) (Sum.elim x.1 x.2 (σ p)) (Sum.elim y.1 y.2 (σ p)) (Sum.elim z.1 z.2 (σ p)) :=
        (Equiv.prod_comp σ _).symm
    _ = (∏ i, full a b (Sum.elim x.1 x.2 (σ (Sum.inl i))) (Sum.elim y.1 y.2 (σ (Sum.inl i)))
          (Sum.elim z.1 z.2 (σ (Sum.inl i)))) *
        ∏ i, mid a b (Sum.elim x.1 x.2 (σ (Sum.inr i))) (Sum.elim y.1 y.2 (σ (Sum.inr i)))
          (Sum.elim z.1 z.2 (σ (Sum.inr i))) := by
        rw [Fintype.prod_sum_type]
        congr 1
        · exact Finset.prod_congr rfl fun i _ => by rw [hg, ite_eq_left (hσl i)]
        · exact Finset.prod_congr rfl fun i _ => by rw [hg, ite_eq_right (hσr i)]

end Cslib.Tensor
