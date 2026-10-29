/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate (Mathlib, set-multilinear polynomials)

public import Complexity.Foundations.Data.Finset.Finpartition
public import Complexity.Foundations.Data.MvPolynomial.SetMultilinearProjection
public import Complexity.Foundations.LinearAlgebra.Matrix.RectPermanent

/-!
# The set-multilinear projection of a product, by set partitions

For a product `∏ j, f j` of polynomials, `MvPolynomial.smProj_prod` writes the part on a set `S` of
blocks as a sum over the ordered splits of `S` into one part for each factor. A factor that gets
the empty part contributes its constant term, so grouping the splits by their nonempty parts
writes it as a sum over the set partitions `P` of `S` and the injections `e` of the parts of `P`
into the factors (`MvPolynomial.smProj_prod_eq_sum_finpartition`):

`π_S(∏ j, f j) = ∑_P ∑_{e : P ↪ ι} ∏_{T ∈ P} π_T(f (e T)) · ∏_{j ∉ im e} f_j(0)`.

Over a field, let `Z` be the set of factors with constant term `0`. Dividing each factor outside
`Z` by its constant term turns the inner sum into a rectangular permanent restricted to the
injections whose image contains `Z` (`Matrix.rectPermSurj`), and the Binet–Minc identity with
inclusion–exclusion (`Matrix.rectPermSurj_eq_sum_sign_prod_sameCycle`) expands it as a signed sum
over the permutations of the parts of `P` and the subsets of `Z`
(`MvPolynomial.smProj_prod_eq_sum_sign`). This is the expansion of the proof of
[Forbes2024, Lemma 26], pp. 31:13–31:14, with inclusion–exclusion in place of [Forbes2024,
Lemma 21] (p. 31:12) and the permutation form of the Binet–Minc identity in place of its partition
form [Forbes2024, Theorem 13] (p. 31:10). Its number of products of sums is bounded in terms of
`#S` and `#Z` only, not of the number of factors. If `#S < #Z` the part is `0`
(`MvPolynomial.smProj_prod_eq_zero_of_card_lt`).

## Main results

* `MvPolynomial.smProj_prod_eq_sum_finpartition`: the part of a product, by set partitions.
* `MvPolynomial.smProj_prod_eq_zero_of_card_lt`: it vanishes when more than `#S` factors have
  constant term `0`.
* `MvPolynomial.smProj_prod_eq_sum_sign`: the part of a product over a field, by the Binet–Minc
  identity.

## References

* [M. A. Forbes, *Low-depth algebraic circuit lower bounds over any field*][Forbes2024], proof of
  Lemma 26, pp. 31:13–31:14, which collects the set-multilinear terms of a product by set partitions
  and injections and writes them as surjective permanents. The statements here as identities of
  polynomials, the normalization by the constant terms in this form and the use of
  inclusion–exclusion and of the permutation form of the Binet–Minc identity are original.
-/

@[expose] public section

open Finset

namespace MvPolynomial

open Equiv Equiv.Perm

variable {σ K ι : Type*} {d : ℕ}

section Split

variable [DecidableEq ι] {S : Finset (Fin d)}

/-- The ordered split of `S` given by a set partition `P` of `S` and an injection `e` of its parts
into `ι`: the part at `j` is the part of `P` sent to `j` by `e`, or `∅` if there is none. -/
private def partSplit (P : Finpartition S) (e : P.parts ↪ ι) (j : ι) : Finset (Fin d) :=
  (univ.filter fun r => e r = j).biUnion Subtype.val

variable {P : Finpartition S} {e : P.parts ↪ ι}

/-- The split puts each part of `P` at its image under `e`. -/
private theorem partSplit_apply (r : P.parts) : partSplit P e (e r) = r := by
  have h : (univ.filter fun r' => e r' = e r) = {r} := by
    ext r'
    simp only [mem_filter, mem_univ, true_and, mem_singleton, e.injective.eq_iff]
  rw [partSplit, h, singleton_biUnion]

/-- The split is empty outside the image of `e`. -/
private theorem partSplit_of_notMem {j : ι} (hj : j ∉ univ.map e) : partSplit P e j = ∅ := by
  rw [partSplit, filter_false_of_mem fun r _ h => hj (mem_map.2 ⟨r, mem_univ r, h⟩),
    biUnion_empty]

/-- A part of `P` sits only at its image under `e`. -/
private theorem eq_of_partSplit_eq {j : ι} {r : P.parts} (h : partSplit P e j = r) :
    j = e r := by
  by_cases hj : j ∈ univ.map e
  · obtain ⟨r', -, rfl⟩ := mem_map.1 hj
    rw [partSplit_apply] at h
    rw [Subtype.ext h]
  · rw [partSplit_of_notMem hj] at h
    exact absurd h.symm (P.nonempty_of_mem_parts r.2).ne_empty

/-- The split is an ordered split of `S`. -/
private theorem partSplit_mem_blockSplits [Fintype ι] : partSplit P e ∈ blockSplits ι S := by
  refine mem_blockSplits.2 ⟨fun j k hjk => ?_, ?_⟩
  · rw [Function.onFun, partSplit, partSplit]
    refine (disjoint_biUnion_left _ _ _).2 fun r hr =>
      (disjoint_biUnion_right _ _ _).2 fun r' hr' => ?_
    have hrr' : r ≠ r' := by
      rintro rfl
      exact hjk ((mem_filter.1 hr).2.symm.trans (mem_filter.1 hr').2)
    exact P.disjoint r.2 r'.2 (Subtype.coe_ne_coe.2 hrr')
  · refine Eq.trans ?_ P.biUnion_parts
    ext x
    simp only [mem_biUnion, partSplit, mem_filter, mem_univ, true_and, id]
    constructor
    · rintro ⟨-, r, -, hx⟩
      exact ⟨r, r.2, hx⟩
    · rintro ⟨t, ht, hx⟩
      exact ⟨e ⟨t, ht⟩, ⟨t, ht⟩, rfl, hx⟩

/-- The parts of `P` are the nonempty parts of the split. -/
private theorem mem_parts_iff_exists_partSplit_eq {t : Finset (Fin d)} :
    t ∈ P.parts ↔ t.Nonempty ∧ ∃ j, partSplit P e j = t := by
  constructor
  · intro ht
    exact ⟨P.nonempty_of_mem_parts ht, e ⟨t, ht⟩, partSplit_apply _⟩
  · rintro ⟨ht, j, rfl⟩
    by_cases hj : j ∈ univ.map e
    · obtain ⟨r, -, rfl⟩ := mem_map.1 hj
      rw [partSplit_apply]
      exact r.2
    · rw [partSplit_of_notMem hj] at ht
      exact absurd ht not_nonempty_empty

/-- The split determines the set partition and the injection. -/
private theorem partSplit_injective {x y : Σ P : Finpartition S, P.parts ↪ ι}
    (h : partSplit x.1 x.2 = partSplit y.1 y.2) : x = y := by
  obtain ⟨P, e⟩ := x
  obtain ⟨P', e'⟩ := y
  dsimp only at h
  obtain rfl : P = P' := Finpartition.ext <| Finset.ext fun t => by
    rw [mem_parts_iff_exists_partSplit_eq (e := e), mem_parts_iff_exists_partSplit_eq (e := e'), h]
  obtain rfl : e = e' := Function.Embedding.ext fun r =>
    eq_of_partSplit_eq ((congrFun h (e r)).symm.trans (partSplit_apply r))
  rfl

/-- Every ordered split of `S` comes from a set partition of `S` and an injection of its parts. -/
private theorem exists_partSplit_eq [Fintype ι] {T : ι → Finset (Fin d)}
    (hT : T ∈ blockSplits ι S) :
    ∃ x : Σ P : Finpartition S, P.parts ↪ ι, partSplit x.1 x.2 = T := by
  obtain ⟨hdisj, hU⟩ := mem_blockSplits.1 hT
  have hind : (univ.image T).SupIndep id := by
    rw [supIndep_iff_pairwiseDisjoint]
    rintro _ hs _ ht hst
    obtain ⟨j, -, rfl⟩ := mem_image.1 hs
    obtain ⟨k, -, rfl⟩ := mem_image.1 ht
    exact hdisj fun hjk => hst (hjk ▸ rfl)
  have hsup : (univ.image T).sup id = S := by
    rw [sup_image, Function.id_comp, sup_eq_biUnion, hU]
  let P := Finpartition.ofErase (univ.image T) hind hsup
  have hP (r : P.parts) : ∃ j, T j = r := by
    obtain ⟨j, -, hj⟩ := mem_image.1 (mem_of_mem_erase r.2)
    exact ⟨j, hj⟩
  choose g hg using hP
  refine ⟨⟨P, ⟨g, fun r r' h => Subtype.ext ((hg r).symm.trans (h ▸ hg r'))⟩⟩,
    funext fun j => ?_⟩
  ext x
  simp only [partSplit, mem_biUnion, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨r, rfl, hx⟩
    exact hg r ▸ hx
  · intro hx
    have hj : T j ∈ P.parts := mem_erase.2 ⟨ne_empty_of_mem hx, mem_image_of_mem T (mem_univ j)⟩
    refine ⟨⟨T j, hj⟩, ?_, hx⟩
    by_contra hne
    exact disjoint_left.1 (hdisj hne) ((hg ⟨T j, hj⟩).symm ▸ hx) hx

/-- The term of the split: the parts of `P` on their factors, and the constant terms of the other
factors. -/
private theorem prod_smProj_partSplit [Fintype ι] [CommSemiring K] (blk : σ → Fin d)
    (f : ι → MvPolynomial σ K) :
    ∏ j, smProj blk (partSplit P e j) (f j) =
      (∏ r : P.parts, smProj blk r (f (e r))) * ∏ j ∈ (univ.map e)ᶜ, C (constantCoeff (f j)) := by
  rw [← prod_mul_prod_compl (univ.map e), prod_map]
  congr 1
  · exact prod_congr rfl fun r _ => by rw [partSplit_apply]
  · exact prod_congr rfl fun j hj => by rw [partSplit_of_notMem (mem_compl.1 hj), smProj_empty]

end Split

variable [Fintype ι] [DecidableEq ι]

/-- **The part of a product, by set partitions** (original as stated; the collection of terms in
the proof of [Forbes2024, Lemma 26], p. 31:14): the part on `S` of `∏ j, f j` is the sum over the
set partitions `P` of `S` and the injections `e` of the parts of `P` into the factors of the
product of the parts `π_T(f (e T))`, times the constant terms of the factors outside the image of
`e`. -/
theorem smProj_prod_eq_sum_finpartition [CommSemiring K] (blk : σ → Fin d) (S : Finset (Fin d))
    (f : ι → MvPolynomial σ K) :
    smProj blk S (∏ j, f j) = ∑ P : Finpartition S, ∑ e : P.parts ↪ ι,
      (∏ r : P.parts, smProj blk r (f (e r))) * ∏ j ∈ (univ.map e)ᶜ, C (constantCoeff (f j)) := by
  rw [smProj_prod, ← Fintype.sum_sigma' fun (P : Finpartition S) (e : P.parts ↪ ι) =>
    (∏ r : P.parts, smProj blk r (f (e r))) * ∏ j ∈ (univ.map e)ᶜ, C (constantCoeff (f j))]
  symm
  refine sum_bij (fun x _ => partSplit x.1 x.2) (fun x _ => partSplit_mem_blockSplits)
    (fun x _ y _ h => partSplit_injective h) (fun T hT => ?_)
    (fun x _ => (prod_smProj_partSplit blk f).symm)
  obtain ⟨x, hx⟩ := exists_partSplit_eq hT
  exact ⟨x, mem_univ x, hx⟩

omit [DecidableEq ι] in
/-- **The part of a product vanishes when too many factors vanish at `0`** (original): if more
than `#S` factors have constant term `0`, the part on `S` of the product is `0`. -/
theorem smProj_prod_eq_zero_of_card_lt [CommSemiring K] (blk : σ → Fin d) {S : Finset (Fin d)}
    (f : ι → MvPolynomial σ K) {Z : Finset ι} (hZ : ∀ j ∈ Z, constantCoeff (f j) = 0)
    (h : #S < #Z) : smProj blk S (∏ j, f j) = 0 := by
  classical
  rw [smProj_prod_eq_sum_finpartition]
  refine sum_eq_zero fun P _ => sum_eq_zero fun e _ => ?_
  obtain ⟨j, hjZ, hje⟩ : ∃ j ∈ Z, j ∉ univ.map e := by
    by_contra! hsub
    have := (card_le_card hsub).trans_eq (card_map e)
    rw [card_univ, Fintype.card_coe] at this
    exact absurd (this.trans P.card_parts_le_card) (not_le.2 h)
  rw [prod_eq_zero (mem_compl.2 hje) (by rw [hZ j hjZ, map_zero]), mul_zero]

section Field

variable [Field K]

/-- Over a field, the sum over the injections of the parts of one set partition, normalized by the
nonzero constant terms, is a rectangular permanent restricted to the injections whose image
contains the factors `Z` with constant term `0` (original). -/
private theorem sum_embedding_eq_C_mul_rectPermSurj (blk : σ → Fin d) {S : Finset (Fin d)}
    (P : Finpartition S) (f : ι → MvPolynomial σ K) {Z : Finset ι}
    (hZ : ∀ j, j ∈ Z ↔ constantCoeff (f j) = 0) {u : ι → K} (hu₀ : ∀ j ∈ Z, u j = 1)
    (hu : ∀ j ∉ Z, u j * constantCoeff (f j) = 1) :
    ∑ e : P.parts ↪ ι,
        (∏ r : P.parts, smProj blk r (f (e r))) * ∏ j ∈ (univ.map e)ᶜ, C (constantCoeff (f j)) =
      C (∏ j ∈ Zᶜ, constantCoeff (f j)) *
        (Matrix.of fun (r : P.parts) j => C (u j) * smProj blk r (f j)).rectPermSurj Z := by
  rw [Matrix.rectPermSurj, sum_filter, mul_sum]
  refine sum_congr rfl fun e _ => ?_
  split_ifs with hZe
  · -- The constant terms outside the image of `e` are the normalization times the scales.
    set a := fun j => constantCoeff (f j)
    set M := univ.map e
    let a' := fun j => if j ∈ Z then 1 else a j
    have ha' : ∏ j ∈ Zᶜ, a j = ∏ j, a' j := by
      rw [← prod_mul_prod_compl Z a', prod_eq_one (s := Z) (f := a') fun j hj => ?_, one_mul]
      · exact prod_congr rfl fun j hj => by simp [a', mem_compl.1 hj]
      · simp [a', hj]
    have hau : (∏ j ∈ M, a' j) * ∏ j ∈ M, u j = 1 := by
      rw [← prod_mul_distrib]
      refine prod_eq_one fun j _ => ?_
      by_cases hj : j ∈ Z
      · simp [a', hj, hu₀ j hj]
      · simpa [a', hj, mul_comm] using hu j hj
    have key : ∏ j ∈ Mᶜ, a j = (∏ j ∈ Zᶜ, a j) * ∏ r, u (e r) := by
      rw [ha', ← prod_mul_prod_compl M a', ← prod_map univ e u, mul_right_comm, hau, one_mul]
      refine prod_congr rfl fun j hj => ?_
      have hjZ : j ∉ Z := fun hjZ => mem_compl.1 hj (hZe hjZ)
      simp [a', hjZ]
    simp only [Matrix.of_apply, prod_mul_distrib, ← map_prod C]
    rw [key, map_mul]
    ring
  · obtain ⟨j, hjZ, hje⟩ := not_subset.1 hZe
    rw [prod_eq_zero (mem_compl.2 hje) (by rw [(hZ j).1 hjZ, map_zero]), mul_zero, mul_zero]

/-- **The part of a product over a field, by the Binet–Minc identity** (original as stated; the
expansion of the proof of [Forbes2024, Lemma 26], pp. 31:13–31:14, with inclusion–exclusion in
place of [Forbes2024, Lemma 21] and the permutation form of the Binet–Minc identity in place of
[Forbes2024, Theorem 13], p. 31:10). Let `Z` be the set
of factors with constant term `0`, and let `u j` be the inverse of the constant term of `f j` for
`j ∉ Z` and `1` for `j ∈ Z`. Then the part on `S` of `∏ j, f j` is the product of the nonzero
constant terms times the sum, over the set partitions `P` of `S`, the permutations `π` of the
parts of `P` and the subsets `Y ⊆ Z`, of `sgn π (-1) ^ #Y` times the product over the orbits `q`
of `π` of `∑_{j ∉ Y} u j ^ #q ∏_{T ∈ q} π_T(f j)`. -/
theorem smProj_prod_eq_sum_sign (blk : σ → Fin d) (S : Finset (Fin d))
    (f : ι → MvPolynomial σ K) {Z : Finset ι} (hZ : ∀ j, j ∈ Z ↔ constantCoeff (f j) = 0)
    {u : ι → K} (hu₀ : ∀ j ∈ Z, u j = 1) (hu : ∀ j ∉ Z, u j * constantCoeff (f j) = 1) :
    smProj blk S (∏ j, f j) = C (∏ j ∈ Zᶜ, constantCoeff (f j)) *
      ∑ P : Finpartition S, ∑ π : Perm P.parts, C ((sign π : ℤ) : K) *
        ∑ Y ∈ Z.powerset, C ((-1) ^ #Y) * ∏ q : Quotient (SameCycle.setoid π),
          ∑ j ∈ Yᶜ, C (u j ^ #{r | Quotient.mk _ r = q}) *
            ∏ r with Quotient.mk _ r = q, smProj blk r (f j) := by
  rw [smProj_prod_eq_sum_finpartition, mul_sum]
  refine sum_congr rfl fun P _ => ?_
  rw [sum_embedding_eq_C_mul_rectPermSurj blk P f hZ hu₀ hu,
    Matrix.rectPermSurj_eq_sum_sign_prod_sameCycle]
  congr 1
  refine sum_congr rfl fun π _ => ?_
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : K →+* MvPolynomial σ K)]
  congr 1
  refine sum_congr rfl fun Y _ => ?_
  rw [map_pow, map_neg, map_one]
  congr 1
  refine prod_congr rfl fun q _ => sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply, prod_mul_distrib, prod_const, map_pow]

end Field

end MvPolynomial
