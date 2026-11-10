/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
import CslibFrontier.Foundations.Combinatorics.SmallSubsets
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Ray-Chaudhuri–Wilson and Frankl–Wilson bounds

Bounds on families of subsets of a finite set `κ`, `n = |κ|`, whose pairwise intersection sizes
are restricted to a set `L` of `s` values, proved by the multilinear polynomial method of Alon,
Babai and Suzuki [AlonBabaiSuzuki1991]. A family `A : ι → Finset κ` is indexed; the hypotheses force
`A` to be injective, so the bounds are on the number of distinct sets.

To each member `A i` attach the function `x ↦ ∏_{l ∈ L} (|A i ∩ X| - l)` on the cube
`κ → Bool`, where `X` is the set of coordinates of `x` that are true, with values in a field `K`.
It has degree at most `s` in the sense of `Cslib.BitString.lowDegree`, whose dimension bound
`Cslib.BitString.finrank_lowDegree_le` counts the sets of at most `s` coordinates. Evaluated at the
indicator vectors of the members, these functions form a diagonal matrix with nonzero diagonal, so
they are linearly independent and number at most `∑_{i ≤ s} C(n, i)`
(`Fintype.card_le_sum_choose_of_card_inter_mem`). For a `d`-uniform family, Alon, Babai and Suzuki
adjoin the functions `x ↦ x_I (|X| - d)` for `|I| < s`, which vanish on every member. The combined
family is triangular at the indicator vectors of the sets `I`, so it is still independent when
`(j : K) ≠ d` for `j < s`; this brings the bound down to `C(n, s)`
(`Fintype.card_le_choose_of_card_inter_mem`). Two specializations:

* **Ray-Chaudhuri–Wilson** (`Fintype.card_le_choose_of_card_inter_mem_of_lt`): a `d`-uniform
  family whose pairwise intersection sizes lie in a set `L` of `s` naturals, all below `d`, has at
  most `C(n, s)` members [RayChaudhuriWilson1975] [AlonBabaiSuzuki1991] [Jukna2011, Chapter 13].
* **Modular Frankl–Wilson**, restricted form (`Fintype.card_le_choose_of_card_inter_mem_zmod`):
  for a prime `p` and a set `L` of `s` residues mod `p`, a `d`-uniform family with `d mod p ∉ L`
  and all pairwise intersection sizes mod `p` in `L` has at most `C(n, s)` members, provided
  `s ≤ d mod p` [FranklWilson1981] [AlonBabaiSuzuki1991].

The condition `s ≤ d mod p` is what the triangular argument above needs over `ZMod p`: it is the
condition `(j : K) ≠ d` for `j < s`. It holds for the Frankl–Wilson Ramsey graph
(`CslibFrontier.Foundations.Combinatorics.SimpleGraph.Ramsey.FranklWilson`), where `d = p² - 1` and
`s = p - 1`. Some side condition is necessary: with `n = 4`, `d = 2`, `p = 5` and
`L = {0, 1, 3, 4}`, the six `2`-subsets of a `4`-set satisfy the other hypotheses but
`C(4, 4) = 1`. Frankl and Wilson's modular theorem is proved with inclusion matrices and reportedly
needs only `s ≤ d` (not checked against the paper). That form is strictly stronger (for instance
`p = 3`, `d = 4`, `L = {0, 2}` satisfies `s ≤ d` but not `s ≤ d mod p`) and is not formalized here.
Without uniformity the bound `∑_{i ≤ s} C(n, i)` needs no side condition; over `ZMod p` this
nonuniform form is due to Deza, Frankl and Singhi [DezaFranklSinghi1983]. The nonuniform theorem of
Frankl and Wilson over the rationals, which needs no hypothesis on the member sizes, is not
formalized.

## Main results

* `Fintype.card_le_sum_choose_of_card_inter_mem`: the nonuniform bound `∑_{i ≤ s} C(n, i)` over any
  field.
* `Fintype.card_le_choose_of_card_inter_mem`: the uniform bound `C(n, s)` over any field.
* `Fintype.card_le_choose_of_card_inter_mem_of_lt`: the Ray-Chaudhuri–Wilson theorem.
* `Fintype.card_le_choose_of_card_inter_mem_zmod`: the modular Frankl–Wilson bound, restricted
  to `s ≤ d mod p`.

## References

* [N. Alon, L. Babai, H. Suzuki, *Multilinear polynomials and Frankl–Ray-Chaudhuri–Wilson type
  intersection theorems*][AlonBabaiSuzuki1991]
* [M. Deza, P. Frankl, N. M. Singhi, *On functions of strength t*][DezaFranklSinghi1983]
* [P. Frankl, R. M. Wilson, *Intersection theorems with geometric consequences*][FranklWilson1981]
* [S. Jukna, *Extremal Combinatorics*][Jukna2011]
* [D. K. Ray-Chaudhuri, R. M. Wilson, *On t-designs*][RayChaudhuriWilson1975]
-/

public section

open Finset Submodule Module

/-! The functions on the cube are those on `κ → Bool`, as in `Cslib.BitString.lowDegree`; a set
`X : Finset κ` is the point `ind X`. -/

section Polynomials

open Cslib.BitString

variable {K κ : Type*} [Field K]

/-- The indicator vector of `X`, a point of the cube. -/
private def ind [DecidableEq κ] (X : Finset κ) : κ → Bool := fun i => decide (i ∈ X)

private theorem monomial_ind_of_subset [DecidableEq κ] {I X : Finset κ} (h : I ⊆ X) :
    monomial K I (ind X) = 1 := by
  rw [monomial_apply]
  split_ifs with h'
  · rfl
  · exact absurd (fun i hi => decide_eq_true (h hi)) h'

private theorem monomial_ind_of_not_subset [DecidableEq κ] {I X : Finset κ} (h : ¬ I ⊆ X) :
    monomial K I (ind X) = 0 := by
  rw [monomial_apply]
  split_ifs with h'
  · exact absurd (fun i hi => of_decide_eq_true (h' i hi)) h
  · rfl

/-- The function `x ↦ |A ∩ X| - c` at `x = ind X`: the sum of the bits of `A`, less `c`. -/
private def cardInterSub (A : Finset κ) (c : K) : (κ → Bool) → K :=
  (∑ i ∈ A, monomial K {i}) - fun _ => c

private theorem cardInterSub_ind [DecidableEq κ] (A X : Finset κ) (c : K) :
    cardInterSub A c (ind X) = (#(A ∩ X) : K) - c := by
  have h : ∀ i, monomial K {i} (ind X) = if i ∈ X then 1 else 0 := fun i => by
    split_ifs with hi
    · exact monomial_ind_of_subset (singleton_subset_iff.2 hi)
    · exact monomial_ind_of_not_subset (mt singleton_subset_iff.1 hi)
  simp only [cardInterSub, Pi.sub_apply, Finset.sum_apply, h]
  rw [sum_boole, filter_mem_eq_inter]

private theorem cardInterSub_mem (A : Finset κ) (c : K) : cardInterSub A c ∈ lowDegree K κ 1 :=
  Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ => monomial_mem_lowDegree (card_singleton i).le)
    (const_mem_lowDegree 1 c)

/-- `x ↦ ∏_{l ∈ L} (|A ∩ X| - l)` has degree at most `|L|`. -/
private theorem prod_cardInterSub_mem (A : Finset κ) (L : Finset K) :
    ∏ l ∈ L, cardInterSub A l ∈ lowDegree K κ #L := by
  simpa only [mul_one] using prod_mem_lowDegree L fun l _ => cardInterSub_mem (K := K) A l

private theorem prod_cardInterSub_ind [DecidableEq κ] (A X : Finset κ) (L : Finset K) :
    (∏ l ∈ L, cardInterSub A l) (ind X) = ∏ l ∈ L, ((#(A ∩ X) : K) - l) := by
  rw [Finset.prod_apply]
  exact prod_congr rfl fun l _ => cardInterSub_ind A X l

/-- A linearly independent family of functions of degree at most `s` has at most as many members
as there are sets of at most `s` coordinates (`Cslib.BitString.finrank_lowDegree_le`). -/
private theorem card_le_of_linearIndependent {ι : Type*} [Fintype ι] [Fintype κ] {s : ℕ}
    (f : ι → (κ → Bool) → K) (hmem : ∀ t, f t ∈ lowDegree K κ s)
    (hli : LinearIndependent K f) : Fintype.card ι ≤ #{S : Finset κ | #S ≤ s} := by
  have hli' : LinearIndependent K (fun t => (⟨f t, hmem t⟩ : lowDegree K κ s)) :=
    LinearIndependent.of_comp (lowDegree K κ s).subtype hli
  exact hli'.fintype_card_le_finrank.trans (finrank_lowDegree_le s)

end Polynomials

/-- The sets of at most `s` points are those of fewer than `s` points and the `s`-sets. -/
private theorem card_filter_card_le_eq_add {κ : Type*} [Fintype κ] (s : ℕ) :
    #{S : Finset κ | #S ≤ s} =
      Fintype.card {I : Finset κ // #I < s} + (Fintype.card κ).choose s := by
  classical
  rw [Fintype.card_subtype, ← Fintype.card_finset_len s, Fintype.card_subtype,
    ← card_union_of_disjoint (disjoint_filter.2 fun I _ h1 h2 => by omega), ← filter_or]
  congr 1
  ext I
  simp only [mem_filter, mem_univ, true_and]
  exact le_iff_lt_or_eq

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- **The nonuniform bound**: if no member size lies in `L ⊆ K` and every pairwise intersection
size of distinct members does, the family has at most `∑_{i ≤ |L|} C(|κ|, i)` members. Over
`ZMod p` this is the bound of Deza, Frankl and Singhi [DezaFranklSinghi1983]; the proof is the
multilinear polynomial method [AlonBabaiSuzuki1991]. -/
theorem Fintype.card_le_sum_choose_of_card_inter_mem (A : ι → Finset κ) (L : Finset K)
    (hself : ∀ i, (#(A i) : K) ∉ L) (hinter : ∀ i j, i ≠ j → (#(A i ∩ A j) : K) ∈ L) :
    Fintype.card ι ≤ ∑ i ∈ range (#L + 1), (Fintype.card κ).choose i := by
  classical
  rw [← Finset.card_filter_card_le_eq_sum_choose]
  refine card_le_of_linearIndependent (fun i => ∏ l ∈ L, cardInterSub (A i) l)
    (fun i => prod_cardInterSub_mem (A i) L) ?_
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrFun hg (ind (A i))
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    prod_cardInterSub_ind] at h
  rw [Finset.sum_eq_single i
    (fun j _ hj => by rw [prod_eq_zero (hinter j i hj) (sub_self _), mul_zero])
    (fun h => absurd (mem_univ i) h), inter_self] at h
  have hne : ∏ l ∈ L, ((#(A i) : K) - l) ≠ 0 :=
    prod_ne_zero_iff.2 fun l hl => sub_ne_zero.2 fun h => hself i (h ▸ hl)
  exact (mul_eq_zero.1 h).resolve_right hne

/-- **The uniform bound**: a `d`-uniform family whose distinct members meet in a number of points
lying in `L ⊆ K`, with `d ∉ L` and `(j : K) ≠ d` for `j < |L|`, has at most `C(|κ|, |L|)` members.
This is the multilinear polynomial method of Alon, Babai and Suzuki [AlonBabaiSuzuki1991]. -/
theorem Fintype.card_le_choose_of_card_inter_mem (A : ι → Finset κ) {d : ℕ} (L : Finset K)
    (hcard : ∀ i, #(A i) = d) (hinter : ∀ i j, i ≠ j → (#(A i ∩ A j) : K) ∈ L)
    (hd : (d : K) ∉ L) (hL : ∀ j < #L, (j : K) ≠ d) :
    Fintype.card ι ≤ (Fintype.card κ).choose #L := by
  classical
  set s := #L with hs
  -- The functions of the members, and `x ↦ x_I (|X| - d)` for `|I| < s`, which vanish on them.
  let f : ι ⊕ {I : Finset κ // #I < s} → (κ → Bool) → K := Sum.elim
    (fun i => ∏ l ∈ L, cardInterSub (A i) l)
    (fun I => Cslib.BitString.monomial K I.1 * cardInterSub univ (d : K))
  have hmem : ∀ t, f t ∈ Cslib.BitString.lowDegree K κ s := by
    rintro (i | I)
    · exact prod_cardInterSub_mem (A i) L
    · refine Cslib.BitString.lowDegree_mono (by have := I.2; omega)
        (Cslib.BitString.mul_mem_lowDegree
          (Cslib.BitString.monomial_mem_lowDegree (R := K) (le_refl #I.1))
          (cardInterSub_mem univ (d : K)))
  have hli : LinearIndependent K f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hev : ∀ X, ∑ t, g t * f t (ind X) = 0 := fun X => by
      have h := congrFun hg (ind X)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      exact h
    -- Evaluating at the members kills the coefficients of the `f (inl i)`.
    have hF : ∀ i, g (Sum.inl i) = 0 := by
      intro i
      have h := hev (A i)
      rw [Fintype.sum_sum_type] at h
      have hr : ∀ I : {I : Finset κ // #I < s},
          g (Sum.inr I) * f (Sum.inr I) (ind (A i)) = 0 := by
        intro I
        simp only [f, Sum.elim_inr, Pi.mul_apply, cardInterSub_ind, univ_inter, hcard, sub_self,
          mul_zero]
      have hl : ∀ j, j ≠ i → g (Sum.inl j) * f (Sum.inl j) (ind (A i)) = 0 := by
        intro j hj
        simp only [f, Sum.elim_inl, prod_cardInterSub_ind]
        rw [prod_eq_zero (hinter j i hj) (sub_self _), mul_zero]
      rw [Finset.sum_eq_zero fun I _ => hr I, add_zero,
        Finset.sum_eq_single i (fun j _ hj => hl j hj) (fun h => absurd (mem_univ i) h)] at h
      simp only [f, Sum.elim_inl, prod_cardInterSub_ind, inter_self, hcard] at h
      have hne : ∏ l ∈ L, ((d : K) - l) ≠ 0 :=
        prod_ne_zero_iff.2 fun l hl => sub_ne_zero.2 fun h => hd (h ▸ hl)
      exact (mul_eq_zero.1 h).resolve_right hne
    have hG : ∀ X, ∑ I : {I : Finset κ // #I < s},
        g (Sum.inr I) * (Cslib.BitString.monomial K I.1 (ind X) * ((#X : K) - d)) = 0 := by
      intro X
      have h := hev X
      rw [Fintype.sum_sum_type] at h
      simp only [hF, zero_mul, sum_const_zero, zero_add, f, Sum.elim_inr, Pi.mul_apply,
        cardInterSub_ind, univ_inter] at h
      exact h
    -- Evaluating at `I` itself, by induction on `|I|`, kills the coefficient of `f (inr I)`.
    have hI : ∀ m, ∀ I : {I : Finset κ // #I < s}, #I.1 = m → g (Sum.inr I) = 0 := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro I hIm
        have h := hG I.1
        rw [Finset.sum_eq_single I] at h
        · rw [monomial_ind_of_subset (subset_refl _), one_mul] at h
          have hne : (#I.1 : K) - d ≠ 0 := sub_ne_zero.2 (hL _ I.2)
          exact (mul_eq_zero.1 h).resolve_right hne
        · intro J _ hJI
          by_cases hsub : J.1 ⊆ I.1
          · have hlt : #J.1 < m := hIm ▸ card_lt_card
              (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun h => hJI (Subtype.ext h)⟩)
            rw [ih _ hlt J rfl, zero_mul]
          · rw [monomial_ind_of_not_subset hsub, zero_mul, mul_zero]
        · exact fun h => absurd (mem_univ I) h
    rintro (i | I)
    · exact hF i
    · exact hI _ I rfl
  have h1 := card_le_of_linearIndependent f hmem hli
  rw [card_filter_card_le_eq_add, Fintype.card_sum] at h1
  omega

/-- **Ray-Chaudhuri–Wilson**: a `d`-uniform family whose distinct members meet in a number of
points lying in a set `L` of naturals below `d` has at most `C(|κ|, |L|)` members
[RayChaudhuriWilson1975] [AlonBabaiSuzuki1991] [Jukna2011, Chapter 13]. -/
theorem Fintype.card_le_choose_of_card_inter_mem_of_lt (A : ι → Finset κ) {d : ℕ} (L : Finset ℕ)
    (hcard : ∀ i, #(A i) = d) (hinter : ∀ i j, i ≠ j → #(A i ∩ A j) ∈ L)
    (hL : ∀ l ∈ L, l < d) :
    Fintype.card ι ≤ (Fintype.card κ).choose #L := by
  have h := Fintype.card_le_choose_of_card_inter_mem (K := ℚ) A (L.map Nat.castEmbedding) hcard
    (fun i j hij => mem_map_of_mem _ (hinter i j hij)) ?_ ?_
  · rwa [Finset.card_map] at h
  · intro hd
    obtain ⟨l, hl, hld⟩ := mem_map.1 hd
    rw [Nat.castEmbedding_apply, Nat.cast_inj] at hld
    exact (hL l hl).ne hld
  · intro j hj hjd
    rw [Finset.card_map] at hj
    rw [Nat.cast_inj] at hjd
    subst hjd
    have h := Finset.card_le_card (s := L) (t := range j) fun l hl => mem_range.2 (hL l hl)
    rw [Finset.card_range] at h
    omega

/-- **Modular Frankl–Wilson**, uniform case: for a prime `p` and a set `L` of residues mod `p`, a
`d`-uniform family with `d mod p ∉ L` whose distinct members meet in a number of points lying in
`L` mod `p` has at most `C(|κ|, |L|)` members, provided `|L| ≤ d mod p` [FranklWilson1981]
[AlonBabaiSuzuki1991]. This is a restricted form: the condition `|L| ≤ d mod p` is the one the
triangular polynomial argument needs, while Frankl and Wilson's inclusion-matrix theorem reportedly
needs only `|L| ≤ d`. -/
theorem Fintype.card_le_choose_of_card_inter_mem_zmod {p : ℕ} [Fact p.Prime] (A : ι → Finset κ)
    {d : ℕ} (L : Finset (ZMod p)) (hcard : ∀ i, #(A i) = d)
    (hinter : ∀ i j, i ≠ j → (#(A i ∩ A j) : ZMod p) ∈ L) (hd : (d : ZMod p) ∉ L)
    (hL : #L ≤ d % p) :
    Fintype.card ι ≤ (Fintype.card κ).choose #L := by
  refine Fintype.card_le_choose_of_card_inter_mem A L hcard hinter hd fun j hj hjd => ?_
  rw [ZMod.natCast_eq_natCast_iff'] at hjd
  have hdp := Nat.mod_lt d (Fact.out : p.Prime).pos
  rw [Nat.mod_eq_of_lt (by omega : j < p)] at hjd
  omega

end
