/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SetFamily/RayChaudhuriWilson.lean`)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Ray-Chaudhuri–Wilson and Frankl–Wilson bounds

Bounds on families of subsets of a finite set `κ`, `n = |κ|`, whose pairwise intersection sizes
are restricted to a set `L` of `s` values, proved by the multilinear polynomial method of Alon,
Babai and Suzuki [AlonBabaiSuzuki1991]. A family `A : ι → Finset κ` is indexed; the hypotheses force
`A` to be injective, so the bounds are on the number of distinct sets.

To each member `A i` attach the function `X ↦ ∏_{l ∈ L} (|A i ∩ X| - l)` on `Finset κ`, viewed as
the cube `{0, 1}^κ`, with values in a field `K`. It is a multilinear polynomial of degree at most
`s` in the coordinates of `X`. Evaluated at the members themselves these functions form a diagonal
matrix with nonzero diagonal, so they are linearly independent in the space of degree-`≤ s`
multilinear polynomials, of dimension `∑_{i ≤ s} C(n, i)`
(`Fintype.card_le_sum_choose_of_card_inter_mem`). For a `d`-uniform family, Alon, Babai and
Suzuki adjoin the functions `X ↦ x_I (|X| - d)` for `|I| < s`, which vanish on every member; the
combined family is still independent when `(j : K) ≠ d` for `j < s`, which brings the bound down
to `C(n, s)` (`Fintype.card_le_choose_of_card_inter_mem`). Two specializations:

* **Ray-Chaudhuri–Wilson** (`Fintype.card_le_choose_of_card_inter_mem_of_lt`): a `d`-uniform
  family whose pairwise intersection sizes lie in a set `L` of `s` naturals, all below `d`, has at
  most `C(n, s)` members [RayChaudhuriWilson1975] [AlonBabaiSuzuki1991] [Jukna2011, Chapter 13].
* **Modular Frankl–Wilson** (`Fintype.card_le_choose_of_card_inter_mem_zmod`): for a prime `p`
  and a set `L` of `s` residues mod `p`, a `d`-uniform family with `d mod p ∉ L` and all pairwise
  intersection sizes mod `p` in `L` has at most `C(n, s)` members, provided `s ≤ d mod p`
  [FranklWilson1981] [AlonBabaiSuzuki1991].

The side condition `s ≤ d mod p` of the modular bound is the condition `(j : K) ≠ d` for `j < s`
of the polynomial method. It holds for the Frankl–Wilson Ramsey graph
(`Complexity.Foundations.Combinatorics.SimpleGraph.Ramsey.FranklWilson`), where `d = p² - 1` and
`s = p - 1`. Some side condition is necessary: with `n = 4`, `d = 2`, `p = 5` and
`L = {0, 1, 3, 4}`, the six `2`-subsets of a `4`-set satisfy the other hypotheses but
`C(4, 4) = 1`. Frankl and Wilson's original modular theorem, proved with inclusion matrices, has
other side conditions; that form is not formalized here. Without uniformity, the bound
`∑_{i ≤ s} C(n, i)` needs no side condition (the nonuniform modular form is due to Deza, Frankl
and Singhi [DezaFranklSinghi1983]).

## Main results

* `Fintype.card_le_sum_choose_of_card_inter_mem`: the nonuniform bound `∑_{i ≤ s} C(n, i)` over any
  field.
* `Fintype.card_le_choose_of_card_inter_mem`: the uniform bound `C(n, s)` over any field.
* `Fintype.card_le_choose_of_card_inter_mem_of_lt`: the Ray-Chaudhuri–Wilson theorem.
* `Fintype.card_le_choose_of_card_inter_mem_zmod`: the modular Frankl–Wilson bound with
  `s ≤ d mod p`.

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

section Polynomials

variable {K κ : Type*} [Field K] [DecidableEq κ]

/-- The multilinear monomial `x_I` as a function on the cube `Finset κ`. -/
private def mono (K : Type*) [Field K] (I : Finset κ) : Finset κ → K :=
  fun X => if I ⊆ X then 1 else 0

/-- The span of the multilinear monomials of degree at most `s`. -/
private def lowSpan (K κ : Type*) [Field K] [DecidableEq κ] (s : ℕ) :
    Submodule K (Finset κ → K) :=
  span K (Set.range fun I : {I : Finset κ // #I ≤ s} => mono K I.1)

private theorem mono_mem_lowSpan {s : ℕ} {I : Finset κ} (h : #I ≤ s) :
    mono K I ∈ lowSpan K κ s :=
  subset_span ⟨⟨I, h⟩, rfl⟩

private theorem mono_mul (I J : Finset κ) : mono K I * mono K J = mono K (I ∪ J) := by
  ext X
  simp only [Pi.mul_apply, mono, union_subset_iff]
  split_ifs <;> simp_all

private theorem lowSpan_mul_le (a b : ℕ) :
    lowSpan K κ a * lowSpan K κ b ≤ lowSpan K κ (a + b) := by
  rw [lowSpan, lowSpan, span_mul_span]
  refine span_le.2 ?_
  rintro _ ⟨_, ⟨I, rfl⟩, _, ⟨J, rfl⟩, rfl⟩
  dsimp only
  rw [mono_mul]
  exact mono_mem_lowSpan ((card_union_le I.1 J.1).trans (add_le_add I.2 J.2))

/-- `X ↦ |A ∩ X| - c` is a multilinear polynomial of degree at most one. -/
private theorem card_inter_sub_mem_lowSpan (A : Finset κ) (c : K) :
    (fun X => (#(A ∩ X) : K) - c) ∈ lowSpan K κ 1 := by
  have h : (fun X => (#(A ∩ X) : K) - c) = (∑ i ∈ A, mono K {i}) - c • mono K ∅ := by
    ext X
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, mono, singleton_subset_iff,
      empty_subset, ite_true, smul_eq_mul, mul_one]
    rw [sum_boole, filter_mem_eq_inter]
  rw [h]
  refine sub_mem (sum_mem fun i _ => mono_mem_lowSpan ?_) (smul_mem _ _ (mono_mem_lowSpan ?_))
  · rw [card_singleton]
  · rw [card_empty]
    exact zero_le_one

/-- `X ↦ ∏_{l ∈ L} (|A ∩ X| - l)` is a multilinear polynomial of degree at most `|L|`. -/
private theorem prod_card_inter_sub_mem_lowSpan (A : Finset κ) (L : Finset K) :
    (fun X => ∏ l ∈ L, ((#(A ∩ X) : K) - l)) ∈ lowSpan K κ #L := by
  classical
  induction L using Finset.induction_on with
  | empty =>
    have h : (fun X : Finset κ => ∏ l ∈ (∅ : Finset K), ((#(A ∩ X) : K) - l)) = mono K ∅ := by
      ext X
      simp only [prod_empty, mono, empty_subset, ite_true]
    rw [h]
    exact mono_mem_lowSpan (by rw [card_empty, card_empty])
  | insert l L hl ih =>
    have h : (fun X => ∏ l ∈ insert l L, ((#(A ∩ X) : K) - l)) =
        (fun X => (#(A ∩ X) : K) - l) * (fun X => ∏ l ∈ L, ((#(A ∩ X) : K) - l)) := by
      ext X
      rw [Pi.mul_apply, prod_insert hl]
    rw [h, card_insert_of_notMem hl, add_comm]
    exact lowSpan_mul_le 1 #L (mul_mem_mul (card_inter_sub_mem_lowSpan A l) ih)

/-- A linearly independent family of degree-`≤ s` polynomials has at most as many members as
there are monomials of degree at most `s`. -/
private theorem card_le_of_linearIndependent {ι : Type*} [Fintype ι] [Fintype κ] {s : ℕ}
    (f : ι → Finset κ → K) (hmem : ∀ t, f t ∈ lowSpan K κ s) (hli : LinearIndependent K f) :
    Fintype.card ι ≤ Fintype.card {I : Finset κ // #I ≤ s} := by
  have hli' : LinearIndependent K (fun t => (⟨f t, hmem t⟩ : lowSpan K κ s)) :=
    LinearIndependent.of_comp (lowSpan K κ s).subtype hli
  exact hli'.fintype_card_le_finrank.trans (finrank_range_le_card _)

end Polynomials

section Counting

variable {κ : Type*} [Fintype κ]

private theorem card_subtype_card_le (s : ℕ) :
    Fintype.card {I : Finset κ // #I ≤ s} =
      Fintype.card {I : Finset κ // #I < s} + (Fintype.card κ).choose s := by
  classical
  rw [Fintype.card_subtype, Fintype.card_subtype, ← Fintype.card_finset_len s,
    Fintype.card_subtype, ← card_union_of_disjoint (disjoint_filter.2 fun I _ h1 h2 => by omega),
    ← filter_or]
  congr 1
  ext I
  simp only [mem_filter, mem_univ, true_and]
  exact le_iff_lt_or_eq

private theorem card_subtype_card_le_eq_sum (s : ℕ) :
    Fintype.card {I : Finset κ // #I ≤ s} = ∑ i ∈ range (s + 1), (Fintype.card κ).choose i := by
  induction s with
  | zero =>
    rw [zero_add, sum_range_one, ← Fintype.card_finset_len 0]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun I => Nat.le_zero)
  | succ s ih =>
    rw [card_subtype_card_le, sum_range_succ, ← ih]
    congr 1
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun I => Nat.lt_succ_iff)

end Counting

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- **The nonuniform bound**: if no member size lies in `L ⊆ K` and every pairwise intersection
size of distinct members does, the family has at most `∑_{i ≤ |L|} C(|κ|, i)` members. Over
`ZMod p` this is the bound of Deza, Frankl and Singhi [DezaFranklSinghi1983]; the proof is the
multilinear polynomial method [AlonBabaiSuzuki1991]. -/
theorem Fintype.card_le_sum_choose_of_card_inter_mem (A : ι → Finset κ) (L : Finset K)
    (hself : ∀ i, (#(A i) : K) ∉ L) (hinter : ∀ i j, i ≠ j → (#(A i ∩ A j) : K) ∈ L) :
    Fintype.card ι ≤ ∑ i ∈ range (#L + 1), (Fintype.card κ).choose i := by
  classical
  rw [← card_subtype_card_le_eq_sum]
  refine card_le_of_linearIndependent (fun i X => ∏ l ∈ L, ((#(A i ∩ X) : K) - l))
    (fun i => prod_card_inter_sub_mem_lowSpan (A i) L) ?_
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrFun hg (A i)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
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
  let f : ι ⊕ {I : Finset κ // #I < s} → Finset κ → K := Sum.elim
    (fun i X => ∏ l ∈ L, ((#(A i ∩ X) : K) - l))
    (fun I X => mono K I.1 X * ((#X : K) - d))
  have hmem : ∀ t, f t ∈ lowSpan K κ s := by
    rintro (i | I)
    · exact prod_card_inter_sub_mem_lowSpan (A i) L
    · have h1 : mono K I.1 ∈ lowSpan K κ (s - 1) := mono_mem_lowSpan (by have := I.2; omega)
      have h2 : (fun X => (#X : K) - d) ∈ lowSpan K κ 1 := by
        have h := card_inter_sub_mem_lowSpan (K := K) (univ : Finset κ) (d : K)
        simp only [univ_inter] at h
        exact h
      have h := lowSpan_mul_le (s - 1) 1 (mul_mem_mul h1 h2)
      rwa [Nat.sub_add_cancel (by have := I.2; omega : 1 ≤ s)] at h
  have hli : LinearIndependent K f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hev : ∀ X, ∑ t, g t * f t X = 0 := fun X => by
      have h := congrFun hg X
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      exact h
    -- Evaluating at the members kills the coefficients of the `f (inl i)`.
    have hF : ∀ i, g (Sum.inl i) = 0 := by
      intro i
      have h := hev (A i)
      rw [Fintype.sum_sum_type] at h
      have hr : ∀ I : {I : Finset κ // #I < s}, g (Sum.inr I) * f (Sum.inr I) (A i) = 0 := by
        intro I
        simp only [f, Sum.elim_inr, hcard, sub_self, mul_zero]
      have hl : ∀ j, j ≠ i → g (Sum.inl j) * f (Sum.inl j) (A i) = 0 := by
        intro j hj
        simp only [f, Sum.elim_inl]
        rw [prod_eq_zero (hinter j i hj) (sub_self _), mul_zero]
      rw [Finset.sum_eq_zero fun I _ => hr I, add_zero,
        Finset.sum_eq_single i (fun j _ hj => hl j hj) (fun h => absurd (mem_univ i) h)] at h
      simp only [f, Sum.elim_inl, inter_self, hcard] at h
      have hne : ∏ l ∈ L, ((d : K) - l) ≠ 0 :=
        prod_ne_zero_iff.2 fun l hl => sub_ne_zero.2 fun h => hd (h ▸ hl)
      exact (mul_eq_zero.1 h).resolve_right hne
    have hG : ∀ X, ∑ I : {I : Finset κ // #I < s},
        g (Sum.inr I) * (mono K I.1 X * ((#X : K) - d)) = 0 := by
      intro X
      have h := hev X
      rw [Fintype.sum_sum_type] at h
      simp only [hF, zero_mul, sum_const_zero, zero_add, f, Sum.elim_inr] at h
      exact h
    -- Evaluating at `I` itself, by induction on `|I|`, kills the coefficient of `f (inr I)`.
    have hI : ∀ m, ∀ I : {I : Finset κ // #I < s}, #I.1 = m → g (Sum.inr I) = 0 := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro I hIm
        have h := hG I.1
        rw [Finset.sum_eq_single I] at h
        · simp only [mono, subset_refl, ite_true, one_mul] at h
          have hne : (#I.1 : K) - d ≠ 0 := sub_ne_zero.2 (hL _ I.2)
          exact (mul_eq_zero.1 h).resolve_right hne
        · intro J _ hJI
          by_cases hsub : J.1 ⊆ I.1
          · have hlt : #J.1 < m := hIm ▸ card_lt_card
              (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun h => hJI (Subtype.ext h)⟩)
            rw [ih _ hlt J rfl, zero_mul]
          · simp only [mono, hsub, ite_false, zero_mul, mul_zero]
        · exact fun h => absurd (mem_univ I) h
    rintro (i | I)
    · exact hF i
    · exact hI _ I rfl
  have h1 := card_le_of_linearIndependent f hmem hli
  rw [card_subtype_card_le, Fintype.card_sum] at h1
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
[AlonBabaiSuzuki1991]. -/
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
