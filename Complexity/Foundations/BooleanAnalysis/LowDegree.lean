/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Complexity.Foundations.Data.BitString.Sign
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.MvPolynomial.Basic
import Complexity.Foundations.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset

/-!
# Low-degree functions on the Boolean cube

Reading the bits of `x : ι → Bool` as `0` and `1` in a commutative ring `R` (`BitString.bitVal`),
the monomial of a set `S` of coordinates is the function `x ↦ ∏_{i ∈ S} x i`
(`BitString.monomial`), and the functions of degree at most `D` are the `R`-linear combinations of
monomials of at most `D` coordinates (`BitString.lowDegree`). This is the degree of the multilinear
polynomial representing a function on the cube, without formal polynomials: on bits every monomial
is idempotent, so products of monomials are monomials (`BitString.monomial_mul`) and degrees add
under multiplication (`BitString.mul_mem_lowDegree`). Evaluated at the bits read in `R`, Mathlib's
polynomials of total degree at most `D` give exactly the functions of degree at most `D`
(`BitString.lowDegree_eq_map_restrictTotalDegree`). Every function has degree at most the number
of coordinates (`BitString.mem_lowDegree_self`), and the functions of degree at most `D` span a
space of dimension at most the number of sets of at most `D` coordinates
(`BitString.finrank_lowDegree_le`), which is at most `(n + 1) ^ D` for `n` coordinates
(`BitString.card_filter_card_le_le_pow`).

These are the polynomials of Razborov's and Smolensky's approximation method
[Razborov1987], [Smolensky1987].

## Main definitions

* `Cslib.BitString.monomial`, `Cslib.BitString.lowDegree`.

## Main results

* `Cslib.BitString.mul_mem_lowDegree`: degrees add under multiplication.
* `Cslib.BitString.lowDegree_eq_map_restrictTotalDegree`: the functions of degree at most `D` are
  the evaluations at bits of the polynomials of total degree at most `D`.
* `Cslib.BitString.mem_lowDegree_self`: every function has degree at most the number of
  coordinates.
* `Cslib.BitString.finrank_lowDegree_le`: the dimension of the functions of degree at most `D`.
* `Cslib.BitString.card_filter_card_le_le_pow`: there are at most `(n + 1) ^ D` sets of at most
  `D` of `n` coordinates.

## References

* [A. A. Razborov, *Lower bounds on the size of bounded depth circuits over a complete basis with
  logical addition*][Razborov1987]
* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
-/

@[expose] public section

namespace Cslib.BitString

open Finset

variable (R : Type*) [CommRing R] {ι : Type*}

/-- The monomial of a set `S` of coordinates: the product of the selected bits, read in `R`. The
empty monomial is the constant `1`. -/
def monomial (S : Finset ι) (x : ι → Bool) : R :=
  ∏ i ∈ S, bitVal R (x i)

variable (ι) in
/-- The functions on the cube of degree at most `D`: the `R`-linear span of the monomials of at most
`D` coordinates. -/
def lowDegree (D : ℕ) : Submodule R ((ι → Bool) → R) :=
  Submodule.span R (monomial R '' {S | #S ≤ D})

variable {R}

/-- A monomial is `1` where all its coordinates are true and `0` elsewhere. -/
theorem monomial_apply (S : Finset ι) (x : ι → Bool) :
    monomial R S x = if ∀ i ∈ S, x i = true then 1 else 0 := by
  unfold monomial bitVal
  rw [prod_boole]

/-- The product of two monomials is the monomial of the union. -/
theorem monomial_mul [DecidableEq ι] (S T : Finset ι) :
    monomial R S * monomial R T = monomial R (S ∪ T) := by
  funext x
  simp only [Pi.mul_apply, monomial_apply, mem_union, or_imp, forall_and]
  split_ifs <;> simp_all

/-- The monomial of the empty set is the constant `1`. -/
@[simp] theorem monomial_empty : monomial R (∅ : Finset ι) = 1 := by
  funext x
  simp [monomial]

/-- The monomial of a single coordinate `i` is the bit at `i`, read in `R`. -/
theorem monomial_singleton (i : ι) : monomial R {i} = fun x => bitVal R (x i) := by
  funext x
  simp [monomial]

/-- The monomial of a set of at most `D` coordinates has degree at most `D`. -/
theorem monomial_mem_lowDegree {S : Finset ι} {D : ℕ} (hS : #S ≤ D) :
    monomial R S ∈ lowDegree R ι D :=
  Submodule.subset_span ⟨S, hS, rfl⟩

/-- The functions of degree at most `D` have degree at most `E` when `D ≤ E`. -/
theorem lowDegree_mono {D E : ℕ} (hDE : D ≤ E) : lowDegree R ι D ≤ lowDegree R ι E :=
  Submodule.span_mono (Set.image_mono fun _ hS => le_trans hS hDE)

/-- The constant function `1` has degree at most `D`, for every `D`. -/
theorem one_mem_lowDegree (D : ℕ) : (1 : (ι → Bool) → R) ∈ lowDegree R ι D := by
  rw [← monomial_empty]
  exact monomial_mem_lowDegree (by simp)

/-- A constant function has degree at most `D`, for every `D`. -/
theorem const_mem_lowDegree (D : ℕ) (c : R) : (fun _ : ι → Bool => c) ∈ lowDegree R ι D := by
  convert Submodule.smul_mem _ c (one_mem_lowDegree (R := R) (ι := ι) D) using 1
  funext x
  simp

/-- The bit at a coordinate `i`, read in `R`, has degree at most `1`. -/
theorem bitVal_mem_lowDegree (i : ι) :
    (fun x : ι → Bool => bitVal R (x i)) ∈ lowDegree R ι 1 :=
  monomial_singleton (R := R) i ▸ monomial_mem_lowDegree (by simp)

/-- Degrees add under multiplication. -/
theorem lowDegree_mul_le (a b : ℕ) :
    lowDegree R ι a * lowDegree R ι b ≤ lowDegree R ι (a + b) := by
  classical
  rw [lowDegree, lowDegree, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨S, hS, rfl⟩, _, ⟨T, hT, rfl⟩, rfl⟩
  change monomial R S * monomial R T ∈ lowDegree R ι (a + b)
  rw [monomial_mul]
  exact monomial_mem_lowDegree ((card_union_le S T).trans (Nat.add_le_add hS hT))

/-- The product of functions of degrees at most `a` and `b` has degree at most `a + b`. -/
theorem mul_mem_lowDegree {a b : ℕ} {f g : (ι → Bool) → R} (hf : f ∈ lowDegree R ι a)
    (hg : g ∈ lowDegree R ι b) : f * g ∈ lowDegree R ι (a + b) :=
  lowDegree_mul_le a b (Submodule.mul_mem_mul hf hg)

/-- The `k`-th power of a function of degree at most `a` has degree at most `k * a`. -/
theorem pow_mem_lowDegree {a : ℕ} {f : (ι → Bool) → R} (hf : f ∈ lowDegree R ι a) (k : ℕ) :
    f ^ k ∈ lowDegree R ι (k * a) := by
  induction k with
  | zero => simpa using one_mem_lowDegree (R := R) (ι := ι) 0
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact mul_mem_lowDegree ih hf

/-- A product over `s` of functions of degree at most `a` has degree at most `#s * a`. -/
theorem prod_mem_lowDegree {α : Type*} (s : Finset α) {a : ℕ} {f : α → (ι → Bool) → R}
    (hf : ∀ i ∈ s, f i ∈ lowDegree R ι a) : ∏ i ∈ s, f i ∈ lowDegree R ι (#s * a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_lowDegree (R := R) (ι := ι) 0
  | insert i s hi ih =>
    rw [prod_insert hi, card_insert_of_notMem hi, Nat.succ_mul, Nat.add_comm]
    exact mul_mem_lowDegree (hf i (mem_insert_self i s))
      (ih fun j hj => hf j (mem_insert_of_mem hj))

/-- A sum of functions of degree at most `a` has degree at most `a`. -/
theorem sum_mem_lowDegree {α : Type*} (s : Finset α) {a : ℕ} {f : α → (ι → Bool) → R}
    (hf : ∀ i ∈ s, f i ∈ lowDegree R ι a) : ∑ i ∈ s, f i ∈ lowDegree R ι a :=
  Submodule.sum_mem _ hf

/-- If `f` has degree at most `a`, so does `1 - f`. -/
theorem one_sub_mem_lowDegree {a : ℕ} {f : (ι → Bool) → R} (hf : f ∈ lowDegree R ι a) :
    1 - f ∈ lowDegree R ι a :=
  Submodule.sub_mem _ (one_mem_lowDegree a) hf

/-- Negating all the bits of the input preserves the degree. -/
theorem comp_not_mem_lowDegree {D : ℕ} {f : (ι → Bool) → R} (hf : f ∈ lowDegree R ι D) :
    (fun x => f fun i => !x i) ∈ lowDegree R ι D := by
  suffices h : lowDegree R ι D ≤
      (lowDegree R ι D).comap (LinearMap.funLeft R R fun (x : ι → Bool) i => !x i) from h hf
  refine Submodule.span_le.2 ?_
  rintro _ ⟨S, hS, rfl⟩
  have h : (fun x : ι → Bool => monomial R S fun i => !x i) =
      ∏ i ∈ S, (1 - fun x : ι → Bool => bitVal R (x i)) := by
    funext x
    simp [monomial, Finset.prod_apply, bitVal_not]
  change (fun x : ι → Bool => monomial R S fun i => !x i) ∈ lowDegree R ι D
  rw [h]
  exact lowDegree_mono (by simpa using hS)
    (prod_mem_lowDegree S fun i _ => one_sub_mem_lowDegree (bitVal_mem_lowDegree i))

open MvPolynomial in
/-- **Low degree as total degree.** The functions of degree at most `D` are the evaluations at the
bits, read in `R`, of the multivariate polynomials of total degree at most `D`: a monomial `x^d`
evaluates to the monomial of the support of `d`, every bit being idempotent. -/
theorem lowDegree_eq_map_restrictTotalDegree (D : ℕ) :
    lowDegree R ι D = (restrictTotalDegree ι R D).map
      (aeval fun i (x : ι → Bool) => bitVal R (x i)).toLinearMap := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨S, hS, rfl⟩
    refine ⟨∏ i ∈ S, X i, (mem_restrictTotalDegree _ _ _).2 ?_, ?_⟩
    · refine (totalDegree_finsetProd _ _).trans ((sum_le_card_nsmul _ _ 1 fun i _ => ?_).trans ?_)
      · exact (totalDegree_monomial_le _ _).trans (by simp)
      · simpa using hS
    · funext x
      simp [BitString.monomial, Finset.prod_apply]
  · rintro _ ⟨p, hp, rfl⟩
    rw [SetLike.mem_coe, mem_restrictTotalDegree] at hp
    rw [p.as_sum, map_sum]
    refine Submodule.sum_mem _ fun d hd => ?_
    have hd' : #d.support ≤ D := by
      refine le_trans ?_ ((le_totalDegree hd).trans hp)
      rw [Finsupp.sum, card_eq_sum_ones]
      exact sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)
    convert Submodule.smul_mem _ (p.coeff d) (monomial_mem_lowDegree (R := R) hd') using 1
    funext x
    simp only [AlgHom.toLinearMap_apply, aeval_monomial, Pi.mul_apply, Pi.smul_apply,
      smul_eq_mul, Finsupp.prod, Finset.prod_apply, Pi.pow_apply, BitString.monomial]
    congr 1
    exact prod_congr rfl fun i hi => bitVal_pow _ (Finsupp.mem_support_iff.1 hi)

variable [Fintype ι]

/-- **Every function on the cube has degree at most the number of coordinates**: it is the sum,
over the points `a`, of its value at `a` times the indicator of `a`, a product of one function of
degree one per coordinate. -/
theorem mem_lowDegree_self (f : (ι → Bool) → R) : f ∈ lowDegree R ι (Fintype.card ι) := by
  classical
  -- the indicator of `a`
  have hδ : ∀ a : ι → Bool, (fun x : ι → Bool => ∏ i, if a i then bitVal R (x i)
      else 1 - bitVal R (x i)) ∈ lowDegree R ι (Fintype.card ι) := fun a => by
    have := prod_mem_lowDegree (R := R) (ι := ι) (a := 1) univ
      (f := fun i x => if a i then bitVal R (x i) else 1 - bitVal R (x i)) fun i _ => by
        by_cases hi : a i
        · simp only [hi, ↓reduceIte]
          exact bitVal_mem_lowDegree i
        · simp only [hi, Bool.false_eq_true, ↓reduceIte]
          exact one_sub_mem_lowDegree (bitVal_mem_lowDegree i)
    simpa [card_univ, Finset.prod_fn] using this
  have hf : f = ∑ a, f a • fun x : ι → Bool => ∏ i, if a i then bitVal R (x i)
      else 1 - bitVal R (x i) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single x]
    · rw [Finset.prod_eq_one fun i _ => by cases x i <;> simp [bitVal]]
      simp
    · intro a _ hax
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hax
      rw [Finset.prod_eq_zero (mem_univ i) (by cases ha : a i <;> cases hx : x i <;>
        simp_all [bitVal]), mul_zero]
    · simp
  rw [hf]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hδ a)

/-- **The dimension of the functions of degree at most `D`** is at most the number of sets of at
most `D` coordinates. -/
theorem finrank_lowDegree_le [StrongRankCondition R] (D : ℕ) :
    Module.finrank R (lowDegree R ι D) ≤ #{S : Finset ι | #S ≤ D} := by
  classical
  rw [lowDegree, show monomial R '' {S | #S ≤ D} =
      (({S : Finset ι | #S ≤ D} : Finset _).image (monomial R) : Set _) by
    ext f
    simp]
  exact (finrank_span_finset_le_card _).trans card_image_le

/-- There are at most `(n + 1) ^ D` sets of at most `D` of the `n` coordinates. -/
theorem card_filter_card_le_le_pow (D : ℕ) :
    #{S : Finset ι | #S ≤ D} ≤ (Fintype.card ι + 1) ^ D := by
  classical
  have hfib : #{S : Finset ι | #S ≤ D} =
      ∑ i ∈ range (D + 1), #{S ∈ ({S : Finset ι | #S ≤ D} : Finset _) | #S = i} :=
    card_eq_sum_card_fiberwise fun S hS =>
      mem_coe.2 (mem_range.2 (Nat.lt_succ_of_le (mem_filter.1 (mem_coe.1 hS)).2))
  have hchoose (i : ℕ) (hi : i ∈ range (D + 1)) :
      #{S ∈ ({S : Finset ι | #S ≤ D} : Finset _) | #S = i} = (Fintype.card ι).choose i := by
    rw [← card_univ, ← card_powersetCard]
    congr 1
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h ▸ Nat.le_of_lt_succ (mem_range.1 hi), h⟩
  rw [hfib, sum_congr rfl hchoose]
  exact Cslib.sum_range_choose_le_add_one_pow _ D

/-- The empty set has at most `D` coordinates, so there is at least one such set. -/
theorem card_filter_card_le_pos (D : ℕ) : 0 < #{S : Finset ι | #S ≤ D} :=
  card_pos.2 ⟨∅, by simp⟩

end Cslib.BitString
