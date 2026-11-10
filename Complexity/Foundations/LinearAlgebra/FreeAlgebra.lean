/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib/LinearAlgebra/FreeAlgebra.lean)

public import Complexity.Init
public import Mathlib.LinearAlgebra.FreeAlgebra
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Coefficients of non-commutative polynomials

The free algebra `FreeAlgebra R X` is the algebra of non-commutative polynomials in the variables
`X`. Its monomials are the words `FreeMonoid X`, which form the basis `basisFreeMonoid R X`. This
file names the coordinate of a word (`FreeAlgebra.coeff`) and proves the product rule: the
coefficient of `w` in `a * b` is a sum over the ways to split `w` into a prefix and a suffix
(`FreeAlgebra.coeff_mul`). A polynomial is *homogeneous of degree `d`* when all its words have
length `d` (`FreeAlgebra.IsHomogeneous`). Against a homogeneous left factor of degree `|u|` the
coefficients multiply: `coeff (u v) (a b) = coeff u a * coeff v b`
(`FreeAlgebra.coeff_mul_mul_of_isHomogeneous`).

`FreeMonoid.ofFn u` is the word `u 0 u 1 ⋯ u (k - 1)` of a tuple `u : Fin k → X`; every word of
length `k` has this form (`FreeMonoid.exists_ofFn_eq`), and the product of the words of a
`k`-tuple and an `m`-tuple determines both tuples (`FreeMonoid.ofFn_mul_ofFn_injective`).

## Main definitions

* `FreeAlgebra.coeff`: the coefficient of a word, as a linear map.
* `FreeAlgebra.IsHomogeneous`: homogeneity of a given degree.
* `FreeMonoid.ofFn`: the word of a tuple.

## Main results

* `FreeAlgebra.coeff_def`: `coeff` reads the coefficients of `equivMonoidAlgebraFreeMonoid`.
* `FreeAlgebra.ext_coeff`: polynomials with the same coefficients are equal.
* `FreeAlgebra.coeff_mul`: the product rule.
* `FreeAlgebra.IsHomogeneous.mul`: degrees add under multiplication.
* `FreeAlgebra.coeff_mul_mul_of_isHomogeneous`: coefficients multiply against a homogeneous left
  factor of matching degree.
-/

public section

namespace FreeMonoid

variable {X : Type*}

/-- The word `u 0 u 1 ⋯ u (k - 1)` of a tuple. -/
@[expose] def ofFn {k : ℕ} (u : Fin k → X) : FreeMonoid X :=
  ofList (List.ofFn u)

/-- The word of a `k`-tuple has length `k`. -/
@[simp] theorem length_ofFn {k : ℕ} (u : Fin k → X) : (ofFn u).length = k :=
  List.length_ofFn

/-- The word of the empty tuple is empty. -/
@[simp] theorem ofFn_zero (u : Fin 0 → X) : ofFn u = 1 := rfl

/-- Appending a letter to a tuple appends it to the word. -/
theorem ofFn_snoc {k : ℕ} (u : Fin k → X) (x : X) :
    ofFn (Fin.snoc u x : Fin (k + 1) → X) = ofFn u * of x := by
  rw [ofFn, List.ofFn_succ', List.concat_eq_append, ofList_append, ofList_singleton]
  simp [ofFn]

/-- Every word of length `k` is the word of a tuple. -/
theorem exists_ofFn_eq {k : ℕ} (w : FreeMonoid X) (h : w.length = k) :
    ∃ u : Fin k → X, ofFn u = w := by
  subst h
  exact ⟨w.toList.get,
    (congrArg ofList (List.ofFn_get w.toList)).trans (ofList_toList w)⟩

/-- Prepending a letter to a tuple prepends it to the word. -/
theorem ofFn_cons {k : ℕ} (x : X) (u : Fin k → X) :
    ofFn (Fin.cons x u : Fin (k + 1) → X) = of x * ofFn u := by
  simp [ofFn, List.ofFn_succ]

/-- Reversing a tuple with a prepended letter appends the letter to the reversed word. -/
theorem ofFn_cons_comp_rev {k : ℕ} (x : X) (u : Fin k → X) :
    ofFn ((Fin.cons x u : Fin (k + 1) → X) ∘ Fin.rev) = ofFn (u ∘ Fin.rev) * of x := by
  rw [← ofFn_snoc]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp [Fin.rev_castSucc]

/-- A product of the words of a `k`-tuple and an `m`-tuple determines both tuples. -/
theorem ofFn_mul_ofFn_injective {k m : ℕ} {a a' : Fin k → X} {b b' : Fin m → X}
    (h : ofFn a * ofFn b = ofFn a' * ofFn b') : a = a' ∧ b = b' := by
  have h' := congrArg toList h
  simp only [toList_mul, ofFn, toList_ofList] at h'
  obtain ⟨h1, h2⟩ := List.append_inj h' (by simp)
  exact ⟨List.ofFn_injective h1, List.ofFn_injective h2⟩

end FreeMonoid

namespace FreeAlgebra

variable {R : Type*} [CommSemiring R] {X : Type*}

/-- The coefficient of the word `w` in `a`. -/
noncomputable def coeff (w : FreeMonoid X) : FreeAlgebra R X →ₗ[R] R :=
  (basisFreeMonoid R X).coord w

/-- `coeff` reads the coefficient through `equivMonoidAlgebraFreeMonoid`. -/
theorem coeff_def (w : FreeMonoid X) (a : FreeAlgebra R X) :
    coeff w a = (equivMonoidAlgebraFreeMonoid a).coeff w := by
  unfold coeff
  rfl

/-- Polynomials with the same coefficients are equal. -/
theorem ext_coeff {a b : FreeAlgebra R X} (h : ∀ w, coeff w a = coeff w b) : a = b :=
  (basisFreeMonoid R X).ext_elem h

/-- A nonzero polynomial has a word with a nonzero coefficient. -/
theorem exists_coeff_ne_zero {a : FreeAlgebra R X} (ha : a ≠ 0) : ∃ w, coeff w a ≠ 0 := by
  by_contra h
  push Not at h
  exact ha (ext_coeff fun w => by rw [h w, map_zero])

/-- The basis vector of a word is its image under `ι`. -/
theorem basisFreeMonoid_apply (w : FreeMonoid X) :
    basisFreeMonoid R X w = FreeMonoid.lift (ι R) w := by
  simp [basisFreeMonoid, equivMonoidAlgebraFreeMonoid]

/-- The coefficients of a monomial. -/
theorem coeff_lift_ι (w w' : FreeMonoid X) :
    coeff w (FreeMonoid.lift (ι R) w' : FreeAlgebra R X) = Finsupp.single w' (1 : R) w := by
  rw [← basisFreeMonoid_apply, coeff, Module.Basis.coord_apply, Module.Basis.repr_self]

/-- The coefficients of a variable. -/
theorem coeff_ι (w : FreeMonoid X) (x : X) :
    coeff w (ι R x) = Finsupp.single (FreeMonoid.of x) (1 : R) w := by
  rw [← coeff_lift_ι, FreeMonoid.lift_eval_of]

/-- The coefficients of `1`. -/
theorem coeff_one (w : FreeMonoid X) :
    coeff w (1 : FreeAlgebra R X) = Finsupp.single 1 (1 : R) w := by
  have h := coeff_lift_ι (R := R) w 1
  rwa [map_one] at h

/-- The coefficients of a scalar. -/
theorem coeff_algebraMap (w : FreeMonoid X) (r : R) :
    coeff w (algebraMap R (FreeAlgebra R X) r) = Finsupp.single 1 r w := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, coeff_one, smul_eq_mul]
  by_cases hw : w = 1
  · subst hw
    simp
  · simp [Ne.symm hw]

/-- The coefficient of a product: a sum over the splittings of the word. -/
theorem coeff_mul (w : FreeMonoid X) (a b : FreeAlgebra R X) :
    coeff w (a * b) = ∑ i ∈ Finset.range (w.length + 1),
      coeff (FreeMonoid.ofList (w.toList.take i)) a *
        coeff (FreeMonoid.ofList (w.toList.drop i)) b := by
  classical
  let split : ℕ → FreeMonoid X × FreeMonoid X := fun i =>
    (FreeMonoid.ofList (w.toList.take i), FreeMonoid.ofList (w.toList.drop i))
  have hinj : Set.InjOn split (Finset.range (w.length + 1)) := by
    intro i hi j hj hij
    have h := congrArg (fun p => p.1.toList.length) hij
    simp only [split, FreeMonoid.toList_ofList, List.length_take] at h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have hw : w.toList.length = w.length := rfl
    omega
  rw [coeff_def, map_mul, MonoidAlgebra.coeff_mul_antidiag _ _ _
    ((Finset.range (w.length + 1)).image split), Finset.sum_image hinj]
  · rfl
  · rintro ⟨p, q⟩
    simp only [Finset.mem_image, Finset.mem_range, Prod.mk.injEq, split]
    constructor
    · rintro ⟨i, -, rfl, rfl⟩
      exact congrArg FreeMonoid.ofList (List.take_append_drop i w.toList)
    · rintro rfl
      refine ⟨p.length, ?_, ?_, ?_⟩
      · rw [FreeMonoid.length_mul]
        omega
      · simp [FreeMonoid.length, FreeMonoid.toList_mul]
      · simp [FreeMonoid.length, FreeMonoid.toList_mul]

/-- `a` is homogeneous of degree `d`: every word with a nonzero coefficient has length `d`. -/
@[expose] def IsHomogeneous (a : FreeAlgebra R X) (d : ℕ) : Prop :=
  ∀ w : FreeMonoid X, coeff w a ≠ 0 → w.length = d

/-- A homogeneous polynomial has no words of another length. -/
theorem IsHomogeneous.coeff_eq_zero {a : FreeAlgebra R X} {d : ℕ} (h : a.IsHomogeneous d)
    {w : FreeMonoid X} (hw : w.length ≠ d) : coeff w a = 0 := by
  by_contra hne
  exact hw (h w hne)

/-- `0` is homogeneous of every degree. -/
theorem IsHomogeneous.zero {d : ℕ} : (0 : FreeAlgebra R X).IsHomogeneous d := by
  intro w hw
  simp at hw

/-- Sums of homogeneous polynomials of degree `d` are homogeneous of degree `d`. -/
theorem IsHomogeneous.add {a b : FreeAlgebra R X} {d : ℕ} (ha : a.IsHomogeneous d)
    (hb : b.IsHomogeneous d) : (a + b).IsHomogeneous d := by
  intro w hw
  by_contra hne
  rw [map_add, ha.coeff_eq_zero hne, hb.coeff_eq_zero hne, add_zero] at hw
  exact hw rfl

/-- Scalar multiples of homogeneous polynomials are homogeneous. -/
theorem IsHomogeneous.smul {a : FreeAlgebra R X} {d : ℕ} (r : R) (ha : a.IsHomogeneous d) :
    (r • a).IsHomogeneous d := by
  intro w hw
  by_contra hne
  rw [map_smul, ha.coeff_eq_zero hne, smul_zero] at hw
  exact hw rfl

/-- Finite sums of homogeneous polynomials of degree `d` are homogeneous of degree `d`. -/
theorem IsHomogeneous.sum {d : ℕ} {ι : Type*} (s : Finset ι) (f : ι → FreeAlgebra R X)
    (hf : ∀ i ∈ s, (f i).IsHomogeneous d) : (∑ i ∈ s, f i).IsHomogeneous d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IsHomogeneous.zero : (0 : FreeAlgebra R X).IsHomogeneous d)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- `1` is homogeneous of degree `0`. -/
theorem isHomogeneous_one : (1 : FreeAlgebra R X).IsHomogeneous 0 := by
  intro w hw
  rw [coeff_one] at hw
  by_contra hne
  exact hw (Finsupp.single_eq_of_ne (fun h => hne (by rw [h]; rfl)))

/-- A variable is homogeneous of degree `1`. -/
theorem isHomogeneous_ι (x : X) : (ι R x).IsHomogeneous 1 := by
  intro w hw
  rw [coeff_ι] at hw
  by_contra hne
  exact hw (Finsupp.single_eq_of_ne (fun h => hne (by rw [h]; rfl)))

/-- The monomial of a word `w` is homogeneous of degree `|w|`. -/
theorem isHomogeneous_lift_ι (w : FreeMonoid X) :
    (FreeMonoid.lift (ι R) w : FreeAlgebra R X).IsHomogeneous w.length := by
  intro w' hw'
  rw [coeff_lift_ι] at hw'
  by_contra hne
  exact hw' (Finsupp.single_eq_of_ne fun h => hne (by rw [h]))

/-- Multiplicativity of coefficients against a homogeneous left factor. -/
theorem coeff_mul_mul_of_isHomogeneous {a : FreeAlgebra R X} (b : FreeAlgebra R X)
    (u v : FreeMonoid X) (ha : a.IsHomogeneous u.length) :
    coeff (u * v) (a * b) = coeff u a * coeff v b := by
  rw [coeff_mul, Finset.sum_eq_single u.length]
  · simp [FreeMonoid.length, FreeMonoid.toList_mul]
  · intro i hmem hi
    have hu : u.length = u.toList.length := rfl
    rw [ha.coeff_eq_zero, zero_mul]
    simp only [Finset.mem_range, FreeMonoid.length, FreeMonoid.toList_ofList,
      FreeMonoid.toList_mul, List.length_take, List.length_append] at hmem hi ⊢
    omega
  · intro h
    simp [FreeMonoid.length_mul] at h

/-- Degrees add under multiplication. -/
theorem IsHomogeneous.mul {a b : FreeAlgebra R X} {d e : ℕ} (ha : a.IsHomogeneous d)
    (hb : b.IsHomogeneous e) : (a * b).IsHomogeneous (d + e) := by
  intro w hw
  rw [coeff_mul] at hw
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  have h1 := ha _ (left_ne_zero_of_mul hne)
  have h2 := hb _ (right_ne_zero_of_mul hne)
  have hw' : w.length = w.toList.length := rfl
  simp only [Finset.mem_range, FreeMonoid.length, FreeMonoid.toList_ofList,
    List.length_take, List.length_drop] at hi h1 h2
  omega

end FreeAlgebra
