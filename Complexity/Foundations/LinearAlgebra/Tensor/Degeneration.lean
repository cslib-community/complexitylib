/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, bilinear complexity: degenerations and border rank)

public import Complexity.Foundations.LinearAlgebra.Tensor.Basic
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Degenerations of tensors and Bini's conversion

A *degeneration of order `h`* of `S` to `T` (`Cslib.Tensor.IsDegen`) is a restriction of `S`
over the polynomial ring `K[ε]` whose result is `ε ^ h • T + ε ^ (h + 1) • E` for some error
tensor `E`. It is the "packing modulo `ε`" of [Pass][Pass2026], Definition 2.2, with the
denominators `ε ^ h` of its maps cleared, and the approximate bilinear algorithms of
[Bini][Bini1980]. The *shared-left* form `Cslib.Tensor.IsSLDegen f h T S` fixes the left
encoder to the inclusion of an injection `f`, as in the same-left packings of [Pass][Pass2026].

Degenerations compose (`IsDegen.trans`): the inner witness is taken at `ε ^ (h + 1)`, as in the
proof of [Pass][Pass2026], Lemma 2.9 (Appendix A.2), so that its error survives the outer
decoder, and the composite has order `(h + 1) (k + 1) - 1`. (The orders do not add: the outer
decoder may divide the inner error by `ε ^ h`.) Degenerations are closed under the tensor
product, finite tensor products, direct sums, leg exchanges and reindexing, like restrictions.
Shared-left degenerations are closed under the operations that keep the left leg: the exchange of
the right input and the output, tensor products and deletion of summands.

**Bini's conversion** (`IsDegen.exists_rank_tpow`, [Bini][Bini1980]; [Pass][Pass2026],
Lemma 2.4): a degeneration of `unit r` to `T` gives, for every `m`, a rank bound
`(D m + 1) r ^ m` on the tensor power `tpow m T`, where `D` bounds the degree in `ε` of the
witness. The coefficient of `ε ^ h` of a polynomial of degree at most `D` is a fixed linear
combination of its values at `D + 1` integer points, so the `D + 1` evaluations of the witness,
each a restriction of `unit r`, combine into a restriction of `unit ((D + 1) r)`.

## Main definitions

* `Cslib.Tensor.IsDegen`, `Cslib.Tensor.IsSLDegen`: degenerations of order `h`.

## Main results

* `Cslib.Tensor.IsDegen.of_isRestriction`, `Cslib.Tensor.IsDegen.trans`,
  `Cslib.Tensor.IsDegen.mono`: restrictions are degenerations of order `0`; composition.
* `Cslib.Tensor.IsDegen.tprod`, `Cslib.Tensor.IsDegen.tprodPi`, `Cslib.Tensor.IsDegen.dsum`,
  `Cslib.Tensor.IsDegen.swap12`, `Cslib.Tensor.IsDegen.swap23`, `Cslib.Tensor.IsDegen.swap13`,
  `Cslib.Tensor.IsDegen.reindex_target`, `Cslib.Tensor.IsDegen.reindex_source`,
  `Cslib.Tensor.IsDegen.of_reindex_target`, `Cslib.Tensor.IsDegen.of_reindex_source`: closure.
* `Cslib.Tensor.IsSLDegen.trans`, `Cslib.Tensor.IsSLDegen.swap23`,
  `Cslib.Tensor.IsSLDegen.tprod`, `Cslib.Tensor.IsSLDegen.tprodPi`,
  `Cslib.Tensor.IsSLDegen.slSum_comp`, `Cslib.Tensor.IsSLDegen.slSum_source_comp`,
  `Cslib.Tensor.IsSLDegen.toIsDegen`.
* `Cslib.Tensor.IsDegen.exists_rank_tpow`: Bini's conversion.

## References

* [D. Bini, *Relations between exact and approximate bilinear algorithms*][Bini1980]
* [R. Pass, *Matrix Multiplication from Polynomial Packings*][Pass2026], Definition 2.2,
  Lemma 2.4 and Appendix A
-/

@[expose] public section

namespace Cslib.Tensor

open Matrix Finset Polynomial

variable {K : Type*} {X Y Z X' Y' Z' X'' Y'' Z'' : Type*}

/-! ### Mapping entries by ring homomorphisms -/

/-- Restriction commutes with mapping all entries by a ring homomorphism. -/
theorem map_restrict {R R' : Type*} [CommSemiring R] [CommSemiring R'] (f : R →+* R')
    [Fintype X'] [Fintype Y'] [Fintype Z'] (α : Matrix X' X R) (β : Matrix Y' Y R)
    (γ : Matrix Z Z' R) (S : Tensor R X' Y' Z') :
    (restrict α β γ S).map f = restrict (α.map f) (β.map f) (γ.map f) (S.map f) := by
  funext x y z
  simp only [Tensor.map_apply, restrict, Matrix.map_apply, map_sum, map_mul]

@[simp] theorem map_incl {R R' : Type*} [CommSemiring R] [CommSemiring R'] (f : R →+* R')
    [DecidableEq X'] (g : X → X') : (incl g : Matrix X' X R).map f = incl g := by
  ext x' x
  simp only [Matrix.map_apply, incl_apply]
  split_ifs <;> simp

/-- Restriction is linear in the decoder. -/
private theorem restrict_smul_decoder {R : Type*} [CommSemiring R] [Fintype X'] [Fintype Y']
    [Fintype Z'] (α : Matrix X' X R) (β : Matrix Y' Y R) (γ : Matrix Z Z' R) (c : R)
    (S : Tensor R X' Y' Z') : restrict α β (c • γ) S = c • restrict α β γ S := by
  funext x y z
  simp only [restrict, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- Mapping entries commutes with tensor products. -/
private theorem tprod_map {R R' : Type*} [CommSemiring R] [CommSemiring R'] (f : R →+* R')
    {X₂ Y₂ Z₂ : Type*} (T : Tensor R X Y Z) (T' : Tensor R X₂ Y₂ Z₂) :
    (tprod T T').map f = tprod (T.map f) (T'.map f) := by
  funext x y z
  simp only [Tensor.map_apply, tprod_apply, map_mul]

/-- Mapping entries commutes with finite tensor products. -/
private theorem tprodPi_map {R R' : Type*} [CommSemiring R] [CommSemiring R'] (f : R →+* R')
    {ι : Type*} [Fintype ι] (T : ι → Tensor R X Y Z) :
    (tprodPi T).map f = tprodPi fun i => (T i).map f := by
  funext x y z
  simp only [Tensor.map_apply, tprodPi_apply, map_prod]

/-- Mapping entries commutes with direct sums. -/
private theorem dsum_map {R R' : Type*} [CommSemiring R] [CommSemiring R'] (f : R →+* R')
    {ι : Type*} [DecidableEq ι] (T : ι → Tensor R X Y Z) :
    (dsum T).map f = dsum fun i => (T i).map f := by
  funext x y z
  simp only [Tensor.map_apply, dsum_apply]
  split_ifs <;> simp

/-- The coefficient of `ε ^ h` of `ε ^ h t + ε ^ (h + 1) e`. -/
private theorem coeff_X_pow_mul_C_add {R : Type*} [Semiring R] (h : ℕ) (t : R) (e : R[X]) :
    (Polynomial.X ^ h * C t + Polynomial.X ^ (h + 1) * e).coeff h = t := by
  simp [Polynomial.coeff_X_pow_mul']

/-- A product of polynomials `a i + ε b i` is `∏ a i` plus a multiple of `ε`. -/
private theorem prod_add_X_mul {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (a b : ι → R[X]) :
    ∏ i ∈ s, (a i + Polynomial.X * b i) = ∏ i ∈ s, a i + Polynomial.X *
      Polynomial.divX (∏ i ∈ s, (a i + Polynomial.X * b i) - ∏ i ∈ s, a i) := by
  have h0 : (∏ i ∈ s, (a i + Polynomial.X * b i) - ∏ i ∈ s, a i).coeff 0 = 0 := by
    simp only [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_sub, Polynomial.eval_prod,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, zero_mul, add_zero, sub_self]
  have := Polynomial.X_mul_divX_add (∏ i ∈ s, (a i + Polynomial.X * b i) - ∏ i ∈ s, a i)
  rw [h0, Polynomial.C_0, add_zero] at this
  rw [this]
  ring

/-- A linear combination of tensors is a restriction of their direct sum. -/
private theorem isRestriction_sum_dsum {R : Type*} [CommSemiring R] {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype X] [Fintype Y] [Fintype Z] (c : ι → R) (T : ι → Tensor R X Y Z) :
    IsRestriction (∑ i, c i • T i) (dsum T) := by
  classical
  refine ⟨Matrix.of fun p x => if p.2 = x then 1 else 0,
    Matrix.of fun p y => if p.2 = y then 1 else 0,
    Matrix.of fun z p => if z = p.2 then c p.1 else 0, ?_⟩
  funext x y z
  simp [restrict, Fintype.sum_prod_type, ite_and, mul_ite, ite_mul, Finset.sum_ite_irrel,
    Finset.sum_apply]

/-! ### Degenerations -/

section Degenerations

variable [CommRing K]

/-- **Degeneration of order `h`**: over `K[ε]`, a restriction of `S` equals
`ε ^ h • T + ε ^ (h + 1) • E` for some error tensor `E`. -/
def IsDegen [Fintype X'] [Fintype Y'] [Fintype Z'] (h : ℕ) (T : Tensor K X Y Z)
    (S : Tensor K X' Y' Z') : Prop :=
  ∃ (α : Matrix X' X K[X]) (β : Matrix Y' Y K[X]) (γ : Matrix Z Z' K[X])
    (E : Tensor K[X] X Y Z),
    restrict α β γ (S.map C) =
      (Polynomial.X ^ h : K[X]) • T.map C + (Polynomial.X ^ (h + 1) : K[X]) • E

/-- **Shared-left degeneration of order `h`** along `f`: a degeneration whose left encoder is
the inclusion matrix of `f`, so that every source receives the common left input. -/
def IsSLDegen [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X'] (f : X → X') (h : ℕ)
    (T : Tensor K X Y Z) (S : Tensor K X' Y' Z') : Prop :=
  ∃ (β : Matrix Y' Y K[X]) (γ : Matrix Z Z' K[X]) (E : Tensor K[X] X Y Z),
    restrict (incl f) β γ (S.map C) =
      (Polynomial.X ^ h : K[X]) • T.map C + (Polynomial.X ^ (h + 1) : K[X]) • E

theorem IsSLDegen.toIsDegen [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X'] {f : X → X'}
    {h : ℕ} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} (hT : IsSLDegen f h T S) :
    IsDegen h T S := by
  obtain ⟨β, γ, E, hE⟩ := hT
  exact ⟨_, β, γ, E, hE⟩

/-- A restriction is a degeneration of order `0`. -/
theorem IsDegen.of_isRestriction [Fintype X'] [Fintype Y'] [Fintype Z'] {T : Tensor K X Y Z}
    {S : Tensor K X' Y' Z'} (h : IsRestriction T S) : IsDegen 0 T S := by
  obtain ⟨α, β, γ, rfl⟩ := h
  refine ⟨α.map C, β.map C, γ.map C, 0, ?_⟩
  rw [← map_restrict]
  ext x y z
  simp

/-- A shared-left restriction is a shared-left degeneration of order `0`. -/
theorem IsSLDegen.of_restrict_incl [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X']
    {f : X → X'} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} (β : Matrix Y' Y K)
    (γ : Matrix Z Z' K) (h : restrict (incl f) β γ S = T) : IsSLDegen f 0 T S := by
  refine ⟨β.map C, γ.map C, 0, ?_⟩
  rw [← map_incl (C : K →+* K[X]) f, ← map_restrict, h]
  ext x y z
  simp

/-- Raising the order of a degeneration: multiply the decoder by `ε`. -/
theorem IsDegen.mono [Fintype X'] [Fintype Y'] [Fintype Z'] {h h' : ℕ} {T : Tensor K X Y Z}
    {S : Tensor K X' Y' Z'} (hT : IsDegen h T S) (hh : h ≤ h') : IsDegen h' T S := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hh
  obtain ⟨α, β, γ, E, hE⟩ := hT
  refine ⟨α, β, (Polynomial.X ^ d : K[X]) • γ, E, ?_⟩
  rw [restrict_smul_decoder, hE]
  funext x y z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem IsSLDegen.mono [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X'] {f : X → X'}
    {h h' : ℕ} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} (hT : IsSLDegen f h T S)
    (hh : h ≤ h') : IsSLDegen f h' T S := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hh
  obtain ⟨β, γ, E, hE⟩ := hT
  refine ⟨β, (Polynomial.X ^ d : K[X]) • γ, E, ?_⟩
  rw [restrict_smul_decoder, hE]
  funext x y z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Substituting `ε ↦ ε ^ N` in a degeneration witness of order `k` gives a witness of order
`N k` whose error is divisible by `ε ^ (N k + N)`. -/
private theorem restrict_map_expand [Fintype X'] [Fintype Y'] [Fintype Z'] {k : ℕ}
    {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} {α : Matrix X' X K[X]} {β : Matrix Y' Y K[X]}
    {γ : Matrix Z Z' K[X]} {E : Tensor K[X] X Y Z}
    (hw : restrict α β γ (S.map C) =
      (Polynomial.X ^ k : K[X]) • T.map C + (Polynomial.X ^ (k + 1) : K[X]) • E) (N : ℕ) :
    restrict (α.map (Polynomial.expand K N).toRingHom) (β.map (Polynomial.expand K N).toRingHom)
        (γ.map (Polynomial.expand K N).toRingHom) (S.map C) =
      (Polynomial.X ^ (N * k) : K[X]) • T.map C +
        (Polynomial.X ^ (N * k + N) : K[X]) • E.map (Polynomial.expand K N).toRingHom := by
  have he : ∀ p : K[X], (Polynomial.expand K N).toRingHom p = Polynomial.expand K N p :=
    fun _ => rfl
  have hS : (S.map C).map (Polynomial.expand K N).toRingHom = S.map C := by
    funext x y z
    simp only [Tensor.map_apply, he, Polynomial.expand_C]
  rw [← hS, ← map_restrict, hw]
  funext x y z
  simp only [Tensor.map_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, he, map_add, map_mul,
    map_pow, Polynomial.expand_X, Polynomial.expand_C]
  ring

/-- A degeneration of order `k` has, for every `N`, a witness of order `N k` whose error is
divisible by `ε ^ (N k + N)`. -/
private theorem exists_restrict_eq_of_isDegen [Fintype X'] [Fintype Y'] [Fintype Z'] {k : ℕ}
    {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} (hT : IsDegen k T S) (N : ℕ) :
    ∃ (α : Matrix X' X K[X]) (β : Matrix Y' Y K[X]) (γ : Matrix Z Z' K[X])
      (E : Tensor K[X] X Y Z),
      restrict α β γ (S.map C) =
        (Polynomial.X ^ (N * k) : K[X]) • T.map C + (Polynomial.X ^ (N * k + N) : K[X]) • E := by
  obtain ⟨α, β, γ, E, hE⟩ := hT
  exact ⟨_, _, _, _, restrict_map_expand hE N⟩

/-- **Composition of degenerations** ([Pass][Pass2026], Lemma 2.9): the inner witness is taken
at `ε ^ (h + 1)`, so that the outer decoder, which divides by at most `ε ^ h`, leaves its error
divisible by `ε`; the composite has order `h k + h + k = (h + 1) (k + 1) - 1`. -/
theorem IsDegen.trans [Fintype X'] [Fintype Y'] [Fintype Z'] [Fintype X''] [Fintype Y'']
    [Fintype Z''] {h k : ℕ} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} {U : Tensor K X'' Y'' Z''}
    (hT : IsDegen h T S) (hS : IsDegen k S U) : IsDegen (h * k + h + k) T U := by
  obtain ⟨α, β, γ, E, hE⟩ := hT
  obtain ⟨α', β', γ', E', hE'⟩ := exists_restrict_eq_of_isDegen hS (h + 1)
  refine ⟨α' * α, β' * β, γ * γ', E + restrict α β γ E', ?_⟩
  rw [← restrict_restrict, hE', restrict_add, restrict_smul, restrict_smul, hE]
  funext x y z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The inclusion matrix of a composite is the product of the inclusion matrices. -/
theorem incl_comp {R : Type*} [CommSemiring R] [Fintype X'] [DecidableEq X'] [DecidableEq X'']
    (f : X → X') (g : X' → X'') : (incl (g ∘ f) : Matrix X'' X R) = incl g * incl f := by
  ext x'' x
  simp only [incl_apply, Matrix.mul_apply, Function.comp_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- A shared-left degeneration of order `k` has, for every `N`, a witness of order `N k` whose
error is divisible by `ε ^ (N k + N)`. -/
private theorem exists_restrict_incl_eq_of_isSLDegen [Fintype X'] [Fintype Y'] [Fintype Z']
    [DecidableEq X'] {f : X → X'} {k : ℕ} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'}
    (hT : IsSLDegen f k T S) (N : ℕ) :
    ∃ (β : Matrix Y' Y K[X]) (γ : Matrix Z Z' K[X]) (E : Tensor K[X] X Y Z),
      restrict (incl f) β γ (S.map C) =
        (Polynomial.X ^ (N * k) : K[X]) • T.map C + (Polynomial.X ^ (N * k + N) : K[X]) • E := by
  obtain ⟨β, γ, E, hE⟩ := hT
  have := restrict_map_expand hE N
  rw [map_incl] at this
  exact ⟨_, _, _, this⟩

/-- Composition of shared-left degenerations, the injections composing; the inner witness is
taken at `ε ^ (h + 1)` as in `IsDegen.trans`. -/
theorem IsSLDegen.trans [Fintype X'] [Fintype Y'] [Fintype Z'] [Fintype X''] [Fintype Y'']
    [Fintype Z''] [DecidableEq X'] [DecidableEq X''] {f : X → X'} {g : X' → X''} {h k : ℕ}
    {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} {U : Tensor K X'' Y'' Z''}
    (hT : IsSLDegen f h T S) (hS : IsSLDegen g k S U) :
    IsSLDegen (g ∘ f) (h * k + h + k) T U := by
  obtain ⟨β, γ, E, hE⟩ := hT
  obtain ⟨β', γ', E', hE'⟩ := exists_restrict_incl_eq_of_isSLDegen hS (h + 1)
  refine ⟨β' * β, γ * γ', E + restrict (incl f) β γ E', ?_⟩
  rw [incl_comp, ← restrict_restrict, hE', restrict_add, restrict_smul, restrict_smul, hE]
  funext x y z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Composing a degeneration with a restriction of its target. -/
theorem IsRestriction.trans_isDegen [Fintype X'] [Fintype Y'] [Fintype Z'] [Fintype X'']
    [Fintype Y''] [Fintype Z''] {h : ℕ} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'}
    {U : Tensor K X'' Y'' Z''} (hT : IsRestriction T S) (hS : IsDegen h S U) : IsDegen h T U := by
  obtain ⟨α, β, γ, rfl⟩ := hT
  obtain ⟨α', β', γ', E', hE'⟩ := hS
  refine ⟨α' * α.map C, β' * β.map C, γ.map C * γ', restrict (α.map C) (β.map C) (γ.map C) E', ?_⟩
  rw [← restrict_restrict, hE', restrict_add, restrict_smul, restrict_smul, map_restrict]

/-- Composing a degeneration with a restriction of its source. -/
theorem IsDegen.trans_isRestriction [Fintype X'] [Fintype Y'] [Fintype Z'] [Fintype X'']
    [Fintype Y''] [Fintype Z''] {h : ℕ} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'}
    {U : Tensor K X'' Y'' Z''} (hT : IsDegen h T S) (hS : IsRestriction S U) : IsDegen h T U := by
  obtain ⟨α, β, γ, E, hE⟩ := hT
  obtain ⟨α', β', γ', rfl⟩ := hS
  refine ⟨α'.map C * α, β'.map C * β, γ * γ'.map C, E, ?_⟩
  rw [← restrict_restrict, ← map_restrict, hE]

/-! ### Leg exchanges and reindexing -/

theorem IsDegen.swap12 [Fintype X'] [Fintype Y'] [Fintype Z'] {h : ℕ} {T : Tensor K X Y Z}
    {S : Tensor K X' Y' Z'} (hT : IsDegen h T S) : IsDegen h (swap12 T) (swap12 S) := by
  obtain ⟨α, β, γ, E, hE⟩ := hT
  refine ⟨β, α, γ, Tensor.swap12 E, ?_⟩
  change restrict β α γ (Tensor.swap12 (S.map C)) = _
  rw [← swap12_restrict, hE]
  rfl

theorem IsDegen.swap23 [Fintype X'] [Fintype Y'] [Fintype Z'] {h : ℕ} {T : Tensor K X Y Z}
    {S : Tensor K X' Y' Z'} (hT : IsDegen h T S) : IsDegen h (swap23 T) (swap23 S) := by
  obtain ⟨α, β, γ, E, hE⟩ := hT
  refine ⟨α, γᵀ, βᵀ, Tensor.swap23 E, ?_⟩
  change restrict α γᵀ βᵀ (Tensor.swap23 (S.map C)) = _
  rw [← swap23_restrict, hE]
  rfl

theorem IsDegen.swap13 [Fintype X'] [Fintype Y'] [Fintype Z'] {h : ℕ} {T : Tensor K X Y Z}
    {S : Tensor K X' Y' Z'} (hT : IsDegen h T S) : IsDegen h (swap13 T) (swap13 S) := by
  obtain ⟨α, β, γ, E, hE⟩ := hT
  refine ⟨γᵀ, β, αᵀ, Tensor.swap13 E, ?_⟩
  change restrict γᵀ β αᵀ (Tensor.swap13 (S.map C)) = _
  rw [← swap13_restrict, hE]
  rfl

/-- The exchange of the right input and the output keeps the left leg, so it preserves
shared-left degenerations. -/
theorem IsSLDegen.swap23 [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X'] {f : X → X'}
    {h : ℕ} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} (hT : IsSLDegen f h T S) :
    IsSLDegen f h (swap23 T) (swap23 S) := by
  obtain ⟨β, γ, E, hE⟩ := hT
  refine ⟨γᵀ, βᵀ, Tensor.swap23 E, ?_⟩
  change restrict (incl f) γᵀ βᵀ (Tensor.swap23 (S.map C)) = _
  rw [← swap23_restrict, hE]
  rfl

theorem IsDegen.reindex_target [Fintype X'] [Fintype Y'] [Fintype Z'] {h : ℕ}
    {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} (e₁ : X ≃ X'') (e₂ : Y ≃ Y'') (e₃ : Z ≃ Z'')
    (hT : IsDegen h T S) :
    IsDegen h (reindex e₁ e₂ e₃ T) S := by
  obtain ⟨α, β, γ, E, hE⟩ := hT
  refine ⟨α.submatrix id e₁.symm, β.submatrix id e₂.symm, γ.submatrix e₃.symm id,
    reindex e₁ e₂ e₃ E, ?_⟩
  rw [← reindex_restrict, hE]
  rfl

theorem IsDegen.reindex_source [Fintype X'] [Fintype Y'] [Fintype Z'] [Fintype X''] [Fintype Y'']
    [Fintype Z''] {h : ℕ} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} (e₁ : X' ≃ X'')
    (e₂ : Y' ≃ Y'') (e₃ : Z' ≃ Z'')
    (hT : IsDegen h T S) : IsDegen h T (reindex e₁ e₂ e₃ S) :=
  hT.trans_isRestriction (isRestriction_of_reindex e₁ e₂ e₃ S)

/-- Removing a reindexing of the target of a degeneration. -/
theorem IsDegen.of_reindex_target [Fintype X'] [Fintype Y'] [Fintype Z'] {h : ℕ}
    {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} {e₁ : X ≃ X''} {e₂ : Y ≃ Y''} {e₃ : Z ≃ Z''}
    (hT : IsDegen h (reindex e₁ e₂ e₃ T) S) : IsDegen h T S := by
  have := hT.reindex_target e₁.symm e₂.symm e₃.symm
  rwa [reindex_symm_reindex] at this

/-- Removing a reindexing of the source of a degeneration. -/
theorem IsDegen.of_reindex_source [Fintype X'] [Fintype Y'] [Fintype Z'] [Fintype X'']
    [Fintype Y''] [Fintype Z''] {h : ℕ} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'}
    {e₁ : X' ≃ X''} {e₂ : Y' ≃ Y''} {e₃ : Z' ≃ Z''} (hT : IsDegen h T (reindex e₁ e₂ e₃ S)) :
    IsDegen h T S := by
  have := hT.reindex_source e₁.symm e₂.symm e₃.symm
  rwa [reindex_symm_reindex] at this

/-- Reindexing the target of a shared-left degeneration composes the injection with the left
equivalence. -/
theorem IsSLDegen.reindex_target [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X']
    {f : X → X'} {h : ℕ} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} (e₁ : X ≃ X'')
    (e₂ : Y ≃ Y'') (e₃ : Z ≃ Z'') (hT : IsSLDegen f h T S) :
    IsSLDegen (f ∘ e₁.symm) h (reindex e₁ e₂ e₃ T) S := by
  obtain ⟨β, γ, E, hE⟩ := hT
  refine ⟨β.submatrix id e₂.symm, γ.submatrix e₃.symm id, reindex e₁ e₂ e₃ E, ?_⟩
  have h₁ : (incl (f ∘ e₁.symm) : Matrix X' X'' K[X]) = (incl f).submatrix id e₁.symm := rfl
  rw [h₁, ← reindex_restrict, hE]
  rfl

/-- Reindexing the source of a shared-left degeneration composes the left equivalence with the
injection. -/
theorem IsSLDegen.reindex_source [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X']
    [Fintype X''] [Fintype Y''] [Fintype Z''] [DecidableEq X''] {f : X → X'} {h : ℕ}
    {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} (e₁ : X' ≃ X'') (e₂ : Y' ≃ Y'') (e₃ : Z' ≃ Z'')
    (hT : IsSLDegen f h T S) : IsSLDegen (e₁ ∘ f) h T (reindex e₁ e₂ e₃ S) := by
  classical
  obtain ⟨β, γ, E, hE⟩ := hT
  refine ⟨incl e₂ * β, γ * (incl e₃)ᵀ, E, ?_⟩
  rw [incl_comp, ← restrict_restrict, restrict_incl]
  have h₁ : (fun x y z => (reindex e₁ e₂ e₃ S).map C (e₁ x) (e₂ y) (e₃ z)) = S.map C := by
    funext x y z
    simp
  rw [h₁, hE]

/-- Removing a reindexing of the target of a shared-left degeneration. -/
theorem IsSLDegen.of_reindex_target [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X']
    {f : X'' → X'} {h : ℕ} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} {e₁ : X ≃ X''}
    {e₂ : Y ≃ Y''} {e₃ : Z ≃ Z''} (hT : IsSLDegen f h (reindex e₁ e₂ e₃ T) S) :
    IsSLDegen (f ∘ e₁) h T S := by
  have := hT.reindex_target e₁.symm e₂.symm e₃.symm
  rwa [reindex_symm_reindex, Equiv.symm_symm] at this

/-- Removing a reindexing of the source of a shared-left degeneration. -/
theorem IsSLDegen.of_reindex_source [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X']
    [Fintype X''] [Fintype Y''] [Fintype Z''] [DecidableEq X''] {f : X → X''} {h : ℕ}
    {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} {e₁ : X' ≃ X''} {e₂ : Y' ≃ Y''} {e₃ : Z' ≃ Z''}
    (hT : IsSLDegen f h T (reindex e₁ e₂ e₃ S)) : IsSLDegen (e₁.symm ∘ f) h T S := by
  have := hT.reindex_source e₁.symm e₂.symm e₃.symm
  rwa [reindex_symm_reindex] at this

/-! ### Tensor products and sums -/

open scoped Kronecker in
theorem IsDegen.tprod [Fintype X'] [Fintype Y'] [Fintype Z'] [Fintype X''] [Fintype Y'']
    [Fintype Z''] {X₂ Y₂ Z₂ : Type*} {h h' : ℕ} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'}
    {T' : Tensor K X₂ Y₂ Z₂} {S' : Tensor K X'' Y'' Z''} (hT : IsDegen h T S)
    (hT' : IsDegen h' T' S') : IsDegen (h + h') (tprod T T') (tprod S S') := by
  obtain ⟨α, β, γ, E, hE⟩ := hT
  obtain ⟨α', β', γ', E', hE'⟩ := hT'
  refine ⟨α ⊗ₖ α', β ⊗ₖ β', γ ⊗ₖ γ', Tensor.tprod (T.map C) E' + Tensor.tprod E (T'.map C) +
    (Polynomial.X : K[X]) • Tensor.tprod E E', ?_⟩
  rw [tprod_map, ← restrict_tprod, hE, hE']
  funext x y z
  simp only [tprod_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Tensor.map_apply, map_mul]
  ring

/-- The finite tensor product of degeneration witnesses is a witness of the summed order. -/
private theorem exists_tprodPi_eq {ι : Type*} [Fintype ι] (h : ι → ℕ) (T : ι → Tensor K X Y Z)
    (E : ι → Tensor K[X] X Y Z) :
    ∃ R : Tensor K[X] (ι → X) (ι → Y) (ι → Z),
      tprodPi (fun i => (Polynomial.X ^ h i : K[X]) • (T i).map C +
          (Polynomial.X ^ (h i + 1) : K[X]) • E i) =
        (Polynomial.X ^ (∑ i, h i) : K[X]) • (tprodPi T).map C +
          (Polynomial.X ^ (∑ i, h i + 1) : K[X]) • R := by
  refine ⟨fun x y z => Polynomial.divX (∏ i, (C (T i (x i) (y i) (z i)) +
    Polynomial.X * E i (x i) (y i) (z i)) - ∏ i, C (T i (x i) (y i) (z i))), ?_⟩
  funext x y z
  simp only [tprodPi_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Tensor.map_apply, map_prod]
  have : ∀ i, Polynomial.X ^ h i * C (T i (x i) (y i) (z i)) +
      Polynomial.X ^ (h i + 1) * E i (x i) (y i) (z i) =
      Polynomial.X ^ h i * (C (T i (x i) (y i) (z i)) + Polynomial.X * E i (x i) (y i) (z i)) :=
    fun i => by ring
  simp only [this, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  conv_lhs => rw [prod_add_X_mul]
  ring

theorem IsDegen.tprodPi {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype X'] [Fintype Y']
    [Fintype Z'] {h : ι → ℕ} {T : ι → Tensor K X Y Z} {S : ι → Tensor K X' Y' Z'}
    (hT : ∀ i, IsDegen (h i) (T i) (S i)) : IsDegen (∑ i, h i) (tprodPi T) (tprodPi S) := by
  choose α β γ E hE using hT
  obtain ⟨R, hR⟩ := exists_tprodPi_eq h T E
  exact ⟨piKronecker α, piKronecker β, piKronecker γ, R, by
    rw [tprodPi_map, ← restrict_tprodPi, funext hE, hR]⟩

theorem IsDegen.tpow [Fintype X'] [Fintype Y'] [Fintype Z'] {h : ℕ} {T : Tensor K X Y Z}
    {S : Tensor K X' Y' Z'} (hT : IsDegen h T S) (d : ℕ) :
    IsDegen (d * h) (tpow d T) (tpow d S) := by
  have := IsDegen.tprodPi (h := fun _ : Fin d => h) fun _ => hT
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  exact this

theorem IsDegen.dsum {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype X'] [Fintype Y']
    [Fintype Z'] {h : ℕ} {T : ι → Tensor K X Y Z} {S : ι → Tensor K X' Y' Z'}
    (hT : ∀ i, IsDegen h (T i) (S i)) : IsDegen h (dsum T) (dsum S) := by
  choose α β γ E hE using hT
  refine ⟨blockDiag α, blockDiag β, blockDiag γ, Tensor.dsum E, ?_⟩
  rw [dsum_map, ← restrict_dsum, funext hE]
  funext ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
  simp only [dsum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Tensor.map_apply]
  split_ifs <;> simp

open scoped Kronecker in
/-- The Kronecker product of inclusion matrices is the inclusion matrix of the product map. -/
private theorem incl_kronecker {R : Type*} [CommSemiring R] {X₂ : Type*} [DecidableEq X']
    [DecidableEq X''] (f : X → X') (f' : X₂ → X'') :
    (incl f : Matrix X' X R) ⊗ₖ (incl f' : Matrix X'' X₂ R) = incl (Prod.map f f') := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.kronecker_apply, incl_apply, Prod.map_apply, Prod.mk.injEq, ite_and, ite_mul,
    one_mul, zero_mul]

/-- The Kronecker product of copies of an inclusion matrix is the inclusion matrix of the
coordinatewise map. -/
private theorem piKronecker_incl {R : Type*} [CommSemiring R] {ι : Type*} [Fintype ι]
    [DecidableEq X'] [DecidableEq (ι → X')] (f : X → X') :
    piKronecker (fun _ : ι => (incl f : Matrix X' X R)) = incl fun x i => f (x i) := by
  ext x' x
  simp only [piKronecker_apply, incl_apply, Fintype.prod_ite_zero, Finset.prod_const_one,
    funext_iff]

/-- Shared-left degenerations tensor, the injections multiplying. -/
theorem IsSLDegen.tprod [Fintype X'] [Fintype Y'] [Fintype Z'] [Fintype X''] [Fintype Y'']
    [Fintype Z''] [DecidableEq X'] [DecidableEq X''] {X₂ Y₂ Z₂ : Type*} {f : X → X'}
    {f' : X₂ → X''} {h h' : ℕ} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} {T' : Tensor K X₂ Y₂ Z₂}
    {S' : Tensor K X'' Y'' Z''} (hT : IsSLDegen f h T S) (hT' : IsSLDegen f' h' T' S') :
    IsSLDegen (Prod.map f f') (h + h') (tprod T T') (tprod S S') := by
  obtain ⟨β, γ, E, hE⟩ := hT
  obtain ⟨β', γ', E', hE'⟩ := hT'
  refine ⟨Matrix.kroneckerMap (· * ·) β β', Matrix.kroneckerMap (· * ·) γ γ',
    Tensor.tprod (T.map C) E' + Tensor.tprod E (T'.map C) +
      (Polynomial.X : K[X]) • Tensor.tprod E E', ?_⟩
  rw [tprod_map, ← incl_kronecker, ← restrict_tprod, hE, hE']
  funext x y z
  simp only [tprod_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Tensor.map_apply, map_mul]
  ring

theorem IsSLDegen.tprodPi {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype X'] [Fintype Y']
    [Fintype Z'] [DecidableEq X'] {f : X → X'} {h : ι → ℕ} {T : ι → Tensor K X Y Z}
    {S : ι → Tensor K X' Y' Z'} (hT : ∀ i, IsSLDegen f (h i) (T i) (S i)) :
    IsSLDegen (fun x i => f (x i)) (∑ i, h i) (tprodPi T) (tprodPi S) := by
  choose β γ E hE using hT
  obtain ⟨R, hR⟩ := exists_tprodPi_eq h T E
  exact ⟨piKronecker β, piKronecker γ, R, by
    rw [tprodPi_map, ← piKronecker_incl, ← restrict_tprodPi, funext hE, hR]⟩

theorem IsSLDegen.tpow [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X'] {f : X → X'}
    {h : ℕ} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} (hT : IsSLDegen f h T S) (d : ℕ) :
    IsSLDegen (fun x i => f (x i)) (d * h) (tpow d T) (tpow d S) := by
  have := IsSLDegen.tprodPi (h := fun _ : Fin d => h) fun _ => hT
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  exact this

/-- Deleting and reordering the summands of the target of a shared-left degeneration. -/
theorem IsSLDegen.slSum_comp {ι κ : Type*} [Finite ι] [DecidableEq ι] [DecidableEq κ]
    [Finite X] [Finite Y] [Finite Z]
    [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X'] {f : X → X'} {h : ℕ}
    {G : ι → Tensor K X Y Z} {S : Tensor K X' Y' Z'} (hT : IsSLDegen f h (Tensor.slSum G) S)
    (e : κ → ι) (he : Function.Injective e) : IsSLDegen f h (Tensor.slSum (G ∘ e)) S := by
  cases nonempty_fintype ι
  cases nonempty_fintype X
  cases nonempty_fintype Y
  cases nonempty_fintype Z
  classical
  obtain ⟨β, γ, E, hE⟩ := hT
  have hG : restrict 1 (incl (Prod.map e id)) (incl (Prod.map e id))ᵀ ((slSum G).map C) =
      (slSum (G ∘ e)).map C := by
    rw [← slSum_comp_eq_restrict G e he, map_restrict, Matrix.map_one _ (map_zero C) (map_one C),
      map_incl, Matrix.transpose_map, map_incl]
  refine ⟨β * incl (Prod.map e id), (incl (Prod.map e id))ᵀ * γ,
    restrict 1 (incl (Prod.map e id)) (incl (Prod.map e id))ᵀ E, ?_⟩
  rw [← hG, ← restrict_smul, ← restrict_smul, ← restrict_add, ← hE, restrict_restrict,
    Matrix.mul_one]

/-- Adding unused sources ([Pass][Pass2026], Observation 2.5): a shared-left degeneration from
a shared-left sum of some of the summands of `slSum G` is one from `slSum G`. -/
theorem IsSLDegen.slSum_source_comp {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X'] {f : X → X'} {h : ℕ}
    {T : Tensor K X Y Z} {G : ι → Tensor K X' Y' Z'} (e : κ → ι) (he : Function.Injective e)
    (hT : IsSLDegen f h T (Tensor.slSum (G ∘ e))) : IsSLDegen f h T (Tensor.slSum G) := by
  classical
  obtain ⟨β, γ, E, hE⟩ := hT
  refine ⟨incl (Prod.map e id) * β, γ * (incl (Prod.map e id))ᵀ, E, ?_⟩
  have hG : restrict 1 (incl (Prod.map e id)) (incl (Prod.map e id))ᵀ ((slSum G).map C) =
      (slSum (G ∘ e)).map C := by
    rw [← slSum_comp_eq_restrict G e he, map_restrict, Matrix.map_one _ (map_zero C) (map_one C),
      map_incl, Matrix.transpose_map, map_incl]
  rw [← hE, ← hG, restrict_restrict, Matrix.one_mul]

/-- Deleting and reordering the summands of the target of a degeneration. -/
theorem IsDegen.dsum_comp {ι κ : Type*} [Finite ι] [DecidableEq ι] [DecidableEq κ] [Finite X]
    [Finite Y] [Finite Z] [Fintype X']
    [Fintype Y'] [Fintype Z'] {h : ℕ} {G : ι → Tensor K X Y Z} {S : Tensor K X' Y' Z'}
    (hT : IsDegen h (Tensor.dsum G) S) (e : κ → ι) (he : Function.Injective e) :
    IsDegen h (Tensor.dsum (G ∘ e)) S := by
  cases nonempty_fintype ι
  cases nonempty_fintype X
  cases nonempty_fintype Y
  cases nonempty_fintype Z
  exact (isRestriction_dsum_comp G e he).trans_isDegen hT

end Degenerations

/-! ### Bini's conversion -/

section Bini

variable [Field K] [CharZero K]

/-- The coefficient of `ε ^ h` of a polynomial of degree at most `D` is a fixed linear
combination of its values at the integer points `0, …, D`. -/
theorem exists_coeff_eq_sum_eval (h D : ℕ) :
    ∃ c : Fin (D + 1) → K, ∀ p : K[X], p.natDegree ≤ D →
      p.coeff h = ∑ k, c k * p.eval (k : K) := by
  refine ⟨fun k => (Lagrange.basis univ (fun k : Fin (D + 1) => (k : K)) k).coeff h,
    fun p hp => ?_⟩
  have hv : Set.InjOn (fun k : Fin (D + 1) => (k : K)) ↑(univ : Finset (Fin (D + 1))) :=
    fun i _ j _ hij => Fin.ext (Nat.cast_injective hij)
  have hdeg : p.degree < (univ : Finset (Fin (D + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_add_one_iff.mpr hp)
  conv_lhs => rw [Lagrange.eq_interpolate hv hdeg]
  simp only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- A degeneration of `unit r` whose witness has degree at most `D` gives rank `(D + 1) r`. -/
theorem IsDegen.rank_of_natDegree_le [Finite X] [Finite Y] [Finite Z] {h D r : ℕ}
    {T : Tensor K X Y Z} (α : Matrix (Fin r) X K[X]) (β : Matrix (Fin r) Y K[X])
    (γ : Matrix Z (Fin r) K[X]) (E : Tensor K[X] X Y Z)
    (hw : restrict α β γ ((unit r).map C) =
      (Polynomial.X ^ h : K[X]) • T.map C + (Polynomial.X ^ (h + 1) : K[X]) • E)
    (hD : ∀ x y z, (restrict α β γ ((unit r).map C) x y z).natDegree ≤ D) :
    Rank ((D + 1) * r) T := by
  cases nonempty_fintype X
  cases nonempty_fintype Y
  cases nonempty_fintype Z
  classical
  obtain ⟨c, hc⟩ := exists_coeff_eq_sum_eval (K := K) h D
  have hT : T = ∑ k : Fin (D + 1), c k •
      (restrict α β γ ((unit r).map C)).map (Polynomial.evalRingHom (k : K)) := by
    funext x y z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Tensor.map_apply,
      Polynomial.coe_evalRingHom]
    rw [← hc _ (hD x y z), hw]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Tensor.map_apply]
    exact (coeff_X_pow_mul_C_add h _ _).symm
  have h₁ : ∀ k : Fin (D + 1), IsRestriction
      ((restrict α β γ ((unit r).map C)).map (Polynomial.evalRingHom (k : K))) (unit r) := by
    intro k
    refine ⟨α.map (Polynomial.evalRingHom (k : K)), β.map (Polynomial.evalRingHom (k : K)),
      γ.map (Polynomial.evalRingHom (k : K)), ?_⟩
    rw [map_restrict]
    congr 1
    funext i j l
    simp only [Tensor.map_apply, unit_apply, Polynomial.coe_evalRingHom]
    split_ifs <;> simp
  have h₂ : IsRestriction T (Tensor.dsum fun _ : Fin (D + 1) => (unit r : Tensor K _ _ _)) := by
    rw [hT]
    exact (isRestriction_sum_dsum c _).trans (IsRestriction.dsum h₁)
  exact Rank.of_isRestriction h₂ (Rank.dsum (D + 1) (IsRestriction.refl _))

/-- **Bini's conversion** ([Bini][Bini1980]; [Pass][Pass2026], Lemma 2.4): a degeneration of
`unit r` to `T` gives rank bounds `(D m + 1) r ^ m` on the tensor powers of `T`, for a degree
bound `D` depending only on the degeneration. -/
theorem IsDegen.exists_rank_tpow [Finite X] [Finite Y] [Finite Z] {h r : ℕ}
    {T : Tensor K X Y Z} (hT : IsDegen h T (unit r)) :
    ∃ D : ℕ, ∀ m : ℕ, Rank ((D * m + 1) * r ^ m) (Tensor.tpow m T) := by
  cases nonempty_fintype X
  cases nonempty_fintype Y
  cases nonempty_fintype Z
  classical
  obtain ⟨α, β, γ, E, hw⟩ := hT
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ x y z, (restrict α β γ ((unit r).map C) x y z).natDegree ≤ D :=
    ⟨univ.sup fun p : X × Y × Z => (restrict α β γ ((unit r).map C) p.1 p.2.1 p.2.2).natDegree,
      fun x y z => Finset.le_sup (f := fun p : X × Y × Z =>
        (restrict α β γ ((unit r).map C) p.1 p.2.1 p.2.2).natDegree) (b := (x, y, z))
        (Finset.mem_univ _)⟩
  refine ⟨D, fun m => ?_⟩
  obtain ⟨R, hR⟩ := exists_tprodPi_eq (fun _ : Fin m => h) (fun _ => T) fun _ => E
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hR
  obtain ⟨α₁, β₁, γ₁, h₁⟩ := Rank.tpow (IsRestriction.refl (unit r : Tensor K _ _ _)) m
  have h₂ : restrict (piKronecker fun _ : Fin m => α) (piKronecker fun _ => β)
      (piKronecker fun _ => γ)
        (restrict (α₁.map C) (β₁.map C) (γ₁.map C) ((unit (r ^ m)).map C)) =
      Tensor.tprodPi fun _ => restrict α β γ ((unit r).map C) := by
    rw [← map_restrict, h₁, Tensor.tpow, tprodPi_map, ← restrict_tprodPi]
  refine IsDegen.rank_of_natDegree_le (h := m * h) (D := D * m)
    (α₁.map C * piKronecker fun _ => α) (β₁.map C * piKronecker fun _ => β)
    ((piKronecker fun _ => γ) * γ₁.map C) R ?_ ?_
  · rw [← restrict_restrict, h₂, hw]
    exact hR
  · intro x y z
    rw [← restrict_restrict, h₂, tprodPi_apply]
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ D fun i _ => hD _ _ _).trans ?_
    exact le_of_eq (by rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm])

end Bini

end Cslib.Tensor
