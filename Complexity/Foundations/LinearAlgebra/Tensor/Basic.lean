/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, bilinear complexity: finite tensors, restrictions and rank)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite tensors, restrictions and rank

A tensor of order three over a commutative semiring `R` with finite index types `X`, `Y`, `Z` is
given by its structure constants `T : X → Y → Z → R` (`Cslib.Tensor`). It is the bilinear map
`Tensor.bil T A B = fun z => ∑ x, ∑ y, T x y z * A x * B y`, with `A` and `B` the coefficient lists
of the two inputs. This is the model of bilinear computation of
[Bürgisser, Clausen and Shokrollahi][BurgisserClausenShokrollahi1997], Chapter 14, and the
selected products of [Pass][Pass2026], Definition 2.1, in which the monomials of a shape are
replaced by their index sets.

A *restriction* of `S` by the matrices `α`, `β`, `γ` (`Tensor.restrict`) computes `T` from `S`
by linear encoding of the two inputs and linear decoding of the output
(`Tensor.bil_restrict`): `T.bil A B = γ *ᵥ S.bil (α *ᵥ A) (β *ᵥ B)`. This is a polynomial
packing of one target by one source in the sense of [Pass][Pass2026], Definition 2.2. The
*rank* of `T` is at most `r` (`Tensor.Rank`) when `T` is a restriction of the unit tensor
`unit r`, the `r` independent scalar multiplications: a bilinear algorithm with `r`
multiplications.

Restrictions compose (`Tensor.restrict_restrict`), and they are compatible with the tensor
product `Tensor.tprod` and its finite form `Tensor.tprodPi`, with the direct sum `Tensor.dsum` and
the shared-left sum `Tensor.slSum`, with the three leg exchanges `Tensor.swap12`,
`Tensor.swap23`, `Tensor.swap13`, and with reindexing by equivalences `Tensor.reindex`. These are
the elementary operations on packings of [Pass][Pass2026], Observation 2.5 and Lemmas 2.7–2.10,
in which renaming the variables of a shape is reindexing.

Matrix multiplication of `p × q` by `q × r` matrices is the tensor `Tensor.mm p q r`.

## Main definitions

* `Cslib.Tensor`, `Cslib.Tensor.bil`: tensors and their bilinear maps.
* `Cslib.Tensor.restrict`, `Cslib.Tensor.IsRestriction`: restriction by three matrices.
* `Cslib.Tensor.unit`, `Cslib.Tensor.Rank`: the unit tensor and rank bounds.
* `Cslib.Tensor.mm`: the matrix multiplication tensor.
* `Cslib.Tensor.tprod`, `Cslib.Tensor.tprodPi`, `Cslib.Tensor.tpow`: tensor products.
* `Cslib.Tensor.dsum`, `Cslib.Tensor.slSum`: direct sums and shared-left sums of a family.
* `Cslib.Tensor.swap12`, `Cslib.Tensor.swap23`, `Cslib.Tensor.swap13`, `Cslib.Tensor.reindex`.

## Main results

* `Cslib.Tensor.bil_restrict`: a restriction computes its target by encoding and decoding.
* `Cslib.Tensor.restrict_restrict`, `Cslib.Tensor.IsRestriction.trans`: composition.
* `Cslib.Tensor.IsRestriction.tprod`, `Cslib.Tensor.IsRestriction.tprodPi`,
  `Cslib.Tensor.IsRestriction.dsum`, `Cslib.Tensor.IsRestriction.swap12`,
  `Cslib.Tensor.IsRestriction.swap23`, `Cslib.Tensor.IsRestriction.swap13`,
  `Cslib.Tensor.isRestriction_reindex`: closure of restriction.
* `Cslib.Tensor.isRestriction_dsum_comp`, `Cslib.Tensor.isRestriction_slSum_comp`: deleting and
  reordering summands.
* `Cslib.Tensor.Rank.tprod`, `Cslib.Tensor.Rank.dsum`, `Cslib.Tensor.rank_mm`: rank bounds.

## References

* [P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity
  Theory*][BurgisserClausenShokrollahi1997], Chapter 14
* [R. Pass, *Matrix Multiplication from Polynomial Packings*][Pass2026], §2
-/

@[expose] public section

namespace Cslib

/-- A tensor of order three over `R` with index types `X`, `Y` and `Z`, by its structure
constants. -/
abbrev Tensor (R X Y Z : Type*) := X → Y → Z → R

namespace Tensor

open Matrix Finset

variable {R R' : Type*} {X Y Z X' Y' Z' X'' Y'' Z'' : Type*}

/-! ### Structural operations -/

section Structural

/-- The entries of a tensor, mapped by `f`. -/
def map (f : R → R') (T : Tensor R X Y Z) : Tensor R' X Y Z :=
  fun x y z => f (T x y z)

@[simp] theorem map_apply (f : R → R') (T : Tensor R X Y Z) (x : X) (y : Y) (z : Z) :
    map f T x y z = f (T x y z) :=
  rfl

/-- Exchange the two input legs. -/
def swap12 (T : Tensor R X Y Z) : Tensor R Y X Z := fun y x z => T x y z

/-- Exchange the right input leg and the output leg. -/
def swap23 (T : Tensor R X Y Z) : Tensor R X Z Y := fun x z y => T x y z

/-- Exchange the left input leg and the output leg. -/
def swap13 (T : Tensor R X Y Z) : Tensor R Z Y X := fun z y x => T x y z

@[simp] theorem swap12_apply (T : Tensor R X Y Z) (y : Y) (x : X) (z : Z) :
    swap12 T y x z = T x y z := rfl

@[simp] theorem swap23_apply (T : Tensor R X Y Z) (x : X) (z : Z) (y : Y) :
    swap23 T x z y = T x y z := rfl

@[simp] theorem swap13_apply (T : Tensor R X Y Z) (z : Z) (y : Y) (x : X) :
    swap13 T z y x = T x y z := rfl

@[simp] theorem swap12_swap12 (T : Tensor R X Y Z) : swap12 (swap12 T) = T := rfl

@[simp] theorem swap23_swap23 (T : Tensor R X Y Z) : swap23 (swap23 T) = T := rfl

@[simp] theorem swap13_swap13 (T : Tensor R X Y Z) : swap13 (swap13 T) = T := rfl

/-- Reindex a tensor along equivalences of its index types. -/
def reindex (e₁ : X ≃ X') (e₂ : Y ≃ Y') (e₃ : Z ≃ Z') (T : Tensor R X Y Z) : Tensor R X' Y' Z' :=
  fun x' y' z' => T (e₁.symm x') (e₂.symm y') (e₃.symm z')

@[simp] theorem reindex_apply (e₁ : X ≃ X') (e₂ : Y ≃ Y') (e₃ : Z ≃ Z') (T : Tensor R X Y Z)
    (x' : X') (y' : Y') (z' : Z') :
    reindex e₁ e₂ e₃ T x' y' z' = T (e₁.symm x') (e₂.symm y') (e₃.symm z') :=
  rfl

@[simp] theorem reindex_refl (T : Tensor R X Y Z) :
    reindex (Equiv.refl X) (Equiv.refl Y) (Equiv.refl Z) T = T :=
  rfl

theorem reindex_reindex (e₁ : X ≃ X') (e₂ : Y ≃ Y') (e₃ : Z ≃ Z') (f₁ : X' ≃ X'') (f₂ : Y' ≃ Y'')
    (f₃ : Z' ≃ Z'') (T : Tensor R X Y Z) :
    reindex f₁ f₂ f₃ (reindex e₁ e₂ e₃ T) = reindex (e₁.trans f₁) (e₂.trans f₂) (e₃.trans f₃) T :=
  rfl

@[simp] theorem reindex_symm_reindex (e₁ : X ≃ X') (e₂ : Y ≃ Y') (e₃ : Z ≃ Z')
    (T : Tensor R X Y Z) : reindex e₁.symm e₂.symm e₃.symm (reindex e₁ e₂ e₃ T) = T := by
  ext x y z
  simp

/-- The tensor product of two tensors, on product index types. -/
def tprod [Mul R] (T : Tensor R X Y Z) (T' : Tensor R X' Y' Z') :
    Tensor R (X × X') (Y × Y') (Z × Z') :=
  fun x y z => T x.1 y.1 z.1 * T' x.2 y.2 z.2

@[simp] theorem tprod_apply [Mul R] (T : Tensor R X Y Z) (T' : Tensor R X' Y' Z') (x : X × X')
    (y : Y × Y') (z : Z × Z') : tprod T T' x y z = T x.1 y.1 z.1 * T' x.2 y.2 z.2 :=
  rfl

/-- The tensor product of a finite family of tensors on common index types, on function
index types. -/
def tprodPi [CommMonoid R] {ι : Type*} [Fintype ι] (T : ι → Tensor R X Y Z) :
    Tensor R (ι → X) (ι → Y) (ι → Z) :=
  fun x y z => ∏ i, T i (x i) (y i) (z i)

@[simp] theorem tprodPi_apply [CommMonoid R] {ι : Type*} [Fintype ι] (T : ι → Tensor R X Y Z)
    (x : ι → X) (y : ι → Y) (z : ι → Z) : tprodPi T x y z = ∏ i, T i (x i) (y i) (z i) :=
  rfl

/-- The `d`-th tensor power. -/
def tpow [CommMonoid R] (d : ℕ) (T : Tensor R X Y Z) :
    Tensor R (Fin d → X) (Fin d → Y) (Fin d → Z) :=
  tprodPi fun _ => T

@[simp] theorem tpow_apply [CommMonoid R] (d : ℕ) (T : Tensor R X Y Z) (x : Fin d → X)
    (y : Fin d → Y) (z : Fin d → Z) : tpow d T x y z = ∏ i, T (x i) (y i) (z i) :=
  rfl

/-- The direct sum of a family of tensors: block diagonal on all three legs. -/
def dsum [Zero R] {ι : Type*} [DecidableEq ι] (G : ι → Tensor R X Y Z) :
    Tensor R (ι × X) (ι × Y) (ι × Z) :=
  fun x y z => if x.1 = y.1 ∧ y.1 = z.1 then G x.1 x.2 y.2 z.2 else 0

/-- The shared-left sum of a family of tensors with a common left leg: block diagonal on the
right input and output legs, the same left input for every summand. -/
def slSum [Zero R] {ι : Type*} [DecidableEq ι] (G : ι → Tensor R X Y Z) :
    Tensor R X (ι × Y) (ι × Z) :=
  fun x y z => if y.1 = z.1 then G y.1 x y.2 z.2 else 0

@[simp] theorem dsum_apply [Zero R] {ι : Type*} [DecidableEq ι] (G : ι → Tensor R X Y Z)
    (x : ι × X) (y : ι × Y) (z : ι × Z) :
    dsum G x y z = if x.1 = y.1 ∧ y.1 = z.1 then G x.1 x.2 y.2 z.2 else 0 :=
  rfl

@[simp] theorem slSum_apply [Zero R] {ι : Type*} [DecidableEq ι] (G : ι → Tensor R X Y Z) (x : X)
    (y : ι × Y) (z : ι × Z) : slSum G x y z = if y.1 = z.1 then G y.1 x y.2 z.2 else 0 :=
  rfl

/-- Exchanging the right input and output legs of a shared-left sum exchanges them in every
summand. -/
theorem swap23_slSum [Zero R] {ι : Type*} [DecidableEq ι] (G : ι → Tensor R X Y Z) :
    swap23 (slSum G) = slSum fun i => swap23 (G i) := by
  ext x z y
  obtain ⟨i, z⟩ := z
  obtain ⟨j, y⟩ := y
  by_cases h : j = i
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- The unit tensor `⟨n⟩`: `n` independent scalar multiplications. -/
def unit [Zero R] [One R] (n : ℕ) : Tensor R (Fin n) (Fin n) (Fin n) :=
  fun i j k => if i = j ∧ j = k then 1 else 0

@[simp] theorem unit_apply [Zero R] [One R] (n : ℕ) (i j k : Fin n) :
    unit n i j k = (if i = j ∧ j = k then 1 else 0 : R) :=
  rfl

/-- The matrix multiplication tensor `⟨p, q, r⟩`: multiply a `p × q` matrix by a `q × r`
matrix. The left input is indexed by `(i, j)`, the right by `(j, k)`, the output by `(i, k)`. -/
def mm [Zero R] [One R] (p q r : ℕ) :
    Tensor R (Fin p × Fin q) (Fin q × Fin r) (Fin p × Fin r) :=
  fun a b c => if a.1 = c.1 ∧ a.2 = b.1 ∧ b.2 = c.2 then 1 else 0

@[simp] theorem mm_apply [Zero R] [One R] (p q r : ℕ) (a : Fin p × Fin q) (b : Fin q × Fin r)
    (c : Fin p × Fin r) :
    mm p q r a b c = (if a.1 = c.1 ∧ a.2 = b.1 ∧ b.2 = c.2 then 1 else 0 : R) :=
  rfl

/-- `n` independent copies of `T` are its tensor product with `unit n`. -/
theorem dsum_const [MulZeroOneClass R] (n : ℕ) (T : Tensor R X Y Z) :
    dsum (fun _ : Fin n => T) = tprod (unit n) T := by
  ext x y z
  simp only [dsum_apply, tprod_apply, unit_apply]
  split_ifs <;> simp

end Structural

/-! ### Bilinear maps and restrictions -/

section Semiring

variable [CommSemiring R]

/-- The bilinear map of a tensor on coefficient lists. -/
def bil [Fintype X] [Fintype Y] (T : Tensor R X Y Z) (A : X → R) (B : Y → R) : Z → R :=
  fun z => ∑ x, ∑ y, T x y z * A x * B y

/-- **Restriction** of `S` along the encoders `α`, `β` and the decoder `γ`:
`T x y z = ∑ α x' x * β y' y * γ z z' * S x' y' z'`. -/
def restrict [Fintype X'] [Fintype Y'] [Fintype Z'] (α : Matrix X' X R) (β : Matrix Y' Y R)
    (γ : Matrix Z Z' R) (S : Tensor R X' Y' Z') : Tensor R X Y Z :=
  fun x y z => ∑ x', ∑ y', ∑ z', α x' x * β y' y * γ z z' * S x' y' z'

/-- `T` is a restriction of `S`: a bilinear algorithm computes `T` from one evaluation of `S`. -/
def IsRestriction [Fintype X'] [Fintype Y'] [Fintype Z'] (T : Tensor R X Y Z)
    (S : Tensor R X' Y' Z') : Prop :=
  ∃ (α : Matrix X' X R) (β : Matrix Y' Y R) (γ : Matrix Z Z' R), restrict α β γ S = T

/-- The inclusion matrix of a map `f : X → X'`: the column `x` is the unit vector at `f x`. -/
def incl [DecidableEq X'] (f : X → X') : Matrix X' X R :=
  Matrix.of fun x' x => if f x = x' then 1 else 0

@[simp] theorem incl_apply [DecidableEq X'] (f : X → X') (x' : X') (x : X) :
    (incl f : Matrix X' X R) x' x = if f x = x' then 1 else 0 :=
  rfl

/-- The inclusion of the identity is the identity matrix. -/
theorem incl_id [DecidableEq X] : (incl id : Matrix X X R) = 1 := by
  ext x' x
  simp [Matrix.one_apply, eq_comm]

/-- Restriction computes the bilinear map of `T` from the bilinear map of `S`: encode the inputs
by `α` and `β`, evaluate `S`, decode by `γ`. -/
theorem bil_restrict [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y'] [Fintype Z']
    (α : Matrix X' X R) (β : Matrix Y' Y R) (γ : Matrix Z Z' R) (S : Tensor R X' Y' Z')
    (A : X → R) (B : Y → R) :
    (restrict α β γ S).bil A B = γ *ᵥ S.bil (α *ᵥ A) (β *ᵥ B) := by
  funext z
  simp only [bil, restrict, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.sum_comm (γ := Y') (α := Z'), Finset.sum_comm (γ := X') (α := Z'),
    Finset.sum_comm (γ := Y) (α := Z'), Finset.sum_comm (γ := X) (α := Z'),
    Finset.sum_comm (γ := Y) (α := X'), Finset.sum_comm (γ := X) (α := X'),
    Finset.sum_comm (γ := Y) (α := Y'), Finset.sum_comm (γ := X) (α := Y'),
    Finset.sum_comm (γ := Y) (α := X)]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- Two tensors with the same bilinear map are equal. -/
theorem ext_of_bil [Fintype X] [Fintype Y] {T T' : Tensor R X Y Z}
    (h : ∀ A B, T.bil A B = T'.bil A B) : T = T' := by
  classical
  funext x y z
  have := congrFun (h (Pi.single x 1) (Pi.single y 1)) z
  simpa [bil, Pi.single_apply, mul_ite] using this

/-- Restriction is linear in the source tensor. -/
theorem restrict_add [Fintype X'] [Fintype Y'] [Fintype Z'] (α : Matrix X' X R) (β : Matrix Y' Y R)
    (γ : Matrix Z Z' R) (S S' : Tensor R X' Y' Z') :
    restrict α β γ (S + S') = restrict α β γ S + restrict α β γ S' := by
  funext x y z
  simp only [restrict, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Restriction is linear in the source tensor. -/
theorem restrict_smul [Fintype X'] [Fintype Y'] [Fintype Z'] (α : Matrix X' X R) (β : Matrix Y' Y R)
    (γ : Matrix Z Z' R) (c : R) (S : Tensor R X' Y' Z') :
    restrict α β γ (c • S) = c • restrict α β γ S := by
  funext x y z
  simp only [restrict, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- Restriction by identity matrices is the identity. -/
theorem restrict_one [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] (S : Tensor R X Y Z) : restrict 1 1 1 S = S := by
  funext x y z
  simp [restrict, Matrix.one_apply, ite_mul, mul_ite]

/-- **Composition of restrictions**: the matrices multiply. -/
theorem restrict_restrict [Fintype X'] [Fintype Y'] [Fintype Z'] [Fintype X''] [Fintype Y'']
    [Fintype Z''] (α : Matrix X' X R) (β : Matrix Y' Y R) (γ : Matrix Z Z' R)
    (α' : Matrix X'' X' R) (β' : Matrix Y'' Y' R) (γ' : Matrix Z' Z'' R)
    (U : Tensor R X'' Y'' Z'') :
    restrict α β γ (restrict α' β' γ' U) = restrict (α' * α) (β' * β) (γ * γ') U := by
  funext x y z
  simp only [restrict, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.sum_comm (γ := X') (α := X''), Finset.sum_comm (γ := X') (α := Y''),
    Finset.sum_comm (γ := X') (α := Z''), Finset.sum_comm (γ := Y') (α := X''),
    Finset.sum_comm (γ := Y') (α := Y''), Finset.sum_comm (γ := Y') (α := Z''),
    Finset.sum_comm (γ := Z') (α := X''), Finset.sum_comm (γ := Z') (α := Y''),
    Finset.sum_comm (γ := Z') (α := Z''), Finset.sum_comm (γ := Z') (α := Y'),
    Finset.sum_comm (γ := Z') (α := X'), Finset.sum_comm (γ := Y') (α := X')]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- A tensor is a restriction of itself. -/
theorem IsRestriction.refl [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor R X Y Z) :
    IsRestriction T T := by
  classical
  exact ⟨1, 1, 1, restrict_one T⟩

/-- Restrictions compose. -/
theorem IsRestriction.trans [Fintype X'] [Fintype Y'] [Fintype Z'] [Fintype X''] [Fintype Y'']
    [Fintype Z''] {T : Tensor R X Y Z} {S : Tensor R X' Y' Z'} {U : Tensor R X'' Y'' Z''}
    (hT : IsRestriction T S) (hS : IsRestriction S U) : IsRestriction T U := by
  obtain ⟨α, β, γ, rfl⟩ := hT
  obtain ⟨α', β', γ', rfl⟩ := hS
  exact ⟨_, _, _, (restrict_restrict α β γ α' β' γ' U).symm⟩

/-! ### Leg exchanges and reindexing of restrictions -/

/-- Exchanging the inputs of a restriction exchanges the encoders. -/
theorem swap12_restrict [Fintype X'] [Fintype Y'] [Fintype Z'] (α : Matrix X' X R)
    (β : Matrix Y' Y R) (γ : Matrix Z Z' R) (S : Tensor R X' Y' Z') :
    swap12 (restrict α β γ S) = restrict β α γ (swap12 S) := by
  funext y x z
  simp only [swap12_apply, restrict]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- Exchanging the right input and the output of a restriction transposes the right encoder and
the decoder and exchanges them (the transposition principle). -/
theorem swap23_restrict [Fintype X'] [Fintype Y'] [Fintype Z'] (α : Matrix X' X R)
    (β : Matrix Y' Y R) (γ : Matrix Z Z' R) (S : Tensor R X' Y' Z') :
    swap23 (restrict α β γ S) = restrict α γᵀ βᵀ (swap23 S) := by
  funext x z y
  simp only [swap23_apply, restrict, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- Exchanging the left input and the output of a restriction transposes the left encoder and
the decoder and exchanges them. -/
theorem swap13_restrict [Fintype X'] [Fintype Y'] [Fintype Z'] (α : Matrix X' X R)
    (β : Matrix Y' Y R) (γ : Matrix Z Z' R) (S : Tensor R X' Y' Z') :
    swap13 (restrict α β γ S) = restrict γᵀ β αᵀ (swap13 S) := by
  funext z y x
  simp only [swap13_apply, restrict, Matrix.transpose_apply]
  simp only [Finset.sum_comm (γ := Y') (α := Z'), Finset.sum_comm (γ := X') (α := Z'),
    Finset.sum_comm (γ := X') (α := Y')]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem IsRestriction.swap12 [Fintype X'] [Fintype Y'] [Fintype Z'] {T : Tensor R X Y Z}
    {S : Tensor R X' Y' Z'} (h : IsRestriction T S) : IsRestriction (swap12 T) (swap12 S) := by
  obtain ⟨α, β, γ, rfl⟩ := h
  exact ⟨β, α, γ, (swap12_restrict α β γ S).symm⟩

theorem IsRestriction.swap23 [Fintype X'] [Fintype Y'] [Fintype Z'] {T : Tensor R X Y Z}
    {S : Tensor R X' Y' Z'} (h : IsRestriction T S) : IsRestriction (swap23 T) (swap23 S) := by
  obtain ⟨α, β, γ, rfl⟩ := h
  exact ⟨α, γᵀ, βᵀ, (swap23_restrict α β γ S).symm⟩

theorem IsRestriction.swap13 [Fintype X'] [Fintype Y'] [Fintype Z'] {T : Tensor R X Y Z}
    {S : Tensor R X' Y' Z'} (h : IsRestriction T S) : IsRestriction (swap13 T) (swap13 S) := by
  obtain ⟨α, β, γ, rfl⟩ := h
  exact ⟨γᵀ, β, αᵀ, (swap13_restrict α β γ S).symm⟩

/-- Restriction along inclusion matrices is precomposition with the maps. -/
theorem restrict_incl [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X']
    [DecidableEq Y'] [DecidableEq Z'] (f : X → X') (g : Y → Y') (h : Z → Z')
    (S : Tensor R X' Y' Z') :
    restrict (incl f) (incl g) (incl h)ᵀ S = fun x y z => S (f x) (g y) (h z) := by
  funext x y z
  simp [restrict, ite_mul, mul_ite]

/-- A reindexed tensor is a restriction of the original, by permutation matrices. -/
theorem isRestriction_reindex [Fintype X] [Fintype Y] [Fintype Z] (e₁ : X ≃ X') (e₂ : Y ≃ Y')
    (e₃ : Z ≃ Z') (T : Tensor R X Y Z) : IsRestriction (reindex e₁ e₂ e₃ T) T := by
  classical
  exact ⟨incl e₁.symm, incl e₂.symm, (incl e₃.symm)ᵀ, restrict_incl _ _ _ T⟩

/-- A tensor is a restriction of its reindexing. -/
theorem isRestriction_of_reindex [Fintype X'] [Fintype Y'] [Fintype Z'] (e₁ : X ≃ X')
    (e₂ : Y ≃ Y') (e₃ : Z ≃ Z') (T : Tensor R X Y Z) :
    IsRestriction T (reindex e₁ e₂ e₃ T) := by
  classical
  refine ⟨incl e₁, incl e₂, (incl e₃)ᵀ, ?_⟩
  rw [restrict_incl]
  funext x y z
  simp

/-- Restriction transfers along reindexings of the source. -/
theorem IsRestriction.reindex_source [Fintype X'] [Fintype Y'] [Fintype Z'] [Fintype X'']
    [Fintype Y''] [Fintype Z''] {T : Tensor R X Y Z} {S : Tensor R X' Y' Z'} (e₁ : X' ≃ X'')
    (e₂ : Y' ≃ Y'') (e₃ : Z' ≃ Z'') (h : IsRestriction T S) :
    IsRestriction T (reindex e₁ e₂ e₃ S) :=
  h.trans (isRestriction_of_reindex e₁ e₂ e₃ S)

/-- Reindexing a restriction reindexes the target-side indices of its matrices. -/
theorem reindex_restrict [Fintype X'] [Fintype Y'] [Fintype Z'] (α : Matrix X' X R)
    (β : Matrix Y' Y R) (γ : Matrix Z Z' R) (S : Tensor R X' Y' Z') (e₁ : X ≃ X'') (e₂ : Y ≃ Y'')
    (e₃ : Z ≃ Z'') :
    reindex e₁ e₂ e₃ (restrict α β γ S) =
      restrict (α.submatrix id e₁.symm) (β.submatrix id e₂.symm) (γ.submatrix e₃.symm id) S :=
  rfl

/-- Restriction transfers along reindexings of the target. -/
theorem IsRestriction.reindex_target [Fintype X'] [Fintype Y'] [Fintype Z'] {T : Tensor R X Y Z}
    {S : Tensor R X' Y' Z'} (e₁ : X ≃ X'') (e₂ : Y ≃ Y'') (e₃ : Z ≃ Z'') (h : IsRestriction T S) :
    IsRestriction (reindex e₁ e₂ e₃ T) S := by
  obtain ⟨α, β, γ, rfl⟩ := h
  exact ⟨_, _, _, (reindex_restrict α β γ S e₁ e₂ e₃).symm⟩

/-! ### Tensor products of restrictions -/

open scoped Kronecker in
/-- Restriction is compatible with tensor products: the matrices multiply as Kronecker
products. -/
theorem restrict_tprod [Fintype X'] [Fintype Y'] [Fintype Z'] [Fintype X''] [Fintype Y'']
    [Fintype Z''] (α : Matrix X' X R) (β : Matrix Y' Y R) (γ : Matrix Z Z' R)
    (S : Tensor R X' Y' Z') {X₂ Y₂ Z₂ : Type*} (α' : Matrix X'' X₂ R) (β' : Matrix Y'' Y₂ R)
    (γ' : Matrix Z₂ Z'' R) (S' : Tensor R X'' Y'' Z'') :
    tprod (restrict α β γ S) (restrict α' β' γ' S') =
      restrict (α ⊗ₖ α') (β ⊗ₖ β') (γ ⊗ₖ γ') (tprod S S') := by
  ext ⟨x, x₂⟩ ⟨y, y₂⟩ ⟨z, z₂⟩
  simp only [tprod_apply, restrict, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.sum_comm (γ := X'') (α := X'), Finset.sum_comm (γ := Y'') (α := X'),
    Finset.sum_comm (γ := Y'') (α := Y'), Finset.sum_comm (γ := Z'') (α := X'),
    Finset.sum_comm (γ := Z'') (α := Y'), Finset.sum_comm (γ := Z'') (α := Z')]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem IsRestriction.tprod [Fintype X'] [Fintype Y'] [Fintype Z'] [Fintype X''] [Fintype Y'']
    [Fintype Z''] {X₂ Y₂ Z₂ : Type*} {T : Tensor R X Y Z} {S : Tensor R X' Y' Z'}
    {T' : Tensor R X₂ Y₂ Z₂} {S' : Tensor R X'' Y'' Z''} (h : IsRestriction T S)
    (h' : IsRestriction T' S') : IsRestriction (tprod T T') (tprod S S') := by
  obtain ⟨α, β, γ, rfl⟩ := h
  obtain ⟨α', β', γ', rfl⟩ := h'
  exact ⟨_, _, _, (restrict_tprod α β γ S α' β' γ' S').symm⟩

/-- The Kronecker product of a family of matrices, on function index types. -/
def piKronecker {ι : Type*} [Fintype ι] (α : ι → Matrix X' X R) : Matrix (ι → X') (ι → X) R :=
  Matrix.of fun x' x => ∏ i, α i (x' i) (x i)

@[simp] theorem piKronecker_apply {ι : Type*} [Fintype ι] (α : ι → Matrix X' X R) (x' : ι → X')
    (x : ι → X) : piKronecker α x' x = ∏ i, α i (x' i) (x i) :=
  rfl

/-- Restriction is compatible with finite tensor products. -/
theorem restrict_tprodPi {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype X'] [Fintype Y']
    [Fintype Z'] (α : ι → Matrix X' X R) (β : ι → Matrix Y' Y R) (γ : ι → Matrix Z Z' R)
    (S : ι → Tensor R X' Y' Z') :
    tprodPi (fun i => restrict (α i) (β i) (γ i) (S i)) =
      restrict (piKronecker α) (piKronecker β) (piKronecker γ) (tprodPi S) := by
  funext x y z
  simp only [tprodPi_apply, restrict, piKronecker_apply, Finset.prod_univ_sum,
    Fintype.piFinset_univ, Finset.prod_mul_distrib]

theorem IsRestriction.tprodPi {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype X'] [Fintype Y']
    [Fintype Z'] {T : ι → Tensor R X Y Z} {S : ι → Tensor R X' Y' Z'}
    (h : ∀ i, IsRestriction (T i) (S i)) : IsRestriction (tprodPi T) (tprodPi S) := by
  choose α β γ hαβγ using h
  have hT : (fun i => restrict (α i) (β i) (γ i) (S i)) = T := funext hαβγ
  exact ⟨piKronecker α, piKronecker β, piKronecker γ, by rw [← restrict_tprodPi, hT]⟩

theorem IsRestriction.tpow [Fintype X'] [Fintype Y'] [Fintype Z'] {T : Tensor R X Y Z}
    {S : Tensor R X' Y' Z'} (h : IsRestriction T S) (d : ℕ) :
    IsRestriction (tpow d T) (tpow d S) :=
  IsRestriction.tprodPi fun _ => h

/-- The tensor product of two finite tensor products is a finite tensor product over the sum of
the index types. -/
theorem tprod_tprodPi {ι κ : Type*} [Fintype ι] [Fintype κ] (T : ι → Tensor R X Y Z)
    (T' : κ → Tensor R X Y Z) :
    tprod (tprodPi T) (tprodPi T') =
      reindex (Equiv.sumArrowEquivProdArrow ι κ X) (Equiv.sumArrowEquivProdArrow ι κ Y)
        (Equiv.sumArrowEquivProdArrow ι κ Z) (tprodPi (Sum.elim T T')) := by
  funext x y z
  simp [Fintype.prod_sum_type, Equiv.sumArrowEquivProdArrow]

/-- A finite tensor product reindexed along a bijection of the index set. -/
theorem tprodPi_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ ≃ ι)
    (T : ι → Tensor R X Y Z) :
    tprodPi (T ∘ e) =
      reindex (Equiv.arrowCongr e.symm (Equiv.refl X)) (Equiv.arrowCongr e.symm (Equiv.refl Y))
        (Equiv.arrowCongr e.symm (Equiv.refl Z)) (tprodPi T) := by
  funext x y z
  simp only [tprodPi_apply, reindex_apply, Function.comp_apply, Equiv.arrowCongr_symm,
    Equiv.symm_symm, Equiv.refl_symm]
  exact Fintype.prod_equiv e _ _ fun k => by simp [Equiv.arrowCongr]

/-! ### Direct sums and shared-left sums of restrictions -/

/-- The block diagonal matrix of a family of matrices. -/
def blockDiag {ι : Type*} [DecidableEq ι] (M : ι → Matrix X' X R) :
    Matrix (ι × X') (ι × X) R :=
  Matrix.of fun x' x => if x'.1 = x.1 then M x.1 x'.2 x.2 else 0

@[simp] theorem blockDiag_apply {ι : Type*} [DecidableEq ι] (M : ι → Matrix X' X R)
    (x' : ι × X') (x : ι × X) : blockDiag M x' x = if x'.1 = x.1 then M x.1 x'.2 x.2 else 0 :=
  rfl

/-- Restriction is compatible with direct sums, by block diagonal matrices. -/
theorem restrict_dsum {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype X'] [Fintype Y']
    [Fintype Z'] (α : ι → Matrix X' X R) (β : ι → Matrix Y' Y R) (γ : ι → Matrix Z Z' R)
    (S : ι → Tensor R X' Y' Z') :
    dsum (fun i => restrict (α i) (β i) (γ i) (S i)) =
      restrict (blockDiag α) (blockDiag β) (blockDiag γ) (dsum S) := by
  ext ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
  simp only [dsum_apply, restrict, blockDiag_apply, Fintype.sum_prod_type]
  simp only [Finset.sum_comm (γ := X') (α := ι), Finset.sum_comm (γ := Y') (α := ι)]
  rw [Fintype.sum_eq_single i, Fintype.sum_eq_single j, Fintype.sum_eq_single k]
  · by_cases h : i = j ∧ j = k
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · simp [h]
  · intro k' hk'
    simp [Ne.symm hk']
  · intro j' hj'
    simp [hj']
  · intro i' hi'
    simp [hi']

theorem IsRestriction.dsum {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype X'] [Fintype Y']
    [Fintype Z'] {T : ι → Tensor R X Y Z} {S : ι → Tensor R X' Y' Z'}
    (h : ∀ i, IsRestriction (T i) (S i)) : IsRestriction (dsum T) (dsum S) := by
  choose α β γ hαβγ using h
  have hT : (fun i => restrict (α i) (β i) (γ i) (S i)) = T := funext hαβγ
  exact ⟨blockDiag α, blockDiag β, blockDiag γ, by rw [← restrict_dsum, hT]⟩

/-- Restriction is compatible with shared-left sums: the left encoder is common, the right
encoders and decoders are block diagonal. -/
theorem restrict_slSum {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype X'] [Fintype Y']
    [Fintype Z'] (α : Matrix X' X R) (β : ι → Matrix Y' Y R) (γ : ι → Matrix Z Z' R)
    (S : ι → Tensor R X' Y' Z') :
    slSum (fun i => restrict α (β i) (γ i) (S i)) =
      restrict α (blockDiag β) (blockDiag γ) (slSum S) := by
  ext x ⟨j, y⟩ ⟨k, z⟩
  simp only [slSum_apply, restrict, blockDiag_apply, Fintype.sum_prod_type]
  simp only [Finset.sum_comm (γ := X') (α := ι), Finset.sum_comm (γ := Y') (α := ι)]
  rw [Fintype.sum_eq_single j, Fintype.sum_eq_single k]
  · by_cases h : j = k
    · subst h
      simp
    · simp [h]
  · intro k' hk'
    simp [Ne.symm hk']
  · intro j' hj'
    simp [hj']

/-- Deleting and reordering summands of a direct sum is a restriction, along an injection of the
index sets. -/
theorem isRestriction_dsum_comp {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    [Fintype X] [Fintype Y] [Fintype Z] (G : ι → Tensor R X Y Z) (e : κ → ι)
    (he : Function.Injective e) : IsRestriction (dsum (G ∘ e)) (dsum G) := by
  classical
  refine ⟨incl (Prod.map e id), incl (Prod.map e id), (incl (Prod.map e id))ᵀ, ?_⟩
  rw [restrict_incl]
  ext ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩
  simp [he.eq_iff]

/-- Deleting and reordering summands of a shared-left sum is a restriction with the identity on
the left leg. -/
theorem slSum_comp_eq_restrict {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (G : ι → Tensor R X Y Z) (e : κ → ι) (he : Function.Injective e) :
    restrict 1 (incl (Prod.map e id)) (incl (Prod.map e id))ᵀ (slSum G) = slSum (G ∘ e) := by
  rw [← incl_id, restrict_incl]
  ext x ⟨b, y⟩ ⟨c, z⟩
  simp [he.eq_iff]

theorem isRestriction_slSum_comp {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    [Fintype X] [Fintype Y] [Fintype Z] (G : ι → Tensor R X Y Z) (e : κ → ι)
    (he : Function.Injective e) : IsRestriction (slSum (G ∘ e)) (slSum G) := by
  classical
  exact ⟨_, _, _, slSum_comp_eq_restrict G e he⟩

/-- The tensor product of two shared-left sums is a shared-left sum over pairs of summands. -/
theorem tprod_slSum {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (G : ι → Tensor R X Y Z)
    (G' : κ → Tensor R X' Y' Z') :
    tprod (slSum G) (slSum G') =
      reindex (Equiv.refl _) (Equiv.prodProdProdComm ι κ Y Y') (Equiv.prodProdProdComm ι κ Z Z')
        (slSum fun p : ι × κ => tprod (G p.1) (G' p.2)) := by
  ext ⟨x, x'⟩ ⟨⟨i, y⟩, ⟨j, y'⟩⟩ ⟨⟨k, z⟩, ⟨l, z'⟩⟩
  by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl]

/-- A tensor power of a shared-left sum is the shared-left sum, over words, of the finite tensor
products of the summands along the word. -/
theorem tpow_slSum {ι : Type*} [DecidableEq ι] (d : ℕ) (G : ι → Tensor R X Y Z) :
    tpow d (slSum G) =
      reindex (Equiv.refl _)
        (Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => ι) (fun _ => Y)).symm
        (Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => ι) (fun _ => Z)).symm
        (slSum fun w : Fin d → ι => tprodPi fun i => G (w i)) := by
  funext x y z
  simp only [tpow_apply, slSum_apply, reindex_apply, Equiv.refl_symm, Equiv.coe_refl, id_eq,
    Equiv.symm_symm, Equiv.arrowProdEquivProdArrow_apply, tprodPi_apply, Fintype.prod_ite_zero,
    funext_iff]
  split_ifs <;> rfl

/-! ### Rank -/

/-- `T` has rank at most `r`: it is a restriction of `unit r`, so a bilinear algorithm with `r`
scalar multiplications computes it. -/
def Rank (r : ℕ) (T : Tensor R X Y Z) : Prop :=
  IsRestriction T (unit r)

/-- A restriction of the unit tensor is a sum of `r` rank-one tensors. -/
private theorem restrict_unit {n : ℕ} (α : Matrix (Fin n) X R) (β : Matrix (Fin n) Y R)
    (γ : Matrix Z (Fin n) R) (x : X) (y : Y) (z : Z) :
    restrict α β γ (unit n) x y z = ∑ k, α k x * β k y * γ z k := by
  simp [restrict, ite_and, mul_ite]

private theorem swap12_unit (r : ℕ) : swap12 (unit r : Tensor R _ _ _) = unit r := by
  funext i j k
  simp only [swap12_apply, unit_apply]
  grind

private theorem swap23_unit (r : ℕ) : swap23 (unit r : Tensor R _ _ _) = unit r := by
  funext i j k
  simp only [swap23_apply, unit_apply]
  grind

private theorem swap13_unit (r : ℕ) : swap13 (unit r : Tensor R _ _ _) = unit r := by
  funext i j k
  simp only [swap13_apply, unit_apply]
  grind

/-- The tensor product of two unit tensors is a unit tensor. -/
theorem tprod_unit_unit (m n : ℕ) :
    tprod (unit m) (unit n) =
      reindex finProdFinEquiv.symm finProdFinEquiv.symm finProdFinEquiv.symm
        (unit (m * n) : Tensor R _ _ _) := by
  ext ⟨a, a'⟩ ⟨b, b'⟩ ⟨c, c'⟩
  simp only [tprod_apply, unit_apply, reindex_apply, Equiv.symm_symm, Equiv.apply_eq_iff_eq,
    Prod.mk.injEq, ite_zero_mul_ite_zero, mul_one]
  grind

/-- The direct sum of `n` unit tensors `unit m` is `unit (n * m)`. -/
theorem dsum_unit (n m : ℕ) :
    dsum (fun _ : Fin n => (unit m : Tensor R _ _ _)) =
      reindex finProdFinEquiv.symm finProdFinEquiv.symm finProdFinEquiv.symm (unit (n * m)) := by
  rw [dsum_const, tprod_unit_unit]

theorem Rank.of_isRestriction [Fintype X'] [Fintype Y'] [Fintype Z'] {T : Tensor R X Y Z}
    {S : Tensor R X' Y' Z'} {r : ℕ} (h : IsRestriction T S) (hS : Rank r S) : Rank r T :=
  h.trans hS

/-- `unit r` is a restriction of `unit r'` for `r ≤ r'`. -/
theorem isRestriction_unit_of_le {r r' : ℕ} (h : r ≤ r') :
    IsRestriction (unit r : Tensor R _ _ _) (unit r') := by
  refine ⟨incl (Fin.castLE h), incl (Fin.castLE h), (incl (Fin.castLE h))ᵀ, ?_⟩
  rw [restrict_incl]
  funext i j k
  simp [Fin.ext_iff]

theorem Rank.mono {T : Tensor R X Y Z} {r r' : ℕ} (h : Rank r T) (hr : r ≤ r') : Rank r' T :=
  h.trans (isRestriction_unit_of_le hr)

theorem Rank.tprod {X₂ Y₂ Z₂ : Type*} {T : Tensor R X Y Z} {T' : Tensor R X₂ Y₂ Z₂} {r r' : ℕ}
    (h : Rank r T) (h' : Rank r' T') : Rank (r * r') (tprod T T') := by
  refine (IsRestriction.tprod h h').trans ?_
  rw [tprod_unit_unit]
  exact isRestriction_reindex _ _ _ _

theorem Rank.dsum {T : Tensor R X Y Z} {r : ℕ} (n : ℕ) (h : Rank r T) :
    Rank (n * r) (dsum fun _ : Fin n => T) := by
  rw [dsum_const]
  exact Rank.tprod (IsRestriction.refl _) h

theorem Rank.swap12 {T : Tensor R X Y Z} {r : ℕ} (h : Rank r T) : Rank r (swap12 T) := by
  have := IsRestriction.swap12 h
  rwa [swap12_unit] at this

theorem Rank.swap23 {T : Tensor R X Y Z} {r : ℕ} (h : Rank r T) : Rank r (swap23 T) := by
  have := IsRestriction.swap23 h
  rwa [swap23_unit] at this

theorem Rank.swap13 {T : Tensor R X Y Z} {r : ℕ} (h : Rank r T) : Rank r (swap13 T) := by
  have := IsRestriction.swap13 h
  rwa [swap13_unit] at this

theorem Rank.reindex {T : Tensor R X Y Z} {r : ℕ} (h : Rank r T) (e₁ : X ≃ X') (e₂ : Y ≃ Y')
    (e₃ : Z ≃ Z') : Rank r (reindex e₁ e₂ e₃ T) :=
  h.reindex_target e₁ e₂ e₃

theorem Rank.tprodPi {ι : Type*} [Fintype ι] {T : ι → Tensor R X Y Z} {r : ι → ℕ}
    (h : ∀ i, Rank (r i) (T i)) : Rank (∏ i, r i) (tprodPi T) := by
  classical
  choose α β γ hαβγ using h
  have e : ((i : ι) → Fin (r i)) ≃ Fin (∏ i, r i) := Fintype.equivFinOfCardEq (by simp)
  refine ⟨Matrix.of fun k x => ∏ i, α i (e.symm k i) (x i),
    Matrix.of fun k y => ∏ i, β i (e.symm k i) (y i),
    Matrix.of fun z k => ∏ i, γ i (z i) (e.symm k i), ?_⟩
  funext x y z
  simp only [tprodPi_apply, ← hαβγ, restrict_unit, Matrix.of_apply, Finset.prod_univ_sum,
    Fintype.piFinset_univ, Finset.prod_mul_distrib]
  exact Fintype.sum_equiv e.symm _ _ fun _ => rfl

theorem Rank.tpow {T : Tensor R X Y Z} {r : ℕ} (h : Rank r T) (d : ℕ) :
    Rank (r ^ d) (tpow d T) := by
  have := Rank.tprodPi (r := fun _ : Fin d => r) fun _ => h
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  exact this

/-! ### Matrix multiplication -/

/-- The bilinear map of `mm p q r` is matrix multiplication. -/
theorem bil_mm (p q r : ℕ) (A : Fin p × Fin q → R) (B : Fin q × Fin r → R) (c : Fin p × Fin r) :
    (mm p q r).bil A B c = ∑ j, A (c.1, j) * B (j, c.2) := by
  simp [bil, Fintype.sum_prod_type, ite_and, ite_mul]

/-- The trivial algorithm: `p q r` scalar multiplications. -/
theorem rank_mm (p q r : ℕ) : Rank (p * q * r) (mm p q r : Tensor R _ _ _) := by
  have e : (Fin p × Fin q) × Fin r ≃ Fin (p * q * r) :=
    (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv
  refine ⟨Matrix.of fun t a => if (e.symm t).1 = a then 1 else 0,
    Matrix.of fun t b => if ((e.symm t).1.2, (e.symm t).2) = b then 1 else 0,
    Matrix.of fun c t => if ((e.symm t).1.1, (e.symm t).2) = c then 1 else 0, ?_⟩
  ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
  rw [restrict_unit]
  refine (Fintype.sum_equiv e.symm _ (fun w : (Fin p × Fin q) × Fin r =>
    (if w.1 = (a₁, a₂) then 1 else 0) * (if (w.1.2, w.2) = (b₁, b₂) then 1 else 0) *
      (if (w.1.1, w.2) = (c₁, c₂) then 1 else 0)) fun _ => rfl).trans ?_
  simp only [Fintype.sum_prod_type, mm_apply, Prod.mk.injEq, ite_and, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  grind

/-- Matrix multiplication tensors multiply as block matrix multiplication. -/
theorem tprod_mm_mm (p q r p' q' r' : ℕ) :
    tprod (mm p q r) (mm p' q' r') =
      reindex ((Equiv.prodProdProdComm _ _ _ _).trans
          (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)).symm
        ((Equiv.prodProdProdComm _ _ _ _).trans
          (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)).symm
        ((Equiv.prodProdProdComm _ _ _ _).trans
          (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)).symm
        (mm (p * p') (q * q') (r * r') : Tensor R _ _ _) := by
  ext ⟨⟨i, j⟩, ⟨i', j'⟩⟩ ⟨⟨j₁, k⟩, ⟨j₁', k'⟩⟩ ⟨⟨i₁, k₁⟩, ⟨i₁', k₁'⟩⟩
  simp only [tprod_apply, mm_apply, reindex_apply, Equiv.symm_symm, Equiv.trans_apply,
    Equiv.prodProdProdComm_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.apply_eq_iff_eq,
    Prod.mk.injEq, ite_zero_mul_ite_zero, mul_one]
  grind

/-- `mm 1 1 1` is the unit tensor `unit 1`, up to reindexing. -/
theorem mm_one_one_one :
    (mm 1 1 1 : Tensor R _ _ _) =
      reindex (Equiv.prodUnique (Fin 1) (Fin 1)).symm (Equiv.prodUnique (Fin 1) (Fin 1)).symm
        (Equiv.prodUnique (Fin 1) (Fin 1)).symm (unit 1) := by
  ext a b c
  simp [Fin.fin_one_eq_zero]

/-- The shared-left sum of `n` copies of `T` is `T` tensored with `mm 1 1 n`. -/
theorem slSum_const (n : ℕ) (T : Tensor R X Y Z) :
    slSum (fun _ : Fin n => T) =
      reindex ((Equiv.prodCongr (Equiv.refl X) (Equiv.prodUnique (Fin 1) (Fin 1))).trans
          (Equiv.prodUnique X (Fin 1)))
        ((Equiv.prodCongr (Equiv.refl Y) (Equiv.uniqueProd (Fin n) (Fin 1))).trans
          (Equiv.prodComm Y (Fin n)))
        ((Equiv.prodCongr (Equiv.refl Z) (Equiv.uniqueProd (Fin n) (Fin 1))).trans
          (Equiv.prodComm Z (Fin n)))
        (tprod T (mm 1 1 n)) := by
  ext x ⟨i, y⟩ ⟨j, z⟩
  simp [mul_ite]

end Semiring

end Tensor

end Cslib
