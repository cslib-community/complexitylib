/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Formula.NodeCount
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Arithmetic formulas of unbounded fan-in and their product-depth

The model of constant-depth algebraic circuits of Limaye, Srinivasan and Tavenas
[LimayeSrinivasanTavenas2021, §1, p. 1, and footnote 1] (paraphrased): gates have unbounded fan-in,
leaves are variables or constants from the field, a sum gate computes a linear combination of its
children with constants labelling the edges (footnote 1), and a product gate computes the product
of its children. A formula is such a circuit whose underlying graph is a tree (footnote 2). The
*size* is the number of nodes, and the *product-depth* is the largest number of product gates on a
path from the root to a leaf.

The signature `sigmaPiSignature K` has, for every `m`, a sum gate `add m c` of arity `m` with edge
constants `c : Fin m → K`, a product gate `mul m` of arity `m`, and a constant `const a` of arity
zero. Formulas over it are the library's generic `Cslib.Circuits.Formula`s, so their API applies
unchanged. The product-depth is the generic weighted depth `Formula.depthWith` in which product
gates cost one and the other operations nothing (`SigmaPiOp.mulCost`); since a gate of unbounded
fan-in absorbs any number of consecutive gates of the same kind, this is the measure of the
source, not of the fan-in-two arithmetic basis `Cslib.Circuits.arithSignature`. The size of the
source is the generic `Cslib.Circuits.Formula.nodeCount`, the operation nodes (constants included)
and the input leaves.

A sum gate `add m c` is the affine operation `⟨m, c, 0⟩` of `Cslib.Circuits.affineSignature`, with
constant term `b = 0`: it computes `∑ j, c j * x j`. The constant term is dropped here because the
source's sum gates are linear, and constants are separate leaves; product gates have no affine
counterpart.

A formula computes a polynomial *formally*: it is evaluated in `MvPolynomial (Fin n) K` at the
variables, a constant `a` denoting `C a` (`SPFormula.polynomial`), as circuits do in
`Cslib.Circuits.Circuit.polynomial`.

Set-multilinearity is relative to a partition of the variables into blocks, given by a block map
`blk : Fin n → Fin d`. A formula is set-multilinear on a set `S` of blocks
(`SPFormula.IsSetMultilinear`) when every input leaf is set-multilinear on its own block, every
constant on no block, the children of a sum gate are all set-multilinear on `S`, and the children
of a product gate are set-multilinear on pairwise disjoint sets whose union is `S`. Such a formula
computes a polynomial homogeneous of degree `#S` (`SPFormula.IsSetMultilinear.isHomogeneous`).

This predicate is a syntactic strengthening, original to this formalization, of the definition in
[LimayeSrinivasanTavenas2021, §1, p. 2], which is semantic: a circuit is set-multilinear when each
of its gates computes a set-multilinear polynomial in a subset of the blocks. A semantically
set-multilinear formula may contain, for example, a sum gate with children on different sets of
blocks whose contributions cancel or carry the edge constant `0`, such as `1 · x₁ + 0 · x₂` for
variables `x₁` and `x₂` of different blocks. The lower bound of
[LimayeSrinivasanTavenas2021, Theorem 2, p. 3] is stated for semantically set-multilinear circuits;
to derive its case of formulas from results about this predicate, a normalization lemma is needed,
turning a semantically set-multilinear formula into a syntactically set-multilinear one computing
the same polynomial without increasing `nodeCount` or `productDepth`.

The encoding of the source's model, with edge constants on the sum gates and size as
`Cslib.Circuits.Formula.nodeCount`, is original.

## Main definitions

* `Cslib.Circuits.Arithmetic.SigmaPiOp`, `Cslib.Circuits.Arithmetic.sigmaPiSignature`: sum gates
  with edge constants and product gates of every arity, and constants.
* `Cslib.Circuits.Arithmetic.sigmaPiInterpretationWith`,
  `Cslib.Circuits.Arithmetic.sigmaPiInterpretation`: their meaning in a commutative semiring.
* `Cslib.Circuits.Arithmetic.SigmaPiOp.mulCost`: product gates cost one.
* `Cslib.Circuits.Arithmetic.SPFormula`: formulas over `sigmaPiSignature K`, with the helpers
  `SPFormula.add`, `SPFormula.mul`, `SPFormula.const` and `SPFormula.zero`.
* `Cslib.Circuits.Arithmetic.SPFormula.productDepth`: the largest number of product gates on a
  root-to-leaf path.
* `Cslib.Circuits.Arithmetic.SPFormula.polynomial`: the polynomial computed formally.
* `Cslib.Circuits.Arithmetic.SPFormula.IsSetMultilinear`: syntactically set-multilinear formulas.

## Main results

* `Cslib.Circuits.Arithmetic.SPFormula.polynomial_add`,
  `Cslib.Circuits.Arithmetic.SPFormula.polynomial_mul`: sum gates compute linear combinations and
  product gates products.
* `Cslib.Circuits.Arithmetic.SPFormula.aeval_polynomial`,
  `Cslib.Circuits.Arithmetic.SPFormula.eval_polynomial`: evaluating the computed polynomial is
  evaluating the formula.
* `Cslib.Circuits.Arithmetic.SPFormula.productDepth_le_depth`: product-depth is at most depth.
* `Cslib.Circuits.Arithmetic.SPFormula.isSetMultilinear_mul_iff` and its siblings: inversion of
  the set-multilinearity predicate.
* `Cslib.Circuits.Arithmetic.SPFormula.IsSetMultilinear.isHomogeneous` (original): a
  set-multilinear formula on `S` computes a homogeneous polynomial of degree `#S`.

## References

* [N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth
  algebraic circuits*][LimayeSrinivasanTavenas2021], ECCC TR21-081 Revision 1, §1, pp. 1–2, and
  footnotes 1 and 2
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open Function MvPolynomial

universe u

/-- The operations of unbounded fan-in arithmetic formulas: a sum gate of `m` arguments with edge
constants `c`, a product gate of `m` arguments, and a constant. -/
inductive SigmaPiOp (K : Type u) : Type u
  /-- The linear combination `∑ j, c j * x j` of `m` arguments. -/
  | add (m : ℕ) (c : Fin m → K)
  /-- The product of `m` arguments. -/
  | mul (m : ℕ)
  /-- A constant. -/
  | const (a : K)

variable {K : Type u}

/-- The arity of an operation: `m` for a sum or product gate of `m` arguments, zero for a
constant. -/
abbrev SigmaPiOp.arity : SigmaPiOp K → ℕ
  | .add m _ => m
  | .mul m => m
  | .const _ => 0

variable (K) in
/-- The signature of sum gates with edge constants and product gates of unbounded fan-in, and
constants. It is reducible, so that case analysis on its operations sees their arities. -/
abbrev sigmaPiSignature : Signature.{u} :=
  ⟨SigmaPiOp K, SigmaPiOp.arity⟩

variable (K) in
/-- Sum and product gates in a commutative semiring `R`, with constant symbols, edge constants
included, interpreted by `constant`. For example, `MvPolynomial.C` interprets field constants as
constant polynomials. -/
def sigmaPiInterpretationWith {R : Type*} [CommSemiring R] (constant : K → R) :
    Interpretation (sigmaPiSignature K) R
  | .add _ c, x => ∑ j, constant (c j) * x j
  | .mul _, x => ∏ j, x j
  | .const a, _ => constant a

variable (K) in
/-- Sum and product gates, and constants, in `K` itself. -/
def sigmaPiInterpretation [CommSemiring K] : Interpretation (sigmaPiSignature K) K :=
  sigmaPiInterpretationWith K id

/-- A sum gate computes the linear combination of its arguments with its edge constants. -/
@[simp] theorem sigmaPiInterpretationWith_add {R : Type*} [CommSemiring R] (constant : K → R)
    (m : ℕ) (c : Fin m → K) (x : Fin m → R) :
    sigmaPiInterpretationWith K constant (.add m c) x = ∑ j, constant (c j) * x j :=
  rfl

/-- A product gate computes the product of its arguments. -/
@[simp] theorem sigmaPiInterpretationWith_mul {R : Type*} [CommSemiring R] (constant : K → R)
    (m : ℕ) (x : Fin m → R) : sigmaPiInterpretationWith K constant (.mul m) x = ∏ j, x j :=
  rfl

/-- A constant gate computes its constant. -/
@[simp] theorem sigmaPiInterpretationWith_const {R : Type*} [CommSemiring R] (constant : K → R)
    (a : K) (x : Fin 0 → R) : sigmaPiInterpretationWith K constant (.const a) x = constant a :=
  rfl

/-- The cost of an operation in the product-depth: product gates cost one, sum gates and
constants nothing. -/
def SigmaPiOp.mulCost : SigmaPiOp K → ℕ
  | .mul _ => 1
  | .add _ _ | .const _ => 0

/-- A sum gate does not count towards the product-depth. -/
@[simp] theorem SigmaPiOp.mulCost_add (m : ℕ) (c : Fin m → K) :
    (SigmaPiOp.add m c).mulCost = 0 :=
  rfl

/-- A product gate counts one towards the product-depth. -/
@[simp] theorem SigmaPiOp.mulCost_mul (m : ℕ) : (SigmaPiOp.mul m : SigmaPiOp K).mulCost = 1 :=
  rfl

/-- A constant does not count towards the product-depth. -/
@[simp] theorem SigmaPiOp.mulCost_const (a : K) : (SigmaPiOp.const a).mulCost = 0 :=
  rfl

/-- Every operation costs at most one in the product-depth. -/
theorem SigmaPiOp.mulCost_le_one (op : SigmaPiOp K) : op.mulCost ≤ 1 := by
  cases op <;> simp

variable (K) in
/-- Arithmetic formulas of unbounded fan-in over `K` in `n` variables. -/
abbrev SPFormula (n : ℕ) : Type u :=
  Formula (sigmaPiSignature K) n

namespace SPFormula

variable {n d : ℕ}

/-- The sum gate with edge constants `c` over the formulas `F`. -/
abbrev add {m : ℕ} (c : Fin m → K) (F : Fin m → SPFormula K n) : SPFormula K n :=
  .gate (.add m c) F

/-- The product gate over the formulas `F`. -/
abbrev mul {m : ℕ} (F : Fin m → SPFormula K n) : SPFormula K n :=
  .gate (.mul m) F

/-- The constant `a`. -/
abbrev const (a : K) : SPFormula K n :=
  .gate (.const a) Fin.elim0

/-- The formula `0`: a sum gate without arguments. It computes `0` and is set-multilinear on every
set of blocks (`SPFormula.isSetMultilinear_zero`). -/
abbrev zero : SPFormula K n :=
  add (m := 0) Fin.elim0 Fin.elim0

/-! ### Product-depth and size

The size of a formula is the generic `Cslib.Circuits.Formula.nodeCount`, the size in the sense of
[LimayeSrinivasanTavenas2021, §1, p. 1]: its operation nodes, constants included, and its input
leaves. -/

/-- The product-depth: the largest number of product gates on a path from the root to a leaf. -/
def productDepth (F : SPFormula K n) : ℕ :=
  F.depthWith SigmaPiOp.mulCost

/-- An input has product-depth zero. -/
@[simp] theorem productDepth_input (i : Fin n) :
    productDepth (.input i : SPFormula K n) = 0 :=
  rfl

/-- A sum gate has the largest product-depth of its arguments. -/
@[simp] theorem productDepth_add {m : ℕ} (c : Fin m → K) (F : Fin m → SPFormula K n) :
    (add c F).productDepth = Finset.univ.sup fun j => (F j).productDepth :=
  rfl

/-- A product gate is one deeper than its arguments. -/
@[simp] theorem productDepth_mul {m : ℕ} (F : Fin m → SPFormula K n) :
    (mul F).productDepth = (Finset.univ.sup fun j => (F j).productDepth) + 1 :=
  rfl

/-- A constant has product-depth zero. -/
@[simp] theorem productDepth_const (a : K) : (const a : SPFormula K n).productDepth = 0 := by
  simp [productDepth]

/-- The formula `0` has product-depth zero. -/
theorem productDepth_zero : (zero : SPFormula K n).productDepth = 0 := by
  simp [productDepth]

/-- The product-depth is at most the depth. -/
theorem productDepth_le_depth (F : SPFormula K n) : F.productDepth ≤ F.depth :=
  F.depthWith_le_depth SigmaPiOp.mulCost_le_one

/-- A constant is one node; the size of the source counts constant leaves. -/
@[simp] theorem nodeCount_const (a : K) : (const a : SPFormula K n).nodeCount = 1 :=
  rfl

/-- The formula `0` is one node. -/
@[simp] theorem nodeCount_zero : (zero : SPFormula K n).nodeCount = 1 :=
  rfl

/-! ### The computed polynomial -/

section Polynomial

variable [CommSemiring K]

/-- The polynomial computed formally by a formula: the formula evaluated in
`MvPolynomial (Fin n) K` at the variables, a constant `a` denoting `C a`. -/
noncomputable def polynomial (F : SPFormula K n) : MvPolynomial (Fin n) K :=
  F.eval (sigmaPiInterpretationWith K C) X

/-- An input computes its variable. -/
@[simp] theorem polynomial_input (i : Fin n) :
    polynomial (.input i : SPFormula K n) = X i :=
  rfl

/-- A sum gate computes the linear combination of its arguments with its edge constants. -/
@[simp] theorem polynomial_add {m : ℕ} (c : Fin m → K) (F : Fin m → SPFormula K n) :
    (add c F).polynomial = ∑ j, C (c j) * (F j).polynomial :=
  rfl

/-- A product gate computes the product of its arguments. -/
@[simp] theorem polynomial_mul {m : ℕ} (F : Fin m → SPFormula K n) :
    (mul F).polynomial = ∏ j, (F j).polynomial :=
  rfl

/-- A constant computes the constant polynomial. -/
@[simp] theorem polynomial_const (a : K) : (const a : SPFormula K n).polynomial = C a :=
  rfl

/-- The formula `0` computes `0`. -/
theorem polynomial_zero : (zero : SPFormula K n).polynomial = 0 := by
  simp [zero]

/-- Evaluating the polynomial computed by a formula at a point of a commutative `K`-algebra is
evaluating the formula there. -/
theorem aeval_polynomial {R : Type*} [CommSemiring R] [Algebra K R] (F : SPFormula K n)
    (x : Fin n → R) :
    aeval x F.polynomial = F.eval (sigmaPiInterpretationWith K (algebraMap K R)) x := by
  let h : Homomorphism (sigmaPiInterpretationWith K (C : K → MvPolynomial (Fin n) K))
      (sigmaPiInterpretationWith K (algebraMap K R)) :=
    ⟨aeval x, fun op args => by cases op <;> simp [sigmaPiInterpretationWith]⟩
  refine (F.map_eval h X).trans ?_
  congr 1
  funext i
  exact aeval_X x i

/-- Evaluating the polynomial computed by a formula at a point of `K` is evaluating the formula
under `sigmaPiInterpretation K`. -/
@[simp] theorem eval_polynomial (F : SPFormula K n) (x : Fin n → K) :
    MvPolynomial.eval x F.polynomial = F.eval (sigmaPiInterpretation K) x := by
  simpa [MvPolynomial.aeval_def, MvPolynomial.eval₂_id, sigmaPiInterpretation] using
    F.aeval_polynomial x

end Polynomial

/-! ### Set-multilinear formulas -/

/-- A formula is *set-multilinear on the set `S` of blocks*, for the partition of the variables
into blocks given by `blk`, when every input is set-multilinear on its own block, every constant
on no block, the arguments of a sum gate are all set-multilinear on `S`, and the arguments of a
product gate are set-multilinear on pairwise disjoint sets of blocks whose union is `S`.

This is a syntactic strengthening, original to this formalization, of the semantic definition of
[LimayeSrinivasanTavenas2021, §1, p. 2], where each gate must compute a set-multilinear polynomial
in a subset of the blocks; see the module docstring. -/
inductive IsSetMultilinear (blk : Fin n → Fin d) : SPFormula K n → Finset (Fin d) → Prop
  /-- An input is set-multilinear on its own block. -/
  | input (i : Fin n) : IsSetMultilinear blk (.input i) {blk i}
  /-- A constant is set-multilinear on no block. -/
  | const (a : K) : IsSetMultilinear blk (const a) ∅
  /-- A sum gate is set-multilinear on `S` when all its arguments are. -/
  | add {m : ℕ} (c : Fin m → K) (F : Fin m → SPFormula K n) (S : Finset (Fin d))
      (hF : ∀ j, IsSetMultilinear blk (F j) S) : IsSetMultilinear blk (add c F) S
  /-- A product gate is set-multilinear on the union of pairwise disjoint sets of blocks on
  which its arguments are set-multilinear. -/
  | mul {m : ℕ} (F : Fin m → SPFormula K n) (T : Fin m → Finset (Fin d))
      (hT : Pairwise (Disjoint on T)) (hF : ∀ j, IsSetMultilinear blk (F j) (T j)) :
      IsSetMultilinear blk (mul F) (Finset.univ.biUnion T)

variable {blk : Fin n → Fin d}

/-- An input is set-multilinear exactly on its own block. -/
theorem isSetMultilinear_input_iff {i : Fin n} {S : Finset (Fin d)} :
    IsSetMultilinear blk (.input i : SPFormula K n) S ↔ S = {blk i} := by
  constructor
  · rintro ⟨⟩
    rfl
  · rintro rfl
    exact .input i

/-- A constant is set-multilinear exactly on no block. -/
theorem isSetMultilinear_const_iff {a : K} {S : Finset (Fin d)} :
    IsSetMultilinear blk (const a : SPFormula K n) S ↔ S = ∅ := by
  constructor
  · rintro ⟨⟩
    rfl
  · rintro rfl
    exact .const a

/-- A sum gate is set-multilinear on `S` exactly when all its arguments are. -/
theorem isSetMultilinear_add_iff {m : ℕ} {c : Fin m → K} {F : Fin m → SPFormula K n}
    {S : Finset (Fin d)} :
    IsSetMultilinear blk (add c F) S ↔ ∀ j, IsSetMultilinear blk (F j) S := by
  constructor
  · rintro ⟨⟩
    assumption
  · exact .add c F S

/-- A product gate is set-multilinear on `S` exactly when its arguments are set-multilinear on
pairwise disjoint sets of blocks whose union is `S`. -/
theorem isSetMultilinear_mul_iff {m : ℕ} {F : Fin m → SPFormula K n} {S : Finset (Fin d)} :
    IsSetMultilinear blk (mul F) S ↔ ∃ T : Fin m → Finset (Fin d), Pairwise (Disjoint on T) ∧
      (∀ j, IsSetMultilinear blk (F j) (T j)) ∧ S = Finset.univ.biUnion T := by
  constructor
  · rintro ⟨⟩
    exact ⟨_, ‹_›, ‹_›, rfl⟩
  · rintro ⟨T, hT, hF, rfl⟩
    exact .mul F T hT hF

/-- The formula `0`, a sum gate without arguments, is set-multilinear on every set of blocks. -/
theorem isSetMultilinear_zero (S : Finset (Fin d)) :
    IsSetMultilinear blk (zero : SPFormula K n) S :=
  .add _ _ S fun j => j.elim0

/-- A set-multilinear formula on `S` computes a homogeneous polynomial of degree `#S`
(original). -/
theorem IsSetMultilinear.isHomogeneous [CommSemiring K] {F : SPFormula K n}
    {S : Finset (Fin d)} (h : IsSetMultilinear blk F S) : F.polynomial.IsHomogeneous S.card := by
  induction h with
  | input i => simpa using isHomogeneous_X K i
  | const a => simpa using isHomogeneous_C (Fin n) a
  | add c F S _ ih =>
    rw [polynomial_add]
    exact IsHomogeneous.sum _ _ _ fun j _ => (ih j).C_mul _
  | mul F T hT _ ih =>
    rw [polynomial_mul, Finset.card_biUnion (hT.set_pairwise _)]
    exact IsHomogeneous.prod _ _ _ fun j _ => ih j

end SPFormula

end Cslib.Circuits.Arithmetic
