/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.Eval
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Matrix.Unique

/-!
# Rational hitting lists: affine realizations

Every rational formula `f` has a linear realization: a square matrix `Formula.pencil f` of affine
forms in the variables, indexed by a finite type `Formula.Index f` with `f.nodeCount + 1`
elements, together with a rational row and column. Wherever `f` is defined, the evaluated pencil
is invertible and the row, inverse and column multiply to the value of `f`. Conversely, `f` is
defined with an invertible value exactly when the pencils of its inverse nodes and of its
augmented root are invertible (`Formula.certificates_iff`); no rational cancellation is performed.

## Main definitions

* `Cslib.Circuits.Rational.Affine.Form`, `Cslib.Circuits.Rational.Affine.eval`: affine forms and
  their evaluation.
* `Cslib.Circuits.Rational.Formula.Index`, `Cslib.Circuits.Rational.Formula.pencil`,
  `Cslib.Circuits.Rational.Formula.row`, `Cslib.Circuits.Rational.Formula.col`: the realization.
* `Cslib.Circuits.Rational.Formula.inverseNodes`, `Cslib.Circuits.Rational.Formula.certificates`:
  the inverse occurrences of a formula, and these together with the augmented root.

## Main results

* `Cslib.Circuits.Rational.Formula.card_index`: the realization has `f.nodeCount + 1` rows.
* `Cslib.Circuits.Rational.Formula.Eval.realization`: exact realization of defined formulas.
* `Cslib.Circuits.Rational.Formula.certificates_iff`: invertible certificate pencils are
  equivalent to a defined invertible value.
* `Cslib.Circuits.Rational.Formula.certificate_bounds`: the number and sizes of the certificates.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/Affine.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Rational

open Matrix

namespace Affine

variable {n : ℕ}

/-- A constant coefficient and one rational coefficient per variable. -/
abbrev Form (n : ℕ) := ℚ × (Fin n → ℚ)

/-- The affine form with the given constant and zero variable coefficients. -/
def constant (a : ℚ) : Form n := (a, 0)

/-- The affine coordinate form for one variable. -/
def varForm (i : Fin n) : Form n := (0, Pi.single i 1)

variable {R : Type*} [Ring R]

/-- Evaluate an affine form in a rational algebra, with coefficients on the left. -/
def eval (c : ℚ →+* R) (X : Fin n → R) : Form n →+ R where
  toFun a := c a.1 + ∑ i, c (a.2 i) * X i
  map_zero' := by simp
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, add_mul,
      Finset.sum_add_distrib]
    abel

@[simp] theorem eval_constant (c : ℚ →+* R) (X : Fin n → R) (a : ℚ) :
    eval c X (constant a) = c a := by
  simp [eval, constant]

@[simp] theorem eval_variable (c : ℚ →+* R) (X : Fin n → R) (i : Fin n) :
    eval c X (varForm i) = X i := by
  simp [eval, varForm, Pi.single_apply, apply_ite]

/-- Regard a rational matrix as a matrix of constant affine forms. -/
def constMatrix {ι κ : Type*} (A : Matrix ι κ ℚ) : Matrix ι κ (Form n) := A.map constant

@[simp] theorem eval_constMatrix {ι κ : Type*} (c : ℚ →+* R) (X : Fin n → R)
    (A : Matrix ι κ ℚ) : (constMatrix A).map (eval c X) = A.map c := by
  ext i j
  exact eval_constant c X (A i j)

end Affine

namespace Formula

noncomputable section

variable {n : ℕ}

/-! The realization is defined by recursion on the native constructors `input` and `gate`, so that
its index type reduces to sums of the index types of the arguments `args j`. The proofs below
therefore also proceed by induction on the native constructors. -/

/-- The finite row and column index type of the formula's linear realization. -/
@[reducible] def Index : Formula n → Type
  | .input _ | .gate (.const _) _ => Unit ⊕ Unit
  | .gate .add a | .gate .mul a => Index (a 0) ⊕ Index (a 1)
  | .gate .inv a => Index (a 0) ⊕ Unit

/-- The index type of a realization is finite. -/
@[reducible] instance indexFintype : (f : Formula n) → Fintype (Index f)
  | .input _ | .gate (.const _) _ => inferInstanceAs (Fintype (Unit ⊕ Unit))
  | .gate .add a | .gate .mul a =>
    letI := indexFintype (a 0)
    letI := indexFintype (a 1)
    inferInstanceAs (Fintype (Index (a 0) ⊕ Index (a 1)))
  | .gate .inv a =>
    letI := indexFintype (a 0)
    inferInstanceAs (Fintype (Index (a 0) ⊕ Unit))

/-- The index type of a realization has decidable equality. -/
@[reducible] instance indexDecidableEq : (f : Formula n) → DecidableEq (Index f)
  | .input _ | .gate (.const _) _ => inferInstanceAs (DecidableEq (Unit ⊕ Unit))
  | .gate .add a | .gate .mul a =>
    letI := indexDecidableEq (a 0)
    letI := indexDecidableEq (a 1)
    inferInstanceAs (DecidableEq (Index (a 0) ⊕ Index (a 1)))
  | .gate .inv a =>
    letI := indexDecidableEq (a 0)
    inferInstanceAs (DecidableEq (Index (a 0) ⊕ Unit))

/-- The realization of a formula has one more row than the formula has nodes. -/
theorem card_index (f : Formula n) : Fintype.card f.Index = f.nodeCount + 1 := by
  rw [nodeCount]
  induction f with
  | input i => simp [Index]
  | gate op args ih =>
    cases op <;>
      simp only [Index, ratSignature, Fintype.card_sum, Fintype.card_unique, ih,
        Circuits.Formula.size, Circuits.Formula.leafSize, Fin.sum_univ_two, Finset.univ_eq_empty,
        Finset.sum_empty, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] <;>
      omega

/-- The left row of the formula's linear realization. -/
def row : (f : Formula n) → Matrix Unit f.Index ℚ
  | .input _ | .gate (.const _) _ => fromCols 1 0
  | .gate .add a => fromCols (row (a 0)) (row (a 1))
  | .gate .mul a => fromCols (row (a 0)) 0
  | .gate .inv _ => fromCols 0 (-1)

/-- The right column of the formula's linear realization. -/
def col : (f : Formula n) → Matrix f.Index Unit ℚ
  | .input _ | .gate (.const _) _ => fromRows 0 1
  | .gate .add a => fromRows (col (a 0)) (col (a 1))
  | .gate .mul a => fromRows 0 (col (a 1))
  | .gate .inv _ => fromRows 0 1

/-- The affine matrix pencil built recursively from a rational formula. -/
def pencil : (f : Formula n) → Matrix f.Index f.Index (Affine.Form n)
  | .input i => fromBlocks (Affine.constMatrix 1) (Matrix.of fun _ _ => -Affine.varForm i) 0
      (Affine.constMatrix 1)
  | .gate (.const q) _ => fromBlocks (Affine.constMatrix 1)
      (Matrix.of fun _ _ => -Affine.constant q) 0 (Affine.constMatrix 1)
  | .gate .add a => fromBlocks (pencil (a 0)) 0 0 (pencil (a 1))
  | .gate .mul a =>
    fromBlocks (pencil (a 0)) (-Affine.constMatrix (col (a 0) * row (a 1))) 0 (pencil (a 1))
  | .gate .inv a =>
    fromBlocks (pencil (a 0)) (Affine.constMatrix (col (a 0))) (Affine.constMatrix (row (a 0))) 0

variable {R : Type*} [Ring R] (c : ℚ →+* R) (X : Fin n → R)

/-- Evaluate all entries of the formula's affine pencil. -/
abbrev realized (f : Formula n) := (pencil f).map (Affine.eval c X)

/-- Map the realization's rational row into the target ring. -/
abbrev rowR (f : Formula n) := (row f).map c

/-- Map the realization's rational column into the target ring. -/
abbrev colR (f : Formula n) := (col f).map c

/-- Represent a scalar as a one-by-one matrix. -/
abbrev scalar (a : R) : Matrix Unit Unit R := (Matrix.uniqueRingEquiv (m := Unit)).symm a

section Native

variable (q : ℚ) (i : Fin n) (a : Fin (ratSignature.Arity .add) → Formula n)
  (m : Fin (ratSignature.Arity .mul) → Formula n) (b : Fin (ratSignature.Arity .inv) → Formula n)

private theorem realized_add : realized c X (.gate .add a) =
    fromBlocks (realized c X (a 0)) 0 0 (realized c X (a 1)) := by
  change (fromBlocks (pencil (a 0)) 0 0 (pencil (a 1))).map (Affine.eval c X) = _
  rw [fromBlocks_map]
  simp

private theorem realized_mul : realized c X (.gate .mul m) =
    fromBlocks (realized c X (m 0)) (-colR c (m 0) * rowR c (m 1)) 0 (realized c X (m 1)) := by
  change (fromBlocks (pencil (m 0)) (-Affine.constMatrix (col (m 0) * row (m 1))) 0
    (pencil (m 1))).map (Affine.eval c X) = _
  rw [fromBlocks_map, Matrix.map_neg _ (map_neg _)]
  simp [Matrix.map_mul, Matrix.neg_mul, rowR, colR]

private theorem realized_inv : realized c X (.gate .inv b) =
    fromBlocks (realized c X (b 0)) (colR c (b 0)) (rowR c (b 0)) 0 := by
  change (fromBlocks (pencil (b 0)) (Affine.constMatrix (col (b 0)))
    (Affine.constMatrix (row (b 0))) 0).map (Affine.eval c X) = _
  rw [fromBlocks_map]
  simp [rowR, colR]

private theorem rowR_add : rowR c (.gate .add a) = fromCols (rowR c (a 0)) (rowR c (a 1)) :=
  fromCols_map _ _ _

private theorem colR_add : colR c (.gate .add a) = fromRows (colR c (a 0)) (colR c (a 1)) :=
  fromRows_map _ _ _

private theorem rowR_mul : rowR c (.gate .mul m) = fromCols (rowR c (m 0)) 0 := by
  change (fromCols (row (m 0)) 0).map c = _
  rw [fromCols_map]
  simp

private theorem colR_mul : colR c (.gate .mul m) = fromRows 0 (colR c (m 1)) := by
  change (fromRows 0 (col (m 1))).map c = _
  rw [fromRows_map]
  simp

private theorem rowR_inv : rowR c (.gate .inv b) = fromCols 0 (-1) := by
  change (fromCols (0 : Matrix Unit (Index (b 0)) ℚ) (-1)).map c = _
  rw [fromCols_map, Matrix.map_neg _ (map_neg _)]
  simp

private theorem colR_inv : colR c (.gate .inv b) = fromRows 0 1 := by
  change (fromRows (0 : Matrix (Index (b 0)) Unit ℚ) 1).map c = _
  rw [fromRows_map]
  simp

private theorem realized_input : realized c X (.input i) = fromBlocks 1 (-scalar (X i)) 0 1 := by
  change (fromBlocks (Affine.constMatrix (1 : Matrix Unit Unit ℚ))
    (Matrix.of fun _ _ => -Affine.varForm i) 0 (Affine.constMatrix 1)).map (Affine.eval c X) = _
  rw [fromBlocks_map]
  simp only [Affine.eval_constMatrix, Matrix.map_one c (map_zero c) (map_one c),
    Matrix.map_zero, map_zero]
  congr 1
  ext
  simp [scalar, Matrix.map, Matrix.of_apply]

private theorem realized_const (args : Fin (ratSignature.Arity (.const q)) → Formula n) :
    realized c X (.gate (.const q) args) = fromBlocks 1 (-scalar (c q)) 0 1 := by
  change (fromBlocks (Affine.constMatrix (1 : Matrix Unit Unit ℚ))
    (Matrix.of fun _ _ => -Affine.constant q) 0 (Affine.constMatrix 1)).map
      (Affine.eval c X) = _
  rw [fromBlocks_map]
  simp only [Affine.eval_constMatrix, Matrix.map_one c (map_zero c) (map_one c),
    Matrix.map_zero, map_zero]
  congr 1
  ext
  simp [scalar, Matrix.map, Matrix.of_apply]

private theorem rowR_input : rowR c (.input i) = fromCols 1 0 := by
  change (fromCols (1 : Matrix Unit Unit ℚ) 0).map c = _
  rw [fromCols_map]
  simp

private theorem colR_input : colR c (.input i) = fromRows 0 1 := by
  change (fromRows 0 (1 : Matrix Unit Unit ℚ)).map c = _
  rw [fromRows_map]
  simp

private theorem rowR_const (args : Fin (ratSignature.Arity (.const q)) → Formula n) :
    rowR c (.gate (.const q) args) = fromCols 1 0 := by
  change (fromCols (1 : Matrix Unit Unit ℚ) 0).map c = _
  rw [fromCols_map]
  simp

private theorem colR_const (args : Fin (ratSignature.Arity (.const q)) → Formula n) :
    colR c (.gate (.const q) args) = fromRows 0 1 := by
  change (fromRows 0 (1 : Matrix Unit Unit ℚ)).map c = _
  rw [fromRows_map]
  simp

end Native

private theorem leaf_realization (a : R) :
    ∃ M : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) R,
      fromBlocks 1 (-scalar a) 0 1 * M = 1 ∧
      M * fromBlocks 1 (-scalar a) 0 1 = 1 ∧
      NoncommBlocks.matMul (NoncommBlocks.matMul (fromCols (1 : Matrix Unit Unit R) 0) M)
        (fromRows (0 : Matrix Unit Unit R) (1 : Matrix Unit Unit R)) = scalar a := by
  refine ⟨fromBlocks 1 (scalar a) 0 1, ?_, ?_, ?_⟩
  · simp [fromBlocks_multiply]
  · simp [fromBlocks_multiply]
  · dsimp only [NoncommBlocks.matMul]
    rw [fromCols_mul_fromBlocks, fromCols_mul_fromRows]
    simp

/-- Exact affine realization of every defined formula: the evaluated pencil is invertible, and
the row, its inverse and the column multiply to the value. -/
theorem Eval.realization {f : Formula n} {v : R} (hv : f.Eval c X v) :
    ∃ M : Matrix f.Index f.Index R,
      realized c X f * M = 1 ∧ M * realized c X f = 1 ∧
      rowR c f * M * colR c f = scalar v := by
  induction f generalizing v with
  | input i =>
    obtain rfl : v = X i := hv
    rw [realized_input, rowR_input, colR_input]
    exact leaf_realization (X i)
  | gate op args ih =>
    cases op with
    | const q =>
      obtain rfl : v = c q := hv
      rw [realized_const, rowR_const, colR_const]
      exact leaf_realization (c q)
    | add =>
      obtain ⟨a, b, ha, hb, rfl⟩ := hv
      obtain ⟨Mf, hf1, hf2, hfr⟩ := ih 0 ha
      obtain ⟨Mg, hg1, hg2, hgr⟩ := ih 1 hb
      refine ⟨fromBlocks Mf 0 0 Mg, ?_, ?_, ?_⟩
      · rw [realized_add, fromBlocks_multiply]
        simp [hf1, hg1, Matrix.mul_zero, Matrix.zero_mul]
      · rw [realized_add, fromBlocks_multiply]
        simp [hf2, hg2, Matrix.mul_zero, Matrix.zero_mul]
      · rw [rowR_add, colR_add, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
        simp only [Matrix.mul_zero, add_zero, zero_add, hfr, hgr]
        exact (map_add (Matrix.uniqueRingEquiv (m := Unit)).symm a b).symm
    | mul =>
      obtain ⟨a, b, ha, hb, rfl⟩ := hv
      obtain ⟨Mf, hf1, hf2, hfr⟩ := ih 0 ha
      obtain ⟨Mg, hg1, hg2, hgr⟩ := ih 1 hb
      let B := Mf * colR c (args 0) * rowR c (args 1) * Mg
      have hB1 : realized c X (args 0) * B = colR c (args 0) * rowR c (args 1) * Mg := by
        simp [B, ← Matrix.mul_assoc, hf1, Matrix.one_mul]
      have hB2 : B * realized c X (args 1) = Mf * colR c (args 0) * rowR c (args 1) := by
        simp [B, Matrix.mul_assoc, hg2, Matrix.mul_one]
      refine ⟨fromBlocks Mf B 0 Mg, ?_, ?_, ?_⟩
      · rw [realized_mul, fromBlocks_multiply]
        simp [hf1, hg1, hB1, Matrix.mul_zero, Matrix.zero_mul, Matrix.neg_mul]
      · rw [realized_mul, fromBlocks_multiply]
        simp [hf2, hg2, hB2, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.neg_mul,
          ← Matrix.mul_assoc]
      · rw [rowR_mul, colR_mul, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, B]
        have hh : rowR c (args 0) * (Mf * colR c (args 0) * rowR c (args 1) * Mg) *
            colR c (args 1) = rowR c (args 0) * Mf * colR c (args 0) *
              (rowR c (args 1) * Mg * colR c (args 1)) := by
          simp only [Matrix.mul_assoc]
        rw [hh, hfr, hgr]
        exact (map_mul (Matrix.uniqueRingEquiv (m := Unit)).symm a b).symm
    | inv =>
      obtain ⟨a, ha, hab, hba⟩ := hv
      obtain ⟨Mf, hf1, hf2, hfr⟩ := ih 0 ha
      rw [realized_inv, rowR_inv, colR_inv]
      exact NoncommBlocks.schur_inverse _ _ _ _ (scalar a) (scalar v)
        hf1 hf2 hfr (by rw [← map_mul, hab, map_one]) (by rw [← map_mul, hba, map_one])

end

end Formula

namespace Formula

noncomputable section

variable {n : ℕ} {R : Type*} [Ring R] (c : ℚ →+* R) (X : Fin n → R)

/-- The inverse nodes of a formula, as a list retaining occurrences rather than distinct
subexpressions. -/
def inverseNodes : Formula n → List (Formula n)
  | .input _ | .gate (.const _) _ => []
  | .gate .add a | .gate .mul a => inverseNodes (a 0) ++ inverseNodes (a 1)
  | .gate .inv a => .gate .inv a :: inverseNodes (a 0)

@[simp] theorem inverseNodes_var (i : Fin n) : inverseNodes (var i) = [] := rfl

@[simp] theorem inverseNodes_const (q : ℚ) : inverseNodes (const q : Formula n) = [] := rfl

@[simp] theorem inverseNodes_add (f g : Formula n) :
    inverseNodes (add f g) = inverseNodes f ++ inverseNodes g := rfl

@[simp] theorem inverseNodes_mul (f g : Formula n) :
    inverseNodes (mul f g) = inverseNodes f ++ inverseNodes g := rfl

@[simp] theorem inverseNodes_inv (f : Formula n) :
    inverseNodes (inv f) = inv f :: inverseNodes f := rfl

/-- The inverse nodes together with the augmented root `inv f`, which is a certificate pencil and
not a new counted gate. -/
def certificates (f : Formula n) : List (Formula n) := inverseNodes f ++ [inv f]

private theorem Eval.pencil_isUnit {f : Formula n} {a : R} (ha : f.Eval c X a) :
    IsUnit (realized c X f) := by
  obtain ⟨M, hM, hM', _⟩ := ha.realization
  exact isUnit_iff_exists.mpr ⟨M, hM, hM'⟩

/-- At a defined point, the augmented pencil is invertible exactly when the value is. -/
theorem Eval.augmented_isUnit_iff {f : Formula n} {a : R} (ha : f.Eval c X a) :
    IsUnit (realized c X (Formula.inv f)) ↔ IsUnit a := by
  obtain ⟨M, hM, hM', hr⟩ := ha.realization
  have key := NoncommBlocks.schur_unit_iff _ _ (colR c f) (rowR c f) hM hM'
  rw [hr] at key
  rw [realized_inv]
  refine key.trans ⟨fun h => ?_, fun h => h.map (Matrix.uniqueRingEquiv (m := Unit)).symm⟩
  simpa using h.map (Matrix.uniqueRingEquiv (m := Unit))

private theorem Eval.inverseNodes_units {f : Formula n} {a : R} (ha : f.Eval c X a) :
    ∀ h ∈ inverseNodes f, IsUnit (realized c X h) := by
  induction f using inductionOn generalizing a with
  | var i => simp
  | const q => simp
  | add f g ihf ihg =>
    obtain ⟨a₁, a₂, ha₁, ha₂, -⟩ := eval_add_iff.mp ha
    simpa only [inverseNodes_add, List.mem_append, or_imp, forall_and] using
      And.intro (ihf ha₁) (ihg ha₂)
  | mul f g ihf ihg =>
    obtain ⟨a₁, a₂, ha₁, ha₂, -⟩ := eval_mul_iff.mp ha
    simpa only [inverseNodes_mul, List.mem_append, or_imp, forall_and] using
      And.intro (ihf ha₁) (ihg ha₂)
  | inv f ih =>
    obtain ⟨b, hb, -, -⟩ := eval_inv_iff.mp ha
    intro h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · exact ha.pencil_isUnit
    · exact ih hb h hh

theorem eval_of_inverseNodes_units (f : Formula n)
    (hu : ∀ h ∈ inverseNodes f, IsUnit (realized c X h)) :
    ∃ a, f.Eval c X a := by
  induction f using inductionOn with
  | var i => exact ⟨X i, .var i⟩
  | const q => exact ⟨c q, .const q⟩
  | add f g ihf ihg =>
    obtain ⟨a, ha⟩ := ihf fun h hh => hu h (List.mem_append_left _ hh)
    obtain ⟨b, hb⟩ := ihg fun h hh => hu h (List.mem_append_right _ hh)
    exact ⟨a + b, .add ha hb⟩
  | mul f g ihf ihg =>
    obtain ⟨a, ha⟩ := ihf fun h hh => hu h (List.mem_append_left _ hh)
    obtain ⟨b, hb⟩ := ihg fun h hh => hu h (List.mem_append_right _ hh)
    exact ⟨a * b, .mul ha hb⟩
  | inv f ih =>
    obtain ⟨a, ha⟩ := ih fun h hh => hu h (List.mem_cons_of_mem _ hh)
    have hua := ha.augmented_isUnit_iff.mp (hu (inv f) List.mem_cons_self)
    obtain ⟨b, hab, hba⟩ := isUnit_iff_exists.mp hua
    exact ⟨b, .inv ha hab hba⟩

/-- Full original-tree definedness and invertible final value are equivalent to invertibility of
all affine-pencil certificates. No rational cancellation is performed. -/
theorem certificates_iff (f : Formula n) :
    (∀ h ∈ certificates f, IsUnit (realized c X h)) ↔ ∃ a, f.Eval c X a ∧ IsUnit a := by
  constructor
  · intro hu
    obtain ⟨a, ha⟩ := eval_of_inverseNodes_units c X f
      fun h hh => hu h (List.mem_append_left _ hh)
    exact ⟨a, ha, ha.augmented_isUnit_iff.mp (hu (inv f) (by simp [certificates]))⟩
  · rintro ⟨a, ha, hua⟩ h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact Eval.inverseNodes_units c X ha h hh
    · obtain rfl : h = inv f := by simpa using hh
      exact ha.augmented_isUnit_iff.mpr hua

private theorem inverseNodes_length (f : Formula n) : (inverseNodes f).length ≤ f.nodeCount := by
  induction f using inductionOn with
  | var i => simp
  | const q => simp
  | add f g ihf ihg => simp only [inverseNodes_add, List.length_append, nodeCount_add]; omega
  | mul f g ihf ihg => simp only [inverseNodes_mul, List.length_append, nodeCount_mul]; omega
  | inv f ih => simp only [inverseNodes_inv, List.length_cons, nodeCount_inv]; omega

theorem nodeCount_le_of_mem_inverseNodes {f h : Formula n} (hh : h ∈ inverseNodes f) :
    h.nodeCount ≤ f.nodeCount := by
  induction f using inductionOn with
  | var i => simp at hh
  | const q => simp at hh
  | add f g ihf ihg =>
    rcases List.mem_append.mp hh with hh | hh
    · have := ihf hh; simp only [nodeCount_add]; omega
    · have := ihg hh; simp only [nodeCount_add]; omega
  | mul f g ihf ihg =>
    rcases List.mem_append.mp hh with hh | hh
    · have := ihf hh; simp only [nodeCount_mul]; omega
    · have := ihg hh; simp only [nodeCount_mul]; omega
  | inv f ih =>
    rcases List.mem_cons.mp hh with rfl | hh
    · rfl
    · have := ih hh; simp only [nodeCount_inv]; omega

/-- A formula with at most `s` nodes has at most `s + 1` certificates, each of dimension at most
`2 * s + 1`. -/
theorem certificate_bounds (f : Formula n) (s : ℕ) (hs : 1 ≤ s) (hf : f.nodeCount ≤ s) :
    (certificates f).length ≤ s + 1 ∧
      ∀ h ∈ certificates f, 0 < Fintype.card h.Index ∧ Fintype.card h.Index ≤ 2 * s + 1 := by
  refine ⟨?_, ?_⟩
  · simp only [certificates, List.length_append, List.length_singleton]
    have := inverseNodes_length f
    omega
  · intro h hh
    rw [card_index]
    refine ⟨by omega, ?_⟩
    rcases List.mem_append.mp hh with hh | hh
    · have := nodeCount_le_of_mem_inverseNodes hh
      omega
    · obtain rfl : h = inv f := by simpa using hh
      rw [nodeCount_inv]
      omega

end

end Formula

end Rational

namespace Rational.Affine

open Matrix

noncomputable section

variable {n : ℕ} {R : Type*} [Ring R]

/-- The homogeneous coefficient, with index zero reserved for the constant term. -/
def coeff (a : Form n) : Fin (n + 1) → ℚ := Fin.cases a.1 a.2

/-- Evaluate the homogeneous form on an extra constant coordinate. -/
def homogeneous (c : ℚ →+* R) (Z : Fin (n + 1) → R) (a : Form n) : R :=
  ∑ i, c (coeff a i) * Z i

theorem homogeneous_one (c : ℚ →+* R) (X : Fin n → R) (a : Form n) :
    homogeneous c (Fin.cases 1 X) a = eval c X a := by
  simp [homogeneous, coeff, Fin.sum_univ_succ, eval]

private theorem normalized [Algebra ℚ R] (Z : Fin (n + 1) → R) (u : R) (hu : Z 0 * u = 1)
    (a : Form n) :
    homogeneous (algebraMap ℚ R) Z a =
      Z 0 * eval (algebraMap ℚ R) (fun i => u * Z i.succ) a := by
  change (∑ i, (algebraMap ℚ R) (coeff a i) * Z i) =
    Z 0 * ((algebraMap ℚ R) a.1 + ∑ i, (algebraMap ℚ R) (a.2 i) * (u * Z i.succ))
  rw [Fin.sum_univ_succ]
  simp only [coeff, Fin.cases_zero, Fin.cases_succ, mul_add, Finset.mul_sum]
  congr 1
  · exact Algebra.commutes a.1 (Z 0)
  · apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, ← Algebra.commutes (a.2 i) (Z 0), mul_assoc,
      ← mul_assoc (Z 0) u, hu, one_mul]

private theorem normalized_pencil {ι : Type*} [Fintype ι] [DecidableEq ι] [Algebra ℚ R]
    (L : Matrix ι ι (Form n)) (Z : Fin (n + 1) → R) (u : R) (hu : Z 0 * u = 1) :
    L.map (homogeneous (algebraMap ℚ R) Z) =
      Matrix.scalar ι (Z 0) * L.map (eval (algebraMap ℚ R) (fun i => u * Z i.succ)) := by
  funext i j
  change homogeneous (algebraMap ℚ R) Z (L i j) =
    (Matrix.diagonal (fun _ : ι => Z 0) *
      L.map (eval (algebraMap ℚ R) (fun i => u * Z i.succ)) : Matrix ι ι R) i j
  rw [Matrix.diagonal_mul]
  exact normalized Z u hu (L i j)

theorem normalized_pencil_unit {ι : Type*} [Fintype ι] [DecidableEq ι] [Algebra ℚ R]
    (L : Matrix ι ι (Form n)) (Z : Fin (n + 1) → R) (z : Rˣ) (hz : (z : R) = Z 0)
    (hL : IsUnit (L.map (homogeneous (algebraMap ℚ R) Z))) :
    IsUnit (L.map (eval (algebraMap ℚ R) (fun i => (↑z⁻¹ : R) * Z i.succ))) := by
  have hu : Z 0 * (↑z⁻¹ : R) = 1 := by rw [← hz]; exact z.val_inv
  rw [normalized_pencil L Z (↑z⁻¹ : R) hu] at hL
  exact (z.isUnit.map (Matrix.scalar ι) |>.mul_left_iff).mp (by simpa [hz] using hL)

/-- Reindexing a pencil's coefficients does not alter its matrix evaluation. -/
theorem eval_reindex {K : Type*} [Field K] [CharZero K] {ι ι' κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : Matrix ι ι (Form n)) (X : Fin n → Matrix κ κ K) (e : ι ≃ ι') :
    (Matrix.reindex e e L).map (eval (algebraMap ℚ (Matrix κ κ K)) X) =
      Matrix.reindex e e (L.map (eval (algebraMap ℚ (Matrix κ κ K)) X)) :=
  rfl

/-- Homogeneous affine coefficients give exactly the ordinary Kronecker pencil. -/
theorem homogeneous_flat {K : Type*} [Field K] [CharZero K] {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (L : Matrix ι ι (Form n)) (Z : Fin (n + 1) → Matrix κ κ K) :
    Matrix.compRingEquiv ι κ K (L.map (homogeneous (algebraMap ℚ (Matrix κ κ K)) Z)) =
      fun a b => ∑ r, (algebraMap ℚ K) (coeff (L a.1 b.1) r) * Z r a.2 b.2 := by
  funext ⟨i, a⟩ ⟨j, b⟩
  change (∑ r, (algebraMap ℚ (Matrix κ κ K)) (coeff (L i j) r) * Z r) a b = _
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  change (Matrix.diagonal (fun _ : κ => (algebraMap ℚ K) (coeff (L i j) r)) * Z r :
    Matrix κ κ K) a b = _
  rw [Matrix.diagonal_mul]

end

end Rational.Affine

end Cslib.Circuits
