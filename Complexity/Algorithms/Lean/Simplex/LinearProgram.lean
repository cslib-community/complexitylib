/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Simplex.Bland
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
import Complexity.Foundations.LinearAlgebra.Matrix.LinearProgramming
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Pi
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The simplex method for linear programs in matrix form

This module connects the simplex method on dictionaries
(`Complexity.Algorithms.Lean.Simplex.Bland`) with linear programs given by matrices over a
linearly ordered field, and reads off an optimal dual solution from the final dictionary.

## Model

A dictionary `D` on variables `ι` *represents* the program `max c ⬝ᵥ x` subject to `x ≥ 0`,
`A *ᵥ x = b` (the equational form of [MatousekGartner2007]) when the solutions of `D` are the
solutions of `A *ᵥ x = b` and its objective agrees with `c ⬝ᵥ x` on them (`Represents`).
Representation is invariant under equivalence of dictionaries, hence under pivoting.

For the program `max c ⬝ᵥ x` subject to `x ≥ 0`, `A *ᵥ x ≤ b` with `A : Matrix (Fin m) (Fin n) K`,
the slack dictionary (`slackDictionary`, [Chvatal1983], Chapter 2) has the variables
`Fin (n + m)`: the original variables `Fin.castAdd m j` and one slack variable `Fin.natAdd n i`
per row, initially basic with `x (natAdd n i) = b i - ∑ j, A i j * x (castAdd m j)`. It represents
the equational form with the matrix `[A | 1]` (`slackMatrix`), and it is feasible when `b ≥ 0`.
The feasible sets are written `{x | 0 ≤ x ∧ A *ᵥ x ≤ b}` and `{y | 0 ≤ y ∧ c ≤ y ᵥ* A}`, as in
`Matrix.exists_isGreatest_isLeast_dotProduct_of_nonneg`.

## Main definitions

* `Cslib.Algorithms.Lean.Simplex.Dictionary.Represents`: a dictionary represents a linear program
  in equational form.
* `Cslib.Algorithms.Lean.Simplex.slackDictionary`, `Cslib.Algorithms.Lean.Simplex.slackMatrix`,
  `Cslib.Algorithms.Lean.Simplex.withSlack`: the slack dictionary of `A *ᵥ x ≤ b`, its
  equational-form matrix `[A | 1]`, and a point extended by its slacks.
* `Cslib.Algorithms.Lean.Simplex.Dictionary.slackDual`: the negated reduced costs of the slack
  variables of a dictionary, the dual solution read off the final dictionary.

## Main results

* `Dictionary.simplex_spec_of_represents`: the simplex method with Bland's rule, started from a
  feasible dictionary representing `max c ⬝ᵥ x` subject to `x ≥ 0`, `A *ᵥ x = b`, returns an
  optimal basic feasible solution or proves the program unbounded.
* `Dictionary.Represents.eq_zero_of_mulVec_eq_zero`: the basic columns of `A` are linearly
  independent (no nonzero kernel vector of `A` is supported on the basis), so the basic solution
  of a representing dictionary is a basic solution of `A *ᵥ x = b`.
* `simplex_slackDictionary_spec`: the simplex method solves `max c ⬝ᵥ x` subject to `x ≥ 0`,
  `A *ᵥ x ≤ b` when `b ≥ 0`.
* `slackDual_nonneg`, `le_slackDual_vecMul`, `slackDual_dotProduct`,
  `isLeast_dotProduct_slackDual`: when the simplex method on the slack dictionary stops at an
  optimal dictionary `D`, `D.slackDual` is a feasible solution of the dual program
  `min y ⬝ᵥ b` subject to `y ≥ 0`, `c ≤ y ᵥ* A` whose value is the primal optimum
  `D.objConst`, hence (by weak duality) an optimal one ([Chvatal1983], Chapter 5).

## Limitations

Only programs with a feasible starting dictionary are covered: for `A *ᵥ x ≤ b`, `x ≥ 0` this is
the hypothesis `b ≥ 0`. Phase I is not formalized. Strong duality itself is already in
`Complexity.Foundations.LinearAlgebra.Matrix.LinearProgramming`, whose weak duality is used here;
the dual solution `slackDual` is the explicit by-product of the simplex method.

## References

* [V. Chvátal, *Linear Programming*][Chvatal1983]
* [J. Matoušek and B. Gärtner, *Understanding and Using Linear Programming*][MatousekGartner2007]
-/

public section

namespace Cslib.Algorithms.Lean.Simplex

open Matrix

namespace Dictionary

section Represents

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- The dictionary `D` *represents* the linear program `max c ⬝ᵥ x` subject to `x ≥ 0`,
`A *ᵥ x = b`: its solutions are exactly the solutions of `A *ᵥ x = b`, and its objective agrees with
`c ⬝ᵥ x` on them. -/
structure Represents {m : Type*} [Fintype m] (D : Dictionary ι K) (A : Matrix m ι K)
    (b : m → K) (c : ι → K) : Prop where
  isSolution_iff : ∀ x, D.IsSolution x ↔ A *ᵥ x = b
  value_eq : ∀ x, A *ᵥ x = b → D.value x = c ⬝ᵥ x

namespace Represents

variable {m : Type*} [Fintype m] {D D' : Dictionary ι K} {A : Matrix m ι K} {b : m → K}
  {c : ι → K}

theorem of_equivalent (h : D.Represents A b c) (hD : D.Equivalent D') : D'.Represents A b c :=
  ⟨fun x => (hD.isSolution_iff x).symm.trans (h.isSolution_iff x),
    fun x hx => (hD.value_eq x ((h.isSolution_iff x).2 hx)).symm.trans (h.value_eq x hx)⟩

theorem mulVec_basicSolution (h : D.Represents A b c) : A *ᵥ D.basicSolution = b :=
  (h.isSolution_iff _).1 D.isSolution_basicSolution

/-- The basic columns of `A` are linearly independent: no nonzero vector of the kernel of `A` is
supported on the basis of a representing dictionary, so the basic solution of the dictionary is a
basic solution of `A *ᵥ x = b`. -/
theorem eq_zero_of_mulVec_eq_zero (h : D.Represents A b c) {w : ι → K}
    (hw : ∀ j ∉ D.basis, w j = 0) (hAw : A *ᵥ w = 0) : w = 0 := by
  have hsol : D.IsSolution (D.basicSolution + w) := by
    rw [h.isSolution_iff, mulVec_add, hAw, add_zero, h.mulVec_basicSolution]
  have := D.eq_basicSolution_of_isSolution hsol fun j hj => by
    rw [Pi.add_apply, D.basicSolution_of_notMem hj, hw j hj, add_zero]
  exact left_eq_add.1 this.symm

variable [LinearOrder K]

theorem feasibleSet_eq (h : D.Represents A b c) :
    D.feasibleSet = {x | 0 ≤ x ∧ A *ᵥ x = b} := by
  ext x
  rw [mem_feasibleSet, and_comm]
  exact and_congr_right' (h.isSolution_iff x)

theorem image_value_feasibleSet (h : D.Represents A b c) :
    D.value '' D.feasibleSet = (c ⬝ᵥ ·) '' {x | 0 ≤ x ∧ A *ᵥ x = b} := by
  rw [h.feasibleSet_eq]
  exact Set.image_congr fun x hx => h.value_eq x hx.2

end Represents

end Represents

variable {ι K : Type*} [Fintype ι] [LinearOrder ι] [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-- **The simplex method with Bland's rule for `max c ⬝ᵥ x` subject to `x ≥ 0`, `A *ᵥ x = b`**,
started from a feasible dictionary `D` representing the program: it returns a dictionary `D'`
representing the same program whose basic solution is an optimal basic feasible solution, or it
proves the objective unbounded on the feasible set. -/
theorem simplex_spec_of_represents {m : Type*} [Fintype m] {D : Dictionary ι K}
    {A : Matrix m ι K} {b : m → K} {c : ι → K} (h : D.Represents A b c) (hD : D.Feasible) :
    (∃ D', D.simplex = .optimal D' ∧ D'.Represents A b c ∧ D'.Feasible ∧
      A *ᵥ D'.basicSolution = b ∧ 0 ≤ D'.basicSolution ∧
      IsGreatest ((c ⬝ᵥ ·) '' {x | 0 ≤ x ∧ A *ᵥ x = b}) (c ⬝ᵥ D'.basicSolution)) ∨
    ((∃ D' s, D.simplex = .unbounded D' s) ∧
      ¬BddAbove ((c ⬝ᵥ ·) '' {x | 0 ≤ x ∧ A *ᵥ x = b})) := by
  rcases D.simplex_spec hD with ⟨D', hrun, hequiv, hD', hgreat⟩ | ⟨hrun, hunb⟩
  · have h' := h.of_equivalent hequiv
    refine .inl ⟨D', hrun, h', hD', h'.mulVec_basicSolution,
      D'.feasible_iff_nonneg_basicSolution.1 hD', ?_⟩
    rw [← h'.value_eq _ h'.mulVec_basicSolution, D'.value_basicSolution,
      ← h.image_value_feasibleSet]
    exact hgreat
  · exact .inr ⟨hrun, h.image_value_feasibleSet ▸ hunb⟩

end Dictionary

/-! ### The slack dictionary of `max c ⬝ᵥ x` subject to `x ≥ 0`, `A *ᵥ x ≤ b` -/

section Slack

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}

/-- The **slack dictionary** of `max c ⬝ᵥ x` subject to `x ≥ 0`, `A *ᵥ x ≤ b`
([Chvatal1983], Chapter 2): the variables are `Fin (n + m)`, with the original variable `j` at
`Fin.castAdd m j` and the slack variable of row `i` at `Fin.natAdd n i`; the slack variables are
basic, with `x (natAdd n i) = b i - ∑ j, A i j * x (castAdd m j)`, and the objective is
`∑ j, c j * x (castAdd m j)`. -/
@[expose] def slackDictionary (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K) :
    Dictionary (Fin (n + m)) K where
  basis := Finset.univ.filter fun i => n ≤ i.val
  rhs := Fin.append 0 b
  coeff := Fin.append 0 fun i => Fin.append (fun j => -A i j) 0
  objConst := 0
  objCoeff := Fin.append c 0

/-- The constraint matrix `[A | 1]` of the equational form of `A *ᵥ x ≤ b`. -/
def slackMatrix (A : Matrix (Fin m) (Fin n) K) : Matrix (Fin m) (Fin (n + m)) K :=
  Matrix.of fun i => Fin.append (A i) (Pi.single i 1)

/-- The point `x` extended by its slacks `b - A *ᵥ x`. -/
def withSlack (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (x : Fin n → K) :
    Fin (n + m) → K :=
  Fin.append x (b - A *ᵥ x)

variable (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (c : Fin n → K)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem mem_slackDictionary_basis {i : Fin (n + m)} :
    i ∈ (slackDictionary A b c).basis ↔ n ≤ i.val := by
  simp only [slackDictionary, Finset.mem_filter, Finset.mem_univ, true_and]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem castAdd_notMem_slackDictionary_basis (j : Fin n) :
    Fin.castAdd m j ∉ (slackDictionary A b c).basis := by
  rw [mem_slackDictionary_basis, Fin.val_castAdd, not_le]
  exact j.isLt

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem natAdd_mem_slackDictionary_basis (i : Fin m) :
    Fin.natAdd n i ∈ (slackDictionary A b c).basis := by
  rw [mem_slackDictionary_basis, Fin.val_natAdd]
  exact Nat.le_add_right n i

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem sum_compl_slack (f : Fin (n + m) → K) :
    ∑ j ∈ (slackDictionary A b c).basisᶜ, f j = ∑ j : Fin n, f (Fin.castAdd m j) := by
  rw [← Finset.univ_inter (slackDictionary A b c).basisᶜ, ← Finset.sum_ite_mem,
    Fin.sum_univ_add]
  simp only [Finset.mem_compl, castAdd_notMem_slackDictionary_basis,
    natAdd_mem_slackDictionary_basis, not_false_eq_true, not_true_eq_false, ↓reduceIte,
    Finset.sum_const_zero, add_zero]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem isSolution_slackDictionary_iff {x : Fin (n + m) → K} :
    (slackDictionary A b c).IsSolution x ↔
      ∀ i, x (Fin.natAdd n i) = b i - ∑ j, A i j * x (Fin.castAdd m j) := by
  have key : ∀ i, (slackDictionary A b c).rhs (Fin.natAdd n i) +
      ∑ j ∈ (slackDictionary A b c).basisᶜ,
        (slackDictionary A b c).coeff (Fin.natAdd n i) j * x j =
      b i - ∑ j, A i j * x (Fin.castAdd m j) := by
    intro i
    rw [sum_compl_slack]
    simp only [slackDictionary, Fin.append_right, Fin.append_left, neg_mul,
      Finset.sum_neg_distrib, sub_eq_add_neg]
  constructor
  · intro h i
    rw [h _ (natAdd_mem_slackDictionary_basis A b c i), key]
  · intro h i hi
    induction i using Fin.addCases with
    | left j => exact absurd hi (castAdd_notMem_slackDictionary_basis A b c j)
    | right i => rw [h i, key]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem slackMatrix_mulVec (x : Fin (n + m) → K) (i : Fin m) :
    (slackMatrix A *ᵥ x) i = ∑ j, A i j * x (Fin.castAdd m j) + x (Fin.natAdd n i) := by
  simp only [slackMatrix, mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right]
  congr 1
  rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_mul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_mul]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The slack dictionary represents the equational form `[A | 1] *ᵥ z = b`, `z ≥ 0` of
`A *ᵥ x ≤ b`, `x ≥ 0`, with the objective `c` extended by zeros. -/
theorem slackDictionary_represents :
    (slackDictionary A b c).Represents (slackMatrix A) b (Fin.append c 0) := by
  constructor
  · intro x
    rw [isSolution_slackDictionary_iff, funext_iff]
    refine forall_congr' fun i => ?_
    rw [slackMatrix_mulVec]
    constructor <;> intro h <;> linear_combination h
  · intro x _
    rw [Dictionary.value, sum_compl_slack, dotProduct, Fin.sum_univ_add]
    simp only [slackDictionary, Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero, zero_add]

omit [IsStrictOrderedRing K] in
/-- The slack dictionary is feasible exactly when `b ≥ 0`. -/
theorem feasible_slackDictionary_iff : (slackDictionary A b c).Feasible ↔ 0 ≤ b := by
  constructor
  · intro h i
    have := h _ (natAdd_mem_slackDictionary_basis A b c i)
    simp only [slackDictionary, Fin.append_right] at this
    exact this
  · intro hb i hi
    induction i using Fin.addCases with
    | left j => exact absurd hi (castAdd_notMem_slackDictionary_basis A b c j)
    | right i => simp only [slackDictionary, Fin.append_right]; exact hb i

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem withSlack_castAdd (x : Fin n → K) (j : Fin n) :
    withSlack A b x (Fin.castAdd m j) = x j := Fin.append_left _ _ _

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem withSlack_natAdd (x : Fin n → K) (i : Fin m) :
    withSlack A b x (Fin.natAdd n i) = b i - (A *ᵥ x) i := Fin.append_right _ _ _

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem isSolution_withSlack (x : Fin n → K) :
    (slackDictionary A b c).IsSolution (withSlack A b x) := by
  rw [isSolution_slackDictionary_iff]
  intro i
  simp only [withSlack_natAdd, withSlack_castAdd, mulVec, dotProduct]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Every solution of the slack dictionary is a point extended by its slacks. -/
theorem eq_withSlack_of_isSolution {z : Fin (n + m) → K}
    (hz : (slackDictionary A b c).IsSolution z) :
    z = withSlack A b (fun j => z (Fin.castAdd m j)) := by
  rw [isSolution_slackDictionary_iff] at hz
  funext i
  induction i using Fin.addCases with
  | left j => rw [withSlack_castAdd]
  | right i => rw [withSlack_natAdd, hz i]; rfl

theorem withSlack_mem_feasibleSet_iff (x : Fin n → K) :
    withSlack A b x ∈ (slackDictionary A b c).feasibleSet ↔ 0 ≤ x ∧ A *ᵥ x ≤ b := by
  rw [Dictionary.mem_feasibleSet]
  simp only [isSolution_withSlack, true_and, Pi.le_def, Pi.zero_apply]
  rw [Fin.forall_fin_add]
  simp only [withSlack_castAdd, withSlack_natAdd, sub_nonneg]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem value_withSlack (x : Fin n → K) :
    (slackDictionary A b c).value (withSlack A b x) = c ⬝ᵥ x := by
  rw [(slackDictionary_represents A b c).value_eq _
    ((slackDictionary_represents A b c).isSolution_iff _ |>.1 (isSolution_withSlack A b c x)),
    dotProduct, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, withSlack_castAdd, dotProduct]

/-- The slack dictionary describes the program `max c ⬝ᵥ x` subject to `x ≥ 0`, `A *ᵥ x ≤ b`. -/
theorem image_value_slackDictionary :
    (slackDictionary A b c).value '' (slackDictionary A b c).feasibleSet =
      (c ⬝ᵥ ·) '' {x | 0 ≤ x ∧ A *ᵥ x ≤ b} := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzx := eq_withSlack_of_isSolution A b c ((Dictionary.mem_feasibleSet _).1 hz).1
    rw [hzx] at hz ⊢
    exact ⟨_, (withSlack_mem_feasibleSet_iff A b c _).1 hz, (value_withSlack A b c _).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, (withSlack_mem_feasibleSet_iff A b c x).2 hx, value_withSlack A b c x⟩

/-- **The simplex method with Bland's rule for `max c ⬝ᵥ x` subject to `x ≥ 0`, `A *ᵥ x ≤ b`**
with `b ≥ 0`, started from the slack dictionary: it finds an optimal solution, read off the
first `n` coordinates of the final basic solution, or proves the objective unbounded. -/
theorem simplex_slackDictionary_spec (hb : 0 ≤ b) :
    (∃ D, (slackDictionary A b c).simplex = .optimal D ∧
      IsGreatest ((c ⬝ᵥ ·) '' {x | 0 ≤ x ∧ A *ᵥ x ≤ b}) D.objConst ∧
      0 ≤ (fun j => D.basicSolution (Fin.castAdd m j)) ∧
      A *ᵥ (fun j => D.basicSolution (Fin.castAdd m j)) ≤ b ∧
      c ⬝ᵥ (fun j => D.basicSolution (Fin.castAdd m j)) = D.objConst) ∨
    ((∃ D s, (slackDictionary A b c).simplex = .unbounded D s) ∧
      ¬BddAbove ((c ⬝ᵥ ·) '' {x | 0 ≤ x ∧ A *ᵥ x ≤ b})) := by
  set S := slackDictionary A b c
  rcases S.simplex_spec ((feasible_slackDictionary_iff A b c).2 hb) with
    ⟨D, hrun, hequiv, hD, hgreat⟩ | ⟨hrun, hunb⟩
  · rw [image_value_slackDictionary] at hgreat
    have hsolS : S.IsSolution D.basicSolution :=
      (hequiv.isSolution_iff _).2 D.isSolution_basicSolution
    have hz := eq_withSlack_of_isSolution A b c hsolS
    have hmem : D.basicSolution ∈ S.feasibleSet :=
      (Dictionary.mem_feasibleSet _).2 ⟨hsolS, D.feasible_iff_nonneg_basicSolution.1 hD⟩
    rw [hz] at hmem
    obtain ⟨h1, h2⟩ := (withSlack_mem_feasibleSet_iff A b c _).1 hmem
    refine .inl ⟨D, hrun, hgreat, h1, h2, ?_⟩
    rw [← value_withSlack A b c, ← hz, hequiv.value_eq _ hsolS, D.value_basicSolution]
  · rw [image_value_slackDictionary] at hunb
    exact .inr ⟨hrun, hunb⟩

/-- The **dual solution read off a dictionary** on the variables of a slack dictionary: the
negated reduced cost of the slack variable of each row, and `0` when that slack variable is basic.
For the final dictionary of the simplex method on `slackDictionary A b c` this is an optimal
solution of the dual program (`isLeast_dotProduct_slackDual`). -/
@[expose] def Dictionary.slackDual (D : Dictionary (Fin (n + m)) K) (i : Fin m) : K :=
  if Fin.natAdd n i ∈ D.basis then 0 else -D.objCoeff (Fin.natAdd n i)

/-- The three dual facts at once: the read-off `D.slackDual` is nonnegative, satisfies
`c ≤ y ᵥ* A` and has value `D.objConst`. -/
private theorem slackDual_spec (hb : 0 ≤ b) {D : Dictionary (Fin (n + m)) K}
    (h : (slackDictionary A b c).simplex = .optimal D) :
    0 ≤ D.slackDual ∧ c ≤ D.slackDual ᵥ* A ∧ D.slackDual ⬝ᵥ b = D.objConst := by
  set S := slackDictionary A b c
  obtain ⟨hequiv, -, -, hopt⟩ := S.run_eq_optimal ((feasible_slackDictionary_iff A b c).2 hb) h
  set g : Fin (n + m) → K := fun j => if j ∈ D.basis then 0 else D.objCoeff j with hg
  have hgle : ∀ j, g j ≤ 0 := fun j => by
    simp only [hg]; split_ifs with hj
    · exact le_rfl
    · exact hopt j hj
  have hvalue : ∀ z, D.value z = D.objConst + ∑ j, g j * z j := fun z => by
    rw [Dictionary.value, ← Finset.sum_compl_add_sum D.basis, Finset.sum_eq_zero (s := D.basis)
      fun j hj => by simp only [hg, hj, ↓reduceIte, zero_mul], add_zero]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by
      simp only [hg, Finset.mem_compl.1 hj, ↓reduceIte]
  have hy : D.slackDual = fun i => -g (Fin.natAdd n i) := funext fun i => by
    simp only [Dictionary.slackDual, hg]
    split_ifs <;> simp only [neg_zero]
  set y := D.slackDual
  have key : ∀ x : Fin n → K, c ⬝ᵥ x =
      D.objConst - y ⬝ᵥ b + ∑ k, g (Fin.castAdd m k) * x k + (y ᵥ* A) ⬝ᵥ x := by
    intro x
    rw [← value_withSlack A b c, hequiv.value_eq _ (isSolution_withSlack A b c x), hvalue,
      Fin.sum_univ_add, ← dotProduct_mulVec, hy]
    simp only [withSlack_castAdd, withSlack_natAdd, dotProduct, mul_sub,
      Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib]
    ring
  have hv : y ⬝ᵥ b = D.objConst := by
    have := key 0
    simp only [dotProduct_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      add_zero] at this
    linarith
  refine ⟨fun i => ?_, fun k => ?_, hv⟩
  · rw [hy]
    exact neg_nonneg.2 (hgle _)
  have := key (Pi.single k 1)
  rw [dotProduct_single_one, dotProduct_single_one, hv, sub_self, zero_add] at this
  rw [Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
    (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, mul_one] at this
  linarith [hgle (Fin.castAdd m k)]

/-- The dual solution read off the final dictionary is nonnegative ([Chvatal1983], Chapter 5):
the reduced costs of the final dictionary are nonpositive. -/
theorem slackDual_nonneg (hb : 0 ≤ b) {D : Dictionary (Fin (n + m)) K}
    (h : (slackDictionary A b c).simplex = .optimal D) : 0 ≤ D.slackDual :=
  (slackDual_spec A b c hb h).1

/-- The dual solution read off the final dictionary satisfies the dual constraints
`c ≤ y ᵥ* A` ([Chvatal1983], Chapter 5). -/
theorem le_slackDual_vecMul (hb : 0 ≤ b) {D : Dictionary (Fin (n + m)) K}
    (h : (slackDictionary A b c).simplex = .optimal D) : c ≤ D.slackDual ᵥ* A :=
  (slackDual_spec A b c hb h).2.1

/-- The dual solution read off the final dictionary has value `D.objConst`, the primal
optimum ([Chvatal1983], Chapter 5). -/
theorem slackDual_dotProduct (hb : 0 ≤ b) {D : Dictionary (Fin (n + m)) K}
    (h : (slackDictionary A b c).simplex = .optimal D) : D.slackDual ⬝ᵥ b = D.objConst :=
  (slackDual_spec A b c hb h).2.2

/-- **The final dictionary certifies dual optimality** ([Chvatal1983], Chapter 5). When the simplex
method on the slack dictionary stops at an optimal dictionary `D`, `D.slackDual` is a feasible
solution of the dual program `min y ⬝ᵥ b` subject to `y ≥ 0`, `c ≤ y ᵥ* A`, and `D.objConst` is
the least dual value: by weak duality
(`Matrix.dotProduct_le_dotProduct_of_nonneg_of_mulVec_le`) no dual solution is below the primal
optimum `D.objConst`, which `D.slackDual` attains. -/
theorem isLeast_dotProduct_slackDual (hb : 0 ≤ b) {D : Dictionary (Fin (n + m)) K}
    (h : (slackDictionary A b c).simplex = .optimal D) :
    D.slackDual ∈ {y | 0 ≤ y ∧ c ≤ y ᵥ* A} ∧
      IsLeast ((· ⬝ᵥ b) '' {y | 0 ≤ y ∧ c ≤ y ᵥ* A}) D.objConst := by
  obtain ⟨hy, hcy, hyb⟩ := slackDual_spec A b c hb h
  refine ⟨⟨hy, hcy⟩, ⟨D.slackDual, ⟨hy, hcy⟩, hyb⟩, ?_⟩
  rintro _ ⟨y', ⟨hy', hcy'⟩, rfl⟩
  rcases simplex_slackDictionary_spec A b c hb with
    ⟨D', hD', -, hx, hAx, hval⟩ | ⟨⟨D', s, hD'⟩, -⟩
  · rw [h] at hD'
    cases hD'
    rw [← hval]
    exact dotProduct_le_dotProduct_of_nonneg_of_mulVec_le hx hAx hy' hcy'
  · rw [h] at hD'
    cases hD'

end Slack

end Cslib.Algorithms.Lean.Simplex
