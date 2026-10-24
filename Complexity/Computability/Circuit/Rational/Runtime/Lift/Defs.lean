/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.Executable
public import Complexity.Computability.Circuit.Rational.Runtime.Determinant
import Mathlib.Data.List.GetD

/-!
# List programs and evaluation equivalences for the integer lift tables

At every grid point the executable generator materializes the integer lift matrices
`Rational.Generator.integralLift`, built from the integer Taylor test matrices
`Rational.IntegralTest.padded` and the signed-monomial formula `Rational.IntegralLift.entry`.
Those definitions are indexed by `Fin` and `ZMod` with a type-level modulus, and use `Nat.choose`.
This file restates them as ordinary programs on natural numbers, integers and lists of rows, and
proves that they compute the landed matrix definitions:

* the coefficients of `(X + c) ^ k` are computed by `k` shift-and-add steps (`coeffRow`), with no
  division;
* the Taylor test matrix is a list of rows of sums over `List.range M` (`testRows`);
* every lift entry is a double sum over `List.range M` of `M ^ 2` terms (`liftEntry`, `liftTable`,
  `liftRows`). The original formula sums over three residues; the residue `β` is forced to be
  `u - v`, so that sum is dropped.

Magnitude bounds, bit-length budgets, and polynomial-time Turing machine certificates for these list
programs are proved in `Complexity/Computability/Circuit/Rational/Runtime/Lift.lean`.

## Main definitions

* `Cslib.Circuits.Rational.shiftAddRow`, `Cslib.Circuits.Rational.coeffRow`,
  `Cslib.Circuits.Rational.coeffRows`: the coefficients of `(X + c) ^ k`, by repeated shift-and-add.
* `Cslib.Circuits.Rational.testTerm`, `Cslib.Circuits.Rational.testTerms`,
  `Cslib.Circuits.Rational.testEntry`, `Cslib.Circuits.Rational.testRows`: the integer Taylor test
  matrix as a list of rows.
* `Cslib.Circuits.Rational.signedCoeff`, `Cslib.Circuits.Rational.liftTerm`,
  `Cslib.Circuits.Rational.liftTerms`, `Cslib.Circuits.Rational.liftSums`,
  `Cslib.Circuits.Rational.liftEntry`: the signed coefficient of the cyclotomic regular
  representation, and the terms and entries of the integer lift.
* `Cslib.Circuits.Rational.liftTable`, `Cslib.Circuits.Rational.liftRows`: one integer lift matrix,
  and all of them at a grid point.

## Main results

* `Cslib.Circuits.Rational.getD_coeffRow`, `Cslib.Circuits.Rational.getD_coeffRow_eq`: `coeffRow`
  computes the coefficients of `(X + C c) ^ k`.
* `Cslib.Circuits.Rational.testEntry_eq`, `Cslib.Circuits.Rational.testRows_eq`:
  `testRows M N a t = rowsOf (IntegralTest.padded M N a t)`.
* `Cslib.Circuits.Rational.liftEntry_eq`: the double sum computes `IntegralLift.entry`.
* `Cslib.Circuits.Rational.liftTable_eq`, `Cslib.Circuits.Rational.liftRows_eq`,
  `Cslib.Circuits.Rational.liftRows_eq_inputTables`: the lift tables are the rows of
  `Generator.integralLift`, and of the executable generator's `inputTables`.

## References

* The index bridges and the forms of `signedCoeff`, `testTerm` and the lift sum are adapted from
  OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (files
  lean/OAI/Computability/RationalHitting/TaylorComputation.lean and LiftComputation.lean), via
  the complexitylib port [Schlesinger2026RationalHitting] at revision
  add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Rational

open Polynomial

/-! ### Index bridges -/

private lemma val_finEquiv {m : ℕ} [NeZero m] (i : Fin m) : (ZMod.finEquiv m i).val = i.val := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m => rfl

lemma val_finEquiv_symm {m : ℕ} [NeZero m] (z : ZMod m) :
    ((ZMod.finEquiv m).symm z).val = z.val := by
  rw [← val_finEquiv, RingEquiv.apply_symm_apply]

/-- A sum over `List.range m` is a sum over `Fin m`. -/
private lemma sum_range_eq_sum_fin {A : Type*} [AddCommMonoid A] (m : ℕ) (f : ℕ → A) :
    ((List.range m).map f).sum = ∑ i : Fin m, f i := by
  rw [← List.map_coe_finRange_eq_range, List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
  rfl

/-- A sum over `List.range m` is a sum over the residues modulo `m`. -/
private lemma sum_range_eq_sum_zmod {A : Type*} [AddCommMonoid A] (m : ℕ) [NeZero m] (f : ℕ → A) :
    ((List.range m).map f).sum = ∑ z : ZMod m, f z.val := by
  rw [sum_range_eq_sum_fin]
  exact Fintype.sum_equiv (ZMod.finEquiv m).toEquiv _ _ fun i => by
    change f i.val = f (ZMod.finEquiv m i).val
    rw [val_finEquiv]

/-- Residue subtraction on values, without truncated subtraction below zero. -/
private lemma val_sub_eq_mod {m : ℕ} [NeZero m] (u v : ZMod m) :
    (u - v).val = (u.val + m - v.val) % m := by
  have hv := v.val_lt
  rw [← ZMod.val_natCast, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, add_zero]

/-- The residue `-a * k + a * u` of the lift formula, on values. -/
private lemma val_neg_mul_add_mul_eq_mod {m : ℕ} [NeZero m] (a u k : ZMod m) :
    (-a * k + a * u).val = a.val * (u.val + m - k.val) % m := by
  have hk := k.val_lt
  rw [← ZMod.val_natCast, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  congr 1
  ring

/-- The residue of the row-major block coordinate is the quotient by the degree. -/
lemma val_coordinate_symm_fst (e : ℕ) (i : Fin (Generator.matrixDimension e)) :
    ((Generator.coordinate e).symm i).1.val = i.val / CyclotomicRing.degree e := by
  change (ZMod.finEquiv _ (finProdFinEquiv.symm i).1).val = _
  rw [val_finEquiv]
  rfl

/-- The position inside the block of the row-major block coordinate is the remainder. -/
lemma val_coordinate_symm_snd (e : ℕ) (i : Fin (Generator.matrixDimension e)) :
    ((Generator.coordinate e).symm i).2.val = i.val % CyclotomicRing.degree e :=
  rfl

/-! ### Lists of rows -/

/-- A tabulated list of rows is the list of rows of a matrix it agrees with. -/
lemma tabulateRows_eq_rowsOf {d : ℕ} (g : ℕ → ℕ → ℤ) (A : Matrix (Fin d) (Fin d) ℤ)
    (h : ∀ i j : Fin d, g i j = A i j) : tabulateRows d g = rowsOf A := by
  simp only [tabulateRows, rowsOf, ← List.map_coe_finRange_eq_range, List.map_map]
  exact List.map_congr_left fun i _ => List.map_congr_left fun j _ => h i j

/-- Every stored entry is bounded once every indexed entry is. -/
lemma natAbs_le_of_mem_rows {rows : List (List ℤ)} {C : ℕ}
    (h : ∀ i j, (rowEntry rows i j).natAbs ≤ C) {row : List ℤ} (hrow : row ∈ rows) {z : ℤ}
    (hz : z ∈ row) : z.natAbs ≤ C := by
  obtain ⟨i, j, rfl⟩ := exists_rowEntry_eq hrow hz
  exact h i j

/-! ### Coefficient rows -/

/-- Multiply a polynomial by `X + c`. The polynomial is given by its list of coefficients,
constant coefficient first; coefficient `i` of the product is `l[i - 1] + c * l[i]`. -/
def shiftAddRow (c : ℤ) (l : List ℤ) : List ℤ :=
  (List.range (l.length + 1)).map fun i => (0 :: l).getD i 0 + c * l.getD i 0

/-- The coefficients of `(X + c) ^ k`, constant coefficient first, computed by `k` shift-and-add
steps from `[1]`. -/
def coeffRow (c : ℤ) (k : ℕ) : List ℤ :=
  (shiftAddRow c)^[k] [1]

/-- The coefficient rows `coeffRow c k` for `k < M`. -/
def coeffRows (c : ℤ) (M : ℕ) : List (List ℤ) :=
  (List.range M).map (coeffRow c)

@[simp] lemma length_shiftAddRow (c : ℤ) (l : List ℤ) :
    (shiftAddRow c l).length = l.length + 1 := by
  simp [shiftAddRow]

lemma getD_shiftAddRow (c : ℤ) (l : List ℤ) (i : ℕ) :
    (shiftAddRow c l).getD i 0 = (0 :: l).getD i 0 + c * l.getD i 0 := by
  rcases Nat.lt_or_ge i (l.length + 1) with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [shiftAddRow]
  · rw [List.getD_eq_default _ _ (by simpa using h), List.getD_eq_default _ _ (by simpa using h),
      List.getD_eq_default _ _ (by omega)]
    simp

@[simp] lemma coeffRow_zero (c : ℤ) : coeffRow c 0 = [1] := rfl

lemma coeffRow_succ (c : ℤ) (k : ℕ) : coeffRow c (k + 1) = shiftAddRow c (coeffRow c k) :=
  Function.iterate_succ_apply' _ _ _

@[simp] lemma length_coeffRow (c : ℤ) (k : ℕ) : (coeffRow c k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [coeffRow_succ, length_shiftAddRow, ih]

/-- `coeffRow` computes the coefficients of `(X + C c) ^ k`. -/
theorem getD_coeffRow (c : ℤ) (k i : ℕ) :
    (coeffRow c k).getD i 0 = ((X + C c) ^ k).coeff i := by
  induction k generalizing i with
  | zero => cases i <;> simp [coeff_one]
  | succ k ih =>
    rw [coeffRow_succ, getD_shiftAddRow, pow_succ, mul_add, coeff_add, coeff_mul_C, ih]
    cases i with
    | zero => simp [mul_comm]
    | succ i => rw [List.getD_cons_succ, ih, coeff_mul_X, mul_comm c]

/-- The closed form of the coefficient rows, as in `IntegralTest.full`. -/
theorem getD_coeffRow_eq (c : ℤ) (k i : ℕ) :
    (coeffRow c k).getD i 0 = c ^ (k - i) * (k.choose i : ℤ) := by
  rw [getD_coeffRow, coeff_X_add_C_pow]

lemma rowEntry_coeffRows (c : ℤ) (M k i : ℕ) :
    rowEntry (coeffRows c M) k i = if k < M then (coeffRow c k).getD i 0 else 0 := by
  unfold rowEntry coeffRows
  split_ifs with h
  · rw [List.getD_eq_getElem ((List.range M).map (coeffRow c)) _ (by simpa using h),
      List.getElem_map, List.getElem_range]
  · rw [List.getD_eq_default ((List.range M).map (coeffRow c)) _ (by simpa using h)]
    rfl

/-! ### The integer Taylor test matrix -/

/-- The summand `q` of entry `(u, v)` of the integer Taylor test matrix: coefficient `u` of
`(X - a) ^ (M - 1 - q)` times coefficient `q` of `(X + a) ^ v` times `t ^ q`, read from the
coefficient rows `minus` and `plus`. -/
def testTerm (M : ℕ) (minus plus : List (List ℤ)) (t : ℤ) (u v q : ℕ) : ℤ :=
  rowEntry minus (M - 1 - q) u * rowEntry plus v q * t ^ q

/-- The summands of entry `(u, v)` of the integer Taylor test matrix. -/
def testTerms (M : ℕ) (minus plus : List (List ℤ)) (t : ℤ) (u v : ℕ) : List ℤ :=
  (List.range M).map (testTerm M minus plus t u v)

/-- Entry `(u, v)` of the integer Taylor test matrix; the columns from `N` on are zero. -/
def testEntry (M N : ℕ) (minus plus : List (List ℤ)) (t : ℤ) (u v : ℕ) : ℤ :=
  if v < N then (testTerms M minus plus t u v).sum else 0

/-- The integer Taylor test matrix `IntegralTest.padded M N a t` as a list of rows. -/
def testRows (M N : ℕ) (a t : ℤ) : List (List ℤ) :=
  tabulateRows M (testEntry M N (coeffRows (-a) M) (coeffRows a M) t)

theorem testEntry_eq (M N : ℕ) (a t : ℤ) (u v : Fin M) :
    testEntry M N (coeffRows (-a) M) (coeffRows a M) t u v = IntegralTest.padded M N a t u v := by
  unfold testEntry IntegralTest.padded IntegralTest.full
  split_ifs
  · rw [testTerms, sum_range_eq_sum_fin]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq := q.isLt
    rw [testTerm, rowEntry_coeffRows, rowEntry_coeffRows, ite_eq_left (by omega),
      ite_eq_left v.isLt, getD_coeffRow_eq, getD_coeffRow_eq, Fin.val_rev,
      show M - (q.val + 1) = M - 1 - q by omega]
  · rfl

private theorem rowEntry_testRows (M N : ℕ) (a t : ℤ) (u v : Fin M) :
    rowEntry (testRows M N a t) u v = IntegralTest.padded M N a t u v := by
  rw [testRows, rowEntry_tabulateRows, ite_eq_left ⟨u.isLt, v.isLt⟩, testEntry_eq]

/-- The list program computes the integer Taylor test matrix. -/
theorem testRows_eq (M N : ℕ) (a t : ℤ) :
    testRows M N a t = rowsOf (IntegralTest.padded M N a t) :=
  tabulateRows_eq_rowsOf _ _ (testEntry_eq M N a t)

/-- The Taylor rows, read at residues, are the residue-indexed `Generator.integerTest`. -/
private theorem rowEntry_testRows_integerTest (N e : ℕ) (a t : ℤ)
    (u v : ZMod (CyclotomicRing.dimension e)) :
    rowEntry (testRows (CyclotomicRing.dimension e) N a t) u.val v.val =
      Generator.integerTest N e a t u v := by
  rw [← val_finEquiv_symm u, ← val_finEquiv_symm v, rowEntry_testRows]
  rfl

@[simp] lemma length_testRows (M N : ℕ) (a t : ℤ) : (testRows M N a t).length = M :=
  length_tabulateRows _ _

/-! ### The integer lift -/

/-- The signed coefficient of the cyclotomic regular representation on natural numbers:
`CyclotomicRing.signedEntry` with the residue replaced by its value. -/
def signedCoeff (Dg z i j : ℕ) : ℤ :=
  if (z + j) % Dg = i then (-1) ^ ((z + j) / Dg) else 0

/-- The term `(α, κ)` of entry `((u, i), (v, j))` of the integer lift with test matrix `T`, with
`M` residues and cyclotomic degree `Dg`. The residue `β` of `IntegralLift.entry` is forced to be
`u - v`, which is `(u + M - v) % M`; `κ - β` and `α * (u - κ)` are computed likewise. -/
def liftTerm (M Dg : ℕ) (T : List (List ℤ)) (p r : ℤ) (u v i j α κ : ℕ) : ℤ :=
  rowEntry T κ ((κ + M - (u + M - v) % M) % M) * signedCoeff Dg (α * (u + M - κ) % M) i j *
    p ^ α * r ^ ((u + M - v) % M)

/-- The terms `κ < M` of the inner sum, for the residue `α`. -/
def liftTerms (M Dg : ℕ) (T : List (List ℤ)) (p r : ℤ) (u v i j α : ℕ) : List ℤ :=
  (List.range M).map (liftTerm M Dg T p r u v i j α)

/-- The inner sums `α < M` of an integer lift entry. -/
def liftSums (M Dg : ℕ) (T : List (List ℤ)) (p r : ℤ) (u v i j : ℕ) : List ℤ :=
  (List.range M).map fun α => (liftTerms M Dg T p r u v i j α).sum

/-- Entry `((u, i), (v, j))` of the integer lift: a double sum of `M ^ 2` terms. -/
def liftEntry (M Dg : ℕ) (T : List (List ℤ)) (p r : ℤ) (u v i j : ℕ) : ℤ :=
  (liftSums M Dg T p r u v i j).sum

/-- The integer lift matrix with test matrix `T`, in the row-major block order: index `i` is the
pair `(i / Dg, i % Dg)`. -/
def liftTable (M Dg : ℕ) (T : List (List ℤ)) (p r : ℤ) : List (List ℤ) :=
  tabulateRows (M * Dg) fun i j => liftEntry M Dg T p r (i / Dg) (j / Dg) (i % Dg) (j % Dg)

/-- The `n + 1` integer lift matrices at the grid point `(t, p, r)`, with truncation `N`, `M`
residues and cyclotomic degree `Dg`. -/
def liftRows (n N M Dg t p r : ℕ) : List (List (List ℤ)) :=
  (List.range (n + 1)).map fun a : ℕ => liftTable M Dg (testRows M N a t) p r

private lemma signedCoeff_eq (e : ℕ) (z : ZMod (CyclotomicRing.dimension e))
    (i j : Fin (CyclotomicRing.degree e)) :
    signedCoeff (CyclotomicRing.degree e) z.val i j = CyclotomicRing.signedEntry e z i j :=
  rfl

/-- The double sum computes the integer lift formula, for any list of rows that agrees with the
test matrix at residues. -/
theorem liftEntry_eq (e : ℕ) {T : List (List ℤ)}
    {T' : Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e)) ℤ}
    (hT : ∀ k l, rowEntry T (ZMod.val k) (ZMod.val l) = T' k l) (p r : ℤ)
    (u v : ZMod (CyclotomicRing.dimension e)) (i j : Fin (CyclotomicRing.degree e)) :
    liftEntry (CyclotomicRing.dimension e) (CyclotomicRing.degree e) T p r u.val v.val i j =
      IntegralLift.entry e T' p r u v i j := by
  have hβ (b : ZMod (CyclotomicRing.dimension e)) : u = v + b ↔ b = u - v := by
    constructor <;> intro h <;> subst h <;> ring
  unfold IntegralLift.entry liftEntry liftSums
  rw [sum_range_eq_sum_zmod]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, hβ, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [liftTerms, sum_range_eq_sum_zmod]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [liftTerm, ← val_sub_eq_mod u v, ← val_sub_eq_mod κ (u - v),
    ← val_neg_mul_add_mul_eq_mod α u κ, hT, signedCoeff_eq]

/-- The integer lift entry of `Generator.integralLift`, on the residues of the test rows. -/
private theorem liftEntry_testRows (N e : ℕ) (a t p r : ℤ) (u v : ZMod (CyclotomicRing.dimension e))
    (i j : Fin (CyclotomicRing.degree e)) :
    liftEntry (CyclotomicRing.dimension e) (CyclotomicRing.degree e)
        (testRows (CyclotomicRing.dimension e) N a t) p r u.val v.val i j =
      IntegralLift.entry e (Generator.integerTest N e a t) p r u v i j :=
  liftEntry_eq e (rowEntry_testRows_integerTest N e a t) p r u v i j

/-- The entries of a lift table are the entries of `Generator.integralLift`. -/
private theorem liftEntry_coordinate (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n + 1))
    (i j : Fin (Generator.matrixDimension e)) :
    liftEntry (CyclotomicRing.dimension e) (CyclotomicRing.degree e)
        (testRows (CyclotomicRing.dimension e) N a (x 0)) (x 1) (x 2)
        (i / CyclotomicRing.degree e) (j / CyclotomicRing.degree e)
        (i % CyclotomicRing.degree e) (j % CyclotomicRing.degree e) =
      Generator.integralLift n N e x a i j := by
  rw [← val_coordinate_symm_fst, ← val_coordinate_symm_fst, ← val_coordinate_symm_snd,
    ← val_coordinate_symm_snd, liftEntry_testRows]
  rfl

/-- The list program computes `Generator.integralLift`. -/
theorem liftTable_eq (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n + 1)) :
    liftTable (CyclotomicRing.dimension e) (CyclotomicRing.degree e)
        (testRows (CyclotomicRing.dimension e) N a (x 0)) (x 1) (x 2) =
      rowsOf (Generator.integralLift n N e x a) :=
  tabulateRows_eq_rowsOf _ _ (liftEntry_coordinate n N e x a)

theorem rowEntry_liftTable (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n + 1))
    (i j : Fin (Generator.matrixDimension e)) :
    rowEntry (liftTable (CyclotomicRing.dimension e) (CyclotomicRing.degree e)
        (testRows (CyclotomicRing.dimension e) N a (x 0)) (x 1) (x 2)) i j =
      Generator.integralLift n N e x a i j := by
  rw [liftTable_eq, rowEntry_rowsOf]

/-- The list program computes all integer lift matrices at a grid point. -/
theorem liftRows_eq (n N e : ℕ) (x : Fin 3 → ℕ) :
    liftRows n N (CyclotomicRing.dimension e) (CyclotomicRing.degree e) (x 0) (x 1) (x 2) =
      (List.finRange (n + 1)).map fun a => rowsOf (Generator.integralLift n N e x a) := by
  rw [liftRows, ← List.map_coe_finRange_eq_range, List.map_map]
  exact List.map_congr_left fun a _ => liftTable_eq n N e x a

/-- The list program computes the executable generator's dense input tables. -/
theorem liftRows_eq_inputTables (n N e : ℕ) (x : Fin 3 → ℕ) :
    liftRows n N (CyclotomicRing.dimension e) (CyclotomicRing.degree e) (x 0) (x 1) (x 2) =
      (ExecutableGenerator.inputTables n N e x).toList.map
        fun A => rowsOf (DeterminantAlgorithm.denote A) := by
  rw [liftRows_eq, ExecutableGenerator.inputTables, Vector.toList_ofFn, List.map_ofFn,
    List.ofFn_eq_map]
  exact List.map_congr_left fun a _ => by simp

@[simp] lemma length_liftTable (M Dg : ℕ) (T : List (List ℤ)) (p r : ℤ) :
    (liftTable M Dg T p r).length = M * Dg :=
  length_tabulateRows _ _

@[simp] lemma length_liftRows (n N M Dg t p r : ℕ) :
    (liftRows n N M Dg t p r).length = n + 1 := by
  simp [liftRows]

end Rational

end Cslib.Circuits
