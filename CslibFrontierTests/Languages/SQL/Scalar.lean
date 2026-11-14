/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module

public import CslibFrontier.Languages.SQL.Scalar

/-! Checked examples of SQL's scalar operators, `NULL` and `IN`, through an ordinary import. The
evaluations are computed by `rfl`, which unfolds the exposed evaluator; Batteries' `DecidableEq`
instance for `Except` does not expose its body, so `decide` cannot compare results. -/

public section

namespace CslibFrontierTests.SQL.Scalar

open Cslib.SQL

/-- The integer datum `z`. -/
abbrev i (z : ℤ) : Datum := some (.int z)

/-- The text datum `s`. -/
abbrev t (s : String) : Datum := some (.text s)

/-- The boolean datum `b`. -/
abbrev b (x : Bool) : Datum := some (.bool x)

/-! ### Arithmetic, `NULL` propagation and errors -/

example : evalBinOp (.arith .add) (i 2) (i 3) = .ok (i 5) := rfl
example : evalBinOp (.arith .add) (i 2) none = .ok none := rfl

-- `/` truncates toward zero and `%` takes the dividend's sign.
example : evalBinOp (.arith .div) (i (-7)) (i 2) = .ok (i (-3)) := rfl
example : evalBinOp (.arith .mod) (i (-7)) (i 2) = .ok (i (-1)) := rfl
example : evalBinOp (.arith .mod) (i 7) (i (-2)) = .ok (i 1) := rfl

-- `1 / 0` fails, while `NULL / 0` is `NULL`: `NULL` propagates before the division is attempted.
example : evalBinOp (.arith .div) (i 1) (i 0) = .error .divisionByZero := rfl
example : evalBinOp (.arith .div) none (i 0) = .ok none := rfl
example : evalBinOp (.arith .mod) (i 1) (i 0) = .error .divisionByZero := rfl

-- A non-null operand of the wrong type is a type error, even next to `NULL`.
example : evalBinOp (.arith .add) (i 1) (t "a") = .error .typeMismatch := rfl
example : evalBinOp (.arith .add) (t "a") none = .error .typeMismatch := rfl
example : evalBinOp (.arith .div) (b true) (i 0) = .error .typeMismatch := rfl
example : evalUnOp .neg (i 4) = .ok (i (-4)) := rfl
example : evalUnOp .neg (t "x") = .error .typeMismatch := rfl

-- `x * 0 = 0` and `x - x = 0` fail when `x` is `NULL`, so a rewriter cannot use them unguarded.
example : evalBinOp (.arith .mul) none (i 0) = .ok none := rfl
example : evalBinOp (.arith .sub) none none = .ok none := rfl

-- `a + 0 = a` needs an integer-typed `a`: on text it is a type error.
example : evalBinOp (.arith .add) (t "a") (i 0) = .error .typeMismatch := rfl
example (a : Datum) (ha : a.HasType .int) : evalBinOp (.arith .add) a (i 0) = .ok a :=
  evalBinOp_add_zero ha

/-! ### Comparisons -/

-- Text compares by code points: `'B' < 'a'` and `'ab' < 'b'`.
example : evalBinOp (.cmp .lt) (t "B") (t "a") = .ok (b true) := rfl
example : evalBinOp (.cmp .lt) (t "ab") (t "b") = .ok (b true) := rfl
example : evalBinOp (.cmp .lt) (b false) (b true) = .ok (b true) := rfl
example : evalBinOp (.cmp .ge) (i 2) (i 3) = .ok (b false) := rfl

-- `NULL = NULL` is `unknown`, represented as `NULL`; comparing different types is an error.
example : evalBinOp (.cmp .eq) none none = .ok none := rfl
example : evalBinOp (.cmp .ne) (i 1) none = .ok none := rfl
example : evalBinOp (.cmp .eq) (i 1) (t "1") = .error .typeMismatch := rfl

-- The rewriter's comparison facts, for symbolic datums.
example (x y : Datum) : evalBinOp (.cmp .gt) y x = evalBinOp (.cmp .lt) x y :=
  evalBinOp_cmp_swap .lt x y
example (x y : Datum) :
    (evalBinOp (.cmp .lt) x y >>= evalUnOp .not) = evalBinOp (.cmp .ge) x y :=
  (evalBinOp_cmp_negate .lt x y).symm

/-! ### Connectives and `IS NULL` -/

example : evalBinOp .and (b false) none = .ok (b false) := rfl
example : evalBinOp .and none (b true) = .ok none := rfl
example : evalBinOp .or (b true) none = .ok (b true) := rfl
example : evalUnOp .not none = .ok none := rfl
-- Strictness: `FALSE AND 1` is a type error although `FALSE` would decide the conjunction.
example : evalBinOp .and (b false) (i 1) = .error .typeMismatch := rfl
example : evalUnOp .isNull none = .ok (b true) := rfl
example : evalUnOp .isNotNull (i 0) = .ok (b true) := rfl

/-! ### Concatenation -/

example : evalBinOp .concat (t "ab") (t "c") = .ok (t "abc") := rfl
example : evalBinOp .concat (t "ab") none = .ok none := rfl
example : evalBinOp .concat (t "ab") (i 1) = .error .typeMismatch := rfl

/-! ### Three-valued `IN` -/

-- `NULL IN ()` is `FALSE`.
example : Datum.inList none [] = .ok .false := rfl
-- `1 IN (2, NULL)` is `unknown`, `1 IN (1, NULL)` is `TRUE`, `1 IN (2, 3)` is `FALSE`.
example : (i 1).inList [i 2, none] = .ok .unknown := rfl
example : (i 1).inList [i 1, none] = .ok .true := rfl
example : (i 1).inList [i 2, i 3] = .ok .false := rfl
-- `NULL IN (1)` is `unknown`.
example : Datum.inList none [i 1] = .ok .unknown := rfl
-- Strict: one ill-typed element makes `IN` fail, even after a match.
example : (i 1).inList [i 1, t "a"] = .error .typeMismatch := rfl

-- `1 NOT IN (2, NULL)` is `unknown`, so a `WHERE` drops the row; `NOT EXISTS (… WHERE v = 1)`
-- keeps it, since no comparison is `TRUE`.
example : ((i 1).inList [i 2, none]).map (fun t => t.not.isTrue) = .ok false := rfl
example : ¬∃ v ∈ [i 2, none], CmpOp.eq.eval v (i 1) = .ok .true := by
  simp [CmpOp.eval_eq_ok_true_iff]

-- The exact condition of `isTrue_not_inList_iff_iff` fails here, and the filters disagree.
example : ¬((Truth.unknown.not.isTrue = true ↔
      ¬∃ v ∈ [i 2, none], CmpOp.eq.eval v (i 1) = .ok .true)) := by
  rw [Datum.isTrue_not_inList_iff_iff (τ := .int) (by simp) (by simp) rfl]
  simp [CmpOp.eval_eq_ok_true_iff]

-- With no `NULL` in the list and a non-null probe the filters agree, symbolically.
example (z : ℤ) (vs : List ℤ) {u : Truth} (h : (i z).inList (vs.map i) = .ok u) :
    u.not.isTrue = true ↔ ¬∃ v ∈ vs.map i, CmpOp.eq.eval v (i z) = .ok .true := by
  refine (Datum.isTrue_not_inList_iff_iff (τ := .int) (by simp) (by simp) h).mpr (.inr (.inr ?_))
  simp

end CslibFrontierTests.SQL.Scalar
