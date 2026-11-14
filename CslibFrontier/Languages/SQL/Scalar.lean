/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Control.Except
public import CslibFrontier.Languages.SQL.Truth
public import CslibFrontier.Languages.SQL.Value

/-!
# SQL scalar operators

This module gives the meaning of SQL's operators on datums. An operator either returns a datum,
possibly `NULL`, or fails with an `EvalError`: `typeMismatch` when a non-null operand has the wrong
type, and `divisionByZero`. The rules are:

* A non-null operand of the wrong type is a type error, even when the other operand is `NULL`.
  Otherwise a `NULL` operand gives `NULL`, so `NULL / 0` is `NULL` while `1 / 0` fails.
* Integers are unbounded. `/` truncates toward zero (`Int.tdiv`) and `%` takes the sign of the
  dividend (`Int.tmod`).
* `= <> < <= > >=` compare two values of the same type: integers numerically, text by code points
  (binary collation), and booleans with `false < true`. Their result is a truth value, as a
  datum: `TRUE`, `FALSE`, or `NULL` for `unknown`.
* `AND`, `OR` and `NOT` are Kleene's connectives `⊓`, `⊔` and `Truth.not` on the operands'
  truth values (`Datum.toTruth`): a boolean gives its value, `NULL` gives `unknown`.
* `IS NULL` and `IS NOT NULL` accept any operand and are never `NULL`.
* `e IN (v₁, …, vₖ)` (`Datum.inList`) is the Kleene disjunction of `e = vᵢ`, starting from
  `FALSE`.

Every primitive operation (`addInt`, `divInt`, `compareText`, `concatText`, …) is a named
function, so that bounded integers or other collations can replace one later without touching the
operator rules.

All operators are strict: both operands of a binary operator are evaluated, and the left operand's
error is reported first. Since every type error is `typeMismatch`, the laws a rewriter needs hold
as equations of results: `NOT (a < b)` is `a >= b` (`evalBinOp_cmp_negate`), `a < b` is `b > a`
(`evalBinOp_cmp_swap`), `AND` and `OR` commute and satisfy De Morgan's laws, and arithmetic
identities hold on integer-typed datums. Some familiar identities fail because of `NULL`:
`x * 0` is `NULL` when `x` is.

Three-valued membership is where `NULL` matters most. Over datums of a common type, `e IN vs` is
`FALSE` for an empty list (even for a `NULL` probe), `TRUE` when `e` is non-null and occurs in
`vs`, `FALSE` when moreover nothing is `NULL`, and `unknown` otherwise (`inList_eq_ok`). So
`NOT IN` agrees with `NOT EXISTS (… WHERE v = e)` as a filter exactly when `vs` is empty, some
element matches, or the probe is non-null and the list has no `NULL`
(`isTrue_not_inList_iff_iff`). Subqueries, a later development, will reuse this membership
function.

It adapts and redesigns the operator evaluators of `sql_equiv` (revision `38030a6b`) by Evelyn
Mitchell. There, an untyped `NULL` result, an evaluation error and a type error shared
representations, `IN` lost `unknown`, and comparisons promoted between types; here errors are a
separate type, membership is three-valued, and comparison requires one type.

## Main definitions

* `Cslib.SQL.EvalError`: why an evaluation fails.
* `Cslib.SQL.Value.cmp`: comparison of two values of the same type.
* `Cslib.SQL.Datum.toTruth`, `Cslib.SQL.Truth.toDatum`: truth values as datums and back.
* `Cslib.SQL.UnOp`, `Cslib.SQL.ArithOp`, `Cslib.SQL.CmpOp`, `Cslib.SQL.BinOp`: the operators.
* `Cslib.SQL.CmpOp.eval`: three-valued comparison of datums.
* `Cslib.SQL.evalUnOp`, `Cslib.SQL.evalBinOp`: operators on datums.
* `Cslib.SQL.Datum.inList`: three-valued `e IN (v₁, …, vₖ)`.

## Main results

* `Cslib.SQL.CmpOp.eval_eq_ok_true_iff`: `a = b` is `TRUE` exactly when both are the same value.
* `Cslib.SQL.evalBinOp_cmp_negate`, `Cslib.SQL.evalBinOp_cmp_swap`: negating and flipping a
  comparison.
* `Cslib.SQL.evalBinOp_and_comm`, `Cslib.SQL.evalBinOp_or_comm`, `Cslib.SQL.not_evalBinOp_and`,
  `Cslib.SQL.not_evalBinOp_or`: commutativity and De Morgan's laws on datums.
* `Cslib.SQL.evalBinOp_add_comm`, `Cslib.SQL.evalBinOp_add_zero`,
  `Cslib.SQL.evalBinOp_arith_null_left`: arithmetic identities and `NULL` propagation.
* `Cslib.SQL.Datum.inList_eq_ok`: the closed form of three-valued membership.
* `Cslib.SQL.Datum.isTrue_not_inList_iff_iff`: when `NOT IN` agrees with `NOT EXISTS`.
-/

@[expose] public section

namespace Cslib.SQL

/-- Why an evaluation fails. -/
inductive EvalError where
  /-- A non-null operand has the wrong type. -/
  | typeMismatch
  /-- An integer division or remainder by zero. -/
  | divisionByZero
  deriving DecidableEq, Repr

/-! ### Primitive operations -/

section Primitives

/-- Integer addition (unbounded). -/
def addInt (a b : ℤ) : ℤ := a + b

/-- Integer subtraction (unbounded). -/
def subInt (a b : ℤ) : ℤ := a - b

/-- Integer multiplication (unbounded). -/
def mulInt (a b : ℤ) : ℤ := a * b

/-- Integer negation (unbounded). -/
def negInt (a : ℤ) : ℤ := -a

/-- Integer division, truncating toward zero; a zero divisor is `divisionByZero`. -/
def divInt (a b : ℤ) : Except EvalError ℤ :=
  if b = 0 then .error .divisionByZero else .ok (a.tdiv b)

/-- Integer remainder, with the sign of the dividend; a zero divisor is `divisionByZero`. -/
def modInt (a b : ℤ) : Except EvalError ℤ :=
  if b = 0 then .error .divisionByZero else .ok (a.tmod b)

/-- Text concatenation. -/
def concatText (s t : String) : String := s ++ t

/-- Integer comparison. -/
def compareInt (a b : ℤ) : Ordering := compare a b

/-- Text comparison by code points (binary collation), lexicographically. -/
def compareText (s t : String) : Ordering := compare s t

/-- Boolean comparison, with `false < true`. -/
def compareBool (a b : Bool) : Ordering := compare a b

end Primitives

namespace Value

/-- Compare two values of the same type; values of different types are a type error. -/
def cmp : Value → Value → Except EvalError Ordering
  | int a, int b => .ok (compareInt a b)
  | text s, text t => .ok (compareText s t)
  | bool a, bool b => .ok (compareBool a b)
  | _, _ => .error .typeMismatch

/-- Comparing in the other order swaps the outcome. -/
theorem cmp_swap (a b : Value) : cmp b a = Ordering.swap <$> cmp a b := by
  cases a <;> cases b <;>
    simp only [cmp, compareInt, compareText, compareBool, Except.map_ok, Except.map_error] <;>
    exact congrArg Except.ok Std.OrientedCmp.eq_swap

/-- Two values compare equal exactly when they are equal. -/
@[simp] theorem cmp_eq_ok_eq_iff {a b : Value} : cmp a b = .ok .eq ↔ a = b := by
  cases a <;> cases b <;>
    simp [cmp, compareInt, compareText, compareBool]

/-- A value compares equal to itself. -/
@[simp] theorem cmp_self (a : Value) : cmp a a = .ok .eq := cmp_eq_ok_eq_iff.mpr rfl

/-- Two values are comparable exactly when they have the same type. -/
theorem exists_cmp_eq_ok_iff {a b : Value} : (∃ o, cmp a b = .ok o) ↔ a.type = b.type := by
  cases a <;> cases b <;> simp [cmp]

/-- Comparison fails only with a type error. -/
theorem cmp_eq_error {a b : Value} {e : EvalError} (h : cmp a b = .error e) :
    e = .typeMismatch := by
  cases a <;> cases b <;> simp_all [cmp]

end Value

/-! ### Truth values as datums -/

/-- A truth value as a datum: `TRUE`, `FALSE`, or `NULL` for `unknown`. -/
def Truth.toDatum : Truth → Datum
  | .false => some (.bool Bool.false)
  | .unknown => none
  | .true => some (.bool Bool.true)

namespace Datum

/-- The truth value of an operand of `AND`, `OR`, `NOT` or `CASE WHEN`: a boolean gives its value,
`NULL` gives `unknown`, and any other value is a type error. -/
def toTruth : Datum → Except EvalError Truth
  | none => .ok .unknown
  | some (.bool b) => .ok (.ofBool b)
  | some _ => .error .typeMismatch

/-- An operand of an integer operator: `NULL` or an integer, any other value is a type error. -/
def asInt : Datum → Except EvalError (Option ℤ)
  | none => .ok none
  | some (.int z) => .ok (some z)
  | some _ => .error .typeMismatch

/-- An operand of a text operator: `NULL` or a string, any other value is a type error. -/
def asText : Datum → Except EvalError (Option String)
  | none => .ok none
  | some (.text s) => .ok (some s)
  | some _ => .error .typeMismatch

@[simp] theorem toTruth_toDatum (t : Truth) : t.toDatum.toTruth = .ok t := by
  cases t <;> rfl

theorem toTruth_eq_ok_iff {d : Datum} {t : Truth} : d.toTruth = .ok t ↔ d = t.toDatum := by
  constructor
  · intro h
    match d, h with
    | none, h => cases h; rfl
    | some (.bool b), h => cases h; cases b <;> rfl
  · rintro rfl
    exact toTruth_toDatum t

/-- A datum has a truth value exactly when it is boolean-typed. -/
theorem exists_toTruth_eq_ok_iff {d : Datum} : (∃ t, d.toTruth = .ok t) ↔ d.HasType .bool := by
  match d with
  | none => simp [toTruth]
  | some (.bool _) => simp [toTruth]
  | some (.int _) => simp [toTruth]
  | some (.text _) => simp [toTruth]

/-- A datum is an integer operand exactly when it is integer-typed. -/
theorem exists_asInt_eq_ok_iff {d : Datum} : (∃ x, d.asInt = .ok x) ↔ d.HasType .int := by
  match d with
  | none => simp [asInt]
  | some (.int _) => simp [asInt]
  | some (.text _) => simp [asInt]
  | some (.bool _) => simp [asInt]

/-- A datum is a text operand exactly when it is text-typed. -/
theorem exists_asText_eq_ok_iff {d : Datum} : (∃ x, d.asText = .ok x) ↔ d.HasType .text := by
  match d with
  | none => simp [asText]
  | some (.text _) => simp [asText]
  | some (.int _) => simp [asText]
  | some (.bool _) => simp [asText]

theorem toTruth_eq_error {d : Datum} {e : EvalError} (h : d.toTruth = .error e) :
    e = .typeMismatch := by
  match d, h with
  | some (.int _), h => cases h; rfl
  | some (.text _), h => cases h; rfl

theorem asInt_eq_error {d : Datum} {e : EvalError} (h : d.asInt = .error e) :
    e = .typeMismatch := by
  match d, h with
  | some (.text _), h => cases h; rfl
  | some (.bool _), h => cases h; rfl

theorem asText_eq_error {d : Datum} {e : EvalError} (h : d.asText = .error e) :
    e = .typeMismatch := by
  match d, h with
  | some (.int _), h => cases h; rfl
  | some (.bool _), h => cases h; rfl

end Datum

namespace Truth

@[simp] theorem toDatum_hasType (t : Truth) : t.toDatum.HasType .bool := by
  cases t <;> trivial

theorem toDatum_injective : Function.Injective toDatum := by
  intro s t h
  simpa using congrArg Datum.toTruth h

@[simp] theorem toDatum_eq_none_iff {t : Truth} : t.toDatum = none ↔ t = .unknown := by
  cases t <;> simp [toDatum]

@[simp] theorem toDatum_ofBool (b : Bool) : (ofBool b).toDatum = some (.bool b) := by
  cases b <;> rfl

end Truth

/-! ### Operators -/

/-- Unary operators. -/
inductive UnOp where
  /-- `NOT`. -/
  | not
  /-- Unary minus. -/
  | neg
  /-- `IS NULL`. -/
  | isNull
  /-- `IS NOT NULL`. -/
  | isNotNull
  deriving DecidableEq, Repr

/-- Integer operators. -/
inductive ArithOp where
  /-- `+`. -/
  | add
  /-- `-`. -/
  | sub
  /-- `*`. -/
  | mul
  /-- `/`, truncating toward zero. -/
  | div
  /-- `%`, with the sign of the dividend. -/
  | mod
  deriving DecidableEq, Repr

/-- Comparison operators. -/
inductive CmpOp where
  /-- `=`. -/
  | eq
  /-- `<>`. -/
  | ne
  /-- `<`. -/
  | lt
  /-- `<=`. -/
  | le
  /-- `>`. -/
  | gt
  /-- `>=`. -/
  | ge
  deriving DecidableEq, Repr

/-- Binary operators. -/
inductive BinOp where
  /-- An integer operator. -/
  | arith (op : ArithOp)
  /-- A comparison. -/
  | cmp (op : CmpOp)
  /-- `AND`. -/
  | and
  /-- `OR`. -/
  | or
  /-- Text concatenation `||`. -/
  | concat
  deriving DecidableEq, Repr

namespace ArithOp

/-- An integer operator on two integers. -/
def eval : ArithOp → ℤ → ℤ → Except EvalError ℤ
  | add, a, b => .ok (addInt a b)
  | sub, a, b => .ok (subInt a b)
  | mul, a, b => .ok (mulInt a b)
  | div, a, b => divInt a b
  | mod, a, b => modInt a b

/-- Whether the operator fails on a zero divisor: `/` and `%`. -/
def isDivision : ArithOp → Bool
  | div | mod => true
  | add | sub | mul => false

/-- An integer operator fails only by dividing by zero. -/
theorem eval_eq_error {op : ArithOp} {a b : ℤ} {e : EvalError} (h : op.eval a b = .error e) :
    e = .divisionByZero ∧ op.isDivision ∧ b = 0 := by
  cases op <;> simp only [eval, divInt, modInt, reduceCtorEq] at h <;> split_ifs at h with hb <;>
    cases h <;> exact ⟨rfl, rfl, hb⟩

/-- An integer operator succeeds unless it divides by zero. -/
theorem exists_eval_eq_ok {op : ArithOp} {a b : ℤ} (h : op.isDivision → b ≠ 0) :
    ∃ z, op.eval a b = .ok z := by
  rcases hr : op.eval a b with e | z
  · obtain ⟨-, hd, hb⟩ := eval_eq_error hr
    exact absurd hb (h hd)
  · exact ⟨z, rfl⟩

end ArithOp

namespace CmpOp

/-- Whether an outcome of `compare` satisfies the comparison. -/
def test : CmpOp → Ordering → Bool
  | eq => Ordering.isEq
  | ne => Ordering.isNe
  | lt => Ordering.isLT
  | le => Ordering.isLE
  | gt => Ordering.isGT
  | ge => Ordering.isGE

/-- The comparison that holds exactly when this one fails: `NOT (a < b)` is `a >= b`. -/
def negate : CmpOp → CmpOp
  | eq => ne
  | ne => eq
  | lt => ge
  | le => gt
  | gt => le
  | ge => lt

/-- The comparison with its operands exchanged: `a < b` is `b > a`. -/
def swap : CmpOp → CmpOp
  | eq => eq
  | ne => ne
  | lt => gt
  | le => ge
  | gt => lt
  | ge => le

@[simp] theorem negate_negate (op : CmpOp) : op.negate.negate = op := by cases op <;> rfl

@[simp] theorem swap_swap (op : CmpOp) : op.swap.swap = op := by cases op <;> rfl

@[simp] theorem test_negate (op : CmpOp) (o : Ordering) : op.negate.test o = !op.test o := by
  cases op <;> cases o <;> rfl

@[simp] theorem test_swap (op : CmpOp) (o : Ordering) : op.swap.test o.swap = op.test o := by
  cases op <;> cases o <;> rfl

/-- Three-valued comparison of datums: `unknown` when either side is `NULL`, otherwise the values
must have the same type. -/
def eval (op : CmpOp) : Datum → Datum → Except EvalError Truth
  | some a, some b => (fun o => Truth.ofBool (op.test o)) <$> Value.cmp a b
  | _, _ => .ok .unknown

@[simp] theorem eval_none_left (op : CmpOp) (b : Datum) : op.eval none b = .ok .unknown := rfl

@[simp] theorem eval_none_right (op : CmpOp) (a : Datum) : op.eval a none = .ok .unknown := by
  cases a <;> rfl

theorem eval_some_some (op : CmpOp) (a b : Value) :
    op.eval (some a) (some b) = (fun o => Truth.ofBool (op.test o)) <$> Value.cmp a b := rfl

/-- The negated comparison has the negated truth value. -/
theorem eval_negate (op : CmpOp) (a b : Datum) :
    op.negate.eval a b = Truth.not <$> op.eval a b := by
  match a, b with
  | none, _ => rfl
  | some _, none => rfl
  | some a, some b =>
    rcases Value.cmp a b with e | o <;> simp [eval_some_some, *]

/-- Exchanging the operands of the swapped comparison does not change it. -/
theorem eval_swap (op : CmpOp) (a b : Datum) : op.swap.eval b a = op.eval a b := by
  match a, b with
  | none, none => rfl
  | none, some _ => rfl
  | some _, none => rfl
  | some a, some b =>
    rw [eval_some_some, eval_some_some, Value.cmp_swap]
    rcases Value.cmp a b with e | o <;> simp

/-- Equality is symmetric. -/
theorem eval_eq_comm (a b : Datum) : eq.eval a b = eq.eval b a :=
  eval_swap eq b a

/-- `a = b` is `TRUE` exactly when `a` and `b` are the same value. -/
theorem eval_eq_ok_true_iff {a b : Datum} :
    eq.eval a b = .ok .true ↔ a ≠ none ∧ a = b := by
  match a, b with
  | none, _ => simp
  | some _, none => simp
  | some a, some b =>
    rw [eval_some_some, Except.map_eq_ok]
    constructor
    · rintro ⟨o, ho, hto⟩
      have : o = .eq := by cases o <;> simp_all [test]
      subst this
      simpa using ho
    · rintro ⟨-, h⟩
      cases h
      exact ⟨.eq, Value.cmp_self a, rfl⟩

/-- A comparison succeeds exactly when the operands have a common type (`NULL` has every type). -/
theorem exists_eval_eq_ok_iff {op : CmpOp} {a b : Datum} :
    (∃ t, op.eval a b = .ok t) ↔ ∃ τ, a.HasType τ ∧ b.HasType τ := by
  match a, b with
  | none, none => simp
  | none, some b => simp
  | some a, none => simp
  | some a, some b =>
    simp only [eval_some_some, Except.map_eq_ok, Datum.hasType_some]
    constructor
    · rintro ⟨-, o, h, -⟩
      exact ⟨a.type, rfl, (Value.exists_cmp_eq_ok_iff.mp ⟨o, h⟩).symm⟩
    · rintro ⟨τ, ha, hb⟩
      obtain ⟨o, h⟩ := Value.exists_cmp_eq_ok_iff.mpr (ha.trans hb.symm)
      exact ⟨_, o, h, rfl⟩

/-- A comparison of datums of a common type succeeds. -/
theorem exists_eval_eq_ok {op : CmpOp} {a b : Datum} {τ : SqlType} (ha : a.HasType τ)
    (hb : b.HasType τ) : ∃ t, op.eval a b = .ok t :=
  exists_eval_eq_ok_iff.mpr ⟨τ, ha, hb⟩

/-- A comparison fails only with a type error. -/
theorem eval_eq_error {op : CmpOp} {a b : Datum} {e : EvalError} (h : op.eval a b = .error e) :
    e = .typeMismatch := by
  match a, b, h with
  | some a, some b, h =>
    simp only [eval_some_some, Except.map_eq_error] at h
    exact Value.cmp_eq_error h

end CmpOp

/-- A unary operator on a datum. -/
def evalUnOp : UnOp → Datum → Except EvalError Datum
  | .not, d => (fun t => t.not.toDatum) <$> d.toTruth
  | .neg, d => Option.map (fun z => .int (negInt z)) <$> d.asInt
  | .isNull, d => .ok (some (.bool d.isNone))
  | .isNotNull, d => .ok (some (.bool d.isSome))

/-- A binary operator on two datums. Both operands are checked, left first, before `NULL`
propagates. -/
def evalBinOp : BinOp → Datum → Datum → Except EvalError Datum
  | .arith op, a, b => do
    let x ← a.asInt
    let y ← b.asInt
    match x, y with
    | some x, some y => return some (.int (← op.eval x y))
    | _, _ => return none
  | .cmp op, a, b => Truth.toDatum <$> op.eval a b
  | .and, a, b => do return ((← a.toTruth) ⊓ (← b.toTruth)).toDatum
  | .or, a, b => do return ((← a.toTruth) ⊔ (← b.toTruth)).toDatum
  | .concat, a, b => do
    let x ← a.asText
    let y ← b.asText
    match x, y with
    | some s, some t => return some (.text (concatText s t))
    | _, _ => return none

/-! ### Laws of the operators -/

/-- `NOT (a op b)` is `a (negate op) b`; for instance `NOT (a < b)` is `a >= b`, also when an
operand is `NULL` and when the comparison fails. -/
theorem evalBinOp_cmp_negate (op : CmpOp) (a b : Datum) :
    evalBinOp (.cmp op.negate) a b = (evalBinOp (.cmp op) a b >>= evalUnOp .not) := by
  simp only [evalBinOp, CmpOp.eval_negate]
  rcases op.eval a b with e | t <;> simp [evalUnOp]

/-- `b (swap op) a` is `a op b`; for instance `b > a` is `a < b`. -/
theorem evalBinOp_cmp_swap (op : CmpOp) (a b : Datum) :
    evalBinOp (.cmp op.swap) b a = evalBinOp (.cmp op) a b := by
  simp only [evalBinOp, CmpOp.eval_swap]

private theorem bind_toTruth_comm {β : Type} (a b : Datum) (f : Truth → Truth → β) :
    (do let s ← a.toTruth; let t ← b.toTruth; return f s t : Except EvalError β) =
      (do let t ← b.toTruth; let s ← a.toTruth; return f s t) := by
  rcases ha : a.toTruth with e | s <;> rcases hb : b.toTruth with e' | t
  · rw [Datum.toTruth_eq_error ha, Datum.toTruth_eq_error hb]; rfl
  all_goals rfl

/-- `a AND b` is `b AND a`, also when an operand is not boolean. -/
theorem evalBinOp_and_comm (a b : Datum) : evalBinOp .and a b = evalBinOp .and b a := by
  simp only [evalBinOp]
  rw [bind_toTruth_comm]
  simp only [inf_comm]

/-- `a OR b` is `b OR a`, also when an operand is not boolean. -/
theorem evalBinOp_or_comm (a b : Datum) : evalBinOp .or a b = evalBinOp .or b a := by
  simp only [evalBinOp]
  rw [bind_toTruth_comm]
  simp only [sup_comm]

/-- `NOT (NOT d)` is `d` on boolean datums. -/
theorem evalUnOp_not_not {d : Datum} (hd : d.HasType .bool) :
    (evalUnOp .not d >>= evalUnOp .not) = .ok d := by
  obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr hd
  rw [Datum.toTruth_eq_ok_iff.mp ht]
  simp [evalUnOp]

/-- De Morgan: `NOT (a AND b)` is `NOT a OR NOT b`, also when an operand is not boolean. -/
theorem not_evalBinOp_and (a b : Datum) :
    (evalBinOp .and a b >>= evalUnOp .not) =
      (do evalBinOp .or (← evalUnOp .not a) (← evalUnOp .not b)) := by
  rcases ha : a.toTruth with e | s <;> rcases hb : b.toTruth with e' | t <;>
    simp [evalBinOp, evalUnOp, ha, hb]

/-- De Morgan: `NOT (a OR b)` is `NOT a AND NOT b`, also when an operand is not boolean. -/
theorem not_evalBinOp_or (a b : Datum) :
    (evalBinOp .or a b >>= evalUnOp .not) =
      (do evalBinOp .and (← evalUnOp .not a) (← evalUnOp .not b)) := by
  rcases ha : a.toTruth with e | s <;> rcases hb : b.toTruth with e' | t <;>
    simp [evalBinOp, evalUnOp, ha, hb]

/-- `NOT (d IS NULL)` is `d IS NOT NULL`. -/
theorem not_evalUnOp_isNull (d : Datum) :
    (evalUnOp .isNull d >>= evalUnOp .not) = evalUnOp .isNotNull d := by
  cases d <;> rfl

private theorem evalBinOp_arith_of_asInt {op : ArithOp} {a b : Datum} {x y : Option ℤ}
    (ha : a.asInt = .ok x) (hb : b.asInt = .ok y) :
    evalBinOp (.arith op) a b =
      match x, y with
      | some x, some y => (fun z => some (.int z)) <$> op.eval x y
      | _, _ => .ok none := by
  simp only [evalBinOp, ha, hb, Except.ok_bind]
  rcases x with _ | x <;> rcases y with _ | y <;> rfl

/-- `NULL op a` is `NULL` for an integer operator and an integer-typed `a`. -/
theorem evalBinOp_arith_null_left (op : ArithOp) {a : Datum} (ha : a.HasType .int) :
    evalBinOp (.arith op) none a = .ok none := by
  obtain ⟨x, hx⟩ := Datum.exists_asInt_eq_ok_iff.mpr ha
  rw [evalBinOp_arith_of_asInt rfl hx]

/-- `a op NULL` is `NULL` for an integer operator and an integer-typed `a`; in particular
`NULL / 0` and `1 / NULL` are `NULL`. -/
theorem evalBinOp_arith_null_right (op : ArithOp) {a : Datum} (ha : a.HasType .int) :
    evalBinOp (.arith op) a none = .ok none := by
  obtain ⟨x, hx⟩ := Datum.exists_asInt_eq_ok_iff.mpr ha
  rw [evalBinOp_arith_of_asInt hx rfl]
  rcases x <;> rfl

private theorem bind_asInt_comm {β : Type} (a b : Datum)
    (f : Option ℤ → Option ℤ → Except EvalError β) :
    (do let x ← a.asInt; let y ← b.asInt; f x y : Except EvalError β) =
      (do let y ← b.asInt; let x ← a.asInt; f x y) := by
  rcases ha : a.asInt with e | x <;> rcases hb : b.asInt with e' | y
  · rw [Datum.asInt_eq_error ha, Datum.asInt_eq_error hb]; rfl
  all_goals rfl

private theorem evalBinOp_arith_comm {op : ArithOp} (hop : ∀ x y, op.eval x y = op.eval y x)
    (a b : Datum) : evalBinOp (.arith op) a b = evalBinOp (.arith op) b a := by
  simp only [evalBinOp]
  rw [bind_asInt_comm]
  congr 1; funext y; congr 1; funext x
  rcases x with _ | x <;> rcases y with _ | y <;> simp only [hop]

/-- `a + b` is `b + a`, also when an operand is not an integer. -/
theorem evalBinOp_add_comm (a b : Datum) :
    evalBinOp (.arith .add) a b = evalBinOp (.arith .add) b a :=
  evalBinOp_arith_comm (fun x y => by simp only [ArithOp.eval, addInt, Int.add_comm]) a b

/-- `a * b` is `b * a`, also when an operand is not an integer. -/
theorem evalBinOp_mul_comm (a b : Datum) :
    evalBinOp (.arith .mul) a b = evalBinOp (.arith .mul) b a :=
  evalBinOp_arith_comm (fun x y => by simp only [ArithOp.eval, mulInt, Int.mul_comm]) a b

private theorem evalBinOp_arith_right_id {op : ArithOp} {c : ℤ} (hop : ∀ x, op.eval x c = .ok x)
    {a : Datum} (ha : a.HasType .int) : evalBinOp (.arith op) a (some (.int c)) = .ok a := by
  obtain ⟨x, hx⟩ := Datum.exists_asInt_eq_ok_iff.mpr ha
  rw [evalBinOp_arith_of_asInt hx rfl]
  match a, x, hx with
  | none, _, hx => cases hx; rfl
  | some (.int z), _, hx => cases hx; simp only [hop, Except.map_ok]

/-- `a + 0` is `a` on integer-typed datums; on a text or boolean `a` it is a type error. -/
theorem evalBinOp_add_zero {a : Datum} (ha : a.HasType .int) :
    evalBinOp (.arith .add) a (some (.int 0)) = .ok a :=
  evalBinOp_arith_right_id (fun x => by simp only [ArithOp.eval, addInt, Int.add_zero]) ha

/-- `a - 0` is `a` on integer-typed datums. -/
theorem evalBinOp_sub_zero {a : Datum} (ha : a.HasType .int) :
    evalBinOp (.arith .sub) a (some (.int 0)) = .ok a :=
  evalBinOp_arith_right_id (fun x => by simp only [ArithOp.eval, subInt, Int.sub_zero]) ha

/-- `a * 1` is `a` on integer-typed datums. -/
theorem evalBinOp_mul_one {a : Datum} (ha : a.HasType .int) :
    evalBinOp (.arith .mul) a (some (.int 1)) = .ok a :=
  evalBinOp_arith_right_id (fun x => by simp only [ArithOp.eval, mulInt, Int.mul_one]) ha

/-- `-(-d)` is `d` on integer-typed datums. -/
theorem evalUnOp_neg_neg {d : Datum} (hd : d.HasType .int) :
    (evalUnOp .neg d >>= evalUnOp .neg) = .ok d := by
  match d, hd with
  | none, _ => rfl
  | some (.int z), _ => simp [evalUnOp, Datum.asInt, negInt]

/-! ### Three-valued membership -/

namespace Datum

/-- Three-valued `e IN (v₁, …, vₖ)`: the Kleene disjunction of the comparisons `e = vᵢ`, starting
from `FALSE`. It is strict: the comparisons are made from left to right and the first failure is
the result. `e NOT IN (v₁, …, vₖ)` is its negation `Truth.not`. -/
def inList (e : Datum) : List Datum → Except EvalError Truth
  | [] => .ok .false
  | v :: vs => do
    let t ← CmpOp.eq.eval e v
    let u ← e.inList vs
    return t ⊔ u

/-- `e IN ()` is `FALSE`, even for a `NULL` probe. -/
@[simp] theorem inList_nil (e : Datum) : e.inList [] = .ok .false := rfl

theorem inList_cons (e v : Datum) (vs : List Datum) :
    e.inList (v :: vs) = do
      let t ← CmpOp.eq.eval e v
      let u ← e.inList vs
      return t ⊔ u := rfl

/-- `e IN (v)` is `e = v`. -/
@[simp] theorem inList_singleton (e v : Datum) : e.inList [v] = CmpOp.eq.eval e v := by
  cases h : CmpOp.eq.eval e v <;> simp [inList_cons, h]

/-- Membership in a concatenation is the disjunction of the memberships. -/
theorem inList_append (e : Datum) (vs ws : List Datum) :
    e.inList (vs ++ ws) = do
      let t ← e.inList vs
      let u ← e.inList ws
      return t ⊔ u := by
  induction vs with
  | nil => cases h : e.inList ws <;> simp [h]
  | cons v vs ih =>
    simp only [List.cons_append, inList_cons, ih]
    rcases CmpOp.eq.eval e v with _ | t <;> rcases e.inList vs with _ | u <;>
      rcases e.inList ws with _ | w <;> simp [sup_assoc]

/-- Membership succeeds exactly when every comparison does. -/
theorem exists_inList_eq_ok_iff {e : Datum} {vs : List Datum} :
    (∃ t, e.inList vs = .ok t) ↔ ∀ v ∈ vs, ∃ t, CmpOp.eq.eval e v = .ok t := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [inList_cons, List.forall_mem_cons, ← ih]
    rcases CmpOp.eq.eval e v with _ | t <;> rcases e.inList vs with _ | u <;> simp

/-- Over a common type, `e = v` is `TRUE` on the same non-null value, `unknown` when one side is
`NULL`, and `FALSE` otherwise. -/
private theorem eval_eq_of_hasType {e v : Datum} {τ : SqlType} (he : e.HasType τ)
    (hv : v.HasType τ) :
    CmpOp.eq.eval e v =
      .ok (if e = none ∨ v = none then .unknown else if e = v then .true else .false) := by
  match e, v with
  | none, _ => simp
  | some _, none => simp
  | some a, some b =>
    obtain ⟨o, ho⟩ := Value.exists_cmp_eq_ok_iff.mpr (he.trans hv.symm)
    rw [CmpOp.eval_some_some, ho]
    by_cases hab : a = b
    · subst hab
      rw [Value.cmp_self] at ho
      cases ho
      simp [CmpOp.test]
    · have : o ≠ .eq := by
        rintro rfl
        exact hab (Value.cmp_eq_ok_eq_iff.mp ho)
      cases o <;> simp_all [CmpOp.test]

/-- Over a common type, membership succeeds. -/
theorem exists_inList_eq_ok {e : Datum} {vs : List Datum} {τ : SqlType} (he : e.HasType τ)
    (hvs : ∀ v ∈ vs, v.HasType τ) : ∃ t, e.inList vs = .ok t :=
  exists_inList_eq_ok_iff.mpr fun v hv => CmpOp.exists_eval_eq_ok he (hvs v hv)

/-- Over a common type, `e IN vs` is `TRUE` exactly when `e` is non-null and occurs in `vs`. -/
theorem inList_eq_ok_true_iff {e : Datum} {vs : List Datum} {τ : SqlType} (he : e.HasType τ)
    (hvs : ∀ v ∈ vs, v.HasType τ) : e.inList vs = .ok .true ↔ e ≠ none ∧ e ∈ vs := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.forall_mem_cons] at hvs
    obtain ⟨u, hu⟩ := exists_inList_eq_ok he hvs.2
    have ih' := ih hvs.2
    rw [hu, Except.ok.injEq] at ih'
    rw [inList_cons, eval_eq_of_hasType he hvs.1, hu]
    simp only [Except.ok_bind, pure, Except.pure, Except.ok.injEq, Truth.sup_eq_true_iff, ih',
      List.mem_cons]
    by_cases h₁ : e = none
    · simp [h₁]
    · by_cases h₂ : v = none
      · simp [h₁, h₂]
      · by_cases h₃ : e = v <;> simp [h₁, h₂, h₃]

/-- Over a common type, `e IN vs` is `FALSE` exactly when `vs` is empty, or `e` is non-null, does
not occur in `vs`, and `vs` has no `NULL`. -/
theorem inList_eq_ok_false_iff {e : Datum} {vs : List Datum} {τ : SqlType} (he : e.HasType τ)
    (hvs : ∀ v ∈ vs, v.HasType τ) :
    e.inList vs = .ok .false ↔ vs = [] ∨ (e ≠ none ∧ none ∉ vs ∧ e ∉ vs) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.forall_mem_cons] at hvs
    obtain ⟨u, hu⟩ := exists_inList_eq_ok he hvs.2
    have ih' := ih hvs.2
    rw [hu, Except.ok.injEq] at ih'
    rw [inList_cons, eval_eq_of_hasType he hvs.1, hu]
    simp only [Except.ok_bind, pure, Except.pure, Except.ok.injEq, Truth.sup_eq_false_iff, ih',
      List.mem_cons]
    by_cases h₁ : e = none
    · simp [h₁]
    · by_cases h₂ : v = none
      · simp [h₁, h₂]
      · by_cases h₃ : e = v
        · simp [h₂, h₃]
        · rcases vs with _ | ⟨w, ws⟩
          · simp [h₁, h₂, h₃, Ne.symm h₂]
          · simp [h₁, h₂, h₃, Ne.symm h₂]

/-- The closed form of three-valued membership over a common type: `FALSE` for an empty list (even
for a `NULL` probe), `TRUE` when the non-null probe occurs, `FALSE` when moreover nothing is `NULL`,
and `unknown` otherwise. -/
theorem inList_eq_ok {e : Datum} {vs : List Datum} {τ : SqlType} (he : e.HasType τ)
    (hvs : ∀ v ∈ vs, v.HasType τ) :
    e.inList vs = .ok
      (if vs = [] then .false
      else if e ≠ none ∧ e ∈ vs then .true
      else if e = none ∨ none ∈ vs then .unknown
      else .false) := by
  obtain ⟨t, ht⟩ := exists_inList_eq_ok he hvs
  have htrue := inList_eq_ok_true_iff he hvs
  have hfalse := inList_eq_ok_false_iff he hvs
  rw [ht, Except.ok.injEq] at htrue hfalse ⊢
  split_ifs with h₁ h₂ h₃
  · exact hfalse.mpr (.inl h₁)
  · exact htrue.mpr h₂
  · cases t
    · obtain h | ⟨h, h', -⟩ := hfalse.mp rfl
      · exact absurd h h₁
      · rcases h₃ with h₃ | h₃ <;> contradiction
    · rfl
    · exact absurd (htrue.mp rfl) h₂
  · exact hfalse.mpr (.inr ⟨by tauto, by tauto, fun h => h₂ ⟨by tauto, h⟩⟩)

/-- `NOT IN` and `NOT EXISTS`. Read as filters, `e NOT IN vs` keeps a row when the negated
membership is `TRUE`, and `NOT EXISTS (SELECT … FROM vs WHERE v = e)` keeps it when no comparison
`v = e` is `TRUE`. Over a common type they agree exactly when `vs` is empty, some element matches,
or `e` is non-null and `vs` has no `NULL`. Without a common type both fail under strict
evaluation, since a comparison raises a type error. -/
theorem isTrue_not_inList_iff_iff {e : Datum} {vs : List Datum} {τ : SqlType} {t : Truth}
    (he : e.HasType τ) (hvs : ∀ v ∈ vs, v.HasType τ) (ht : e.inList vs = .ok t) :
    (t.not.isTrue = .true ↔ ¬∃ v ∈ vs, CmpOp.eq.eval v e = .ok .true) ↔
      vs = [] ∨ (∃ v ∈ vs, CmpOp.eq.eval v e = .ok .true) ∨ (e ≠ none ∧ none ∉ vs) := by
  have hmatch : (∃ v ∈ vs, CmpOp.eq.eval v e = .ok .true) ↔ e ≠ none ∧ e ∈ vs := by
    simp only [CmpOp.eval_eq_comm _ e, CmpOp.eval_eq_ok_true_iff]
    constructor
    · rintro ⟨v, hv, hne, rfl⟩
      exact ⟨hne, hv⟩
    · rintro ⟨hne, hv⟩
      exact ⟨e, hv, hne, rfl⟩
  have htrue := inList_eq_ok_true_iff he hvs
  have hfalse := inList_eq_ok_false_iff he hvs
  rw [ht, Except.ok.injEq] at htrue hfalse
  rw [hmatch, Truth.isTrue_iff, Truth.not_eq_true_iff]
  constructor
  · intro h
    by_cases hm : e ≠ none ∧ e ∈ vs
    · exact .inr (.inl hm)
    · obtain h' | ⟨hne, hnull, -⟩ := hfalse.mp (h.mpr hm)
      · exact .inl h'
      · exact .inr (.inr ⟨hne, hnull⟩)
  · rintro (h | h | ⟨hne, hnull⟩)
    · exact ⟨fun _ ⟨_, hv⟩ => by simp [h] at hv, fun _ => hfalse.mpr (.inl h)⟩
    · exact ⟨fun hf hm => by simp [htrue.mpr hm] at hf, fun hm => absurd h hm⟩
    · exact ⟨fun hf hm => by simp [htrue.mpr hm] at hf,
        fun hm => hfalse.mpr (.inr ⟨hne, hnull, fun hv => hm ⟨hne, hv⟩⟩)⟩

end Datum

end Cslib.SQL
