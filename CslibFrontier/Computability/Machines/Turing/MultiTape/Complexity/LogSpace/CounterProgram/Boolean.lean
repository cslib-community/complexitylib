/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram
public import Mathlib.Data.Nat.Digits.Defs

/-!
# Boolean expressions of counter programs

Expressions of counter programs (`Turing.CounterProgram.Expr`) compute natural numbers. A Boolean
value `b` is represented by `b.toNat`, so comparisons, connectives, finite conjunctions and
disjunctions, and conditionals are again expressions. Each lemma below states the value of a
combinator from the values of its arguments, in the form `e.eval regs = b.toNat` for Boolean
results. Digits in a radix are expressions too (`Turing.CounterProgram.Expr.ofDigits`).

## Main definitions

* `Turing.CounterProgram.Expr.ltB`, `Turing.CounterProgram.Expr.eqB`: comparisons.
* `Turing.CounterProgram.Expr.notB`, `Turing.CounterProgram.Expr.andB`,
  `Turing.CounterProgram.Expr.orB`, `Turing.CounterProgram.Expr.allB`,
  `Turing.CounterProgram.Expr.anyB`: connectives.
* `Turing.CounterProgram.Expr.iteB`: a conditional on a Boolean expression.
* `Turing.CounterProgram.Expr.ofDigits`: the number with given digits in a radix.

## Main results

* `Turing.CounterProgram.Expr.eval_ltB`, `Turing.CounterProgram.Expr.eval_eqB`,
  `Turing.CounterProgram.Expr.eval_andB`, …: the values of the combinators.
* `Turing.CounterProgram.Expr.eval_ofDigits`: the value of a number given by digits.
-/

@[expose] public section

namespace Turing.CounterProgram.Expr

variable {regs : List ℕ} {a b c : Expr} {p q : Bool}

/-- `1` if `a < b`, `0` otherwise. -/
def ltB (a b : Expr) : Expr := sub (const 1) (sub (const 1) (sub b a))

/-- The negation of a Boolean expression. -/
def notB (a : Expr) : Expr := sub (const 1) a

/-- The conjunction of Boolean expressions. -/
def andB (a b : Expr) : Expr := mul a b

/-- The disjunction of Boolean expressions. -/
def orB (a b : Expr) : Expr := sub (add a b) (mul a b)

/-- `1` if `a = b`, `0` otherwise. -/
def eqB (a b : Expr) : Expr := andB (notB (ltB a b)) (notB (ltB b a))

/-- The conjunction of a list of Boolean expressions. -/
def allB (l : List Expr) : Expr := l.foldr andB (const 1)

/-- The disjunction of a list of Boolean expressions. -/
def anyB (l : List Expr) : Expr := l.foldr orB (const 0)

/-- The value of `a` if the Boolean expression `c` holds, of `b` otherwise. -/
def iteB (c a b : Expr) : Expr := add (mul c a) (mul (notB c) b)

/-- The number with the digits `l`, least significant first, in the radix `B`. -/
def ofDigits (B : Expr) (l : List Expr) : Expr := l.foldr (fun e acc => add e (mul B acc)) (const 0)

@[simp]
theorem eval_ltB : (ltB a b).eval regs = (decide (a.eval regs < b.eval regs)).toNat := by
  simp only [ltB, eval_sub, eval_const]
  by_cases h : a.eval regs < b.eval regs <;> simp [h] <;> omega

theorem eval_notB (ha : a.eval regs = p.toNat) : (notB a).eval regs = (!p).toNat := by
  cases p <;> simp [notB, ha]

theorem eval_andB (ha : a.eval regs = p.toNat) (hb : b.eval regs = q.toNat) :
    (andB a b).eval regs = (p && q).toNat := by
  cases p <;> cases q <;> simp [andB, ha, hb]

theorem eval_orB (ha : a.eval regs = p.toNat) (hb : b.eval regs = q.toNat) :
    (orB a b).eval regs = (p || q).toNat := by
  cases p <;> cases q <;> simp [orB, ha, hb]

@[simp]
theorem eval_eqB : (eqB a b).eval regs = (decide (a.eval regs = b.eval regs)).toNat := by
  rw [eqB, eval_andB (eval_notB eval_ltB) (eval_notB eval_ltB)]
  by_cases h : a.eval regs = b.eval regs
  · simp [h]
  · rcases Nat.lt_or_gt_of_ne h with h' | h' <;> simp [h, h', Nat.lt_asymm h']

theorem eval_allB {l : List Expr} {f : List Bool} (h : List.Forall₂ (fun e p => e.eval regs =
    p.toNat) l f) : (allB l).eval regs = (f.all id).toNat := by
  induction h with
  | nil => rfl
  | cons he _ ih => simpa [allB] using eval_andB he ih

theorem eval_anyB {l : List Expr} {f : List Bool} (h : List.Forall₂ (fun e p => e.eval regs =
    p.toNat) l f) : (anyB l).eval regs = (f.any id).toNat := by
  induction h with
  | nil => rfl
  | cons he _ ih => simpa [anyB] using eval_orB he ih

/-- A conjunction over a list, from the values of the conjuncts. -/
theorem eval_allB_map {ι : Type*} (l : List ι) (e : ι → Expr) (f : ι → Bool)
    (h : ∀ i ∈ l, (e i).eval regs = (f i).toNat) :
    (allB (l.map e)).eval regs = (l.all f).toNat := by
  rw [eval_allB (f := l.map f)]
  · simp
  · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun i hi => h i hi))

/-- A disjunction over a list, from the values of the disjuncts. -/
theorem eval_anyB_map {ι : Type*} (l : List ι) (e : ι → Expr) (f : ι → Bool)
    (h : ∀ i ∈ l, (e i).eval regs = (f i).toNat) :
    (anyB (l.map e)).eval regs = (l.any f).toNat := by
  rw [eval_anyB (f := l.map f)]
  · simp
  · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun i hi => h i hi))

/-- A conjunction over the elements of `Fin m`, from the values of the conjuncts. -/
theorem eval_allB_ofFn {m : ℕ} (e : Fin m → Expr) (f : Fin m → Bool)
    (h : ∀ i, (e i).eval regs = (f i).toNat) :
    (allB (List.ofFn e)).eval regs = ((List.ofFn f).all id).toNat := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map, List.all_map, eval_allB_map _ _ _ fun i _ => h i]
  rfl

theorem eval_iteB (hc : c.eval regs = p.toNat) :
    (iteB c a b).eval regs = if p then a.eval regs else b.eval regs := by
  cases p <;> simp [iteB, notB, hc]

@[simp]
theorem eval_ofDigits (B : Expr) (l : List Expr) :
    (ofDigits B l).eval regs = Nat.ofDigits (B.eval regs) (l.map fun e => e.eval regs) := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [ofDigits, Nat.ofDigits_cons, ← ih]

end Turing.CounterProgram.Expr
