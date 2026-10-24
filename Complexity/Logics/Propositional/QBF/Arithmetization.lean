/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.QBF
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Arithmetization of quantified Boolean formulas with linearization

A quantified Boolean formula is arithmetized over a commutative ring by reading `true` as `1`,
`false` as `0`, negation as `1 - a`, conjunction as `a * b`, disjunction as `1 - (1 - a) * (1 - b)`,
`∀ x` as the product and `∃ x` as the arithmetized disjunction of the values at `x = 0` and
`x = 1` [Lund, Fortnow, Karloff and Nisan][LundFortnowKarloffNisan1992], [Shamir][Shamir1992].
Each quantifier can double the degree of the result in the other variables, so Shen's
*linearization operator* `L x`, with value `(1 - x) * a + x * b` from the values `a` and `b` at
`x = 0` and `x = 1`, is applied after every quantifier: it does not change the value on `0`-`1`
points and makes the result affine in `x` [Shen][Shen1992], [Arora and Barak, Section
8.3][AroraBarak09].

`Cslib.Logic.PL.ArithQBF` is the syntax of formulas with the two quantifiers and linearization as
*operators* binding a variable (`Cslib.Logic.PL.ArithQBF.Operator`). Its value at a point
`r : V → R` is `Cslib.Logic.PL.ArithQBF.eval`. Fixing every variable but `x` gives a univariate
polynomial (`Cslib.Logic.PL.ArithQBF.restrict`), of degree at most the syntactic bound
`Cslib.Logic.PL.ArithQBF.degBound x` (`Cslib.Logic.PL.ArithQBF.natDegree_restrict_le`). These are
the polynomials a prover sends in the interactive proof for quantified Boolean formulas, and
`Cslib.Logic.PL.ArithQBF.roundDegree`, the sum over the operators of the degree of their body in
the bound variable, is the numerator of its soundness error.

On `0`-`1` points an arithmetic formula has the value of the quantified Boolean formula obtained by
dropping its linearizations (`Cslib.Logic.PL.ArithQBF.eval_boolean`). The arithmetization
`Cslib.Logic.PL.QBF.arithmetize xs φ` linearizes every variable of the list `xs` after every
quantifier, so it has the value of `φ` on `0`-`1` points
(`Cslib.Logic.PL.QBF.eval_arithmetize`). When `xs` contains every variable of `φ`, all degrees are
at most the size of `φ` (`Cslib.Logic.PL.QBF.degBound_arithmetize_le`) and the sum of the round
degrees is at most `(2 * |xs| + 1) * size φ ^ 2` (`Cslib.Logic.PL.QBF.roundDegree_arithmetize_le`).
For a verifier reading the same number of coefficients in every round, the arithmetization has
at most `(|xs| + 1) * size φ` operators (`Cslib.Logic.PL.QBF.ops_arithmetize_le`), and, when `xs`
contains every variable of `φ`, the body of each has degree at most `2 * size φ` in its variable
(`Cslib.Logic.PL.QBF.maxRoundDegree_arithmetize_le`). Values and restrictions depend only on the
variables of a formula (`Cslib.Logic.PL.ArithQBF.eval_congr`,
`Cslib.Logic.PL.ArithQBF.restrict_congr`). Shen linearizes only the free variables of each
quantified subformula; linearizing a fixed list of
variables is simpler to compute and costs only polynomially many more rounds.

## Main definitions

* `Cslib.Logic.PL.ArithQBF`, `Cslib.Logic.PL.ArithQBF.Connective`: arithmetic formulas with
  connectives and the operators `∃`, `∀` and `L`.
* `Cslib.Logic.PL.ArithQBF.Connective.apply`, `Cslib.Logic.PL.ArithQBF.Operator.apply`: evaluation
  of connectives and operators over a commutative ring.
* `Cslib.Logic.PL.ArithQBF.eval`, `Cslib.Logic.PL.ArithQBF.restrict`: values and univariate
  restrictions.
* `Cslib.Logic.PL.ArithQBF.Operator.degMul`, `Cslib.Logic.PL.ArithQBF.degBound`,
  `Cslib.Logic.PL.ArithQBF.roundDegree`: syntactic degree bounds.
* `Cslib.Logic.PL.ArithQBF.ops`, `Cslib.Logic.PL.ArithQBF.maxRoundDegree`: the number of
  operators and the largest degree of their bodies.
* `Cslib.Logic.PL.ArithQBF.vars`: the variables of an arithmetic formula.
* `Cslib.Logic.PL.ArithQBF.toQBF`: the formula without its linearizations.
* `Cslib.Logic.PL.ArithQBF.lins`, `Cslib.Logic.PL.QBF.arithmetize`: linearization of a list of
  variables and the arithmetization with linearization.

## Main results

* `Cslib.Logic.PL.ArithQBF.eval_restrict`, `Cslib.Logic.PL.ArithQBF.natDegree_restrict_le`: the
  restriction to a variable is a polynomial of degree at most `degBound`.
* `Cslib.Logic.PL.ArithQBF.eval_boolean`: on `0`-`1` points the value is that of the formula without
  its linearizations.
* `Cslib.Logic.PL.QBF.eval_arithmetize`, `Cslib.Logic.PL.QBF.eval_arithmetize_zero`: the
  arithmetization is faithful on `0`-`1` points, and a closed formula has value `1` or `0` at the
  origin.
* `Cslib.Logic.PL.QBF.degBound_arithmetize_le`, `Cslib.Logic.PL.QBF.roundDegree_arithmetize_le`,
  `Cslib.Logic.PL.QBF.ops_arithmetize_le`, `Cslib.Logic.PL.QBF.maxRoundDegree_arithmetize_le`:
  polynomial bounds.
* `Cslib.Logic.PL.ArithQBF.eval_congr`, `Cslib.Logic.PL.ArithQBF.restrict_congr`: dependence on
  the variables only.

## References

* [C. Lund, L. Fortnow, H. Karloff, N. Nisan, *Algebraic methods for interactive proof
  systems*][LundFortnowKarloffNisan1992]
* [A. Shamir, *IP = PSPACE*][Shamir1992]
* [A. Shen, *IP = SPACE: simplified proof*][Shen1992]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL

/-! ### Arithmetic formulas -/

/-- The binary connectives of arithmetic formulas. -/
inductive ArithQBF.Connective where
  /-- Conjunction, arithmetized as `a * b`. -/
  | and
  /-- Disjunction, arithmetized as `1 - (1 - a) * (1 - b)`. -/
  | or
  deriving DecidableEq

/-- The operators of arithmetic formulas, each binding a variable. -/
inductive ArithQBF.Operator where
  /-- Existential quantification, the arithmetized disjunction of the values at `0` and `1`. -/
  | ex
  /-- Universal quantification, the product of the values at `0` and `1`. -/
  | all
  /-- Linearization: `(1 - x) * a + x * b` for the values `a` and `b` at `0` and `1`. -/
  | lin
  deriving DecidableEq

/-- **Arithmetic formulas**: quantified Boolean formulas over variables of type `V` whose operators
binding a variable are the two quantifiers and Shen's linearization [Shen][Shen1992]. -/
inductive ArithQBF (V : Type*) where
  /-- The variable `v`. -/
  | var (v : V)
  /-- The constant `1`. -/
  | top
  /-- The constant `0`. -/
  | bot
  /-- Negation, `1 - a`. -/
  | not (e : ArithQBF V)
  /-- A binary connective. -/
  | bin (o : ArithQBF.Connective) (e₁ e₂ : ArithQBF V)
  /-- An operator binding the variable `v`. -/
  | op (o : ArithQBF.Operator) (v : V) (e : ArithQBF V)
  deriving DecidableEq

namespace ArithQBF

open Polynomial

variable {V R S : Type*} [CommRing R] [CommRing S]

/-! ### Values -/

/-- The value of a connective on the values `a` and `b` of its two arguments. -/
def Connective.apply : Connective → R → R → R
  | .and, a, b => a * b
  | .or, a, b => 1 - (1 - a) * (1 - b)

/-- The value of an operator binding `x`, on the value `t` of `x` and the values `a` and `b` of
its body at `x = 0` and `x = 1`. -/
def Operator.apply : Operator → R → R → R → R
  | .ex, _, a, b => 1 - (1 - a) * (1 - b)
  | .all, _, a, b => a * b
  | .lin, t, a, b => (1 - t) * a + t * b

/-- Ring homomorphisms commute with `Connective.apply`. -/
theorem Connective.map_apply (f : R →+* S) (o : Connective) (a b : R) :
    f (o.apply a b) = o.apply (f a) (f b) := by
  cases o <;> simp only [apply, map_mul, map_sub, map_one]

/-- Ring homomorphisms commute with `Operator.apply`. -/
theorem Operator.map_apply (f : R →+* S) (o : Operator) (t a b : R) :
    f (o.apply t a b) = o.apply (f t) (f a) (f b) := by
  cases o <;> simp only [apply, map_add, map_mul, map_sub, map_one]

variable [DecidableEq V]

/-- The value of an arithmetic formula at the point `r`. An operator binding `v` combines the
values of its body with `v` set to `0` and to `1`, and, for linearization, the value `r v`. -/
def eval (r : V → R) : ArithQBF V → R
  | .var v => r v
  | .top => 1
  | .bot => 0
  | .not e => 1 - eval r e
  | .bin o e₁ e₂ => o.apply (eval r e₁) (eval r e₂)
  | .op o v e => o.apply (r v) (eval (Function.update r v 0) e) (eval (Function.update r v 1) e)

variable (r : V → R) (v : V) (e e₁ e₂ : ArithQBF V)

/-- Evaluating a variable returns its value under the assignment `r`. -/
@[simp] theorem eval_var : (var v).eval r = r v := rfl

/-- Evaluating `top` yields `1`. -/
@[simp] theorem eval_top : (top : ArithQBF V).eval r = 1 := rfl

/-- Evaluating `bot` yields `0`. -/
@[simp] theorem eval_bot : (bot : ArithQBF V).eval r = 0 := rfl

/-- Evaluating `e.not` yields `1 - e.eval r`. -/
@[simp] theorem eval_not : e.not.eval r = 1 - e.eval r := rfl

/-- Evaluating a binary connective applies `o.apply` to the values of its subformulas. -/
@[simp] theorem eval_bin (o : Connective) :
    (bin o e₁ e₂).eval r = o.apply (e₁.eval r) (e₂.eval r) := rfl

/-- Evaluating an operator binding `v` applies `o.apply` to `r v` and the values at `0` and `1`. -/
@[simp] theorem eval_op (o : Operator) :
    (op o v e).eval r =
      o.apply (r v) (e.eval (Function.update r v 0)) (e.eval (Function.update r v 1)) := rfl

/-! ### Univariate restrictions and their degrees -/

/-- The univariate polynomial obtained from an arithmetic formula by fixing every variable but `x`
to its value in `r` (`Cslib.Logic.PL.ArithQBF.eval_restrict`). -/
noncomputable def restrict (r : V → R) (x : V) : ArithQBF V → R[X]
  | .var v => if v = x then X else C (r v)
  | .top => 1
  | .bot => 0
  | .not e => 1 - restrict r x e
  | .bin o e₁ e₂ => o.apply (restrict r x e₁) (restrict r x e₂)
  | .op o v e =>
    if v = x then
      o.apply X (C (eval (Function.update r v 0) e)) (C (eval (Function.update r v 1) e))
    else o.apply (C (r v)) (restrict (Function.update r v 0) x e)
      (restrict (Function.update r v 1) x e)

/-- The restriction of a formula to `x` at `r`, evaluated at `z`, is the value of the formula at
`r` with `x` set to `z`. -/
theorem eval_restrict (x : V) (z : R) :
    (e.restrict r x).eval z = e.eval (Function.update r x z) := by
  induction e generalizing r with
  | var v =>
    by_cases h : v = x
    · subst h
      simp only [restrict, ↓reduceIte, eval_X, eval_var, Function.update_self]
    · simp only [restrict, h, ↓reduceIte, eval_C, eval_var, Function.update_of_ne h]
  | top => simp only [restrict, eval_one, eval_top]
  | bot => simp only [restrict, Polynomial.eval_zero, eval_bot]
  | not e ih => simp only [restrict, eval_sub, eval_one, ih, eval_not]
  | bin o e₁ e₂ ih₁ ih₂ =>
    rw [restrict, ← coe_evalRingHom, Connective.map_apply, coe_evalRingHom, ih₁, ih₂, eval_bin]
  | op o v e ih =>
    rw [restrict, eval_op, ← coe_evalRingHom]
    by_cases h : v = x
    · subst h
      simp only [↓reduceIte, Operator.map_apply, coe_evalRingHom, eval_X, eval_C,
        Function.update_self, Function.update_idem]
    · simp only [h, ↓reduceIte, Operator.map_apply, coe_evalRingHom, eval_C, ih,
        Function.update_of_ne h, Function.update_comm h]

/-- The factor by which an operator binding another variable can multiply the degree in `x`. -/
def Operator.degMul : Operator → ℕ
  | .ex => 2
  | .all => 2
  | .lin => 1

/-- A syntactic bound on the degree of an arithmetic formula in the variable `x`
(`Cslib.Logic.PL.ArithQBF.natDegree_restrict_le`). -/
def degBound (x : V) : ArithQBF V → ℕ
  | .var v => if v = x then 1 else 0
  | .top => 0
  | .bot => 0
  | .not e => degBound x e
  | .bin _ e₁ e₂ => degBound x e₁ + degBound x e₂
  | .op o v e => if v = x then 1 else o.degMul * degBound x e

private theorem natDegree_one_sub_le (p : R[X]) : (1 - p).natDegree ≤ p.natDegree :=
  (natDegree_sub_le 1 p).trans (by rw [natDegree_one, Nat.zero_max])

/-- Applying a binary connective to polynomials `p` and `q` has degree at most the sum of their
degrees. -/
theorem Connective.natDegree_apply_le (o : Connective) (p q : R[X]) :
    (o.apply p q).natDegree ≤ p.natDegree + q.natDegree := by
  cases o
  · exact natDegree_mul_le
  · exact (natDegree_one_sub_le _).trans (natDegree_mul_le.trans
      (Nat.add_le_add (natDegree_one_sub_le p) (natDegree_one_sub_le q)))

/-- Applying an operator at a constant `C t` to polynomials of degree at most `d` has degree at
most `o.degMul * d`. -/
theorem Operator.natDegree_apply_le (o : Operator) (t : R) {p q : R[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    (o.apply (C t) p q).natDegree ≤ o.degMul * d := by
  cases o
  · refine (natDegree_one_sub_le _).trans (natDegree_mul_le.trans ?_)
    have := natDegree_one_sub_le p
    have := natDegree_one_sub_le q
    simp only [degMul]
    omega
  · refine natDegree_mul_le.trans ?_
    simp only [degMul]
    omega
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine natDegree_mul_le.trans ?_
      rw [← C_1, ← C_sub, natDegree_C, degMul, one_mul, zero_add]
      exact hp
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_C, degMul, one_mul, zero_add]
      exact hq

/-- Applying an operator at `X` to constant polynomials `C a` and `C b` has degree at most `1`. -/
theorem Operator.natDegree_apply_X_le (o : Operator) (a b : R) :
    (o.apply X (C a) (C b)).natDegree ≤ 1 := by
  cases o
  · refine (natDegree_one_sub_le _).trans (natDegree_mul_le.trans ?_)
    have := natDegree_one_sub_le (C a)
    have := natDegree_one_sub_le (C b)
    rw [natDegree_C] at *
    omega
  · refine natDegree_mul_le.trans ?_
    rw [natDegree_C, natDegree_C]
    omega
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_C, add_zero]
      exact (natDegree_one_sub_le X).trans natDegree_X_le
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_C, add_zero]
      exact natDegree_X_le

/-- The restriction of a formula to `x` has degree at most `degBound x`. -/
theorem natDegree_restrict_le (x : V) : (e.restrict r x).natDegree ≤ e.degBound x := by
  induction e generalizing r with
  | var v =>
    by_cases h : v = x
    · simp only [restrict, degBound, h, ↓reduceIte]
      exact natDegree_X_le
    · simp only [restrict, degBound, h, ↓reduceIte, natDegree_C, le_refl]
  | top => simp only [restrict, degBound, natDegree_one, le_refl]
  | bot => simp only [restrict, degBound, natDegree_zero, le_refl]
  | not e ih => exact (natDegree_one_sub_le _).trans (ih r)
  | bin o e₁ e₂ ih₁ ih₂ =>
    exact (Connective.natDegree_apply_le o _ _).trans (Nat.add_le_add (ih₁ r) (ih₂ r))
  | op o v e ih =>
    by_cases h : v = x
    · simp only [restrict, degBound, h, ↓reduceIte]
      exact Operator.natDegree_apply_X_le o _ _
    · simp only [restrict, degBound, h, ↓reduceIte]
      exact Operator.natDegree_apply_le o _ (ih _) (ih _)

/-- The sum, over the operators of a formula, of the degree of their body in the variable they
bind: the number of roots that can fool the verifier in the interactive proof. -/
def roundDegree : ArithQBF V → ℕ
  | .var _ => 0
  | .top => 0
  | .bot => 0
  | .not e => roundDegree e
  | .bin _ e₁ e₂ => roundDegree e₁ + roundDegree e₂
  | .op _ v e => degBound v e + roundDegree e

/-- The number of operators of a formula: the number of rounds of the interactive proof that
draw a random element. -/
def ops : ArithQBF V → ℕ
  | .var _ => 0
  | .top => 0
  | .bot => 0
  | .not e => ops e
  | .bin _ e₁ e₂ => ops e₁ + ops e₂
  | .op _ _ e => ops e + 1

/-- The largest degree, over the operators of a formula, of their body in the variable they bind.
A prover sending polynomials of this degree can be honest in every round. -/
def maxRoundDegree : ArithQBF V → ℕ
  | .var _ => 0
  | .top => 0
  | .bot => 0
  | .not e => maxRoundDegree e
  | .bin _ e₁ e₂ => max (maxRoundDegree e₁) (maxRoundDegree e₂)
  | .op _ v e => max (degBound v e) (maxRoundDegree e)

/-- The round degrees sum to at most the number of rounds times the largest round degree. -/
theorem roundDegree_le_ops_mul : e.roundDegree ≤ e.ops * e.maxRoundDegree := by
  induction e with
  | var v => exact le_refl 0
  | top => exact le_refl 0
  | bot => exact le_refl 0
  | not e ih => exact ih
  | bin o e₁ e₂ ih₁ ih₂ =>
    simp only [roundDegree, ops, maxRoundDegree, Nat.add_mul]
    exact Nat.add_le_add (ih₁.trans (Nat.mul_le_mul_left _ (le_max_left _ _)))
      (ih₂.trans (Nat.mul_le_mul_left _ (le_max_right _ _)))
  | op o v e ih =>
    simp only [roundDegree, ops, maxRoundDegree, Nat.add_mul, Nat.one_mul]
    have := ih.trans (Nat.mul_le_mul_left e.ops (le_max_right (e.degBound v) e.maxRoundDegree))
    have := le_max_left (e.degBound v) e.maxRoundDegree
    omega

/-! ### Variables -/

/-- The variables of an arithmetic formula, free or bound, with multiplicity, in prefix order. -/
def vars : ArithQBF V → List V
  | .var v => [v]
  | .top => []
  | .bot => []
  | .not e => vars e
  | .bin _ e₁ e₂ => vars e₁ ++ vars e₂
  | .op _ v e => v :: vars e

/-- The value of a formula depends only on the values of its variables. -/
theorem eval_congr {r r' : V → R} (h : ∀ w ∈ e.vars, r w = r' w) : e.eval r = e.eval r' := by
  induction e generalizing r r' with
  | var v => exact h v (List.mem_singleton_self v)
  | top => rfl
  | bot => rfl
  | not e ih => rw [eval_not, eval_not, ih h]
  | bin o e₁ e₂ ih₁ ih₂ =>
    rw [eval_bin, eval_bin, ih₁ fun w hw => h w (List.mem_append_left _ hw),
      ih₂ fun w hw => h w (List.mem_append_right _ hw)]
  | op o v e ih =>
    have hupd (b : R) : ∀ w ∈ e.vars, Function.update r v b w = Function.update r' v b w := by
      intro w hw
      by_cases hwv : w = v
      · subst hwv
        simp only [Function.update_self]
      · rw [Function.update_of_ne hwv, Function.update_of_ne hwv]
        exact h w (List.mem_cons_of_mem v hw)
    rw [eval_op, eval_op, h v List.mem_cons_self, ih (hupd 0), ih (hupd 1)]

/-- The restriction of a formula to a variable depends only on the values of its variables. -/
theorem restrict_congr {r r' : V → R} (x : V) (h : ∀ w ∈ e.vars, r w = r' w) :
    e.restrict r x = e.restrict r' x := by
  induction e generalizing r r' with
  | var v => simp only [restrict, h v (List.mem_singleton_self v)]
  | top => rfl
  | bot => rfl
  | not e ih => simp only [restrict, ih h]
  | bin o e₁ e₂ ih₁ ih₂ =>
    simp only [restrict, ih₁ fun w hw => h w (List.mem_append_left _ hw),
      ih₂ fun w hw => h w (List.mem_append_right _ hw)]
  | op o v e ih =>
    have hupd (b : R) : ∀ w ∈ e.vars, Function.update r v b w = Function.update r' v b w := by
      intro w hw
      by_cases hwv : w = v
      · subst hwv
        simp only [Function.update_self]
      · rw [Function.update_of_ne hwv, Function.update_of_ne hwv]
        exact h w (List.mem_cons_of_mem v hw)
    simp only [restrict, h v List.mem_cons_self, ih (hupd 0), ih (hupd 1),
      eval_congr e (hupd 0), eval_congr e (hupd 1)]

/-! ### Values on `0`-`1` points -/

/-- The quantified Boolean formula obtained by dropping the linearizations. -/
def toQBF : ArithQBF V → QBF V
  | .var v => .var v
  | .top => .top
  | .bot => .bot
  | .not e => .not (toQBF e)
  | .bin .and e₁ e₂ => .and (toQBF e₁) (toQBF e₂)
  | .bin .or e₁ e₂ => .or (toQBF e₁) (toQBF e₂)
  | .op .ex v e => .ex v (toQBF e)
  | .op .all v e => .all v (toQBF e)
  | .op .lin _ e => toQBF e

private theorem cond_update (σ : V → Bool) (v : V) (b : Bool) :
    (fun w => cond (Function.update σ v b w) (1 : R) 0) =
      Function.update (fun w => cond (σ w) (1 : R) 0) v (cond b 1 0) := by
  funext w
  exact Function.apply_update (fun _ (c : Bool) => cond c (1 : R) 0) σ v b w

private theorem eval_cond (σ : V → Bool) :
    e.eval (fun w => cond (σ w) (1 : R) 0) = cond (e.toQBF.eval σ) 1 0 := by
  induction e generalizing σ with
  | var v => rfl
  | top => rfl
  | bot => rfl
  | not e ih =>
    rw [eval_not, ih]
    simp only [toQBF, QBF.eval_not]
    cases e.toQBF.eval σ <;> simp
  | bin o e₁ e₂ ih₁ ih₂ =>
    rw [eval_bin, ih₁, ih₂]
    cases o <;> simp only [toQBF, QBF.eval_and, QBF.eval_or, Connective.apply] <;>
      cases e₁.toQBF.eval σ <;> cases e₂.toQBF.eval σ <;> simp
  | op o v e ih =>
    have h0 := cond_update (R := R) σ v false
    have h1 := cond_update (R := R) σ v true
    simp only [Bool.cond_false, Bool.cond_true] at h0 h1
    rw [eval_op, ← h0, ← h1, ih, ih]
    cases o
    · simp only [toQBF, QBF.eval_ex, Operator.apply]
      cases e.toQBF.eval (Function.update σ v false) <;>
        cases e.toQBF.eval (Function.update σ v true) <;> simp
    · simp only [toQBF, QBF.eval_all, Operator.apply]
      cases e.toQBF.eval (Function.update σ v false) <;>
        cases e.toQBF.eval (Function.update σ v true) <;> simp
    · simp only [toQBF, Operator.apply]
      cases hσ : σ v
      · rw [← hσ, Function.update_eq_self]
        simp only [hσ, Bool.cond_false, sub_zero, one_mul, zero_mul, add_zero]
      · rw [← hσ, Function.update_eq_self]
        simp only [hσ, Bool.cond_true, sub_self, zero_mul, one_mul, zero_add]

/-- **Faithfulness on `0`-`1` points.** At the point given by a truth assignment, an arithmetic
formula has value `1` or `0` according to the truth value of the formula without its
linearizations. -/
theorem eval_boolean (σ : V → Bool) :
    e.eval (fun w => if σ w then (1 : R) else 0) = if e.toQBF.eval σ then 1 else 0 := by
  have h := eval_cond (R := R) e σ
  simp only [Bool.cond_eq_ite] at h
  exact h

/-! ### Linearization -/

/-- Linearization of each variable of a list, the first one outermost. -/
def lins (xs : List V) (e : ArithQBF V) : ArithQBF V := xs.foldr (op .lin) e

omit [DecidableEq V] in
/-- Linearizing over the empty list of variables leaves the formula unchanged. -/
@[simp] theorem lins_nil : lins [] e = e := rfl

omit [DecidableEq V] in
/-- Linearizing over `x :: xs` applies `.op .lin x` to `lins xs e`. -/
@[simp] theorem lins_cons (x : V) (xs : List V) : lins (x :: xs) e = op .lin x (lins xs e) := rfl

omit [DecidableEq V] in
/-- Dropping linearizations from `lins xs e` yields `e.toQBF`. -/
@[simp] theorem toQBF_lins (xs : List V) : (lins xs e).toQBF = e.toQBF := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [lins_cons, toQBF, ih]

/-- After linearizing the variables of `xs`, the degree in each of them is at most `1`. -/
private theorem degBound_lins (x : V) (xs : List V) :
    (lins xs e).degBound x = if x ∈ xs then 1 else e.degBound x := by
  induction xs with
  | nil => simp
  | cons y xs ih =>
    rw [lins_cons, degBound, ih]
    by_cases hy : y = x
    · simp [hy]
    · simp [hy, Ne.symm hy, Operator.degMul]

/-- Linearizing the variables of `xs` costs at most `D` per variable when every degree is at most
`D`. -/
private theorem roundDegree_lins_le (xs : List V) {D : ℕ} (h : ∀ x, e.degBound x ≤ D) (hD : 1 ≤ D) :
    (lins xs e).roundDegree ≤ xs.length * D + e.roundDegree := by
  induction xs with
  | nil => simp
  | cons y xs ih =>
    rw [lins_cons, roundDegree, degBound_lins, List.length_cons]
    have : (if y ∈ xs then 1 else e.degBound y) ≤ D := by split_ifs <;> simp_all
    nlinarith

omit [DecidableEq V] in
/-- Linearizing `xs` adds `xs.length` operators to `e.ops`. -/
@[simp] theorem ops_lins (xs : List V) : (lins xs e).ops = xs.length + e.ops := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [lins_cons, ops, ih, List.length_cons]
    omega

omit [DecidableEq V] in
private theorem mem_vars_lins {xs : List V} {w : V} (h : w ∈ (lins xs e).vars) :
    w ∈ xs ∨ w ∈ e.vars := by
  induction xs with
  | nil => exact Or.inr h
  | cons x xs ih =>
    rw [lins_cons, vars, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inl List.mem_cons_self
    · exact (ih h).imp_left (List.mem_cons_of_mem x)

/-- Linearizing the variables of `xs` keeps the largest round degree at most `D` when every degree
is at most `D`. -/
private theorem maxRoundDegree_lins_le (xs : List V) {D : ℕ} (h : ∀ x, e.degBound x ≤ D)
    (hD : 1 ≤ D) : (lins xs e).maxRoundDegree ≤ max D e.maxRoundDegree := by
  induction xs with
  | nil => exact le_max_right _ _
  | cons y xs ih =>
    rw [lins_cons, maxRoundDegree, degBound_lins]
    refine max_le ?_ ih
    split_ifs
    · exact hD.trans (le_max_left _ _)
    · exact (h y).trans (le_max_left _ _)

end ArithQBF

/-! ### Arithmetization -/

namespace QBF

open ArithQBF

variable {V R : Type*} [DecidableEq V] [CommRing R]

/-- **Arithmetization with linearization** [Shen][Shen1992]: the arithmetic formula of `φ` that
linearizes every variable of `xs` after every quantifier. -/
def arithmetize (xs : List V) : QBF V → ArithQBF V
  | .var v => .var v
  | .top => .top
  | .bot => .bot
  | .not φ => .not (arithmetize xs φ)
  | .and φ ψ => .bin .and (arithmetize xs φ) (arithmetize xs ψ)
  | .or φ ψ => .bin .or (arithmetize xs φ) (arithmetize xs ψ)
  | .ex v φ => lins xs (.op .ex v (arithmetize xs φ))
  | .all v φ => lins xs (.op .all v (arithmetize xs φ))

omit [DecidableEq V] in
/-- Dropping linearizations from `φ.arithmetize xs` recovers `φ`. -/
@[simp] theorem toQBF_arithmetize (xs : List V) (φ : QBF V) : (φ.arithmetize xs).toQBF = φ := by
  induction φ with
  | var v => rfl
  | top => rfl
  | bot => rfl
  | not φ ih => rw [arithmetize, ArithQBF.toQBF, ih]
  | and φ ψ ihφ ihψ => rw [arithmetize, ArithQBF.toQBF, ihφ, ihψ]
  | or φ ψ ihφ ihψ => rw [arithmetize, ArithQBF.toQBF, ihφ, ihψ]
  | ex v φ ih => rw [arithmetize, toQBF_lins, ArithQBF.toQBF, ih]
  | all v φ ih => rw [arithmetize, toQBF_lins, ArithQBF.toQBF, ih]

/-- **The arithmetization is faithful on `0`-`1` points.** -/
theorem eval_arithmetize (xs : List V) (φ : QBF V) (σ : V → Bool) :
    (φ.arithmetize xs).eval (fun v => if σ v then (1 : R) else 0) = if φ.eval σ then 1 else 0 := by
  rw [eval_boolean, toQBF_arithmetize]

/-- A closed formula's arithmetization has value `1` or `0` at the origin, according to its truth
value. -/
theorem eval_arithmetize_zero (xs : List V) {φ : QBF V} (hφ : φ.Closed) (σ : V → Bool) :
    (φ.arithmetize xs).eval (0 : V → R) = if φ.eval σ then 1 else 0 := by
  have h0 : (0 : V → R) = fun v => if (fun _ => false : V → Bool) v then (1 : R) else 0 := by
    funext v
    simp
  rw [h0, eval_arithmetize, eval_eq_of_closed hφ]

/-- A variable that does not occur in `φ` nor in `xs` does not occur in the arithmetization. -/
theorem degBound_arithmetize_eq_zero {xs : List V} {x : V} (hx : x ∉ xs) {φ : QBF V}
    (hφ : x ∉ φ.vars) : (φ.arithmetize xs).degBound x = 0 := by
  induction φ with
  | var v =>
    have : v ≠ x := fun h => hφ (h ▸ List.mem_singleton_self v)
    simp [arithmetize, degBound, this]
  | top => rfl
  | bot => rfl
  | not φ ih => exact ih hφ
  | and φ ψ ihφ ihψ =>
    simp only [vars, List.mem_append, not_or] at hφ
    simp only [arithmetize, degBound, ihφ hφ.1, ihψ hφ.2]
  | or φ ψ ihφ ihψ =>
    simp only [vars, List.mem_append, not_or] at hφ
    simp only [arithmetize, degBound, ihφ hφ.1, ihψ hφ.2]
  | ex v φ ih =>
    simp only [vars, List.mem_cons, not_or] at hφ
    simp [arithmetize, degBound_lins, hx, degBound, Ne.symm hφ.1, ih hφ.2]
  | all v φ ih =>
    simp only [vars, List.mem_cons, not_or] at hφ
    simp [arithmetize, degBound_lins, hx, degBound, Ne.symm hφ.1, ih hφ.2]

/-- **Degrees stay small.** When `xs` contains every variable of `φ`, the arithmetization has
degree at most the size of `φ` in every variable. -/
theorem degBound_arithmetize_le {xs : List V} {φ : QBF V} (hxs : ∀ v ∈ φ.vars, v ∈ xs) (x : V) :
    (φ.arithmetize xs).degBound x ≤ φ.size := by
  induction φ with
  | var v =>
    simp only [arithmetize, degBound, size]
    split_ifs <;> omega
  | top => simp [arithmetize, degBound]
  | bot => simp [arithmetize, degBound]
  | not φ ih =>
    simp only [arithmetize, degBound, size]
    have := ih hxs
    omega
  | and φ ψ ihφ ihψ =>
    simp only [vars, List.mem_append] at hxs
    have := ihφ fun v hv => hxs v (Or.inl hv)
    have := ihψ fun v hv => hxs v (Or.inr hv)
    simp only [arithmetize, degBound, size]
    omega
  | or φ ψ ihφ ihψ =>
    simp only [vars, List.mem_append] at hxs
    have := ihφ fun v hv => hxs v (Or.inl hv)
    have := ihψ fun v hv => hxs v (Or.inr hv)
    simp only [arithmetize, degBound, size]
    omega
  | ex v φ ih =>
    rw [arithmetize, degBound_lins]
    by_cases hx : x ∈ xs
    · simp only [hx, ↓reduceIte, size]
      omega
    · have hxv : x ∉ (ex v φ).vars := fun h => hx (hxs x h)
      have := degBound_arithmetize_eq_zero hx hxv
      rw [arithmetize, degBound_lins] at this
      simp only [hx, ↓reduceIte] at this ⊢
      omega
  | all v φ ih =>
    rw [arithmetize, degBound_lins]
    by_cases hx : x ∈ xs
    · simp only [hx, ↓reduceIte, size]
      omega
    · have hxv : x ∉ (all v φ).vars := fun h => hx (hxs x h)
      have := degBound_arithmetize_eq_zero hx hxv
      rw [arithmetize, degBound_lins] at this
      simp only [hx, ↓reduceIte] at this ⊢
      omega

/-- The rounds of a quantifier and of the linearizations after it cost at most
`(2 * |xs| + 1) * size φ` for the body `φ`. -/
private theorem roundDegree_arithmetize_op_le {xs : List V} {φ : QBF V}
    (hxs : ∀ v ∈ φ.vars, v ∈ xs) (o : Operator) (ho : o.degMul ≤ 2) (v : V) :
    (lins xs (.op o v (φ.arithmetize xs))).roundDegree ≤
      (2 * xs.length + 1) * φ.size + (φ.arithmetize xs).roundDegree := by
  have hdeg := degBound_arithmetize_le hxs
  have hs := one_le_size φ
  have hD : ∀ x, (ArithQBF.op o v (φ.arithmetize xs)).degBound x ≤ 2 * φ.size := by
    intro x
    simp only [degBound]
    split_ifs
    · omega
    · have := hdeg x
      exact (Nat.mul_le_mul ho this)
  refine (roundDegree_lins_le _ xs hD (by omega)).trans ?_
  simp only [ArithQBF.roundDegree]
  have := hdeg v
  nlinarith

/-- **The round degrees are polynomial.** When `xs` contains every variable of `φ`, the sum of
the round degrees of the arithmetization is at most `(2 * |xs| + 1) * size φ ^ 2`. -/
theorem roundDegree_arithmetize_le {xs : List V} {φ : QBF V} (hxs : ∀ v ∈ φ.vars, v ∈ xs) :
    (φ.arithmetize xs).roundDegree ≤ (2 * xs.length + 1) * φ.size ^ 2 := by
  induction φ with
  | var v => simp [arithmetize, ArithQBF.roundDegree]
  | top => simp [arithmetize, ArithQBF.roundDegree]
  | bot => simp [arithmetize, ArithQBF.roundDegree]
  | not φ ih =>
    simp only [arithmetize, ArithQBF.roundDegree, size]
    exact (ih hxs).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) 2))
  | and φ ψ ihφ ihψ =>
    simp only [vars, List.mem_append] at hxs
    have h₁ := ihφ fun v hv => hxs v (Or.inl hv)
    have h₂ := ihψ fun v hv => hxs v (Or.inr hv)
    simp only [arithmetize, ArithQBF.roundDegree, size]
    refine (Nat.add_le_add h₁ h₂).trans ?_
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by nlinarith [Nat.zero_le (φ.size * ψ.size)])
  | or φ ψ ihφ ihψ =>
    simp only [vars, List.mem_append] at hxs
    have h₁ := ihφ fun v hv => hxs v (Or.inl hv)
    have h₂ := ihψ fun v hv => hxs v (Or.inr hv)
    simp only [arithmetize, ArithQBF.roundDegree, size]
    refine (Nat.add_le_add h₁ h₂).trans ?_
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by nlinarith [Nat.zero_le (φ.size * ψ.size)])
  | ex v φ ih =>
    simp only [vars, List.mem_cons] at hxs
    have hxs' : ∀ w ∈ φ.vars, w ∈ xs := fun w hw => hxs w (Or.inr hw)
    refine (roundDegree_arithmetize_op_le hxs' .ex (le_refl _) v).trans ?_
    refine (Nat.add_le_add_left (ih hxs') _).trans ?_
    rw [← Nat.mul_add, size]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  | all v φ ih =>
    simp only [vars, List.mem_cons] at hxs
    have hxs' : ∀ w ∈ φ.vars, w ∈ xs := fun w hw => hxs w (Or.inr hw)
    refine (roundDegree_arithmetize_op_le hxs' .all (le_refl _) v).trans ?_
    refine (Nat.add_le_add_left (ih hxs') _).trans ?_
    rw [← Nat.mul_add, size]
    exact Nat.mul_le_mul_left _ (by nlinarith)

omit [DecidableEq V] in
/-- Every variable of the arithmetization is a variable of `φ` or of `xs`. -/
theorem mem_vars_arithmetize {xs : List V} {φ : QBF V} {w : V}
    (h : w ∈ (φ.arithmetize xs).vars) : w ∈ φ.vars ∨ w ∈ xs := by
  induction φ with
  | var v => exact Or.inl h
  | top => exact absurd h List.not_mem_nil
  | bot => exact absurd h List.not_mem_nil
  | not φ ih => exact ih h
  | and φ ψ ihφ ihψ =>
    simp only [arithmetize, ArithQBF.vars, List.mem_append] at h
    rcases h with h | h
    · exact (ihφ h).imp_left fun h => List.mem_append_left _ h
    · exact (ihψ h).imp_left fun h => List.mem_append_right _ h
  | or φ ψ ihφ ihψ =>
    simp only [arithmetize, ArithQBF.vars, List.mem_append] at h
    rcases h with h | h
    · exact (ihφ h).imp_left fun h => List.mem_append_left _ h
    · exact (ihψ h).imp_left fun h => List.mem_append_right _ h
  | ex v φ ih =>
    rcases mem_vars_lins _ h with h | h
    · exact Or.inr h
    · rw [ArithQBF.vars, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl List.mem_cons_self
      · exact (ih h).imp_left (List.mem_cons_of_mem v)
  | all v φ ih =>
    rcases mem_vars_lins _ h with h | h
    · exact Or.inr h
    · rw [ArithQBF.vars, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl List.mem_cons_self
      · exact (ih h).imp_left (List.mem_cons_of_mem v)

omit [DecidableEq V] in
/-- The arithmetization has at most `(|xs| + 1) * size φ` operators. -/
theorem ops_arithmetize_le (xs : List V) (φ : QBF V) :
    (φ.arithmetize xs).ops ≤ (xs.length + 1) * φ.size := by
  induction φ with
  | var v => exact Nat.zero_le _
  | top => exact Nat.zero_le _
  | bot => exact Nat.zero_le _
  | not φ ih =>
    simp only [arithmetize, ArithQBF.ops, size]
    exact ih.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
  | and φ ψ ihφ ihψ =>
    simp only [arithmetize, ArithQBF.ops, size]
    nlinarith
  | or φ ψ ihφ ihψ =>
    simp only [arithmetize, ArithQBF.ops, size]
    nlinarith
  | ex v φ ih =>
    simp only [arithmetize, ArithQBF.ops_lins, ArithQBF.ops, size]
    nlinarith
  | all v φ ih =>
    simp only [arithmetize, ArithQBF.ops_lins, ArithQBF.ops, size]
    nlinarith

/-- **Every round is of small degree.** When `xs` contains every variable of `φ`, the body of
every operator of the arithmetization has degree at most `2 * size φ` in its variable. -/
theorem maxRoundDegree_arithmetize_le {xs : List V} {φ : QBF V} (hxs : ∀ v ∈ φ.vars, v ∈ xs) :
    (φ.arithmetize xs).maxRoundDegree ≤ 2 * φ.size := by
  induction φ with
  | var v => exact Nat.zero_le _
  | top => exact Nat.zero_le _
  | bot => exact Nat.zero_le _
  | not φ ih =>
    simp only [arithmetize, ArithQBF.maxRoundDegree, size]
    have := ih hxs
    omega
  | and φ ψ ihφ ihψ =>
    simp only [vars, List.mem_append] at hxs
    have := ihφ fun v hv => hxs v (Or.inl hv)
    have := ihψ fun v hv => hxs v (Or.inr hv)
    simp only [arithmetize, ArithQBF.maxRoundDegree, size]
    omega
  | or φ ψ ihφ ihψ =>
    simp only [vars, List.mem_append] at hxs
    have := ihφ fun v hv => hxs v (Or.inl hv)
    have := ihψ fun v hv => hxs v (Or.inr hv)
    simp only [arithmetize, ArithQBF.maxRoundDegree, size]
    omega
  | ex v φ ih =>
    simp only [vars, List.mem_cons] at hxs
    have hxs' : ∀ w ∈ φ.vars, w ∈ xs := fun w hw => hxs w (Or.inr hw)
    have hdeg := degBound_arithmetize_le hxs'
    have hs := one_le_size φ
    have hD : ∀ x, (ArithQBF.op .ex v (φ.arithmetize xs)).degBound x ≤ 2 * φ.size := by
      intro x
      simp only [degBound, Operator.degMul]
      split_ifs
      · omega
      · have := hdeg x
        omega
    refine (maxRoundDegree_lins_le _ xs hD (by omega)).trans (max_le (by rw [size]; omega) ?_)
    simp only [ArithQBF.maxRoundDegree, size]
    have := hdeg v
    have := ih hxs'
    omega
  | all v φ ih =>
    simp only [vars, List.mem_cons] at hxs
    have hxs' : ∀ w ∈ φ.vars, w ∈ xs := fun w hw => hxs w (Or.inr hw)
    have hdeg := degBound_arithmetize_le hxs'
    have hs := one_le_size φ
    have hD : ∀ x, (ArithQBF.op .all v (φ.arithmetize xs)).degBound x ≤ 2 * φ.size := by
      intro x
      simp only [degBound, Operator.degMul]
      split_ifs
      · omega
      · have := hdeg x
        omega
    refine (maxRoundDegree_lins_le _ xs hD (by omega)).trans (max_le (by rw [size]; omega) ?_)
    simp only [ArithQBF.maxRoundDegree, size]
    have := hdeg v
    have := ih hxs'
    omega

end QBF

end Cslib.Logic.PL
