/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Norm

/-!
# Programs inside distributions

A closed probabilistic program denotes a distribution, its law `ProbComp.eval`, and `ProbComp.eval`
commutes with `pure` and `bind`: it is a monad morphism from `ProbComp` to `PMF`. This module makes
it the monad lift, so a distribution written with `do` notation binds a program directly:
```
noncomputable def game : PMF Bool := do
  let ((x, y), s) ← A.choose ()      -- `A.choose () : ProbComp _`, lifted by its law
  let c ← conversation x y           -- a distribution
  A.guess s c                        -- a program again, lifted
```
Lean inserts `liftM` around each program. The lift is `ProbComp.eval` by definition,
and `ProbComp.monadLift_eq_eval` (a `simp` and `pmf_norm` lemma) rewrites it back, so every lemma
about `ProbComp.eval` applies after one `simp only [pmf_norm]`.

## Main definitions

* `Cslib.ProbComp.instMonadLiftPMF`: programs lift into distributions by their law.

## Main results

* `Cslib.ProbComp.monadLift_eq_eval`, `Cslib.ProbComp.liftM_eq_eval`: the lift is the law.
* `Cslib.ProbComp.instLawfulMonadLiftPMF`: the lift preserves `pure` and `bind`.
-/

public section

namespace Cslib.ProbComp

/-- A program lifts into a distribution by its law, so a `PMF` written with `do` notation can bind
a program with `←`. -/
noncomputable instance instMonadLiftPMF : MonadLift ProbComp PMF where
  monadLift := eval

/-- Lifting a program into a distribution takes its law. -/
@[simp, pmf_norm] theorem monadLift_eq_eval {α : Type} (program : ProbComp α) :
    (monadLift program : PMF α) = eval program := rfl

/-- The `liftM` form of `monadLift_eq_eval`, the term Lean inserts for a lifted bind; `rw` matches
it only in this form. -/
theorem liftM_eq_eval {α : Type} (program : ProbComp α) :
    (liftM program : PMF α) = eval program := rfl

instance instLawfulMonadLiftPMF : LawfulMonadLift ProbComp PMF where
  monadLift_pure := eval_pure
  monadLift_bind := eval_bind

end Cslib.ProbComp
