/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.PPZ

/-!
# PPSZ with w-implication: definitions

The PPSZ algorithm of Paturi, Pudlák, Saks and Zane processes the variables of a CNF formula in a
uniformly random order, like PPZ (`Cslib.Complexity.PPZ.round`). A variable is set to a value
when that value is *w-implied*: some subformula of at most `w` clauses, together with the values
already chosen, forces it. Otherwise the variable is set uniformly at random. This is PPSZ with
w-implication [Hertli, Definition 3][Hertli2011] [Scheder, Algorithm 1][Scheder2021]; the analysis
of [Paturi, Pudlák, Saks, Zane][PaturiPudlakSaksZane2005] uses nothing about its bounded
resolution beyond this property [Scheder, p. 3][Scheder2021]. [Hertli][Hertli2011] calls this
*s-implication*: his `s` is our `w`, a number of clauses. It is unrelated to the `s` of
[Paturi, Pudlák, Saks, Zane][PaturiPudlakSaksZane2005], whose `s`-bounded resolution only
considers clauses of at most `s` literals.

PPZ and PPSZ are both rounds with values proposed by an oracle (`Cslib.Complexity.PPZ.roundWith`):
PPZ asks for unit clauses, PPSZ for w-implied values (`implied`).

## Main definitions

* `Cslib.Complexity.PPSZ.WImplied`: a subformula of at most `w` clauses implies `x = b` under
  a partial assignment.
* `Cslib.Complexity.PPSZ.implied`: the value implied on a variable, if any.
* `Cslib.Complexity.PPSZ.run`: the first `i` steps of a round in a fixed order.
* `Cslib.Complexity.PPSZ.round`: one round of PPSZ, in a uniformly random order.

## References

* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
* [T. Hertli, *3-SAT faster and simpler*][Hertli2011]
* [D. Scheder, *PPSZ is better than you think*][Scheder2021]
-/

@[expose] public section

namespace Cslib.Complexity.PPSZ

open Cslib.Logic.PL Finset

variable {n : ℕ}

/-- **w-implication.** Under the partial assignment `τ`, the literal `x = b` is implied by a
subformula of `φ` with at most `w` clauses: every total assignment extending `τ` that satisfies
the subformula sets `x` to `b`. -/
def WImplied (φ : CNF (Fin n)) (w : ℕ) (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) :
    Prop :=
  ∃ ψ : CNF (Fin n), (∀ c ∈ ψ, c ∈ φ) ∧ ψ.length ≤ w ∧
    ∀ σ : Fin n → Bool, (∀ y c, τ y = some c → σ y = c) → ψ.eval σ = true → σ x = b

open Classical in
/-- The value w-implied on `x` under `τ`, if any (`true` is preferred if both are implied, which
happens only when no extension of `τ` satisfies `φ`). -/
noncomputable def implied (φ : CNF (Fin n)) (w : ℕ) (τ : Fin n → Option Bool) (x : Fin n) :
    Option Bool :=
  if WImplied φ w τ x true then some true
  else if WImplied φ w τ x false then some false else none

/-- `WImplied` is decidable, classically, as in `implied`. -/
noncomputable instance instDecidableWImplied (φ : CNF (Fin n)) (w : ℕ)
    (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) : Decidable (WImplied φ w τ x b) :=
  Classical.dec _

/-- One step of PPSZ on `x`: the implied value if there is one, and a uniform bit otherwise. -/
noncomputable def step (φ : CNF (Fin n)) (w : ℕ) (τ : Fin n → Option Bool) (x : Fin n) :
    PMF Bool :=
  PPZ.stepWith (implied φ w) τ x

/-- **The first `i` steps of a PPSZ round** in the order `π`: the variable `π j` is processed at
step `j`. This is the run of PPZ (`Cslib.Complexity.PPZ.runWith`) with w-implication in place
of unit clauses. -/
noncomputable def run (φ : CNF (Fin n)) (w : ℕ) (π : Equiv.Perm (Fin n)) :
    ℕ → PMF (Fin n → Option Bool) :=
  PPZ.runWith (implied φ w) π

/-- **One round of PPSZ** with w-implication: process all variables in a uniformly random
order. -/
noncomputable def round (φ : CNF (Fin n)) (w : ℕ) : PMF (Fin n → Option Bool) :=
  PPZ.roundWith (implied φ w)

end Cslib.Complexity.PPSZ
