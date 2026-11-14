/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Data.List.Basic
import Mathlib.Tactic.Abel

/-!
# Sampling affine solutions with bounded retries

The MAYO `SampleSolution` subroutine takes a linear system `A x = y` and an explicit randomness
vector `r`. It solves the shifted system `A x' = y - A r` and returns `x' + r`; it reports failure
whenever `A` does not have full row rank, even when this particular target is in the range. MAYO
signing tries fresh componentwise randomness in order and keeps the first successful attempt
([BeullensCamposCeliHessKannwischer2026], Section 2.1.2, Algorithm 2, pp. 8--9, and
Section 2.1.5, Algorithm 7, p. 14).

`Cslib.LinearAlgebra.AffineSolutionSolver` records only the deterministic contract of the inner
solver. It deliberately leaves the elimination algorithm abstract; a concrete implementation can
reuse `Matrix.GaussJordan`. `AffineSolutionSolver.sampleSolution` implements the source's shift,
and `retrySampleSolution` reuses `List.findSome?` for ordered first-success semantics. The latter
returns the successful attempt data along with the solution, so a client does not lose separate
randomness components such as MAYO's vinegar vectors and solution shift.

This module proves deterministic equation and failure behavior only. It does not assert that a
random input produces a uniform solution, that attempts are independent, or that a system is
surjective with any particular probability.

## Main definitions

* `Cslib.LinearAlgebra.AffineSolutionSolver`: a deterministic solver that succeeds exactly for
  surjective linear maps.
* `Cslib.LinearAlgebra.AffineSolutionSolver.sampleSolution`: solve after shifting by explicit
  randomness.
* `Cslib.LinearAlgebra.retrySampleSolution`: return the first successful attempt and solution.

## Main results

* `Cslib.LinearAlgebra.AffineSolutionSolver.map_eq_of_sampleSolution_eq_some`: every returned
  sample solves the original affine system.
* `Cslib.LinearAlgebra.AffineSolutionSolver.sampleSolution_eq_none_iff`: sampling fails exactly
  when the linear map is not surjective.
* `Cslib.LinearAlgebra.retrySampleSolution_eq_some_iff`: a successful retry is the first successful
  element of the ordered attempt list.
* `Cslib.LinearAlgebra.retrySampleSolution_eq_none_iff`: retries fail exactly when every listed
  system is nonsurjective.

## References

* [W. Beullens, F. Campos, S. Celi, B. Hess, M. J. Kannwischer, *MAYO: Round 3 Version*]
  [BeullensCamposCeliHessKannwischer2026]
-/

@[expose] public section

namespace Cslib.LinearAlgebra

variable {F U V : Type*} [Field F]
  [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]

/-- The deterministic contract of a solver for `A x = y` that accepts exactly when `A` is
surjective. In particular, a nonsurjective map is rejected even when the requested target happens
to lie in its range. This structure specifies correctness and failure, not an elimination
algorithm or a running-time bound. -/
structure AffineSolutionSolver (A : U →ₗ[F] V) where
  /-- Solve the affine system for a target, or report that `A` is not surjective. -/
  solve : V → Option U
  /-- Every returned value solves the requested system. -/
  map_eq_of_solve_eq_some {y : V} {x : U} : solve y = some x → A x = y
  /-- Failure depends only on lack of surjectivity, not on consistency for the particular target. -/
  solve_eq_none_iff_not_surjective (y : V) :
    solve y = none ↔ ¬Function.Surjective A

namespace AffineSolutionSolver

variable {A : U →ₗ[F] V} (solver : AffineSolutionSolver A)

/-- Shift by explicit randomness `r`, solve `A x' = y - A r`, and return `x' + r`.

The randomness is data supplied by the caller. This definition makes no distributional claim. -/
def sampleSolution (y : V) (r : U) : Option U :=
  (solver.solve (y - A r)).map fun x' ↦ x' + r

/-- Every successful shifted sample solves the original affine system. -/
theorem map_eq_of_sampleSolution_eq_some {y : V} {r x : U}
    (h : solver.sampleSolution y r = some x) : A x = y := by
  unfold sampleSolution at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨x', hx', rfl⟩ := h
  rw [A.map_add, solver.map_eq_of_solve_eq_some hx']
  abel

/-- Shifted sampling fails exactly when the linear map is not surjective. This preserves the
source behavior that a consistent target still fails for a rank-deficient system. -/
theorem sampleSolution_eq_none_iff (y : V) (r : U) :
    solver.sampleSolution y r = none ↔ ¬Function.Surjective A := by
  rw [sampleSolution, Option.map_eq_none_iff, solver.solve_eq_none_iff_not_surjective]

end AffineSolutionSolver

variable {Attempt : Type*}

/-- Try explicit attempt data in list order and return the first successful attempt together with
its solution. The functions `system`, `target`, and `randomness` keep the attempt's components
separate; for example, a MAYO client can put all vinegar vectors and the solution-shift vector in
`Attempt` and recover them on success.

The empty list and a list whose systems are all nonsurjective return `none`. -/
def retrySampleSolution (attempts : List Attempt)
    (system : Attempt → U →ₗ[F] V)
    (solver : (a : Attempt) → AffineSolutionSolver (system a))
    (target : Attempt → V) (randomness : Attempt → U) : Option (Attempt × U) :=
  attempts.findSome? fun a ↦
    ((solver a).sampleSolution (target a) (randomness a)).map fun x ↦ (a, x)

/-- Exact first-success semantics: a retry returns `(a, x)` exactly when the list splits at `a`,
all earlier systems are nonsurjective, and attempt `a` returns `x`. -/
theorem retrySampleSolution_eq_some_iff {attempts : List Attempt}
    {system : Attempt → U →ₗ[F] V}
    {solver : (a : Attempt) → AffineSolutionSolver (system a)}
    {target : Attempt → V} {randomness : Attempt → U} {a : Attempt} {x : U} :
    retrySampleSolution attempts system solver target randomness = some (a, x) ↔
      ∃ before after, attempts = before ++ a :: after ∧
        (solver a).sampleSolution (target a) (randomness a) = some x ∧
        ∀ a' ∈ before, ¬Function.Surjective (system a') := by
  unfold retrySampleSolution
  rw [List.findSome?_eq_some_iff]
  constructor
  · rintro ⟨before, a', after, hattempts, hcurrent, hbefore⟩
    rw [Option.map_eq_some_iff] at hcurrent
    obtain ⟨x', hx', hpair⟩ := hcurrent
    have ha : a' = a := congrArg Prod.fst hpair
    have hx : x' = x := congrArg Prod.snd hpair
    subst a'
    subst x'
    refine ⟨before, after, hattempts, hx', fun a' ha' ↦ ?_⟩
    simpa only [Option.map_eq_none_iff,
      AffineSolutionSolver.sampleSolution_eq_none_iff] using hbefore a' ha'
  · rintro ⟨before, after, hattempts, hcurrent, hbefore⟩
    refine ⟨before, a, after, hattempts, ?_, ?_⟩
    · rw [hcurrent, Option.map_some]
    · intro a' ha'
      rw [Option.map_eq_none_iff, AffineSolutionSolver.sampleSolution_eq_none_iff]
      exact hbefore a' ha'

/-- A returned attempt belongs to the input list, and its returned vector solves that attempt's
affine system. -/
theorem mem_and_map_eq_of_retrySampleSolution_eq_some {attempts : List Attempt}
    {system : Attempt → U →ₗ[F] V}
    {solver : (a : Attempt) → AffineSolutionSolver (system a)}
    {target : Attempt → V} {randomness : Attempt → U} {a : Attempt} {x : U}
    (h : retrySampleSolution attempts system solver target randomness = some (a, x)) :
    a ∈ attempts ∧ system a x = target a := by
  rw [retrySampleSolution_eq_some_iff] at h
  obtain ⟨before, after, rfl, hcurrent, -⟩ := h
  refine ⟨by simp, (solver a).map_eq_of_sampleSolution_eq_some hcurrent⟩

/-- Bounded retries fail exactly when every listed attempt has a nonsurjective system. No
probability or independence premise is hidden in this deterministic statement. -/
theorem retrySampleSolution_eq_none_iff (attempts : List Attempt)
    (system : Attempt → U →ₗ[F] V)
    (solver : (a : Attempt) → AffineSolutionSolver (system a))
    (target : Attempt → V) (randomness : Attempt → U) :
    retrySampleSolution attempts system solver target randomness = none ↔
      ∀ a ∈ attempts, ¬Function.Surjective (system a) := by
  simp only [retrySampleSolution, List.findSome?_eq_none_iff, Option.map_eq_none_iff,
    AffineSolutionSolver.sampleSolution_eq_none_iff]

end Cslib.LinearAlgebra
