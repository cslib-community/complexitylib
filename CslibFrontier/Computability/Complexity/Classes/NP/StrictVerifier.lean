/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Length-checked verifiers

An `NP` verifier `V` is only required by `Cslib.Complexity.IsVerifier` to decide membership when
given a certificate of the prescribed length `p |enc a|`; its behavior on shorter or longer strings
is unconstrained. Wrapping `V` in `Cslib.Complexity.strictVerifier` adds an explicit polynomial-time
check that the certificate has length `p |enc a|`.

Because the guarded verifier checks the length itself, an instance belongs to the problem iff some
certificate of any length is accepted (`IsVerifier.exists_strictVerifier_eq_true_iff`). In Fagin's
theorem the existential second-order sentence can therefore guess where the certificate ends
without evaluating the polynomial `p` in first-order logic.

## Main definitions

* `Cslib.Complexity.strictVerifier`: a verifier guarded by the certificate-length check
  `w.length == p.eval (enc a).length`.

## Main results

* `Cslib.Complexity.IsVerifier.strictVerifier`: `strictVerifier` verifies the same problem with the
  same certificate polynomial.
* `Cslib.Complexity.computableInPolyTime_strictVerifier`: `strictVerifier` is computable in
  polynomial time when `V` is.
* `Cslib.Complexity.IsVerifier.exists_strictVerifier_eq_true_iff`: with the guard, membership is
  acceptance of some certificate of any length.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

variable {α : Type}

/-- A verifier augmented with an explicit check that the certificate has the prescribed length
`p.eval (enc a).length`. -/
def strictVerifier (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (x : α × List Bool) : Bool :=
  (x.2.length == p.eval (enc x.1).length) && V x

@[simp]
theorem strictVerifier_eq_true_iff (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (a : α) (w : List Bool) :
    strictVerifier enc p V (a, w) = true ↔
      w.length = p.eval (enc a).length ∧ V (a, w) = true := by
  simp [strictVerifier]

theorem length_eq_of_strictVerifier_eq_true {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {a : α} {w : List Bool}
    (h : strictVerifier enc p V (a, w) = true) :
    w.length = p.eval (enc a).length :=
  ((strictVerifier_eq_true_iff enc p V a w).1 h).1

/-- Guarding a verifier by its certificate-length check preserves `IsVerifier`. -/
theorem IsVerifier.strictVerifier {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {A : Set α} (hV : IsVerifier enc p V A) :
    IsVerifier enc p (Cslib.Complexity.strictVerifier enc p V) A := by
  intro a
  rw [hV a]
  simp [strictVerifier_eq_true_iff]

/-- Because `strictVerifier` checks the certificate length itself, an instance belongs to `A` iff
some certificate of any length is accepted. -/
theorem IsVerifier.exists_strictVerifier_eq_true_iff {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {A : Set α} (hV : IsVerifier enc p V A) (a : α) :
    a ∈ A ↔ ∃ w : List Bool, Cslib.Complexity.strictVerifier enc p V (a, w) = true := by
  rw [hV a]
  simp [strictVerifier_eq_true_iff]

/-- Guarding a polynomial-time verifier by its certificate-length check preserves polynomial-time
computability. -/
@[fun_prop]
theorem computableInPolyTime_strictVerifier (enc : α ↪ List Bool) (p : Polynomial ℕ)
    {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    ComputableInPolyTime (strictVerifier enc p V) (encPair enc encBits) encBool := by
  unfold strictVerifier
  fun_prop

end Cslib.Complexity
