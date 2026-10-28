/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Logics.Propositional.FiniteCSP
public import Complexity.Computability.Complexity.FineGrained.CountingNativeEndpoint
public import Complexity.Computability.Complexity.FineGrained.CountingEndpoint
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Complexity.FineGrained.CountingScale

/-!
# Fine-grained complexity of finite-domain CSPs

This module connects finite-domain constraint satisfaction problems (`FiniteCSP`) to the native
fine-grained counting endpoints (`CountingNativeEndpoint`).

For any fixed domain size `q` and arity bound `k`, each domain variable is compiled into
`b = bitWidth q` Boolean variables, yielding an equivalent CNF formula of clause width at most
`max 1 k * b` on `n * b` declared variables. Invoking the native counting endpoint
(`CountingNativeEndpoint.exists_declaredCounter`) yields exact declared-variable model counting
in time `2 ^ (O(interpolationScale (n * b))) * poly(L) = 2 ^ o(n) * poly(L)` and polynomial space
([OpenAI2026ETH], Corollary C.2).

## Main definitions

* `Cslib.Complexity.CountingFiniteCSP.encConstraint`: bitstring encoding of finite-domain
  constraints.
* `Cslib.Complexity.CountingFiniteCSP.encCSP`: bitstring encoding of finite-domain CSPs.
* `Cslib.Complexity.CountingFiniteCSP.encInput`: bitstring encoding of pairs `(n, φ)` of declared
  variable count and CSP instance.
* `Cslib.Complexity.CountingFiniteCSP.ValidFiniteKCSP`: decision language of valid, satisfiable
  finite-domain `k`-CSP instances.

## Main results

* `Cslib.Complexity.CountingFiniteCSP.exists_declaredCounter_FiniteCSP`: subexponential-time,
  polynomial-space exact model counting for finite-domain CSPs on declared scopes.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix C.2, Corollary C.2.
-/

@[expose] public section

namespace Cslib.Complexity.CountingFiniteCSP

noncomputable section

open Cslib.Logic.PL
open Cslib.Logic.PL.FiniteCSP
open Turing.MultiTapeTM
open Turing.MultiTapeTM.Universal
open Cslib.Complexity
open Cslib.Complexity.CountingNativeEndpoint
open SubexponentialSAT

/-- Flattened tuple representation of a `Constraint ℕ` used for bitstring encoding. -/
abbrev PairConstraint := List ℕ × ℕ × List (List ℕ)

/-- Bitstring encoding of flattened constraint tuples. -/
def encPairConstraint : PairConstraint ↪ List Bool :=
  encPair (encList encNat) (encPair encNat (encList (encList encNat)))

/-- Conversion from `Constraint ℕ` to its flattened representation tuple. -/
def constraintToPair (c : Constraint ℕ) : PairConstraint :=
  (c.vars, c.arity, c.forbidden)

/-- Bitstring encoding of a finite-domain constraint. -/
def encConstraint : Constraint ℕ ↪ List Bool :=
  ⟨fun c => encPairConstraint (constraintToPair c), fun c1 c2 h => by
    cases c1; cases c2
    have hinj := encPairConstraint.injective h
    simp only [constraintToPair, Prod.mk.injEq] at hinj
    obtain ⟨h1, h2, h3⟩ := hinj
    subst h1 h2 h3
    rfl⟩

/-- Bitstring encoding of a finite-domain CSP instance. -/
def encCSP : CSP ℕ ↪ List Bool :=
  encList encConstraint

/-- Bitstring encoding of declared variable budget paired with a CSP instance. -/
def encInput : ℕ × CSP ℕ ↪ List Bool :=
  encPair encUnary encCSP

/-- The decision problem for valid finite-domain CSP instances of maximum arity `k`
over domain size `q`. -/
def ValidFiniteKCSP (q k : ℕ) : Set (ℕ × CSP ℕ) :=
  {x | x.2.HasWidth k ∧ (∀ c ∈ x.2, c.vars.length = c.arity) ∧
    (∀ c ∈ x.2, ∀ v ∈ c.vars, v < x.1) ∧
    ∃ τ : Fin x.1 → Fin q, x.2.eval (fun v => if h : v < x.1 then (τ ⟨v, h⟩).val else 0) = true}

/-- **Subexponential declared-variable model counting for finite-domain CSPs.**
For fixed domain size `q` and arity bound `k`, there is an exact counter that evaluates the
compiled model count on every valid finite-domain instance of width at most `k`, in time
subexponential in `n` and polynomial space. -/
public theorem exists_declaredCounter_FiniteCSP (q k : ℕ) :
    ∃ (count : ℕ × CNF ℕ → ℕ) (T S : ℕ × CNF ℕ → ℕ) (A c e a b : ℕ),
      ComputableInO count (encPair encUnary encCNF) encNat T S ∧
      (∀ x : ℕ × CSP ℕ, x.2.HasWidth k → (∀ constr ∈ x.2, constr.vars.length = constr.arity) →
        (∀ constr ∈ x.2, ∀ v ∈ constr.vars, v < x.1) →
        count (x.1 * bitWidth q, toCNF x.2 q x.1) =
          (toCNF x.2 q x.1).modelCountOn (Finset.range (x.1 * bitWidth q))) ∧
      (∀ x : ℕ × CSP ℕ,
        (T (x.1 * bitWidth q, toCNF x.2 q x.1) : ℝ) ≤
          c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale (x.1 * bitWidth q)) *
            (((encPair encUnary encCNF (x.1 * bitWidth q, toCNF x.2 q x.1)).length : ℝ) + 1) ^ e) +
            c) ∧
      (∀ x : ℕ × CSP ℕ,
        S (x.1 * bitWidth q, toCNF x.2 q x.1) ≤
          a * ((encPair encUnary encCNF (x.1 * bitWidth q, toCNF x.2 q x.1)).length + 1) ^ b) := by
  obtain ⟨count, T, S, A, c, e, a, b, hcount, hspec, hT, hS⟩ :=
    exists_declaredCounter (max 1 k * bitWidth q)
  refine ⟨count, T, S, A, c, e, a, b, hcount, fun x hw hlen hvars => ?_,
    fun x => hT (x.1 * bitWidth q, toCNF x.2 q x.1),
    fun x => hS (x.1 * bitWidth q, toCNF x.2 q x.1)⟩
  rw [hspec]
  have hvalid := validDeclaredInput_toCNF x.2 q x.1 k hw hlen hvars
  rw [hvalid]
  simp only [ite_true]

end

end Cslib.Complexity.CountingFiniteCSP

end
