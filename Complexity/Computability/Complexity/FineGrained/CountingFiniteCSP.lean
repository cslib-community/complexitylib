/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Logics.Propositional.FiniteCSP
public import Complexity.Computability.Complexity.FineGrained.CountingCSP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Complexity.FineGrained.CountingScale

/-!
# Fine-grained complexity of finite-domain CSPs

This module connects finite-domain constraint satisfaction problems (`Cslib.Logic.PL.FiniteCSP`)
to the subexponential counting endpoint for bounded-arity Boolean CSPs
(`Cslib.Complexity.CSP.exists_declaredCounter_of_finite`).

For any fixed finite domain size `q` and arity bound `k`, each domain variable is compiled into
`b = bitWidth q` Boolean variables, yielding an equivalent Boolean CSP instance of constraint scope
length at most `max 1 k * b` on `N * b` declared variables. Invoking the bounded-arity Boolean CSP
counter yields exact declared-variable model counting in time
`2 ^ (O(interpolationScale (N * b))) * poly(L) = 2 ^ o(N) * poly(L)` and polynomial space
([OpenAI2026ETH], Corollary C.2).

## Main results

* `Cslib.Complexity.CountingFiniteCSP.exists_declaredCounter_FiniteCSP`: subexponential-time,
  polynomial-space exact declared-variable model counting for finite-domain CSPs, returning
  `x.2.modelCountOn sem (Finset.range x.1)`.

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
open SubexponentialSAT

/-- **Subexponential declared-variable model counting for finite-domain CSPs.**
For any fixed domain size `q`, arity bound `k`, and finite relation alphabet `Rel` with semantics
`sem : Rel → List (Fin q) → Bool`, there is an exact counter that evaluates the declared-variable
model count `x.2.modelCountOn sem (Finset.range x.1)` on every valid finite-domain instance `x` of
width at most `k`, in time subexponential in `N` and polynomial space. -/
public theorem exists_declaredCounter_FiniteCSP {Rel : Type} [Finite Rel]
    (encRel : Rel ↪ List Bool) (q : ℕ) [Inhabited (Fin q)] (k : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) :
    let b := bitWidth q
    let enc := encPair encUnary (encCSP (encOption encRel) encNat)
    ∃ (count : ℕ × CSP (Option Rel) ℕ → ℕ) (T S : ℕ × CSP (Option Rel) ℕ → ℕ)
      (A c e a b_space : ℕ),
      ComputableInO count enc encNat T S ∧
      (∀ x : ℕ × CSP Rel ℕ,
        (∀ c ∈ x.2, c.2.length ≤ k) →
        (∀ v ∈ x.2.vars, v < x.1) →
        count (x.1 * b, toBooleanCSP q x.1 x.2) =
          x.2.modelCountOn sem (Finset.range x.1)) ∧
      (∀ x : ℕ × CSP Rel ℕ,
        (T (x.1 * b, toBooleanCSP q x.1 x.2) : ℝ) ≤
          c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale (x.1 * b)) *
            (((enc (x.1 * b, toBooleanCSP q x.1 x.2)).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x : ℕ × CSP Rel ℕ,
        S (x.1 * b, toBooleanCSP q x.1 x.2) ≤
          a * ((enc (x.1 * b, toBooleanCSP q x.1 x.2)).length + 1) ^ b_space) := by
  let b := bitWidth q
  let k' := max 1 k * b
  let sem' := semBoolean q sem
  let enc := encPair encUnary (encCSP (encOption encRel) encNat)
  obtain ⟨count, T, S, A, c, e, a, b_space, hcount, hspec, hT, hS⟩ :=
    CSP.exists_declaredCounter_of_finite (encOption encRel) k' sem'
  refine ⟨count, T, S, A, c, e, a, b_space, hcount, fun x hw hvars => ?_,
    fun x => hT (x.1 * b, toBooleanCSP q x.1 x.2),
    fun x => hS (x.1 * b, toBooleanCSP q x.1 x.2)⟩
  rw [hspec (x.1 * b, toBooleanCSP q x.1 x.2)]
  dsimp only [Prod.fst, Prod.snd]
  have hvalid := validDeclaredCSP_toBooleanCSP (q := q) hw hvars
  rw [hvalid]
  simp only [eq_self, ↓reduceIte]
  exact modelCountOn_toBooleanCSP q x.1 hq sem x.2 hvars

end

end Cslib.Complexity.CountingFiniteCSP
