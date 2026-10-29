/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Logics.Propositional.CSP.ToBoolean
public import Complexity.Computability.Complexity.FineGrained.CountingCSP

/-!
# Fine-grained complexity of finite-domain CSPs: Boolean counting transfer

This module connects finite-domain constraint satisfaction problems
(`Cslib.Logic.PL.CSP.toBoolean`) to the subexponential counting endpoint for bounded-arity
Boolean CSPs (`Cslib.Complexity.CSP.exists_declaredCounter_of_finite`).

For any fixed finite domain size `q` and arity bound `k`, each domain variable is compiled into
`b = CSP.bitWidth q` Boolean variables. The Boolean instance has constraint scope length at most
`max 1 k * b` on `N * b` declared variables. Evaluating the bounded-arity Boolean
CSP counter on the compiled Boolean instance computes the exact declared-variable model count.
Its time bound has factor `2^(A * interpolationScale (N * b))` multiplied by a polynomial in the
compiled Boolean encoding length; space is polynomial in that compiled encoding length
([OpenAI2026ETH], Corollary C.2 / Theorem 1.1, paraphrased and extended to finite domains via binary
validity constraints). No bound on the compilation cost or on the compiled encoding length in
terms of the native finite-domain input is proved here; those remain open in #1326, Milestone 2.

## Main results

* `Cslib.Complexity.CSP.exists_declaredCounter_toBoolean`: transfer lemma establishing that
  evaluating the bounded-arity Boolean CSP counter on the compiled Boolean instance computes
  the exact finite-domain model count `x.2.modelCountOn sem (Finset.range x.1)`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix C.2, Corollary C.2.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL
open Turing.MultiTapeTM
open Turing.MultiTapeTM.Universal
open SubexponentialSAT

/-- **Declared-variable model counting transfer via Boolean compilation.**
For any fixed domain size `q`, arity bound `k`, and finite relation alphabet `Rel` with semantics
`sem : Rel → List (Fin q) → Bool`, evaluating the bounded-arity Boolean CSP counter on the
compiled Boolean instance `(x.1 * CSP.bitWidth q, x.2.toBoolean q x.1)` computes the exact
declared-variable model count `x.2.modelCountOn sem (Finset.range x.1)` for every valid
finite-domain instance `x` of constraint width at most `k`.

This is a one-way counting transfer through the Boolean endpoint ([OpenAI2026ETH], Corollary C.2 /
Theorem 1.1). The machine consumes the compiled Boolean encoding: time has factor
`2^(A * interpolationScale (N * b))` times a polynomial in that encoding length, and space is
polynomial in that length. Bounding the compiled encoding in terms of the native finite-domain
input, proving `toBoolean` polynomial-time and composing it into a counter on native encodings
remain open in #1326, Milestone 2. -/
public theorem CSP.exists_declaredCounter_toBoolean {Rel : Type} [Finite Rel]
    (encRel : Rel ↪ List Bool) (q : ℕ) [Inhabited (Fin q)] (k : ℕ)
    (sem : Rel → List (Fin q) → Bool) :
    let b := CSP.bitWidth q
    let enc := encPair encUnary (encCSP (encOption encRel) encNat)
    ∃ (count : ℕ × CSP (Option Rel) ℕ → ℕ) (T S : ℕ × CSP (Option Rel) ℕ → ℕ)
      (A c e a b_space : ℕ),
      ComputableInO count enc encNat T S ∧
      (∀ x : ℕ × CSP Rel ℕ,
        (∀ c ∈ x.2, c.2.length ≤ k) →
        (∀ v ∈ x.2.vars, v < x.1) →
        count (x.1 * b, x.2.toBoolean q x.1) =
          x.2.modelCountOn sem (Finset.range x.1)) ∧
      (∀ x : ℕ × CSP Rel ℕ,
        (T (x.1 * b, x.2.toBoolean q x.1) : ℝ) ≤
          c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale (x.1 * b)) *
            (((enc (x.1 * b, x.2.toBoolean q x.1)).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x : ℕ × CSP Rel ℕ,
        S (x.1 * b, x.2.toBoolean q x.1) ≤
          a * ((enc (x.1 * b, x.2.toBoolean q x.1)).length + 1) ^ b_space) := by
  let b := CSP.bitWidth q
  let k' := max 1 k * b
  let sem' := CSP.semBoolean q sem
  let enc := encPair encUnary (encCSP (encOption encRel) encNat)
  obtain ⟨count, T, S, A, c, e, a, b_space, hcount, hspec, hT, hS⟩ :=
    CSP.exists_declaredCounter_of_finite (encOption encRel) k' sem'
  refine ⟨count, T, S, A, c, e, a, b_space, hcount, fun x hw hvars => ?_,
    fun x => hT (x.1 * b, x.2.toBoolean q x.1),
    fun x => hS (x.1 * b, x.2.toBoolean q x.1)⟩
  rw [hspec (x.1 * b, x.2.toBoolean q x.1)]
  dsimp only [Prod.fst, Prod.snd]
  have hvalid := CSP.validDeclaredCSP_toBoolean (q := q) hw hvars
  rw [hvalid]
  simp only [eq_self, ↓reduceIte]
  exact CSP.modelCountOn_toBoolean q x.1 sem x.2 hvars

end Cslib.Complexity
