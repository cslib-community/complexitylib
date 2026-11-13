/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Semantics

/-!
# Evaluating oracle programs against a deterministic oracle

`OracleComp.evalPure h prog` runs an oracle program against a total function
`h : (q : ι) → spec q` in the `Id` monad. It is the deterministic counterpart of
`OracleComp.evalWith`: evaluating with the point-mass oracle `fun q => PMF.pure (h q)` gives the
point mass at `evalPure h prog` (`OracleComp.evalWith_pure_oracle`). `OracleComp.sumPure` combines
deterministic oracles for the two sides of `spec₁ ⊕ₒ spec₂`, and `evalPure` of a lifted program
under `sumPure` only reads the matching side.

Random-oracle arguments use `evalPure` to compare an oracle program with its pure specification
once the oracle's answers are fixed
(`CslibFrontier.Languages.Probabilistic.RandomOracle.Invariant`).

## Main definitions

* `Cslib.OracleComp.evalPure`: deterministic evaluation against a total function.
* `Cslib.OracleComp.sumPure`: the deterministic oracle for `spec₁ ⊕ₒ spec₂` built from one for
  each side.

## Main results

* `Cslib.OracleComp.evalPure_bind`, `Cslib.OracleComp.evalPure_mapM`,
  `Cslib.OracleComp.evalPure_foldlM`: `evalPure` commutes with the monad operations.
* `Cslib.OracleComp.evalWith_pure_oracle`: evaluation against point masses.
* `Cslib.OracleComp.evalPure_liftLeft`, `Cslib.OracleComp.evalPure_liftRight`: lifted programs
  read only their own side of `sumPure`.
-/

@[expose] public section

namespace Cslib

namespace OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α β : Type v}

/-- Evaluate an oracle program deterministically against a pure function `h : (q : ι) → spec q`
in the `Id` monad. -/
def evalPure (h : (q : ι) → spec q) (prog : OracleComp spec α) : α :=
  (interpret (m := Id) (fun q => pure (h q)) prog).run

@[simp]
theorem evalPure_pure (h : (q : ι) → spec q) (a : α) :
    evalPure h (pure a : OracleComp spec α) = a := rfl

@[simp]
theorem evalPure_query (h : (q : ι) → spec q) (q : ι) :
    evalPure h (query (spec := spec) q) = h q := rfl

@[simp]
theorem evalPure_bind (h : (q : ι) → spec q) (prog : OracleComp spec α)
    (cont : α → OracleComp spec β) :
    evalPure h (prog >>= cont) = evalPure h (cont (evalPure h prog)) := by
  simp [evalPure]

@[simp]
theorem evalPure_map (h : (q : ι) → spec q) (f : α → β) (prog : OracleComp spec α) :
    evalPure h (f <$> prog) = f (evalPure h prog) := by
  rw [← bind_pure_comp, evalPure_bind, evalPure_pure]

@[simp]
theorem evalPure_mapM {γ : Type v} (h : (q : ι) → spec q)
    (f : γ → OracleComp spec α) (xs : List γ) :
    evalPure h (xs.mapM f) = xs.map (fun x => evalPure h (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, evalPure_bind, evalPure_pure, List.map_cons, ih]

@[simp]
theorem evalPure_foldlM {γ : Type v} (h : (q : ι) → spec q)
    (f : α → γ → OracleComp spec α) (init : α) (xs : List γ) :
    evalPure h (xs.foldlM f init) = xs.foldl (fun acc x => evalPure h (f acc x)) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldlM_cons, evalPure_bind, List.foldl_cons, ih]

/-- Evaluating an oracle program with `PMF.pure (h q)` produces the point mass at `evalPure h`. -/
@[simp]
theorem evalWith_pure_oracle (h : (q : ι) → spec q) (prog : OracleComp spec α) :
    evalWith (fun q => PMF.pure (h q)) prog = PMF.pure (evalPure h prog) := by
  induction prog using OracleComp.induction with
  | pure a => rfl
  | query_bind q cont ih =>
    simp only [evalWith_bind, evalWith_query, PMF.pure_bind, evalPure_bind, evalPure_query]
    exact ih (h q)

/-- Combine two deterministic oracles into a deterministic oracle for `spec₁ ⊕ₒ spec₂`. -/
def sumPure {ι₁ : Type u} {ι₂ : Type u} {spec₁ : OracleSpec.{u, v} ι₁}
    {spec₂ : OracleSpec.{u, v} ι₂} (h₁ : (q : ι₁) → spec₁ q) (h₂ : (q : ι₂) → spec₂ q) :
    (q : ι₁ ⊕ ι₂) → (spec₁ ⊕ₒ spec₂) q
  | .inl q => h₁ q
  | .inr q => h₂ q

@[simp]
theorem sumPure_inl {ι₁ : Type u} {ι₂ : Type u} {spec₁ : OracleSpec.{u, v} ι₁}
    {spec₂ : OracleSpec.{u, v} ι₂} (h₁ : (q : ι₁) → spec₁ q) (h₂ : (q : ι₂) → spec₂ q)
    (q : ι₁) : sumPure h₁ h₂ (.inl q) = h₁ q := rfl

@[simp]
theorem sumPure_inr {ι₁ : Type u} {ι₂ : Type u} {spec₁ : OracleSpec.{u, v} ι₁}
    {spec₂ : OracleSpec.{u, v} ι₂} (h₁ : (q : ι₁) → spec₁ q) (h₂ : (q : ι₂) → spec₂ q)
    (q : ι₂) : sumPure h₁ h₂ (.inr q) = h₂ q := rfl

@[simp]
theorem evalPure_liftLeft {ι₁ : Type u} {ι₂ : Type u} {spec₁ : OracleSpec.{u, v} ι₁}
    {spec₂ : OracleSpec.{u, v} ι₂} (h₁ : (q : ι₁) → spec₁ q) (h₂ : (q : ι₂) → spec₂ q)
    (prog : OracleComp spec₁ α) :
    evalPure (sumPure h₁ h₂) (liftLeft (spec₂ := spec₂) prog) = evalPure h₁ prog := by
  induction prog using OracleComp.induction with
  | pure a => rfl
  | query_bind q cont ih =>
    simp only [liftLeft_bind, liftLeft_query, evalPure_bind, evalPure_query, sumPure_inl]
    exact ih (h₁ q)

@[simp]
theorem evalPure_liftRight {ι₁ : Type u} {ι₂ : Type u} {spec₁ : OracleSpec.{u, v} ι₁}
    {spec₂ : OracleSpec.{u, v} ι₂} (h₁ : (q : ι₁) → spec₁ q) (h₂ : (q : ι₂) → spec₂ q)
    (prog : OracleComp spec₂ α) :
    evalPure (sumPure h₁ h₂) (liftRight (spec₁ := spec₁) prog) = evalPure h₂ prog := by
  induction prog using OracleComp.induction with
  | pure a => rfl
  | query_bind q cont ih =>
    simp only [liftRight_bind, liftRight_query, evalPure_bind, evalPure_query, sumPure_inr]
    exact ih (h₂ q)

end OracleComp

end Cslib
