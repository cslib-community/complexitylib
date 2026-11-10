/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Basic

/-!
# Sums of oracle interfaces

A program may call two interfaces at once: a query of `spec₁ ⊕ₒ spec₂` is a query of either,
answered as there. A program with private coins is the main instance (`probOracleSpec`), with
uniform sampling on the left; a forger calling a signer and a hash function, and the prover and
verifier oracles of an interactive protocol, are others.

`OracleComp.sumHandler left right` answers the two kinds of call with handlers in the same monad,
and `OracleComp.liftLeft` and `OracleComp.liftRight` embed a program over one side. Interpreting
an embedded program uses only the corresponding handler (`interpret_sumHandler_liftLeft`).

## Main definitions

* `Cslib.OracleSpec.sum`, notation `spec₁ ⊕ₒ spec₂`: the disjoint sum of two interfaces.
* `Cslib.OracleSpec.empty`: the interface without queries.
* `Cslib.OracleComp.sumHandler`: answer the two sides with separate handlers.
* `Cslib.OracleComp.liftLeft`, `Cslib.OracleComp.liftRight`: embed a program over one side.

## Main results

* `Cslib.OracleComp.interpret_sumHandler_liftLeft`,
  `Cslib.OracleComp.interpret_sumHandler_liftRight`: an embedded program uses only its own side's
  handler.
* `Cslib.OracleComp.interpret_sumHandler`: interpretation distributes over the two sides.

## References

* For the underlying oracle-program design, see the
  [VCVio](https://github.com/Verified-zkEVM/VCVio) credit in `Languages.Probabilistic.Basic`.
-/

@[expose] public section

namespace Cslib

universe u v w

/-- The disjoint sum of two interfaces: a query of either, answered as there. -/
abbrev OracleSpec.sum {ι₁ ι₂ : Type u} (spec₁ : OracleSpec.{u, v} ι₁)
    (spec₂ : OracleSpec.{u, v} ι₂) : OracleSpec.{u, v} (ι₁ ⊕ ι₂)
  | .inl q => spec₁ q
  | .inr q => spec₂ q

@[inherit_doc] scoped infixr:65 " ⊕ₒ " => OracleSpec.sum

/-- The interface without queries, for a party that uses no oracle. -/
abbrev OracleSpec.empty : OracleSpec.{0, v} Empty := fun q => q.elim

namespace OracleComp

variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, v} ι₁} {spec₂ : OracleSpec.{u, v} ι₂}
  {α β : Type v}

/-- Answer the calls of the left interface with `left` and those of the right with `right`. -/
abbrev sumHandler {m : Type v → Type w} (left : (q : ι₁) → m (spec₁ q))
    (right : (q : ι₂) → m (spec₂ q)) : (q : ι₁ ⊕ ι₂) → m ((spec₁ ⊕ₒ spec₂) q)
  | .inl q => left q
  | .inr q => right q

/-- `sumHandler` answers a left query `.inl q` with `left q`. -/
theorem sumHandler_inl {m : Type v → Type w} (left : (q : ι₁) → m (spec₁ q))
    (right : (q : ι₂) → m (spec₂ q)) (q : ι₁) : sumHandler left right (.inl q) = left q := rfl

/-- `sumHandler` answers a right query `.inr q` with `right q`. -/
theorem sumHandler_inr {m : Type v → Type w} (left : (q : ι₁) → m (spec₁ q))
    (right : (q : ι₂) → m (spec₂ q)) (q : ι₂) : sumHandler left right (.inr q) = right q := rfl

/-- A program over the left interface, as a program over the sum. -/
def liftLeft (program : OracleComp spec₁ α) : OracleComp (spec₁ ⊕ₒ spec₂) α :=
  interpret (fun q => query (spec := spec₁ ⊕ₒ spec₂) (.inl q)) program

/-- A program over the right interface, as a program over the sum. -/
def liftRight (program : OracleComp spec₂ α) : OracleComp (spec₁ ⊕ₒ spec₂) α :=
  interpret (fun q => query (spec := spec₁ ⊕ₒ spec₂) (.inr q)) program

/-- Lifting `pure a` from the left interface yields `pure a`. -/
@[simp] theorem liftLeft_pure (a : α) :
    liftLeft (spec₂ := spec₂) (pure a : OracleComp spec₁ α) = pure a := rfl

/-- Lifting `pure a` from the right interface yields `pure a`. -/
@[simp] theorem liftRight_pure (a : α) :
    liftRight (spec₁ := spec₁) (pure a : OracleComp spec₂ α) = pure a := rfl

/-- `liftLeft` commutes with monadic bind `>>=`. -/
@[simp] theorem liftLeft_bind (program : OracleComp spec₁ α) (next : α → OracleComp spec₁ β) :
    liftLeft (spec₂ := spec₂) (program >>= next) =
      liftLeft program >>= fun a => liftLeft (next a) :=
  interpret_bind _ _ _

/-- `liftRight` commutes with monadic bind `>>=`. -/
@[simp] theorem liftRight_bind (program : OracleComp spec₂ α) (next : α → OracleComp spec₂ β) :
    liftRight (spec₁ := spec₁) (program >>= next) =
      liftRight program >>= fun a => liftRight (next a) :=
  interpret_bind _ _ _

/-- `liftLeft` commutes with functorial map `<$>`. -/
@[simp] theorem liftLeft_map (f : α → β) (program : OracleComp spec₁ α) :
    liftLeft (spec₂ := spec₂) (f <$> program) = f <$> liftLeft program :=
  interpret_map _ _ _

/-- `liftRight` commutes with functorial map `<$>`. -/
@[simp] theorem liftRight_map (f : α → β) (program : OracleComp spec₂ α) :
    liftRight (spec₁ := spec₁) (f <$> program) = f <$> liftRight program :=
  interpret_map _ _ _

/-- Lifting a single query `query q` from the left interface produces `query (.inl q)`. -/
@[simp] theorem liftLeft_query (q : ι₁) :
    liftLeft (spec₂ := spec₂) (query q) = query (spec := spec₁ ⊕ₒ spec₂) (.inl q) :=
  interpret_query _ _

/-- Lifting a single query `query q` from the right interface produces `query (.inr q)`. -/
@[simp] theorem liftRight_query (q : ι₂) :
    liftRight (spec₁ := spec₁) (query q) = query (spec := spec₁ ⊕ₒ spec₂) (.inr q) :=
  interpret_query _ _

variable {m : Type v → Type w} [Monad m] [LawfulMonad m]

/-- An embedded left program uses only the left handler. -/
@[simp] theorem interpret_sumHandler_liftLeft (left : (q : ι₁) → m (spec₁ q))
    (right : (q : ι₂) → m (spec₂ q)) (program : OracleComp spec₁ α) :
    interpret (sumHandler left right) (liftLeft program) = interpret left program := by
  simp [liftLeft, interpret_interpret]

/-- An embedded right program uses only the right handler. -/
@[simp] theorem interpret_sumHandler_liftRight (left : (q : ι₁) → m (spec₁ q))
    (right : (q : ι₂) → m (spec₂ q)) (program : OracleComp spec₂ α) :
    interpret (sumHandler left right) (liftRight program) = interpret right program := by
  simp [liftRight, interpret_interpret]

omit [LawfulMonad m] in
/-- Interpretation distributes over the two sides of a combined handler. -/
theorem interpret_sumHandler {κ : Type u} {target : OracleSpec.{u, v} κ}
    (oracle : (q : κ) → m (target q)) (left : (q : ι₁) → OracleComp target (spec₁ q))
    (right : (q : ι₂) → OracleComp target (spec₂ q)) :
    (fun q => interpret oracle (sumHandler left right q)) =
      sumHandler (fun q => interpret oracle (left q)) (fun q => interpret oracle (right q)) := by
  funext q
  cases q <;> rfl

end OracleComp

end Cslib
