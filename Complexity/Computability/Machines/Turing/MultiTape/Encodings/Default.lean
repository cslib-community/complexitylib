/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public meta import Lean.Elab.Term
public meta import Lean.Meta.Transform

/-!
# Explicitly selected default encodings

Encoding terms are often determined by a type. `enc%` selects the encoding registered for the type
demanded by its expected type, so that a statement need not repeat it:

```lean
ComputableInPolyTime (fun q : List ℕ × ℕ => q.2 :: q.1) enc% enc%
```

A default is used only where `enc%` is written. `DefaultEnc` is a registry read at elaboration
time: it is not a parameter of any predicate, and `enc%` elaborates to the registered term itself,
here `encPair (encList encNat) encNat` and `encList encNat`. Statements, `fun_prop` and the
capability classes therefore see ordinary encoding terms, and goals display them in full.

`ℕ` defaults to `encNat`, so unary positions stay visible as `encUnary`. A section whose types have
another natural encoding registers it with a `local instance`. `ℤ` has no default: the library uses
more than one encoding of it, and an unregistered type is an error rather than a guess.

Curated abstracts are rendered from their source, so they should keep spelling encodings out.

## Main definitions

* `Turing.MultiTapeTM.DefaultEnc`: the registry of default encodings.
* `enc%`: the registered encoding of the expected type.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- The registered default encoding of `α`. It is read by `enc%` and does not occur in the terms
that `enc%` produces. -/
class DefaultEnc (α : Type) where
  /-- The registered encoding. Use `enc%` rather than this projection. -/
  enc : α ↪ List Bool

instance : DefaultEnc ℕ := ⟨encNat⟩
instance : DefaultEnc Bool := ⟨encBool⟩
instance : DefaultEnc SignType := ⟨encSign⟩

instance {α β : Type} [DefaultEnc α] [DefaultEnc β] : DefaultEnc (α × β) :=
  ⟨encPair DefaultEnc.enc DefaultEnc.enc⟩

instance {α : Type} [DefaultEnc α] : DefaultEnc (List α) := ⟨encList DefaultEnc.enc⟩

instance {α : Type} [DefaultEnc α] : DefaultEnc (Option α) := ⟨encOption DefaultEnc.enc⟩

/-- Raw bit strings take precedence over a list of encoded Booleans. -/
instance (priority := high) : DefaultEnc (List Bool) := ⟨encBits⟩

end Turing.MultiTapeTM

end

public meta section

namespace Turing.MultiTapeTM

open Lean Meta Elab Term

/-- Replace each `DefaultEnc.enc inst` by the registered term, leaving that term's own definitions
and abbreviations folded. -/
private partial def eraseDefaultEnc (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    unless x.isAppOfArity ``DefaultEnc.enc 2 do return .continue
    let some y ← withReducibleAndInstances (unfoldProjInst? x) |
      throwError "enc%: cannot unfold the registered encoding{indentExpr x}"
    return .visit y)

/-- `enc%` is the encoding registered with `DefaultEnc` for the type demanded by its expected type
`α ↪ List Bool`. It elaborates to the registered term, with no trace of `DefaultEnc`. -/
elab "enc%" : term <= expected => do
  let expected ← tryPostponeIfHasMVars (some expected) "enc%"
  let some (α, _) := expected.app2? ``Function.Embedding |
    throwError "enc%: expected an encoding `α ↪ List Bool`, got{indentExpr expected}"
  let inst ← try synthInstance (← mkAppM ``DefaultEnc #[α])
    catch _ => throwError "enc%: no default encoding is registered for{indentExpr α}"
  eraseDefaultEnc (← mkAppOptM ``DefaultEnc.enc #[α, inst])

end Turing.MultiTapeTM
