/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate (Batteries, `Batteries/Data/Except.lean`)

public import CslibFrontier.Init

/-!
# Sequencing and observing `Except`

Core and Batteries state how `<$>` acts on `Except.ok` and `Except.error`, but not `>>=`, and
nothing about `Except.toOption`, which forgets which error occurred. These equations let `simp`
evaluate `do` blocks over `Except` and compare computations up to the error they raise.

## Main results

* `Except.ok_bind`, `Except.error_bind`: `>>=` on a result and on an error.
* `Except.bind_eq_ok`: a sequenced computation succeeds when both steps do.
* `Except.toOption_bind`, `Except.toOption_map`: observing success commutes with sequencing.
-/

public section

namespace Except

universe u v

variable {ε : Type u} {α β : Type v}

@[simp] theorem ok_bind (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

@[simp] theorem error_bind (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = .error e := rfl

theorem bind_eq_ok {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp

@[simp] theorem toOption_ok (a : α) : (Except.ok a : Except ε α).toOption = some a := rfl

@[simp] theorem toOption_error (e : ε) : (Except.error e : Except ε α).toOption = none := rfl

theorem toOption_bind (x : Except ε α) (f : α → Except ε β) :
    (x >>= f).toOption = x.toOption.bind fun a => (f a).toOption := by
  cases x <;> rfl

theorem toOption_map (f : α → β) (x : Except ε α) : (f <$> x).toOption = f <$> x.toOption := by
  cases x <;> rfl

end Except
